"""Arithmetic-aware Z3 translation (Real/Int) and SMT solving over the theory of numbers.

The default ``Node.to_z3`` translates every term into a single *uninterpreted*
sort, so arithmetic is opaque to it: ``x + 1 = 2 ∧ x > 0`` cannot be solved and
``∀x (x * 2 = x + x)`` cannot be proved valid, because ``+``, ``*``, ``>`` and the
numeric literals carry no meaning. This module instead interprets numbers,
arithmetic functions, and comparisons in Z3's theory of reals (or integers), so
those formulas are decided by genuine arithmetic reasoning.

Translation rules (see ``to_z3_arith``):

* ``Number``                       → ``z3.RealVal``/``z3.IntVal``.
* ``Variable`` / ``Constant``      → a Real/Int constant named after the symbol.
* ``Function`` ``+ - * /`` (binary) → the matching Z3 arithmetic operator.
* other ``Function``               → an uninterpreted function over the numeric sort.
* ``Atom`` ``= ≠ < > ≤ ≥`` (binary) → the matching Z3 comparison.
* other ``Atom`` (predicate)       → an uninterpreted (numeric-sort)→Bool function.
* ``Not/And/Or/Xor/Implies/Iff``   → the matching Z3 connective.
* ``Quantifier``                   → ``z3.ForAll``/``z3.Exists`` over the bound
  variable's numeric constant.

Sorted quantifiers, sorted constants, and Łukasiewicz operators are first lowered
to classical FOL with :func:`unicode_fol_kit.fol.nodes.to_fol`; the sort guards
introduced there become uninterpreted predicates over the numeric sort. Lambda
nodes have no first-order meaning and raise ``TypeError`` (beta-reduce and
lambda-eliminate them first).
"""

from typing import Dict, Optional

import z3

from ..fol.nodes import (
    Node, to_fol,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)


# Node types that must be eliminated (lowered to classical FOL) before the
# arithmetic translation can run.
_MSFL_NODES = (
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
)

# Lambda-calculus nodes have no first-order arithmetic meaning.
_LAMBDA_NODES = (LambdaVar, Lambda, Application)

_ARITH_OPS = frozenset({"+", "-", "*", "/"})


class ArithEnv:
    """Caches Z3 declarations for an arithmetic translation over one numeric sort.

    A single environment is threaded through a whole formula so that every
    occurrence of a name maps to the same Z3 declaration. The numeric sort is
    fixed at construction: ``'real'`` (the default) uses ``z3.RealSort`` and
    ``'int'`` uses ``z3.IntSort``.
    """

    def __init__(self, sort: str = "real"):
        """Initialise empty symbol/function/predicate tables for the given sort.

        Args:
            sort: ``'real'`` or ``'int'``; selects the Z3 numeric sort that every
                term lives in. Any other value raises ``ValueError``.
        """
        if sort not in ("real", "int"):
            raise ValueError(f"sort must be 'real' or 'int', got {sort!r}")
        self.sort_name = sort
        self.sort = z3.RealSort() if sort == "real" else z3.IntSort()
        self.symbols: Dict[str, z3.ExprRef] = {}
        self.funcs: Dict[str, z3.FuncDeclRef] = {}
        self.preds: Dict[str, z3.FuncDeclRef] = {}

    def num(self, value) -> z3.ExprRef:
        """Return a Z3 numeric literal for ``value`` in this environment's sort."""
        return z3.RealVal(value) if self.sort_name == "real" else z3.IntVal(value)

    def get_symbol(self, name: str) -> z3.ExprRef:
        """Get or create a Z3 numeric constant for a variable or constant name."""
        if name not in self.symbols:
            self.symbols[name] = z3.Const(name, self.sort)
        return self.symbols[name]

    def get_func(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted function mapping (numeric sort)^arity → numeric sort."""
        if name not in self.funcs:
            self.funcs[name] = z3.Function(name, *([self.sort] * arity), self.sort)
        return self.funcs[name]

    def get_pred(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted predicate mapping (numeric sort)^arity → Bool."""
        if name not in self.preds:
            self.preds[name] = z3.Function(name, *([self.sort] * arity), z3.BoolSort())
        return self.preds[name]


def _term_to_z3(node: Node, env: ArithEnv) -> z3.ExprRef:
    """Translate a term-position node (number, symbol, or arithmetic/uninterpreted function)."""
    if isinstance(node, Number):
        return env.num(node.value)
    if isinstance(node, (Variable, Constant)):
        return env.get_symbol(node.name)
    if isinstance(node, Function):
        args = [_term_to_z3(a, env) for a in node.args]
        if node.name in _ARITH_OPS and len(args) == 2:
            left, right = args
            if node.name == "+":
                return left + right
            if node.name == "-":
                return left - right
            if node.name == "*":
                return left * right
            return left / right  # node.name == "/"
        return env.get_func(node.name, len(node.args))(*args)
    if isinstance(node, _LAMBDA_NODES):
        raise TypeError(
            "Lambda terms have no arithmetic meaning; beta-reduce and "
            "lambda-eliminate before to_z3_arith."
        )
    # SortedConstant should have been lowered by to_fol already.
    raise TypeError(f"to_z3_arith: cannot translate term node {type(node).__name__}")


def to_z3_arith(node: Node, env: Optional[ArithEnv] = None, sort: str = "real") -> z3.ExprRef:
    """Translate a formula/term node into an arithmetic-interpreted Z3 expression.

    Numbers, the binary arithmetic functions ``+ - * /``, and the comparisons
    ``= ≠ < > ≤ ≥`` are mapped to Z3's interpreted Real/Int operations; all other
    functions and predicates become uninterpreted symbols over the numeric sort.
    Sorted and Łukasiewicz nodes are lowered with :func:`to_fol` first (the
    resulting sort guards become uninterpreted predicates). Lambda nodes raise
    ``TypeError``.

    Args:
        node: the AST node to translate.
        env: an :class:`ArithEnv` to thread declarations through; created from
            ``sort`` when omitted. Pass an explicit env to share symbols across
            several translations.
        sort: ``'real'`` (default) or ``'int'``; only consulted when ``env`` is
            ``None``.

    Returns:
        A Z3 expression — Bool for formula nodes, numeric for term nodes.
    """
    if env is None:
        env = ArithEnv(sort)

    # Lower sorted / Łukasiewicz constructs to classical FOL up front, then
    # translate the result. (to_fol turns sorts into ordinary predicates, which
    # this translation treats as uninterpreted numeric-sort predicates.)
    if isinstance(node, _MSFL_NODES):
        return to_z3_arith(to_fol(node), env)

    # Term-position nodes.
    if isinstance(node, (Number, Variable, Constant, Function)):
        return _term_to_z3(node, env)

    if isinstance(node, Atom):
        if node.predicate in ("=", "≠", "<", ">", "≤", "≥") and len(node.args) == 2:
            left = _term_to_z3(node.args[0], env)
            right = _term_to_z3(node.args[1], env)
            if node.predicate == "=":
                return left == right
            if node.predicate == "≠":
                return left != right
            if node.predicate == "<":
                return left < right
            if node.predicate == ">":
                return left > right
            if node.predicate == "≤":
                return left <= right
            return left >= right  # "≥"
        pred = env.get_pred(node.predicate, len(node.args))
        return pred(*[_term_to_z3(a, env) for a in node.args])

    if isinstance(node, Not):
        return z3.Not(to_z3_arith(node.formula, env))
    if isinstance(node, And):
        return z3.And(to_z3_arith(node.left, env), to_z3_arith(node.right, env))
    if isinstance(node, Or):
        return z3.Or(to_z3_arith(node.left, env), to_z3_arith(node.right, env))
    if isinstance(node, Xor):
        return z3.Xor(to_z3_arith(node.left, env), to_z3_arith(node.right, env))
    if isinstance(node, Implies):
        return z3.Implies(to_z3_arith(node.left, env), to_z3_arith(node.right, env))
    if isinstance(node, Iff):
        return to_z3_arith(node.left, env) == to_z3_arith(node.right, env)

    if isinstance(node, Quantifier):
        z3_var = env.get_symbol(node.variable.name)
        body = to_z3_arith(node.formula, env)
        if node.type in ("forall", "∀"):
            return z3.ForAll([z3_var], body)
        if node.type in ("exists", "∃"):
            return z3.Exists([z3_var], body)
        raise ValueError(f"Unknown quantifier: {node.type}")

    if isinstance(node, _LAMBDA_NODES):
        raise TypeError(
            "Lambda terms have no arithmetic meaning; beta-reduce and "
            "lambda-eliminate before to_z3_arith."
        )

    raise TypeError(f"to_z3_arith: unknown node type {type(node).__name__}")


def _solver(timeout: int) -> z3.Solver:
    """Create a Z3 solver with a deterministic seed and the given millisecond timeout."""
    solver = z3.Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    return solver


def is_satisfiable_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> bool:
    """Return True iff ``formula`` has a model under interpreted arithmetic.

    Translates with :func:`to_z3_arith` and asks Z3 for a model. A Z3 ``unknown``
    result (e.g. a hard quantified formula hitting ``timeout`` milliseconds) is
    treated as not-known-satisfiable and returns False.

    Args:
        formula: the formula to check.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.
    """
    solver = _solver(timeout)
    solver.add(to_z3_arith(formula, sort=sort))
    return solver.check() == z3.sat


def is_valid_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> bool:
    """Return True iff ``formula`` is valid under interpreted arithmetic.

    A formula is valid exactly when its negation is unsatisfiable, so this asks
    Z3 to refute ``¬formula``. A Z3 ``unknown`` result (e.g. hitting ``timeout``
    milliseconds) is treated as not-known-valid and returns False.

    Args:
        formula: the formula to check.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.
    """
    solver = _solver(timeout)
    solver.add(z3.Not(to_z3_arith(formula, sort=sort)))
    return solver.check() == z3.unsat


def get_model_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> Optional[dict]:
    """Return a satisfying assignment under interpreted arithmetic, or None.

    On ``sat``, returns a dict mapping each Z3 declaration name (numeric
    constants, plus any uninterpreted functions/predicates) to the string form of
    its interpretation — e.g. ``{"x": "1"}`` for ``x + 1 = 2 ∧ x > 0``. Returns
    None when the formula is unsatisfiable or Z3 cannot decide it within
    ``timeout`` milliseconds.

    Args:
        formula: the formula to solve.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.
    """
    solver = _solver(timeout)
    solver.add(to_z3_arith(formula, sort=sort))
    if solver.check() != z3.sat:
        return None
    model = solver.model()
    return {str(decl.name()): str(model[decl]) for decl in model.decls()}
