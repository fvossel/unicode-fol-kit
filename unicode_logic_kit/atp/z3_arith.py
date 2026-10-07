"""Arithmetic-aware Z3 translation (Real/Int) and SMT solving over the theory of numbers.

The default ``Node.to_z3`` translates every term into a single *uninterpreted*
sort, so arithmetic is opaque to it: ``x + 1 = 2 ∧ x > 0`` cannot be solved and
``∀x (x * 2 = x + x)`` cannot be proved valid, because ``+``, ``*``, ``>`` and the
numeric literals carry no meaning. This module instead interprets numbers,
arithmetic functions, and comparisons in Z3's theory of reals (or integers), so
those formulas are decided by genuine arithmetic reasoning.

Translation rules (see ``to_z3_arith``):

* ``Number``                       → ``z3.RealVal``/``z3.IntVal``; a numeral that is not an
  integer (``2.5``) has no integer literal and is refused by name under ``sort='int'``
  (``NotImplementedError``), never read as its integer part.
* ``Constant``                     → a Real/Int constant named after the symbol.
* ``Variable``                     → a Real/Int constant of its own, named ``x!v`` for
  the variable ``x`` (see below).
* ``Function`` ``+ - * /`` (binary) → the matching Z3 arithmetic operator.
* ``Function`` ``-`` (one argument) → the negation of its argument: ``-t`` is ``0 - t``. This is
  the node the Prover9 and SMT-LIB readers build for ``-t`` and ``(- t)``, and what the typed
  TPTP writer writes as ``$uminus``.
* other ``Function``               → an uninterpreted function over the numeric sort (also
  ``+``, ``*``, ``/`` at a number of arguments other than two, and ``-`` at three or more).
* ``Atom`` ``= ≠ < > ≤ ≥`` (binary) → the matching Z3 comparison.
* other ``Atom`` (predicate)       → an uninterpreted (numeric-sort)→Bool function.
* ``Not/And/Or/Xor/Implies/Iff``   → the matching Z3 connective.
* ``Quantifier``                   → ``z3.ForAll``/``z3.Exists`` over the bound
  variable's numeric constant.

**A variable is a symbol of its own.** A :class:`~unicode_logic_kit.fol.nodes.Variable` and
a :class:`~unicode_logic_kit.fol.nodes.Constant` of one name are two symbols, in every
position, exactly as they are in :class:`~unicode_logic_kit.fol.nodes.Z3Env`: with
``c = Constant('x')`` the quantifier of ``∀x x ≤ c`` binds the variable and leaves ``c``
alone, so the formula says that ``c`` is an upper bound of every number and is not valid.
The naming is :func:`~unicode_logic_kit.fol._fol_nodes.z3_variable_name` (``x!v``) for a
variable and :func:`~unicode_logic_kit.fol._fol_nodes.z3_constant_name` for a constant (its
own name), the one the other Z3 routes use. A variable that a sort guard or a counting
expansion mints is a variable like any other, so it never meets a user constant spelled
like it. A model reports a constant under its plain name, and a free variable under its
own name too (``x!v`` only when a constant ``x`` is declared as well).

A counting quantifier (``∃≥n x φ``, ``∃≤n``, ``∃=n``) is expanded to its distinct-witnesses
formula (:meth:`~unicode_logic_kit.fol.nodes.Count._expand`), as the default route expands it;
a sorted one, and the sorted quantifiers, sorted constants and Łukasiewicz operators, are
first lowered to classical FOL with :func:`unicode_logic_kit.fol.nodes.to_fol`; the sort
guards introduced there become uninterpreted predicates over the numeric sort. A sorted constant
``c:S`` inside an atom or a function is the SAME numeric symbol as the plain
constant ``c`` (there is one constant, whatever it is annotated with). Lambda
nodes have no first-order meaning and raise ``TypeError`` (beta-reduce and
lambda-eliminate them first); a ``SortedCardinality`` term is a set cardinality,
which has no first-order reading, and is refused by name with
``NotImplementedError``.

**Many-sorted (MSFOL) soundness.** A sort guard is just an uninterpreted
predicate over the (real/int) numeric sort once lowered — nothing stops Z3
from interpreting it as always-false, even though the numeric domain itself
is infinite, and MSFOL, by convention, never gives a sort an EMPTY universe
(see the classical-reasoning guide's many-sorted section). Lowering likewise
reads a sorted constant ``c:S`` as the plain constant ``c``, which forgets that
``c`` lies in ``S``. The three `*_arith` decision functions below close both
gaps exactly like :mod:`unicode_logic_kit.atp.z3_models` does for the default
uninterpreted-sort translation: they add
``unicode_logic_kit.fol._msfl_nodes.sort_axioms(formula)`` (one ``∃x S(x)`` per
sort, one ``S(c)`` per sorted constant), translated with :func:`to_z3_arith`
through the SAME :class:`ArithEnv` as ``formula`` itself (so a sort's guard
predicate and a constant are the identical Z3 declaration in both places), as
extra unconditional assertions — never folded inside :func:`to_z3_arith`
itself, which stays polarity-blind and shared with every other caller. Empty
for an unsorted formula, so behaviour there is unchanged.
"""

from typing import Dict, List, Optional, Tuple

import z3

from ..fol._fol_nodes import check_z3_name, z3_constant_name, z3_variable_name
from ..fol._msfl_nodes import sort_axioms
from ..fol._tptp_symbols import is_tptp_boolean_atom as _is_tptp_boolean_atom
from ..fol._tptp_symbols import truth_constant_word as _truth_constant_word
from ..fol.nodes import (
    Node, to_fol,
    Variable, Constant, Count, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant, SortedCount, SortedCardinality,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)
from .z3_models import model_assignment


# Node types that must be eliminated (lowered to classical FOL) before the
# arithmetic translation can run.
_MSFL_NODES = (
    SortedQuantifier, SortedConstant, SortedCount,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
)

# Lambda-calculus nodes have no first-order arithmetic meaning.
_LAMBDA_NODES = (LambdaVar, Lambda, Application)

_ARITH_OPS = frozenset({"+", "-", "*", "/"})


def _refuse_sorted_cardinality(node: SortedCardinality):
    """Raise the refusal for a ``SortedCardinality`` term, which names it and says why."""
    raise NotImplementedError(
        f"to_z3_arith: {type(node).__name__} ('|{{{node.variable.name}:{node.sort} : φ}}|') "
        "is a set cardinality, a second-order notion with no first-order counterpart. "
        "Express a fixed-bound sorted count with the SortedCount quantifier "
        "(∃≥n / ∃≤n / ∃=n x:S) instead.")


class ArithEnv:
    """Caches Z3 declarations for an arithmetic translation over one numeric sort.

    A single environment is threaded through a whole formula so that every
    occurrence of a name maps to the same Z3 declaration. The numeric sort is
    fixed at construction: ``'real'`` (the default) uses ``z3.RealSort`` and
    ``'int'`` uses ``z3.IntSort``.

    A function and a predicate are keyed on ``(name, arity)``, each in a table
    of its own, exactly as in :class:`~unicode_logic_kit.fol.nodes.Z3Env`: one
    name at two arities is two symbols. A numeral is the value it names here
    (``z3.RealVal``), never a symbol, so a constant named ``1`` is a symbol
    that is not the number 1 and the numeral/constant refusal of ``Z3Env`` has
    no counterpart in this translation.

    A :class:`~unicode_logic_kit.fol.nodes.Variable` is a symbol of its own: the variable ``x``
    and the constant ``x`` are two Z3 constants (``x!v`` and ``x``), kept in two tables, so
    a quantifier over ``x`` never binds the constant of that name. A function of no
    arguments is the constant of its name.
    """

    def __init__(self, sort: str = "real"):
        """Initialise empty symbol/variable/function/predicate tables for the given sort.

        Args:
            sort: ``'real'`` or ``'int'``; selects the Z3 numeric sort that every
                term lives in. Any other value raises ``ValueError``.
        """
        if sort not in ("real", "int"):
            raise ValueError(f"sort must be 'real' or 'int', got {sort!r}")
        self.sort_name = sort
        self.sort = z3.RealSort() if sort == "real" else z3.IntSort()
        self.symbols: Dict[str, z3.ExprRef] = {}
        self.variables: Dict[str, z3.ExprRef] = {}
        self.funcs: Dict[Tuple[str, int], z3.FuncDeclRef] = {}
        self.preds: Dict[Tuple[str, int], z3.FuncDeclRef] = {}

    def num(self, value) -> z3.ExprRef:
        """Return a Z3 numeric literal for ``value`` in this environment's sort.

        Raises:
            NotImplementedError: the sort is ``'int'`` and ``value`` is not an integer. No
                integer is ``2.5``: Z3 would take the integer part of it and read the
                numeral as ``2``, and ``2.5 = 2`` would be valid. Pass ``sort='real'``, or
                write a whole number.
        """
        if self.sort_name == "real":
            return z3.RealVal(value)
        if not isinstance(value, int):
            raise NotImplementedError(
                f"to_z3_arith: the numeral {value!r} has a fractional part, so it is no "
                "integer and has no literal under sort='int' (reading it as its integer part "
                "would make 2.5 = 2 valid). Pass sort='real', or write a whole number.")
        return z3.IntVal(value)

    def get_symbol(self, name: str) -> z3.ExprRef:
        """Get or create the Z3 numeric constant of the CONSTANT ``name``.

        Named as the constant is (:func:`~unicode_logic_kit.fol._fol_nodes.z3_constant_name`).
        A variable is not asked for here (:meth:`get_variable`).
        """
        if name not in self.symbols:
            check_z3_name(name)
            self.symbols[name] = z3.Const(z3_constant_name(name), self.sort)
        return self.symbols[name]

    def get_variable(self, name: str) -> z3.ExprRef:
        """Get or create the Z3 numeric constant that stands for the VARIABLE ``name``.

        A symbol of its own, named by :func:`~unicode_logic_kit.fol._fol_nodes.z3_variable_name`
        and apart from the constant of the same name, so that a quantifier over it never
        binds that constant.
        """
        if name not in self.variables:
            check_z3_name(name)
            self.variables[name] = z3.Const(z3_variable_name(name), self.sort)
        return self.variables[name]

    def get_func(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted function mapping (numeric sort)^arity → numeric sort.

        Keyed on ``(name, arity)``: one name at two arities is two functions. A function
        of no arguments is the constant of its name, so it takes the constant's Z3 name.
        """
        key = (name, arity)
        if key not in self.funcs:
            check_z3_name(name)
            z3_name = z3_constant_name(name) if arity == 0 else name
            self.funcs[key] = z3.Function(z3_name, *([self.sort] * arity), self.sort)
        return self.funcs[key]

    def get_pred(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted predicate mapping (numeric sort)^arity → Bool.

        Keyed on ``(name, arity)``: one name at two arities is two predicates.
        """
        key = (name, arity)
        if key not in self.preds:
            check_z3_name(name)
            self.preds[key] = z3.Function(name, *([self.sort] * arity), z3.BoolSort())
        return self.preds[key]


def _term_to_z3(node: Node, env: ArithEnv) -> z3.ExprRef:
    """Translate a term-position node (number, symbol, or arithmetic/uninterpreted function)."""
    if isinstance(node, Number):
        return env.num(node.value)
    if isinstance(node, Variable):
        return env.get_variable(node.name)
    if isinstance(node, Constant):
        return env.get_symbol(node.name)
    if isinstance(node, SortedConstant):
        # One constant, whatever it is annotated with: ``c:S`` and plain ``c`` are the
        # same numeric symbol. (That ``c`` lies in ``S`` is a fact the decision
        # functions assert next to the formula, see ``_sort_assertions``.)
        return env.get_symbol(node.name)
    if isinstance(node, SortedCardinality):
        _refuse_sorted_cardinality(node)
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
        if node.name == "-" and len(args) == 1:
            # The negation, not a function symbol of its own: ``∀x (-x + x = 0)`` is valid.
            return -args[0]
        return env.get_func(node.name, len(node.args))(*args)
    if isinstance(node, _LAMBDA_NODES):
        raise TypeError(
            "Lambda terms have no arithmetic meaning; beta-reduce and "
            "lambda-eliminate before to_z3_arith."
        )
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

    Raises:
        NotImplementedError: the sort is ``'int'`` and a numeral is not an integer (``2.5``),
            or the node is a ``SortedCardinality``.
    """
    if env is None:
        env = ArithEnv(sort)

    # Lower sorted / Łukasiewicz constructs to classical FOL up front, then
    # translate the result. (to_fol turns sorts into ordinary predicates, which
    # this translation treats as uninterpreted numeric-sort predicates.)
    if isinstance(node, _MSFL_NODES):
        return to_z3_arith(to_fol(node), env)

    # A counting quantifier is first-order: it is the distinct-witnesses formula, which is what
    # the default route translates (:meth:`Count.to_z3`). The witnesses are variables, so they
    # are symbols ``x0!v`` of their own here and meet no constant, predicate or function.
    if isinstance(node, Count):
        return to_z3_arith(node._expand(), env)

    if isinstance(node, SortedCardinality):
        _refuse_sorted_cardinality(node)

    # Term-position nodes.
    if isinstance(node, (Number, Variable, Constant, Function)):
        return _term_to_z3(node, env)

    if isinstance(node, Atom):
        if _is_tptp_boolean_atom(node):          # TPTP's defined propositions
            return z3.BoolVal(_truth_constant_word(node) == "$true")
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
        z3_var = env.get_variable(node.variable.name)
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


def _sort_assertions(formula: Node, env: ArithEnv):
    """Translate ``sort_axioms(formula)`` through ``env``.

    Threading the SAME env through the axioms and ``formula`` itself is what
    makes a sort's guard predicate and a sorted constant resolve to the
    identical Z3 declaration in both places — see the module docstring. Empty
    for an unsorted formula.
    """
    return [to_z3_arith(axiom, env) for axiom in sort_axioms(formula)]


def _model_assignment(model: z3.ModelRef, env: ArithEnv) -> Dict[str, str]:
    """Read a satisfying ``z3.ModelRef`` into ``{key: interpretation}`` under the kit's names.

    The keys are those of :func:`unicode_logic_kit.atp.z3_models.model_assignment`, with the
    numeric constants decoded the way that function decodes the constants of the
    uninterpreted sort: a constant is under its plain name; a free variable (a symbol of its
    own) is under its own name too, and as ``x!v`` when a constant ``x`` is declared as well.
    """
    return model_assignment(model, ranges=(str(env.sort),))


def is_satisfiable_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> bool:
    """Return True iff ``formula`` has a model under interpreted arithmetic.

    Translates with :func:`to_z3_arith` and asks Z3 for a model. A Z3 ``unknown``
    result (e.g. a hard quantified formula hitting ``timeout`` milliseconds) is
    treated as not-known-satisfiable and returns False. A many-sorted
    ``formula``'s sorts are asserted non-empty, and its sorted constants are
    asserted to lie in their sorts, alongside it — see the module docstring.

    Args:
        formula: the formula to check.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.

    Raises:
        NotImplementedError: ``sort`` is ``'int'`` and a numeral of ``formula`` is not an
            integer (``2.5``): it has no integer literal, and is refused rather than read as
            its integer part (see :meth:`ArithEnv.num`).
    """
    solver = _solver(timeout)
    env = ArithEnv(sort)
    solver.add(to_z3_arith(formula, env))
    for assertion in _sort_assertions(formula, env):
        solver.add(assertion)
    return solver.check() == z3.sat


def is_valid_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> bool:
    """Return True iff ``formula`` is valid under interpreted arithmetic.

    A formula is valid exactly when its negation is unsatisfiable, so this asks
    Z3 to refute ``¬formula``. A Z3 ``unknown`` result (e.g. hitting ``timeout``
    milliseconds) is treated as not-known-valid and returns False. A
    many-sorted ``formula``'s sorts are asserted non-empty and its sorted
    constants are asserted to lie in their sorts, as extra, UNNEGATED premises
    alongside the negated goal — see the module docstring.

    Args:
        formula: the formula to check.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.

    Raises:
        NotImplementedError: ``sort`` is ``'int'`` and a numeral of ``formula`` is not an
            integer (``2.5``): it has no integer literal, and is refused rather than read as
            its integer part (see :meth:`ArithEnv.num`).
    """
    solver = _solver(timeout)
    env = ArithEnv(sort)
    for assertion in _sort_assertions(formula, env):
        solver.add(assertion)
    solver.add(z3.Not(to_z3_arith(formula, env)))
    return solver.check() == z3.unsat


def get_model_arith(formula: Node, sort: str = "real", timeout: int = 10000) -> Optional[dict]:
    """Return a satisfying assignment under interpreted arithmetic, or None.

    On ``sat``, returns a dict mapping each Z3 declaration name (numeric
    constants, plus any uninterpreted functions/predicates) to the string form of
    its interpretation — e.g. ``{"x": "1"}`` for ``x + 1 = 2 ∧ x > 0``. A constant
    is reported under its plain name; a free variable is a symbol of its own and is
    reported under its name too, as ``x!v`` only when a constant ``x`` is part of the
    formula as well. Returns
    None when the formula is unsatisfiable or Z3 cannot decide it within
    ``timeout`` milliseconds. A many-sorted ``formula``'s sorts are asserted
    non-empty, and its sorted constants are asserted to lie in their sorts,
    alongside it — see the module docstring.

    Args:
        formula: the formula to solve.
        sort: ``'real'`` (default) or ``'int'`` numeric sort.
        timeout: solver timeout in milliseconds.

    Raises:
        NotImplementedError: ``sort`` is ``'int'`` and a numeral of ``formula`` is not an
            integer (``2.5``): it has no integer literal, and is refused rather than read as
            its integer part (see :meth:`ArithEnv.num`).
    """
    solver = _solver(timeout)
    env = ArithEnv(sort)
    solver.add(to_z3_arith(formula, env))
    for assertion in _sort_assertions(formula, env):
        solver.add(assertion)
    if solver.check() != z3.sat:
        return None
    return _model_assignment(solver.model(), env)
