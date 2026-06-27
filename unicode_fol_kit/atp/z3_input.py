"""Z3 input: turn a Z3 expression (or an SMT-LIB2 string) back into the AST.

Two reverse directions for the Z3 back-end:

- :func:`from_z3` — convert a ``z3.ExprRef`` into a toolkit :class:`Node` (the inverse
  of :meth:`Node.to_z3`).
- :func:`parse_smtlib` / :func:`load_smtlib` — parse an SMT-LIB2 string/file (via Z3's
  own parser) and convert every assertion with :func:`from_z3`.

Lossiness (inherent to Z3): :meth:`Node.to_z3` maps :class:`Variable`, :class:`Constant`
and :class:`Number` all onto symbols of one uninterpreted sort ``S``, so a *free*
variable comes back as a :class:`Constant` (a numeric-looking symbol comes back as a
:class:`Number`); only *bound* variables (Z3 de-Bruijn ``Var`` nodes) come back as
:class:`Variable`. The conversion is therefore **meaning-preserving**, not necessarily
structure-preserving. ``A == B`` is read as :class:`Iff` when the operands are Boolean
and as an ``=`` :class:`Atom` when they are individuals; ``distinct`` becomes ``≠``;
``xor`` becomes :class:`Xor`; an uninterpreted application returning ``Bool`` becomes an
:class:`Atom`, one returning ``S`` a :class:`Function`; the arithmetic operators /
relations and numerals are recognised too (so SMT-LIB with ``Int``/``Real`` imports).

Public API: :func:`from_z3`, :func:`parse_smtlib`, :func:`load_smtlib`.
"""

import z3

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff,
)
from ..fol._fol_nodes import Quantifier


# Arithmetic operator / relation kinds → toolkit symbol names.
_ARITH_FUNC = {
    z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_MUL: "*",
    z3.Z3_OP_DIV: "/", z3.Z3_OP_IDIV: "/",
}
_ARITH_PRED = {
    z3.Z3_OP_LT: "<", z3.Z3_OP_LE: "≤", z3.Z3_OP_GT: ">", z3.Z3_OP_GE: "≥",
}


def _fold(cls, parts):
    """Right-fold a list of >=1 formulas into nested binary ``cls`` nodes."""
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = cls(part, result)
    return result


def _const_or_number(name: str) -> Node:
    """A 0-ary sort-``S`` symbol: a :class:`Number` if its name is numeric, else Constant."""
    try:
        return Number(int(name))
    except ValueError:
        pass
    try:
        return Number(float(name))
    except ValueError:
        return Constant(name)


def _is_bool(expr) -> bool:
    """True iff the Z3 expression has Boolean sort."""
    return expr.sort_kind() == z3.Z3_BOOL_SORT


def from_z3(expr, _scope=None) -> Node:
    """Convert a Z3 expression (``z3.ExprRef``) into a toolkit :class:`Node`.

    The inverse of :meth:`Node.to_z3`; meaning-preserving (see the module docstring
    for the inherent Z3 lossiness around free variables / constants / numbers).

    Raises:
        TypeError: on a Z3 construct with no first-order toolkit counterpart.
    """
    if _scope is None:
        _scope = []

    # --- quantifiers (Z3 stores the body with de-Bruijn Var nodes) ---
    if z3.is_quantifier(expr):
        if expr.is_lambda():
            raise TypeError("from_z3: Z3 lambda terms have no first-order AST counterpart.")
        qtype = "∀" if expr.is_forall() else "∃"
        names = [expr.var_name(i) for i in range(expr.num_vars())]
        # In the body, Var(0) is the LAST bound name; append in order so that
        # Var(idx) -> scope[len-1-idx].
        body = from_z3(expr.body(), _scope + names)
        for name in reversed(names):
            body = Quantifier(qtype, Variable(str(name)), body)
        return body

    if z3.is_var(expr):
        idx = z3.get_var_index(expr)
        return Variable(str(_scope[len(_scope) - 1 - idx]))

    # --- logical connectives ---
    if z3.is_not(expr):
        return Not(from_z3(expr.arg(0), _scope))
    if z3.is_and(expr):
        return _fold(And, [from_z3(expr.arg(i), _scope) for i in range(expr.num_args())])
    if z3.is_or(expr):
        return _fold(Or, [from_z3(expr.arg(i), _scope) for i in range(expr.num_args())])
    if z3.is_implies(expr):
        return Implies(from_z3(expr.arg(0), _scope), from_z3(expr.arg(1), _scope))
    if z3.is_true(expr):
        return Atom("$true", [])
    if z3.is_false(expr):
        return Atom("$false", [])

    if z3.is_app(expr):
        kind = expr.decl().kind()

        if z3.is_eq(expr):
            left, right = expr.arg(0), expr.arg(1)
            sub = [from_z3(left, _scope), from_z3(right, _scope)]
            return Iff(*sub) if _is_bool(left) else Atom("=", sub)
        if kind == z3.Z3_OP_DISTINCT:
            args = [from_z3(expr.arg(i), _scope) for i in range(expr.num_args())]
            if len(args) == 2:
                return Atom("≠", args)
            # n-ary distinct = conjunction of pairwise disequalities.
            pairs = [Atom("≠", [args[i], args[j]])
                     for i in range(len(args)) for j in range(i + 1, len(args))]
            return _fold(And, pairs)
        if kind == z3.Z3_OP_XOR:
            return Xor(from_z3(expr.arg(0), _scope), from_z3(expr.arg(1), _scope))
        if kind == z3.Z3_OP_IFF:
            return Iff(from_z3(expr.arg(0), _scope), from_z3(expr.arg(1), _scope))

        # numerals
        if z3.is_int_value(expr):
            return Number(expr.as_long())
        if z3.is_rational_value(expr):
            denom = expr.denominator_as_long()
            num = expr.numerator_as_long()
            return Number(num if denom == 1 else num / denom)

        # arithmetic
        if kind in _ARITH_PRED:
            return Atom(_ARITH_PRED[kind],
                        [from_z3(expr.arg(i), _scope) for i in range(expr.num_args())])
        if kind in _ARITH_FUNC and expr.num_args() == 2:
            return Function(_ARITH_FUNC[kind],
                            [from_z3(expr.arg(0), _scope), from_z3(expr.arg(1), _scope)])
        if kind == z3.Z3_OP_UMINUS:
            return Function("-", [from_z3(expr.arg(0), _scope)])

        # generic (uninterpreted) application, constant, or predicate
        name = expr.decl().name()
        nargs = expr.num_args()
        args = [from_z3(expr.arg(i), _scope) for i in range(nargs)]
        if nargs == 0:
            return Atom(name, []) if _is_bool(expr) else _const_or_number(name)
        return Atom(name, args) if _is_bool(expr) else Function(name, args)

    raise TypeError(
        f"from_z3: unsupported Z3 expression {expr!r} (no first-order AST counterpart)."
    )


def parse_smtlib(text: str) -> list:
    """Parse an SMT-LIB2 string and return its assertions as toolkit :class:`Node`\\ s.

    Uses Z3's own SMT-LIB2 parser (``z3.parse_smt2_string``) to read the assertions,
    then converts each with :func:`from_z3`.

    Args:
        text: SMT-LIB2 source (``declare-fun`` / ``assert`` … ).

    Returns:
        A list of :class:`Node`, one per top-level ``assert``.
    """
    vector = z3.parse_smt2_string(text)
    return [from_z3(assertion) for assertion in vector]


def load_smtlib(path: str) -> list:
    """Read an SMT-LIB2 (``.smt2``) file and :func:`parse_smtlib` its contents."""
    vector = z3.parse_smt2_file(path)
    return [from_z3(assertion) for assertion in vector]
