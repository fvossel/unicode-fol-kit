"""Z3 input/output: turn a Z3 expression (or an SMT-LIB2 string) into the AST,
and a toolkit :class:`Node` back into SMT-LIB2 text.

Two reverse (read) directions for the Z3 back-end:

- :func:`from_z3` — convert a ``z3.ExprRef`` into a toolkit :class:`Node` (the inverse
  of :meth:`Node.to_z3`).
- :func:`parse_smtlib` / :func:`load_smtlib` — parse an SMT-LIB2 string/file (via Z3's
  own parser) and convert every assertion with :func:`from_z3`.

And one forward (write) direction:

- :func:`to_smtlib` — the general inverse of :func:`parse_smtlib`: render a
  :class:`Node` (plus optional premises) as a standalone, sanitisation-correct
  SMT-LIB2 problem. See its own docstring for what "sanitisation-correct" buys
  over a naive ``to_z3()`` + ``z3.Solver.to_smt2()`` combination.

Lossiness (inherent to Z3): :meth:`Node.to_z3` maps :class:`Variable`, :class:`Constant`
and :class:`Number` all onto symbols of one uninterpreted sort ``S``. A *bound* variable
(a Z3 de-Bruijn ``Var`` node) comes back as a :class:`Variable`; a *free* symbol comes
back as a :class:`Constant`, except for the symbol ``x!v`` that ``to_z3`` writes for a
free :class:`Variable` ``x`` (see :class:`~unicode_logic_kit.fol.nodes.Z3Env`), which comes
back as that variable, and the symbol ``x!v!c`` or ``x!c!c`` it writes for a constant named
``x!v`` or ``x!c``, which comes back as that constant. A symbol is a :class:`Number` only
when its name IS the text a numeral is written as (ASCII digits, a minus sign, a point:
``5``, ``-3``, ``2.5``, ``1e-07``); ``inf``, ``nan``, ``+5`` and a name in other digits
are constants. The reading of a marked name is injective on the names of one text: a
bound or free ``x!v`` is read as the variable ``x`` unless ``x`` is itself a variable of the
text, and then as the variable ``x!v`` (a text that binds ``a!v`` and ``a`` binds two
variables); a symbol ``a!c`` that no writer produces is the constant ``a!c``, and the symbol
``a!c!c`` that the writer gives that constant is read as ``a!c`` unless the text holds
``a!c`` too, and then as ``a!c!c`` (a text with both holds two constants). A numeral is
the constant of its VALUE, so ``1.0`` and
``1`` come back as one :class:`Number`. The conversion is therefore **meaning-preserving**,
not necessarily structure-preserving. ``A == B`` is read as :class:`Iff` when the operands are Boolean
and as an ``=`` :class:`Atom` when they are individuals; ``distinct`` becomes ``≠``;
``xor`` becomes :class:`Xor`; an uninterpreted application returning ``Bool`` becomes an
:class:`Atom`, one returning ``S`` a :class:`Function`; the arithmetic operators /
relations and numerals are recognised too (so SMT-LIB with ``Int``/``Real`` imports).
This same lossiness applies to a :func:`to_smtlib` round trip: it goes through
``Node.to_z3``/``from_z3`` on the way back in, so it inherits exactly this table.

Public API: :func:`from_z3`, :func:`parse_smtlib`, :func:`load_smtlib`, :func:`to_smtlib`.
"""

import math
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Mapping, Sequence, Set

import z3

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff,
)
from ..fol._fol_nodes import Quantifier, Z3Env, kit_name_of_z3_symbol, numeral_key


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
    """A 0-ary symbol of an uninterpreted sort: a :class:`Number` if its name is a numeral as the kit writes it, else Constant.

    A numeral is written as :func:`~unicode_logic_kit.fol._fol_nodes.numeral_key` of its value,
    so a symbol is read back as the number exactly when its name IS that text of a finite
    number: ASCII digits, a minus sign, a point, an exponent. Python's own ``int`` and
    ``float`` accept more (``inf``, ``nan``, ``+5``, ``1_000``, ``5.``, a number with
    spaces around it, digits of other scripts), and each of those is a CONSTANT of that
    name here: reading two of them as one number would merge distinct constants of the text.

    Only a symbol of an uninterpreted sort is read this way (the caller sees to it): that
    is where the kit's writer puts a numeral. A symbol of an arithmetic sort is a symbol
    whatever its name, because a text over ``Int`` or ``Real`` has numerals of its own:
    in ``(declare-fun |1| () Int) (assert (not (= |1| 1)))`` the symbol ``|1|`` and the
    numeral ``1`` are two terms (the text is satisfiable), and reading both as the number
    would make the assertion ``¬ 1 = 1``.
    """
    try:
        integer = int(name)
    except ValueError:
        pass
    else:
        return Number(integer) if numeral_key(integer) == name else Constant(name)
    try:
        real = float(name)
    except ValueError:
        return Constant(name)
    return Number(real) if math.isfinite(real) and numeral_key(real) == name else Constant(name)


def _numeral_of_rational(numerator: int, denominator: int) -> float:
    """The value of the Z3 numeral ``numerator / denominator`` (lowest terms) as a :class:`Number` holds it.

    That is an ``int`` for a whole numeral and a ``float`` for any other. A numeral is read exactly
    or refused, as a decimal text is
    (:func:`~unicode_logic_kit.fol._fol_nodes._numeral_from_text`): a whole value is the ``int``, and
    a fraction is the decimal text it spells, when it spells one (the denominator has no prime
    factor but 2 and 5), read by that same function, so ``1/10`` is ``0.1``, a decimal of more than
    15 significant digits is refused (Z3 reads ``0.30000000000000004`` and ``0.30000000000000005``
    as two different rationals, and one float is the nearest to both), and so is a fraction that
    has no decimal text (``1/3``: no float is that number, and the nearest one would be another
    numeral).

    Raises:
        ValueError: the numeral is not a whole number and has no decimal text of at most 15
            significant digits (see above).
    """
    from ..fol._fol_nodes import _numeral_from_text

    if denominator == 1:
        return numerator
    remaining, twos, fives = denominator, 0, 0
    while remaining % 2 == 0:
        remaining //= 2
        twos += 1
    while remaining % 5 == 0:
        remaining //= 5
        fives += 1
    if remaining != 1:
        raise ValueError(
            f"the numeral {numerator}/{denominator} has no decimal text (its denominator has a prime "
            f"factor other than 2 and 5), so no floating-point number is that numeral, and reading "
            f"the nearest one would make it another numeral than the one written. Keep it as the "
            f"quotient of two integers, or give a decimal with at most 15 significant digits "
            f"instead")
    places = max(twos, fives)
    scaled = str(abs(numerator) * 10 ** places // denominator).rjust(places + 1, "0")
    text = f"{'-' if numerator < 0 else ''}{scaled[:-places]}.{scaled[-places:]}"
    return _numeral_from_text(text)


@dataclass(frozen=True)
class _TextNames:
    """The names of one text (one or several Z3 expressions) that decide how a marked symbol is read.

    Fields:

    * ``variables``: every name, as Z3 holds it, that is read back as a variable: the names of all
      the bound variables of all the quantifiers, and the free symbols of the sort ``S`` whose name
      ends in ``!v`` (the mark of :func:`~unicode_logic_kit.fol._fol_nodes.z3_variable_name`). See
      :func:`_variable_name`.
    * ``constants``: the kit's name of every free symbol of no arguments that is not a Boolean and
      is read back as a constant, by the name Z3 holds it under. See :func:`_constant_readings`.
    """

    variables: FrozenSet[str] = frozenset()
    constants: Mapping[str, str] = field(default_factory=dict)


def _text_names(exprs) -> _TextNames:
    """The :class:`_TextNames` of ``exprs``: every name the reading of one text has to keep apart."""
    variables: Set[str] = set()
    constants: Set[str] = set()
    seen: Set[int] = set()
    stack = list(exprs)
    while stack:
        node = stack.pop()
        key = node.get_id()
        if key in seen:
            continue
        seen.add(key)
        if z3.is_quantifier(node):
            variables.update(str(node.var_name(i)) for i in range(node.num_vars()))
            stack.append(node.body())
        elif z3.is_app(node):
            if (node.num_args() == 0 and not _is_bool(node)
                    and node.decl().kind() == z3.Z3_OP_UNINTERPRETED):
                name = str(node.decl().name())
                (variables if kit_name_of_z3_symbol(name)[1] else constants).add(name)
            stack.extend(node.children())
    return _TextNames(frozenset(variables), _constant_readings(constants))


def _constant_readings(names) -> Dict[str, str]:
    """The kit's name of each constant that a text holds under the Z3 names ``names``: two symbols, two names.

    The writer W (:func:`~unicode_logic_kit.fol._fol_nodes.z3_constant_name`) gives the constant ``n``
    the symbol ``n``, or ``n!c`` when ``n`` ends in a mark (``!v`` or ``!c``). Its inverse R
    (:func:`~unicode_logic_kit.fol._fol_nodes.kit_name_of_z3_symbol`) strips a ``!c`` that follows
    a mark and keeps every other name. R alone does not keep two symbols of a text that a writer did
    not write apart: ``a!c`` is no writer's symbol (the constant ``a`` is written ``a``) and R keeps
    it, while ``a!c!c`` is the symbol of the constant ``a!c`` and R gives that name too. So the
    symbols are read shortest first, each as R of it unless an earlier symbol has that reading
    already, and then as written: a text that holds both is read as two constants, ``a!c`` and
    ``a!c!c``; a symbol that no writer writes is read as itself, whatever else the text holds.
    """
    # (1) R(W(n)) = n for every name n, so R is injective on the image of W; (2) R(s) = s unless s = W(R(s)), so a symbol
    # outside the image is read as itself; (3) shortest first, s is read as R(s) or as s, and no earlier reading is s: an
    # earlier s' is no longer than s and R(s') = s needs s' = s or len(s') = len(s) + 2, so no two readings are equal.
    readings: Dict[str, str] = {}
    taken: Set[str] = set()
    for raw in sorted(names, key=lambda name: (len(name), name)):
        kit_name = kit_name_of_z3_symbol(raw)[0]
        if kit_name in taken:
            kit_name = raw
        taken.add(kit_name)
        readings[raw] = kit_name
    return readings


def _variable_name(name, taken: FrozenSet[str]) -> str:
    """The kit's name of a variable that Z3 holds as ``name`` (a bound name, or a free symbol ``x!v``).

    ``x!v`` is what :meth:`Node.to_z3` writes for the variable ``x``, so it is read back as ``x``
    -- unless ``x`` is itself the name of a variable of the text (``taken``, the ``variables`` of
    :func:`_text_names`): a text that binds ``a!v`` and ``a`` in one quantifier names TWO
    variables, and stripping the mark would make them one (``∀a ∀a (P(a, a) → Q)`` is a weaker
    sentence than ``∀a!v ∀a (P(a!v, a) → Q)``), or would let a bound ``a`` capture a free symbol
    ``a!v``. A name whose stripped form is taken is read as it is written. So the reading is
    injective on the names of one text: two names read alike only when they are one.
    """
    raw = str(name)
    kit_name, is_variable = kit_name_of_z3_symbol(raw)
    return kit_name if is_variable and kit_name not in taken else raw


def _is_bool(expr) -> bool:
    """True iff the Z3 expression has Boolean sort."""
    return expr.sort_kind() == z3.Z3_BOOL_SORT


def from_z3(expr, _scope=None, _taken=None) -> Node:
    """Convert a Z3 expression (``z3.ExprRef``) into a toolkit :class:`Node`.

    The inverse of :meth:`Node.to_z3`; meaning-preserving (see the module docstring
    for the inherent Z3 lossiness around free variables / constants / numbers).

    Raises:
        TypeError: on a Z3 construct with no first-order toolkit counterpart.
        ValueError: a rational numeral that no :class:`Number` holds exactly: a fraction with
            more than 15 significant digits or no decimal text at all (the rule is that of a
            decimal text in every other reader). It is refused, never read as the nearest float.
    """
    if _scope is None:
        _scope = []
    if _taken is None:
        _taken = _text_names([expr])

    # --- quantifiers (Z3 stores the body with de-Bruijn Var nodes) ---
    if z3.is_quantifier(expr):
        if expr.is_lambda():
            raise TypeError("from_z3: Z3 lambda terms have no first-order AST counterpart.")
        qtype = "∀" if expr.is_forall() else "∃"
        names = [_variable_name(expr.var_name(i), _taken.variables) for i in range(expr.num_vars())]
        # In the body, Var(0) is the LAST bound name; append in order so that
        # Var(idx) -> scope[len-1-idx].
        body = from_z3(expr.body(), _scope + names, _taken)
        for name in reversed(names):
            body = Quantifier(qtype, Variable(name), body)
        return body

    if z3.is_var(expr):
        idx = z3.get_var_index(expr)
        return Variable(str(_scope[len(_scope) - 1 - idx]))

    # --- logical connectives ---
    if z3.is_not(expr):
        return Not(from_z3(expr.arg(0), _scope, _taken))
    if z3.is_and(expr):
        return _fold(And, [from_z3(expr.arg(i), _scope, _taken) for i in range(expr.num_args())])
    if z3.is_or(expr):
        return _fold(Or, [from_z3(expr.arg(i), _scope, _taken) for i in range(expr.num_args())])
    if z3.is_implies(expr):
        return Implies(from_z3(expr.arg(0), _scope, _taken), from_z3(expr.arg(1), _scope, _taken))
    if z3.is_true(expr):
        return Atom("$true", [])
    if z3.is_false(expr):
        return Atom("$false", [])

    if z3.is_app(expr):
        kind = expr.decl().kind()

        if z3.is_eq(expr):
            left, right = expr.arg(0), expr.arg(1)
            sub = [from_z3(left, _scope, _taken), from_z3(right, _scope, _taken)]
            return Iff(*sub) if _is_bool(left) else Atom("=", sub)
        if kind == z3.Z3_OP_DISTINCT:
            args = [from_z3(expr.arg(i), _scope, _taken) for i in range(expr.num_args())]
            if len(args) == 2:
                return Atom("≠", args)
            # n-ary distinct = conjunction of pairwise disequalities.
            pairs = [Atom("≠", [args[i], args[j]])
                     for i in range(len(args)) for j in range(i + 1, len(args))]
            return _fold(And, pairs)
        if kind == z3.Z3_OP_XOR:
            return Xor(from_z3(expr.arg(0), _scope, _taken), from_z3(expr.arg(1), _scope, _taken))
        if kind == z3.Z3_OP_IFF:
            return Iff(from_z3(expr.arg(0), _scope, _taken), from_z3(expr.arg(1), _scope, _taken))

        # numerals
        if z3.is_int_value(expr):
            return Number(expr.as_long())
        if z3.is_rational_value(expr):
            return Number(_numeral_of_rational(expr.numerator_as_long(), expr.denominator_as_long()))

        # arithmetic
        if kind in _ARITH_PRED:
            return Atom(_ARITH_PRED[kind],
                        [from_z3(expr.arg(i), _scope, _taken) for i in range(expr.num_args())])
        if kind in _ARITH_FUNC and expr.num_args() == 2:
            return Function(_ARITH_FUNC[kind],
                            [from_z3(expr.arg(0), _scope, _taken), from_z3(expr.arg(1), _scope, _taken)])
        if kind == z3.Z3_OP_UMINUS:
            return Function("-", [from_z3(expr.arg(0), _scope, _taken)])

        # generic (uninterpreted) application, constant, or predicate
        name = expr.decl().name()
        nargs = expr.num_args()
        args = [from_z3(expr.arg(i), _scope, _taken) for i in range(nargs)]
        if nargs == 0:
            if _is_bool(expr):
                return Atom(name, [])
            if kit_name_of_z3_symbol(name)[1]:
                return Variable(_variable_name(name, _taken.variables))
            reading = _taken.constants.get(name, kit_name_of_z3_symbol(name)[0])
            if expr.sort().kind() != z3.Z3_UNINTERPRETED_SORT:
                return Constant(reading)
            return _const_or_number(reading)
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
    return _from_assertions(z3.parse_smt2_string(text))


def load_smtlib(path: str) -> list:
    """Read an SMT-LIB2 (``.smt2``) file and :func:`parse_smtlib` its contents."""
    return _from_assertions(z3.parse_smt2_file(path))


def _from_assertions(vector) -> list:
    """:func:`from_z3` of every assertion of ``vector``, naming one symbol alike in all of them.

    The variables and the constants of the whole text are looked at together
    (:func:`_text_names`), so that a free symbol ``x!v`` is read under one name wherever it
    occurs, whichever of the assertions bind a variable ``x``, and two symbols of the text are
    never read as one name (:func:`_constant_readings`).
    """
    assertions = list(vector)
    taken = _text_names(assertions)
    return [from_z3(assertion, None, taken) for assertion in assertions]


def to_smtlib(formula: Node, premises: Sequence[Node] = (), *, logic: str = "ALL") -> str:
    """Render ``premises`` and ``formula`` as one standalone SMT-LIB2 problem.

    The general inverse of :func:`parse_smtlib`: each of ``premises`` then
    ``formula`` becomes its OWN top-level ``(assert ...)`` command (not one
    folded ``(∧ premises) → formula`` implication) — that is what
    :func:`parse_smtlib` reads back (one :class:`Node` per top-level
    ``assert``), and it is the more idiomatic reading of a standalone
    SMT-LIB2 problem: a list of asserted facts, not a single implication
    that happens to encode an entailment question. Logically nothing is
    lost either way (an SMT solver conjoins every assertion regardless of
    how many ``(assert ...)`` commands they arrived in) — see
    :func:`~atp.cvc5_backend._sanitize_many_for_smtlib`'s docstring for the
    sibling design decision this mirrors.

    This is deliberately NOT built as ``to_z3()`` + ``z3.Solver.to_smt2()``
    alone: that combination is unsound for a symbol name that is pure ASCII
    and digit-leading (``2008SummerOlympics``) or that IS one of SMT-LIB2's
    own reserved words (``let``, ``forall``, ...) — Z3's own serialiser
    quotes every OTHER illegal name correctly (including any non-ASCII one)
    but silently emits these two kinds unquoted, producing ``.smt2`` text
    that fails to parse back (reproduced live; see
    :mod:`atp.cvc5_backend`'s module docstring). So every name across
    ``premises`` and ``formula`` is first sanitised against ONE SHARED name
    map — :func:`~atp.cvc5_backend._sanitize_many_for_smtlib`, promoted from
    :class:`Cvc5Backend`'s own already-proven translation rather than
    reimplemented here — so a symbol used in more than one formula renames
    consistently, before any of them reaches ``to_z3()``. A counting quantifier is
    expanded before the renaming (the witnesses are then names of the problem like any
    other, and are never spelled like a predicate, a function, a constant or a sort of
    it: in this text a bound variable and the symbol it shadows are one identifier).

    Args:
        formula: the goal (or the only formula, when ``premises`` is empty).
        premises: additional formulas, each asserted on its own line ahead
            of ``formula``'s.
        logic: the SMT-LIB2 logic string emitted on the leading
            ``(set-logic ...)`` command (default ``"ALL"`` — safe for
            anything ``to_z3()`` can produce: one uninterpreted sort with
            equality plus uninterpreted functions/predicates, never genuine
            interpreted arithmetic).

    Returns:
        SMT-LIB2 source text: ``(set-logic ...)``, the ``declare-sort``/
        ``declare-fun`` preamble Z3's own ``Solver.to_smt2()`` derives from
        the declarations actually used, one ``(assert ...)`` per premise
        then the goal, and a trailing ``(check-sat)``.

    **Symbols.** A symbol is a predicate, a function or a variable at one arity, so
    ``P(a)`` and ``P(a, b)``, a predicate and a function of one name, a variable and a
    constant of one name, are written under different names (the second and every later
    one gets a token such as ``P_2``; two declarations of one name are an error in
    SMT-LIB2). A name that is a symbol of an SMT-LIB theory (``+``, ``select``,
    ``str.len``, ...) is renamed too, so the text is the same whatever the logic of the
    reading solver, and so is a constant or a variable whose name ends in ``!v`` or ``!c``
    (the reader decodes such a symbol as a variable or as another constant), and so is a
    symbol spelled like a name that Z3's printer mints for a shared sub-term (``$x24``,
    ``?x10``: the printer writes ``(let (($x24 ...)) ...)`` without looking at the symbols the
    text declares, and would shadow a declared symbol of that spelling inside the ``let``). A
    symbol that is renamed is written under its token and read back under it. A numeral is
    the constant of its value: ``1`` and ``1.0`` are one. Every formula is one
    ``(assert ...)``, a truth constant included.

    Raises:
        NotImplementedError: ``formula`` or a premise uses a construct with
            no first-order SMT-LIB2 encoding (second/third-order
            quantification, modal/hybrid/linear/Lambek/team operators, ...)
            — the exact refusal :meth:`Node.to_z3` itself raises for it,
            reused rather than reimplemented (see the ``to_z3`` overrides in
            ``fol/_so_nodes.py``, ``fol/_modal_nodes.py``, etc.), with one
            sentence appended naming this entry point; or the problem holds a
            numeral and a constant of the same text (``Number(1)`` and
            ``Constant('1')``), which are one symbol; or a counting quantifier has a bound
            above 500, which :meth:`~unicode_logic_kit.fol.nodes.Count._expand` refuses by
            naming the bound (a bound up to 500 is written: its expansion is that many
            nested quantifiers, and nothing here recurses on it).
    """
    # Lazy import: atp/__init__.py imports this module before cvc5_backend
    # (which itself imports atp.protocol, which imports cvc5_backend again at
    # its own bottom to register it) — importing cvc5_backend at THIS
    # module's top level would run into that chain mid-load and fail with a
    # partial-module ImportError. By the time to_smtlib() is actually
    # called, package import has long finished, so this is safe.
    from .cvc5_backend import _lower_counting_for_smtlib, _sanitize_many_for_smtlib

    # The counting quantifiers are expanded BEFORE the sanitiser renames the symbols: their
    # witnesses are then names of the problem like any other and are kept apart from every
    # predicate, function, constant and sort (one namespace in the text).
    all_nodes, _ = _lower_counting_for_smtlib(list(premises) + [formula])
    sanitised_nodes, _name_map = _sanitize_many_for_smtlib(all_nodes)
    # The sanitiser has given every variable and every constant a name of its own, so the
    # environment writes a variable as it is named and the text holds those names.
    env = Z3Env(variables_apart=False)
    try:
        z3_exprs = [node.to_z3(env) for node in sanitised_nodes]
    except NotImplementedError as exc:
        raise NotImplementedError(
            f"{exc} SMT-LIB2 export is first-order only."
        ) from exc

    solver = z3.Solver()
    for expr in z3_exprs:
        solver.add(expr)
    text = solver.to_smt2()
    if z3_exprs and z3.is_true(z3_exprs[-1]):
        # ``Solver.to_smt2`` prints its LAST assertion as the formula of a benchmark, and the
        # printer leaves out a formula that is ``true``: the text would have no ``(assert true)``
        # for a problem that ends in a truth constant (a lone ``⊤`` has no assertion at all), and
        # would read back as fewer formulas than were written.
        text = _benchmark_text(z3_exprs)
    return f"(set-logic {logic})\n{text}"


def _benchmark_text(exprs) -> str:
    """The SMT-LIB2 text of ``exprs``, one ``(assert ...)`` each, a ``true`` among them too.

    What ``Solver.to_smt2`` prints, with every expression handed over as an assumption of the
    benchmark and none as its formula, so that the printer writes all of them.
    """
    context = z3.main_ctx()
    assumptions = (z3.Ast * len(exprs))()
    for i, expr in enumerate(exprs):
        assumptions[i] = expr.as_ast()
    return z3.Z3_benchmark_to_smtlib_string(
        context.ref(), "benchmark generated from python API", "", "unknown", "",
        len(exprs), assumptions, z3.BoolVal(True, context).as_ast())
