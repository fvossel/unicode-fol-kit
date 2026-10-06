"""Native TFA (typed first-order arithmetic) export: ONE numeric sort, typed.

:mod:`atp.tptp_tff` already emits genuinely typed TPTP (`tff(...)`), but its
own module docstring puts TPTP's built-in arithmetic sorts (`$int`/`$rat`/
`$real`) explicitly out of scope, refusing every arithmetic operator/
comparison BY NAME (see that module's 'Scope: TF0 only' section) — its
union-find sort-inference machinery is built for genuine many-sorted
problems (several DISTINCT user sorts coexisting), which is a harder, and
different, problem than this module solves. This module is the arithmetic
sibling that FILLS that gap, mirroring :mod:`atp.z3_arith`'s already-proven
design choice instead: the WHOLE problem lives in ONE numeric sort chosen by
the caller (`"real"` or `"int"`, exactly :class:`atp.z3_arith.ArithEnv`'s own
two choices) — no attempt at general sort inference, no mixing of a numeric
and a non-numeric individual domain in the same problem. A predicate or
function that is not itself arithmetic (`Human`, `Prime`, ...) is simply
declared as an uninterpreted symbol over that SAME numeric sort — exactly
:class:`~unicode_fol_kit.atp.z3_arith.ArithEnv`'s `get_pred`/`get_func`
convention, carried over to typed TPTP text.

Why a native `tff` export matters here specifically: this is the ONE problem
writer that asks for ARITHMETIC. The other problem writers, the classical `fof`
route (:mod:`atp._tptp_problem`) and the many-sorted TF0 route
(:mod:`atp.tptp_tff`), read `+`/`-`/`*`/`/` and `</>/≤/≥` as ordinary
uninterpreted symbols and a number as an ordinary constant, which is what this
kit means by them unless arithmetic is asked for by name (writing TPTP's
arithmetic dollar-words under an untyped `fof` role would be a trap: a prover
reads `$less(1,2)` and `$sum(1,1) = 2` as theorems of its own arithmetic and
`p(1)` as a type error). This module emits TPTP's own arithmetic vocabulary
(`$sum`/`$difference`/`$product`/`$quotient`, `$less`/`$greater`/`$lesseq`/
`$greatereq` — see :class:`~unicode_fol_kit.fol.nodes.Function.TPTP_ARITH_OPS`
and :class:`~unicode_fol_kit.fol.nodes.Atom.PREFIX_PREDS_TPTP`, reused verbatim,
see :func:`_render_term`/:func:`_render_atom`, except that `/` over `$int` is
`$quotient_e`: see 'Arithmetic operators' below) and the number literals under `tff` type
declarations that pin every symbol to `$int`/`$real`, which is what actually
lets Vampire switch on its built-in linear-arithmetic reasoning. E 3.5.1 reads the
text but does no arithmetic with it (it stops with a type error on `$sum` and the
other operators, and reads a `$real` literal approximately), so the E backend refuses
by name what E cannot do: see the module docstring of :mod:`atp.eprover_backend`.

Design rule: refuse loudly, never guess a sort
-----------------------------------------------
A :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` /
:class:`~unicode_fol_kit.fol.nodes.SortedConstant` /
:class:`~unicode_fol_kit.fol.nodes.SortedCount` node is, by construction,
introducing a genuinely different (and not necessarily numeric) sort — the
exact situation this module's single-sort design exists to avoid silently
guessing about. Rather than either (a) lowering it through
:func:`~unicode_fol_kit.fol.nodes.to_fol` into an uninterpreted guard
predicate over the numeric sort the way :func:`atp.z3_arith.to_z3_arith`
does, or (b) attempting real multi-sort inference the way
:mod:`atp.tptp_tff` does, :func:`_check_fragment` below refuses every one of
these nodes BY NAME with `NotImplementedError`, naming the many-sorted
export route (:func:`atp.tptp_tff.generate_tff_problem`) as the alternative
for a problem that genuinely mixes several sorts. The (unsorted) `Count`
quantifier and every non-classical construct (modal/temporal, second-order,
Łukasiewicz, lambda) are refused the same way — none of those are in scope
for a linear/simple-nonlinear arithmetic exporter.

Free variables are refused, not implicitly closed
---------------------------------------------------
Mirrors :mod:`atp.tptp_tff`'s identical refusal, for a related but distinct
reason: TPTP itself gives no single universally-agreed implicit-closure
convention for a free variable (conventionally universal, but not every
reader/writer pair treats it that way), and this module's own differential
test oracle (:mod:`atp.z3_arith`'s `is_valid_arith`/`is_satisfiable_arith`)
treats an unquantified symbol as an ARBITRARY witness whose reading
(existential vs. universal) depends on which of the two functions is asked
— silently picking one TPTP convention here could give a verdict that
disagrees with the oracle for a reason that has nothing to do with either
route's own correctness. Every variable this module renders therefore comes
from an explicit :class:`~unicode_fol_kit.fol.nodes.Quantifier` binder.

Name legality and round-tripping: reuses :mod:`atp._tptp_problem` directly
-----------------------------------------------------------------------------
(A predicate and a function/constant that fold to the same identifier are
renamed on the term side, exactly as in the ``fof`` and TF0 writers, and
recorded in the returned map — see :func:`atp._tptp_problem._separate_term_names`.
TFF has one flat symbol table, so leaving the pair alone would declare one
identifier at two types.)

Unlike :mod:`atp.tptp_tff` (which duplicates the small ASCII/fold renaming
primitives to avoid a circular import with :mod:`atp._tptp_problem`, since
THAT module imports the many-sorted writer), this module has no such cycle
— nothing in :mod:`atp._tptp_problem` depends on this one — so it reuses
:func:`atp._tptp_problem._sanitize_for_tptp` and
:func:`atp._tptp_problem._check_no_symbol_collisions` directly rather than
re-implementing them a third time. Both already skip exactly the right
symbols (`=`/`≠`, the `<`/`>`/`≤`/`≥` dollar-predicates, and the `+`/`-`/`*`/
`/` dollar-functions — see their own module docstring) during collection AND
rewriting, which is precisely what this single-sort fragment also needs.
The returned :class:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap` is a
REAL, usable mapping here, as it is on :mod:`atp.tptp_tff`'s many-sorted
`tff` route (:func:`~unicode_fol_kit.atp.tptp_tff.generate_tff_problem_with_mapping`
returns one too, and the backends use it to read a prover's output back to
kit-level names; sort names are the one thing that route leaves out of its
map, and this route has no sorts): this module's own rendering
(:func:`_fold_pred`/:func:`_fold_term`) applies EXACTLY the same
first-character fold :meth:`~unicode_fol_kit.fol.nodes.Node.to_tptp` uses,
so :meth:`TptpNameMap.reverse_rendered` — built for that fold — works
unmodified against a prover's raw TFA-route output too.

A variable that has no TPTP spelling (``ä`` is written ``Ä``, ``x-1``, ``1x``) is
renamed to a fresh legal one, per formula and without a record
(:func:`unicode_fol_kit.fol._tptp_symbols.legalise_variables`: a variable is bound).
The nullary atoms ``$true`` and ``$false`` are TPTP's own propositions (this kit's
TPTP reader produces them): they are written verbatim and are neither declared nor
renamed.

Numeric literals
-----------------
:class:`~unicode_fol_kit.fol.nodes.Number` renders as a plain TPTP integer
literal for `sort="int"` (a literal WITH a decimal point is refused —
`2.0` was written with a decimal point for a reason, and silently truncating
it to `2` could silently change the formula's meaning) and as a
decimal-fraction real literal (guaranteed a `.` — `3` becomes `3.0`) for
`sort="real"`. An integer is written with its own digits under both sorts and
never through a `float`: `9007199254740993` stays `9007199254740993` (as a real,
`9007199254740993.0`, a different number from `9007199254740992.0`) and `10**400`
is written, not an `OverflowError`. A float with a fractional part is written as
the shortest text that reads back as it; one that would need TPTP's exponent syntax
to render (a very small float) is refused rather than emitting invalid TPTP text.

Arithmetic operators
---------------------
`+`, `-`, `*` are `$sum`, `$difference`, `$product` and `/` is `$quotient` under
`sort="real"`; under `sort="int"` a `/` is the integer division `$quotient_e` (TPTP's
`$quotient` is for rationals and reals only, and Vampire stops at it over `$int`).
`$quotient_e` is the Euclidean quotient, whose remainder is never negative, which is
what Z3's `/` on integers is (:mod:`atp.z3_arith`), so the two routes agree on
`-7 / 2`, which is `-4`. A one-argument `-` (the node the Prover9 and SMT-LIB readers
build for `-t` and `(- t)`) is the negation `$uminus`, as it is in :mod:`atp.z3_arith`.
Every other operator is binary: `+`, `*`, `/` at another number of arguments, and `-`
at three or more, are refused by name, because TPTP's `$sum(X)` and its like are
ill-typed.
"""

import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Set, Tuple, Union

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    free_variables,
)
from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol._tptp_symbols import is_tptp_boolean_atom, legalise_variables
from ._tptp_problem import (
    TptpNameMap, _sanitize_for_tptp, _check_no_symbol_collisions,
    _separate_term_names,
)
from ._writer_support import (
    check_against_generated, normalise_premise_names, refusals_speak_as, tptp_name_token,
)

__all__ = [
    "generate_tff_arith_problem", "formula_to_tff_arith", "TFA_SORT_TOKENS", "TfaRefusal",
]


class TfaRefusal(ValueError, NotImplementedError):
    """The typed arithmetic (TFA) writer will not write this problem.

    Raised for a free variable, a predicate or a function used at two arities, and a name
    used both as a constant and as a function: the writer declares ONE type per name, so
    those problems cannot be written as typed text. The message names the symbol.

    It derives from both :class:`ValueError` and :class:`NotImplementedError`: the
    refusals were ``ValueError`` before this class existed, and a backend reports a
    ``NotImplementedError`` of a writer as ``unknown`` / ``unsupported`` with the writer's
    message, which is what a refusal of a problem that this writer cannot state is (an
    invalid ``sort=`` or a premise name the writer cannot spell stays a plain
    ``ValueError``: it is a wrong argument, not a problem the writer cannot state)."""

#: The two numeric sorts this exporter supports, and their TPTP dollar-word
#: tokens — the exact pair :class:`atp.z3_arith.ArithEnv` accepts.
TFA_SORT_TOKENS: Dict[str, str] = {"real": "$real", "int": "$int"}

_INVALID_SORT = (
    "generate_tff_arith_problem: sort must be 'real' or 'int', got {sort!r} "
    "(mirrors atp.z3_arith.ArithEnv's own two choices)."
)


# =============================================================================
# Fragment gate
# =============================================================================

# Every classical connective/quantifier plus the arithmetic term/atom nodes —
# deliberately NOT SortedQuantifier/SortedConstant/SortedCount/Count (see
# module docstring's 'Design rule' section) nor anything non-classical.
_ALLOWED_TFA_NODES = frozenset({
    "Variable", "Constant", "Number", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff", "Quantifier",
})


def _check_fragment(formula: Node) -> None:
    """Walk ``formula`` and refuse (loudly, by name) the first node outside
    the single-numeric-sort arithmetic fragment this exporter covers."""
    for node in formula.walk():
        cls = type(node).__name__
        if cls not in _ALLOWED_TFA_NODES:
            raise NotImplementedError(
                f"generate_tff_arith_problem: {cls!r} is outside the "
                "single-numeric-sort arithmetic fragment this exporter "
                "covers (only Number, Variable, Constant, Function, Atom, "
                "Not, And, Or, Xor, Implies, Iff, and a plain, unsorted "
                "Quantifier are expressible in ONE numeric sort — see the "
                "module docstring). A SortedQuantifier/SortedConstant/"
                "SortedCount/Count would introduce a genuinely different "
                "domain, which this single-sort exporter refuses to guess "
                "about rather than silently fold into the numeric sort; "
                "use atp.tptp_tff.generate_tff_problem (many-sorted TF0) or "
                "the classical fof route for a formula that genuinely mixes "
                "several sorts."
            )


def _check_no_free_variables(formula: Node) -> None:
    free = free_variables(formula)
    if free:
        names = ", ".join(sorted(v.name for v in free))
        raise TfaRefusal(
            f"generate_tff_arith_problem: free variable(s) {names} — every "
            "variable must be bound by an enclosing Quantifier; this "
            "exporter refuses to pick an implicit-closure convention rather "
            "than risk disagreeing with the atp.z3_arith differential "
            "oracle for a reason unrelated to either route's correctness "
            "(see module docstring)."
        )


# =============================================================================
# Signature analysis: arity + constant/function-name-clash checks only —
# every argument/result position is the ONE caller-chosen numeric sort, so
# (unlike atp.tptp_tff) no union-find sort inference is needed at all.
# =============================================================================

@dataclass
class _Signature:
    pred_arity: Dict[str, int] = field(default_factory=dict)
    func_arity: Dict[str, int] = field(default_factory=dict)
    const_names: Set[str] = field(default_factory=set)
    func_names: Set[str] = field(default_factory=set)


_CONST_VS_FUNCTION = (
    "generate_tff_arith_problem: {name!r} is used both as a constant and as "
    "a function — this exporter declares at most one 'tff(...,type,...)' "
    "entry per name, so the two uses cannot be reconciled into one symbol."
)

_PRED_VS_FUNCTION = (
    "generate_tff_arith_problem: predicate {pred!r} and {kind} {other!r} "
    "would both render as the TPTP identifier {rendered!r} — TFF has ONE "
    "flat symbol table (unlike untyped fof, where syntactic position alone "
    "tells a predicate from a function/constant apart, which is why "
    "atp._tptp_problem._check_no_symbol_collisions guards them as two "
    "separate namespaces), so a predicate and a function/constant cannot "
    "share a rendered identifier here; rename one of them before exporting "
    "this problem."
)


def _check_no_predicate_function_collision(sig: _Signature) -> None:
    """BACKSTOP. Both entry points run :func:`~unicode_fol_kit.atp._tptp_problem
    ._separate_term_names` before :func:`_analyze`, which renames the term side
    of every such clash, so this check cannot fire for text those entry points
    produce; it stays so that a clash which ever slipped past that pass is
    refused by name instead of being written as two type declarations.

    TFF (unlike untyped ``fof``) has ONE flat symbol table: a predicate
    and a function/constant declared with the same rendered TPTP identifier
    would get two conflicting ``tff(...,type,...)`` entries. The reused
    :func:`~unicode_fol_kit.atp._tptp_problem._check_no_symbol_collisions`
    (called before :func:`_analyze`, see its callers) only guards
    predicates and functions/constants as two SEPARATE namespaces — correct
    for the untyped ``fof`` route it was built for, where syntactic position
    alone disambiguates a predicate from a function — so it does not catch
    a cross-namespace clash. This checks ACROSS the two namespaces instead,
    once ``_analyze`` has collected the full per-problem signature (by which
    point :func:`_check_no_symbol_collisions` has already ruled out an
    internal clash within each namespace, so only pred-vs-term needs
    checking here).
    """
    term_rendered: Dict[str, Tuple[str, str]] = {}
    for name in sig.func_names:
        term_rendered[tptp_fold_first_letter(name)] = ("function", name)
    for name in sig.const_names:
        term_rendered[tptp_fold_first_letter(constant_name_to_ascii(name))] = ("constant", name)
    for pred_name in sig.pred_arity:
        rendered = tptp_fold_first_letter(pred_name)
        hit = term_rendered.get(rendered)
        if hit is not None:
            kind, other = hit
            raise NotImplementedError(_PRED_VS_FUNCTION.format(
                pred=pred_name, kind=kind, other=other, rendered=rendered))


def _analyze(formulas: Sequence[Node], check_flat_table: bool = True) -> _Signature:
    """Collect every predicate/function/constant name and arity used across
    ``formulas`` (already ASCII-sanitised — see :func:`generate_tff_arith_problem`),
    checking for an arity conflict or a constant/function clash on the way.

    ``check_flat_table=False`` skips the final predicate-vs-term backstop; the
    entry points use it for the validation pass that runs BEFORE the term side
    is renamed, so that an arity or constant-vs-function error still names the
    symbol the caller wrote rather than its ``<name>_term`` replacement."""
    sig = _Signature()
    for f in formulas:
        for node in f.walk():
            if isinstance(node, Atom):
                if (node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP
                        or is_tptp_boolean_atom(node)):
                    continue
                arity = len(node.args)
                prev = sig.pred_arity.get(node.predicate)
                if prev is not None and prev != arity:
                    raise TfaRefusal(
                        f"generate_tff_arith_problem: predicate "
                        f"'{node.predicate}' used with conflicting arities "
                        f"{prev} and {arity}."
                    )
                sig.pred_arity[node.predicate] = arity
            elif isinstance(node, Function):
                if node.name in Function.TPTP_ARITH_OPS:
                    continue
                if node.name in sig.const_names:
                    raise TfaRefusal(_CONST_VS_FUNCTION.format(name=node.name))
                arity = len(node.args)
                prev = sig.func_arity.get(node.name)
                if prev is not None and prev != arity:
                    raise TfaRefusal(
                        f"generate_tff_arith_problem: function "
                        f"'{node.name}' used with conflicting arities "
                        f"{prev} and {arity}."
                    )
                sig.func_arity[node.name] = arity
                sig.func_names.add(node.name)
            elif isinstance(node, Constant):
                if node.name in sig.func_names:
                    raise TfaRefusal(_CONST_VS_FUNCTION.format(name=node.name))
                sig.const_names.add(node.name)
    if check_flat_table:
        _check_no_predicate_function_collision(sig)
    return sig


# =============================================================================
# Rendering — numbers, terms, atoms, formulas, type declarations
# =============================================================================

def _fold_pred(name: str) -> str:
    """The exact fold :meth:`~unicode_fol_kit.fol.nodes.Atom.to_tptp` applies
    to a predicate name — first character only."""
    return tptp_fold_first_letter(name)


def _fold_term(name: str) -> str:
    """The exact fold :meth:`~unicode_fol_kit.fol.nodes.Function.to_tptp` /
    :meth:`~unicode_fol_kit.fol.nodes.Constant.to_tptp` apply to a
    function/constant name."""
    return tptp_fold_first_letter(constant_name_to_ascii(name))


def _render_number(value: Union[int, float], sort: str) -> str:
    """The TPTP literal of the numeral ``value`` under ``sort``, in the digits it has.

    An integer is written with its own digits under both sorts (``9007199254740993`` stays
    ``9007199254740993``, and under ``real`` it is ``9007199254740993.0``): the text never goes
    through a ``float``, which holds 53 bits and would make ``2**53 + 1`` the numeral ``2**53``, or
    raise ``OverflowError`` for ``10**400``. A float is written as the shortest text that reads back
    as it (``repr``), which a ``$real`` literal can be; one that needs an exponent is refused.

    Raises:
        NotImplementedError: the value is no integer or finite float (a ``bool`` is no numeral), is
            a float under ``sort='int'`` (no ``$int`` literal has a decimal point), or is a float
            whose text needs TPTP's exponent syntax.
    """
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise NotImplementedError(
            f"generate_tff_arith_problem: Number({value!r}) holds a {type(value).__name__}, and "
            "only an int or a finite float is a numeral this exporter can write — convert the "
            "value first (a bool is no number)."
        )
    if isinstance(value, float) and not math.isfinite(value):
        raise NotImplementedError(
            f"generate_tff_arith_problem: Number({value!r}) is not a finite number, and TPTP has "
            "no literal for it — use a finite value."
        )
    if sort == "int":
        if isinstance(value, float):
            raise NotImplementedError(
                f"generate_tff_arith_problem: numeric literal {value!r} has "
                "a decimal point, which has no $int representation — pass "
                "sort='real', or drop the decimal point if a whole number "
                "was meant."
            )
        return str(value)
    if isinstance(value, int):
        return f"{value}.0"
    text = repr(value)
    if "e" in text or "E" in text:
        raise NotImplementedError(
            f"generate_tff_arith_problem: numeric literal {value!r} would "
            f"render as {text!r}, which needs TPTP's exponent syntax — out "
            "of scope for this exporter (only plain decimal-fraction $real "
            "literals are supported)."
        )
    return text


def _operator_word(name: str, arity: int, sort: str) -> str:
    """The TPTP dollar-word of the arithmetic operator ``name`` applied to ``arity`` arguments.

    ``$sum``, ``$difference``, ``$product`` are binary and the same over both sorts. ``/`` is
    ``$quotient`` over ``$real``, and over ``$int`` the integer division ``$quotient_e`` (TPTP's
    ``$quotient`` is for rationals and reals only: Vampire stops at it over ``$int``): the
    Euclidean quotient, whose remainder is never negative, which is what Z3's ``/`` on integers
    is (``-7 / 2`` is ``-4``, ``7 / -2`` is ``-3``, ``-7 / -2`` is ``4``). A one-argument ``-``
    is the negation ``$uminus`` over both sorts, the reading
    :mod:`unicode_fol_kit.atp.z3_arith` gives it.

    Raises:
        NotImplementedError: the operator has a number of arguments that is neither two nor,
            for ``-``, one. TPTP's ``$sum(X)`` and ``$difference(X, Y, Z)`` are ill-typed, and
            :mod:`unicode_fol_kit.atp.z3_arith` reads such a node as an uninterpreted function,
            which this exporter cannot write under the operator's name, so the node is refused
            by name.
    """
    if name == "-" and arity == 1:
        return "$uminus"
    if arity != 2:
        raise NotImplementedError(
            f"generate_tff_arith_problem: the arithmetic operator {name!r} is applied to {arity} "
            f"argument(s), and {Function.TPTP_ARITH_OPS[name]} takes two. The kit's other "
            "arithmetic route (atp.z3_arith) reads an operator at that number of arguments as an "
            "uninterpreted function, which this exporter cannot write under that name."
        )
    if name == "/" and sort == "int":
        return "$quotient_e"
    return Function.TPTP_ARITH_OPS[name]


def _render_term(node: Node, sort: str) -> str:
    if isinstance(node, Number):
        return _render_number(node.value, sort)
    if isinstance(node, Variable):
        return node.name.upper()
    if isinstance(node, Constant):
        return _fold_term(node.name)
    if isinstance(node, Function):
        args = [_render_term(a, sort) for a in node.args]
        if node.name in Function.TPTP_ARITH_OPS:
            tptp_name = _operator_word(node.name, len(node.args), sort)
        else:
            tptp_name = _fold_term(node.name)
        if not args:
            return tptp_name
        return f"{tptp_name}({','.join(args)})"
    raise AssertionError(
        f"generate_tff_arith_problem: unreachable term node {type(node).__name__!r}."
    )


def _render_atom(node: Atom, sort: str) -> str:
    if is_tptp_boolean_atom(node):
        return node.to_tptp()        # the truth constant's own word, whichever spelling it has
    if ((node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP)
            and len(node.args) != 2):
        raise NotImplementedError(
            f"generate_tff_arith_problem: the comparison {node.predicate!r} is applied to "
            f"{len(node.args)} argument(s), and a comparison relates two terms. It has no "
            "typed TPTP text, so it is refused rather than written as a symbol a prover rejects."
        )
    if node.predicate in Atom.INFIX_PREDS_TPTP and len(node.args) == 2:
        op = Atom.INFIX_PREDS_TPTP[node.predicate]
        left = _render_term(node.args[0], sort)
        right = _render_term(node.args[1], sort)
        return f"({left} {op} {right})"
    if node.predicate in Atom.PREFIX_PREDS_TPTP and len(node.args) == 2:
        op = Atom.PREFIX_PREDS_TPTP[node.predicate]
        left = _render_term(node.args[0], sort)
        right = _render_term(node.args[1], sort)
        return f"{op}({left},{right})"
    pred = _fold_pred(node.predicate)
    if not node.args:
        return pred
    args = ",".join(_render_term(a, sort) for a in node.args)
    return f"{pred}({args})"


def _quant_symbol(qtype: str) -> str:
    if qtype in ("∀", "forall"):
        return "!"
    if qtype in ("∃", "exists"):
        return "?"
    raise ValueError(f"generate_tff_arith_problem: unknown quantifier type {qtype!r}.")


def _render(node: Node, sort: str) -> str:
    if isinstance(node, Atom):
        return _render_atom(node, sort)
    if isinstance(node, Not):
        return f"~({_render(node.formula, sort)})"
    if isinstance(node, And):
        return f"({_render(node.left, sort)} & {_render(node.right, sort)})"
    if isinstance(node, Or):
        return f"({_render(node.left, sort)} | {_render(node.right, sort)})"
    if isinstance(node, Xor):
        return f"({_render(node.left, sort)} <~> {_render(node.right, sort)})"
    if isinstance(node, Implies):
        return f"({_render(node.left, sort)} => {_render(node.right, sort)})"
    if isinstance(node, Iff):
        return f"({_render(node.left, sort)} <=> {_render(node.right, sort)})"
    if isinstance(node, Quantifier):
        var = node.variable.name.upper()
        q = _quant_symbol(node.type)
        sort_tok = TFA_SORT_TOKENS[sort]
        return f"({q}[{var}: {sort_tok}]: {_render(node.formula, sort)})"
    raise AssertionError(
        f"generate_tff_arith_problem: unreachable formula node {type(node).__name__!r}."
    )


def _render_map_type(arg_sorts: List[str], result_sort: str) -> str:
    """Mirrors ``atp.tptp_tff._render_map_type`` — duplicated (small, and
    tied to this module's own type-declaration rendering) rather than
    imported, per the sibling modules' own established convention of
    duplicating small rendering primitives instead of cross-importing them."""
    if not arg_sorts:
        return result_sort
    if len(arg_sorts) == 1:
        return f"{arg_sorts[0]} > {result_sort}"
    return "(" + " * ".join(arg_sorts) + ") > " + result_sort


def _render_type_decls(sig: _Signature, sort: str) -> List[str]:
    sort_tok = TFA_SORT_TOKENS[sort]
    lines: List[str] = []
    counter = [0]

    def next_name(prefix: str) -> str:
        counter[0] += 1
        return f"{prefix}_{counter[0]}"

    for name in sorted(sig.func_names):
        arity = sig.func_arity[name]
        type_str = _render_map_type([sort_tok] * arity, sort_tok)
        lines.append(f"tff({next_name('func_decl')}, type, {_fold_term(name)}: {type_str} ).")
    for name in sorted(sig.const_names):
        lines.append(f"tff({next_name('const_decl')}, type, {_fold_term(name)}: {sort_tok} ).")
    for name in sorted(sig.pred_arity):
        arity = sig.pred_arity[name]
        type_str = _render_map_type([sort_tok] * arity, "$o")
        lines.append(f"tff({next_name('pred_decl')}, type, {_fold_pred(name)}: {type_str} ).")
    return lines


# =============================================================================
# Public API
# =============================================================================

def formula_to_tff_arith(formula: Node, sort: str = "real") -> str:
    """Render a single formula as bare TFA formula text (no ``tff(...)``
    statement wrapper, no type declarations) — the single-numeric-sort
    sibling of :func:`atp.tptp_tff.formula_to_tff`.

    Runs the fragment check, free-variable check, and ASCII/name-legality
    sanitisation on ``formula`` ALONE, exactly like
    :func:`~unicode_fol_kit.atp.tptp_tff.formula_to_tff` does for the
    many-sorted route.

    Args:
        formula: a classical (or plain-quantified, unsorted) FOL formula —
            see the module docstring's 'Design rule' for exactly which node
            types are in scope.
        sort: ``'real'`` (default) or ``'int'`` — the ONE numeric sort every
            individual in ``formula`` is declared to inhabit.

    Raises:
        NotImplementedError: ``formula`` contains a node outside the
            single-sort arithmetic fragment (see module docstring), a
            numeric literal that cannot be rendered for the chosen ``sort``
            (see :func:`_render_number`), an arithmetic operator or comparison
            applied to other than two arguments (a one-argument ``-`` is the
            negation and is written), a
            name-folding collision within a
            namespace (two distinct predicates, or two distinct functions/
            constants), or two LEGAL variables that render as one TPTP variable
            (``x`` and ``X``: ``∀x ∃X R(x, X)`` would be ``![X]: ?[X]: r(X,X)``).
            A predicate and a function/constant that would render
            as the same TFF identifier are NOT refused: the term side is
            renamed (see the module docstring), and
            :func:`generate_tff_arith_problem` returns the map.
        TfaRefusal: a free variable, an arity conflict, or a constant-vs-function
            name clash (a ``ValueError`` and a ``NotImplementedError`` at once).
        ValueError: an invalid ``sort``.
    """
    with refusals_speak_as("formula_to_tff_arith", "generate_tff_arith_problem"):
        if sort not in TFA_SORT_TOKENS:
            raise ValueError(_INVALID_SORT.format(sort=sort))
        _check_fragment(formula)
        _check_no_free_variables(formula)
        [sanitised], name_map = _sanitize_for_tptp([formula])
        sanitised = legalise_variables(sanitised)
        _check_no_symbol_collisions([sanitised], where="generate_tff_arith_problem",
                                    subject="formula")
        _analyze([sanitised], check_flat_table=False)   # errors name the caller's own symbols
        [sanitised], _name_map = _separate_term_names([sanitised], name_map)
        _analyze([sanitised])  # validation side-effect only (backstop for the flat table)
        return _render(sanitised, sort)


def generate_tff_arith_problem(premises: List[Node], conclusion: Optional[Node] = None,
                               sort: str = "real", *,
                               premise_names: Optional[Sequence[str]] = None
                               ) -> Tuple[str, TptpNameMap]:
    """Build a native, genuinely-typed TPTP ``tff`` problem string, with
    EVERY individual declared to inhabit the ONE numeric sort ``sort``.

    The single-numeric-sort sibling of
    :func:`atp.tptp_tff.generate_tff_problem` (many-sorted, arithmetic-free)
    and the typed-TPTP sibling of :func:`atp.z3_arith.to_z3_arith`/
    :func:`atp.z3_arith.is_valid_arith` (same single-sort design, aimed at
    Vampire instead of Z3; E reads the text but does no arithmetic with it) — see
    the module docstring for the full design rationale.

    Args:
        premises: classical FOL premises using the arithmetic operators
            (``+ - * /``), comparisons (``= ≠ < > ≤ ≥``), and ordinary
            (non-arithmetic) predicates/functions/constants/plain
            Quantifiers freely — every individual position is the ONE
            numeric sort ``sort``. See the module docstring's 'Design rule'
            for exactly which node types are refused.
        conclusion: the conjecture, or ``None`` for a problem without one (no
            ``conjecture`` line is written; the prover is asked whether the
            premises are satisfiable).
        sort: ``'real'`` (default) or ``'int'`` — the numeric sort every
            declared symbol and quantifier ranges over, exactly
            :class:`atp.z3_arith.ArithEnv`'s own two choices.
        premise_names: one name per premise for the ``axiom`` lines instead of
            ``premise_<i>``, written as a TPTP name and recorded, in order and also by
            default, in the returned map's ``premises`` — see
            :func:`~unicode_fol_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`.
            The names the writer gives its own lines are ``goal``, ``func_decl_<n>``,
            ``const_decl_<n>`` and ``pred_decl_<n>``; a premise named like one of them
            is a ``ValueError``.

    Returns:
        A ``(text, name_map)`` pair: ``text`` is the complete ``tff``
        problem, newline-terminated — type declarations first (functions,
        then constants, then predicates, alphabetically within each —
        declaration-before-use, matching
        :func:`atp.tptp_tff.generate_tff_problem`'s own ordering), then one
        ``tff(premise_<i>, axiom, ...).`` per premise (1-based), then
        ``tff(goal, conjecture, ...).`` unless ``conclusion`` is ``None``.
        ``name_map`` is the
        :class:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap` recording
        every ASCII-legality rename applied (see module docstring's 'Name
        legality' section) — pass it to
        :func:`~unicode_fol_kit.atp._tptp_problem.apply_reverse_tptp` or use
        its :meth:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap.reverse_rendered`
        to translate a prover's own output back to kit-level names, exactly
        as the classical ``fof`` route's mapping is used.

    Raises:
        NotImplementedError: a node outside the single-sort arithmetic
            fragment (see module docstring), a numeric literal that cannot
            be rendered for the chosen ``sort``, an arithmetic operator or
            comparison applied to other than two arguments, a name-folding
            collision within a namespace, or two LEGAL variables of one formula that render as
            one TPTP variable (``x`` and ``X``) — see
            :func:`formula_to_tff_arith`. (A predicate and a function/constant
            that fold to one identifier are renamed on the term side and
            recorded in ``name_map``.)
        TypeError: ``premise_names`` is one string rather than a sequence of strings, or
            one of its entries is not a string.
        TfaRefusal: a free variable, an arity conflict, or a constant-vs-function name
            clash — see :func:`formula_to_tff_arith`. It is a ``ValueError`` as it
            always was, and a ``NotImplementedError`` too, so that a backend reports
            it as ``unknown`` / ``unsupported`` with this message.
        ValueError: an invalid ``sort``; or ``premise_names`` holds other than one name
            per premise, a name no TPTP name spells, two names that are the same as
            written, or a name the writer gives one of its own lines.
    """
    if sort not in TFA_SORT_TOKENS:
        raise ValueError(_INVALID_SORT.format(sort=sort))
    premises = list(premises)
    premise_labels = normalise_premise_names(premise_names, len(premises),
                                             where="generate_tff_arith_problem")
    formulas = premises + ([] if conclusion is None else [conclusion])
    for f in formulas:
        _check_fragment(f)
        _check_no_free_variables(f)
    sanitised, name_map = _sanitize_for_tptp(formulas)
    sanitised = [legalise_variables(f) for f in sanitised]
    _check_no_symbol_collisions(sanitised, where="generate_tff_arith_problem")
    _analyze(sanitised, check_flat_table=False)     # errors name the caller's own symbols
    sanitised, name_map = _separate_term_names(sanitised, name_map)
    sig = _analyze(sanitised)

    lines = _render_type_decls(sig, sort)
    generated = [("goal", "the conjecture")] if conclusion is not None else []
    for line in lines:
        # tff(func_decl_1, type, ...): the name of each declaration the writer gave
        generated.append((line[len("tff("):line.index(",")], "a type declaration"))
    check_against_generated(premise_labels, generated, where="generate_tff_arith_problem")
    for label, premise in zip(premise_labels, sanitised):
        lines.append(f"tff({tptp_name_token(label)}, axiom, {_render(premise, sort)} ).")
    if conclusion is not None:
        lines.append(f"tff(goal, conjecture, {_render(sanitised[-1], sort)} ).")
    name_map.premises = premise_labels
    return "\n".join(lines) + "\n", name_map
