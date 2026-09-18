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

Why a native `tff` export matters here specifically: the classical `fof`
route (:mod:`atp._tptp_problem`) already renders `+`/`-`/`*`/`/` and
`</>/≤/≥` using TPTP's own arithmetic dollar-words (`$sum`/`$difference`/
`$product`/`$quotient`, `$less`/`$greater`/`$lesseq`/`$greatereq` — see
:class:`~unicode_fol_kit.fol.nodes.Function.TPTP_ARITH_OPS` and
:class:`~unicode_fol_kit.fol.nodes.Atom.PREFIX_PREDS_TPTP`), but under the
UNTYPED `fof` role: a receiving prover has no `$int`/`$real` type
declaration anywhere in the problem, so it cannot activate its native
arithmetic decision procedure on them — they read as ordinary uninterpreted
symbols that ONLY HAPPEN to be named `$sum` and friends. This module emits
the SAME dollar-word vocabulary (reused verbatim, see :func:`_render_term`/
:func:`_render_atom` — no new arithmetic-operator mapping is invented here)
under `tff` type declarations that pin every symbol to `$int`/`$real`, which
is what actually lets Vampire/E switch on their built-in linear-arithmetic
reasoning.

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
REAL, usable mapping here (unlike :mod:`atp.tptp_tff`'s own `tff` route,
which returns no mapping at all — reading its proof output back to
kit-level names is an explicit non-goal there): this module's own rendering
(:func:`_fold_pred`/:func:`_fold_term`) applies EXACTLY the same
first-character fold :meth:`~unicode_fol_kit.fol.nodes.Node.to_tptp` uses,
so :meth:`TptpNameMap.reverse_rendered` — built for that fold — works
unmodified against a prover's raw TFA-route output too.

Numeric literals
-----------------
:class:`~unicode_fol_kit.fol.nodes.Number` renders as a plain TPTP integer
literal for `sort="int"` (a literal WITH a decimal point is refused —
`2.0` was written with a decimal point for a reason, and silently truncating
it to `2` could silently change the formula's meaning) and as a
decimal-fraction real literal (guaranteed a `.` — `3` becomes `3.0`) for
`sort="real"`. A value that would need TPTP's exponent syntax to render
(very large/small floats) is refused rather than emitting invalid TPTP
text — out of scope for the hand-checked textbook battery this exporter
targets.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Sequence, Set, Tuple, Union

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    free_variables,
)
from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ._tptp_problem import TptpNameMap, _sanitize_for_tptp, _check_no_symbol_collisions

__all__ = [
    "generate_tff_arith_problem", "formula_to_tff_arith", "TFA_SORT_TOKENS",
]

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
        raise ValueError(
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
    """TFF (unlike untyped ``fof``) has ONE flat symbol table: a predicate
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


def _analyze(formulas: Sequence[Node]) -> _Signature:
    """Collect every predicate/function/constant name and arity used across
    ``formulas`` (already ASCII-sanitised — see :func:`generate_tff_arith_problem`),
    checking for an arity conflict or a constant/function clash on the way."""
    sig = _Signature()
    for f in formulas:
        for node in f.walk():
            if isinstance(node, Atom):
                if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
                    continue
                arity = len(node.args)
                prev = sig.pred_arity.get(node.predicate)
                if prev is not None and prev != arity:
                    raise ValueError(
                        f"generate_tff_arith_problem: predicate "
                        f"'{node.predicate}' used with conflicting arities "
                        f"{prev} and {arity}."
                    )
                sig.pred_arity[node.predicate] = arity
            elif isinstance(node, Function):
                if node.name in Function.TPTP_ARITH_OPS:
                    continue
                if node.name in sig.const_names:
                    raise ValueError(_CONST_VS_FUNCTION.format(name=node.name))
                arity = len(node.args)
                prev = sig.func_arity.get(node.name)
                if prev is not None and prev != arity:
                    raise ValueError(
                        f"generate_tff_arith_problem: function "
                        f"'{node.name}' used with conflicting arities "
                        f"{prev} and {arity}."
                    )
                sig.func_arity[node.name] = arity
                sig.func_names.add(node.name)
            elif isinstance(node, Constant):
                if node.name in sig.func_names:
                    raise ValueError(_CONST_VS_FUNCTION.format(name=node.name))
                sig.const_names.add(node.name)
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
    if sort == "int":
        if isinstance(value, float):
            raise NotImplementedError(
                f"generate_tff_arith_problem: numeric literal {value!r} has "
                "a decimal point, which has no $int representation — pass "
                "sort='real', or drop the decimal point if a whole number "
                "was meant."
            )
        return str(value)
    text = str(float(value))
    if "e" in text or "E" in text:
        raise NotImplementedError(
            f"generate_tff_arith_problem: numeric literal {value!r} would "
            f"render as {text!r}, which needs TPTP's exponent syntax — out "
            "of scope for this exporter (only plain decimal-fraction $real "
            "literals are supported)."
        )
    return text


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
            tptp_name = Function.TPTP_ARITH_OPS[node.name]
        else:
            tptp_name = _fold_term(node.name)
        if not args:
            return tptp_name
        return f"{tptp_name}({','.join(args)})"
    raise AssertionError(
        f"generate_tff_arith_problem: unreachable term node {type(node).__name__!r}."
    )


def _render_atom(node: Atom, sort: str) -> str:
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
            (see :func:`_render_number`), a name-folding collision within a
            namespace (two distinct predicates, or two distinct functions/
            constants), or a predicate and a function/constant that would
            render as the same TFF identifier (TFF, unlike untyped ``fof``,
            has one flat symbol table — see
            :func:`_check_no_predicate_function_collision`).
        ValueError: an invalid ``sort``, a free variable, an arity conflict,
            or a constant-vs-function name clash.
    """
    if sort not in TFA_SORT_TOKENS:
        raise ValueError(_INVALID_SORT.format(sort=sort))
    _check_fragment(formula)
    _check_no_free_variables(formula)
    [sanitised], _name_map = _sanitize_for_tptp([formula])
    _check_no_symbol_collisions([sanitised])
    _analyze([sanitised])  # validation side-effect only (arity/clash checks)
    return _render(sanitised, sort)


def generate_tff_arith_problem(premises: List[Node], conclusion: Node,
                               sort: str = "real") -> Tuple[str, TptpNameMap]:
    """Build a native, genuinely-typed TPTP ``tff`` problem string, with
    EVERY individual declared to inhabit the ONE numeric sort ``sort``.

    The single-numeric-sort sibling of
    :func:`atp.tptp_tff.generate_tff_problem` (many-sorted, arithmetic-free)
    and the typed-TPTP sibling of :func:`atp.z3_arith.to_z3_arith`/
    :func:`atp.z3_arith.is_valid_arith` (same single-sort design, aimed at
    Vampire/E instead of Z3) — see the module docstring for the full design
    rationale.

    Args:
        premises: classical FOL premises using the arithmetic operators
            (``+ - * /``), comparisons (``= ≠ < > ≤ ≥``), and ordinary
            (non-arithmetic) predicates/functions/constants/plain
            Quantifiers freely — every individual position is the ONE
            numeric sort ``sort``. See the module docstring's 'Design rule'
            for exactly which node types are refused.
        conclusion: the conjecture.
        sort: ``'real'`` (default) or ``'int'`` — the numeric sort every
            declared symbol and quantifier ranges over, exactly
            :class:`atp.z3_arith.ArithEnv`'s own two choices.

    Returns:
        A ``(text, name_map)`` pair: ``text`` is the complete ``tff``
        problem, newline-terminated — type declarations first (functions,
        then constants, then predicates, alphabetically within each —
        declaration-before-use, matching
        :func:`atp.tptp_tff.generate_tff_problem`'s own ordering), then one
        ``tff(premise_<i>, axiom, ...).`` per premise (1-based), then
        ``tff(goal, conjecture, ...).``. ``name_map`` is the
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
            be rendered for the chosen ``sort``, a name-folding collision
            within a namespace, or a predicate/function-or-constant
            cross-namespace clash — see :func:`formula_to_tff_arith`.
        ValueError: an invalid ``sort``, a free variable, an arity conflict,
            or a constant-vs-function name clash — see
            :func:`formula_to_tff_arith`.
    """
    if sort not in TFA_SORT_TOKENS:
        raise ValueError(_INVALID_SORT.format(sort=sort))
    formulas = list(premises) + [conclusion]
    for f in formulas:
        _check_fragment(f)
        _check_no_free_variables(f)
    sanitised, name_map = _sanitize_for_tptp(formulas)
    _check_no_symbol_collisions(sanitised)
    sig = _analyze(sanitised)

    lines = _render_type_decls(sig, sort)
    for i, premise in enumerate(sanitised[:-1], start=1):
        lines.append(f"tff(premise_{i}, axiom, {_render(premise, sort)} ).")
    lines.append(f"tff(goal, conjecture, {_render(sanitised[-1], sort)} ).")
    return "\n".join(lines) + "\n", name_map
