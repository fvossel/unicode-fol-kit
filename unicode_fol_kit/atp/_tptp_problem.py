"""Shared TPTP ``fof`` problem generation for the external TPTP-speaking backends.

:mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend` (E and
Zipperposition), and :mod:`atp.twee_entailment` each build the IDENTICAL TPTP
problem shape from ``(premises, conclusion)``: one ``fof(premise_<i>, axiom,
...).`` line per premise (1-based) plus one ``fof(goal, conjecture, ...).``
line — three copies of the same seven lines that had already started to
drift apart in their docstrings. :func:`generate_tptp_problem` is the single
place that shape is written; the three backends' own ``_generate_*_input``
functions now delegate here (same name, same signature, same output — no
behaviour change for their callers or their tests).

**ASCII/legality sanitisation (problem-level seam).** ``Node.to_tptp()``
renders a predicate/function/constant name close to verbatim — only a
Constant is transliterated to ASCII (:func:`constant_name_to_ascii`), and
only the first character of any of the three is folded for TPTP's
lowercase-initial rule (:func:`tptp_fold_first_letter`). Neither step fixes
a DIGIT-LEADING name (``2008SummerOlympics`` stays digit-leading, which
TPTP's ``lower_word: [a-z][A-Za-z0-9_]*`` grammar forbids), and neither
``Atom.to_tptp`` nor ``Function.to_tptp`` transliterates non-ASCII at all —
gaps the toolkit's identifier grammar could not reach before it was widened
to accept Unicode letters and digit-leading names, but can now. Fixing
either INSIDE a node's own ``to_tptp()`` would be wrong: each node would
rename independently, two distinct kit-level names could collide on their
fix with no whole-problem view to catch it, and the rewrite could never
reach a caller that needs to translate a prover's answer back. So the fix
lives here instead, exactly where the pre-existing case-fold collision
guard below already lives: :func:`_sanitize_for_tptp` walks every premise
and the conclusion TOGETHER, replaces only the names that are not already
TPTP-legal (checked BEFORE any fold — see :func:`_is_tptp_safe`) with an
ASCII, non-digit-leading, whole-problem-injective replacement, and returns
a :class:`TptpNameMap` recording exactly what was renamed so a caller can
translate prover output back (:func:`apply_reverse_tptp`). A name that was
already TPTP-legal is returned completely untouched — the very same
``Node`` object, not a copy — so ``Node.to_tptp()``'s existing output for
every formula this module was already handling correctly is byte-identical
to before this sanitisation step existed.

**Soundness guard.** :meth:`~unicode_fol_kit.fol.nodes.Node.to_tptp` folds a
predicate/function/constant name for TPTP's lowercase-initial identifier rule
by lower-casing only its FIRST character (see
:func:`unicode_fol_kit.fol._fol_nodes.tptp_fold_first_letter`) — the exact
mirror of ``tptp_input.py``'s ``_cap()``, which capitalises only the first
character of a parsed predicate name on import. That fold is not injective by
itself: ``Foo`` and ``foo`` (or two constants, or two functions) still both
fold to ``foo``. A single node's ``to_tptp()`` has no way to know whether some
OTHER node elsewhere in the same problem folds to the same identifier, so the
check has to happen here, where every premise and the conclusion are in view
together. Two distinct kit-level names colliding on export would otherwise be
silently merged into ONE TPTP symbol — e.g. a premise ``Foo(a)`` and its
negation ``¬FOO(a)`` would both render as ``foo(a)``, making the exported
axiom set ``{foo(a), ~foo(a)}`` — internally CONTRADICTORY, so an external
prover proves any conjecture from it via ex falso quodlibet, a false
"Theorem" verdict for a query the premises never actually entail. Rather than
risk that, :func:`generate_tptp_problem` refuses with ``NotImplementedError``
naming both colliding kit-level names, mirroring
:func:`unicode_fol_kit.atp.tptp_ncl.to_tptp_ncl`'s own (separately
implemented, since NXF's modal connectives are outside ``to_tptp``'s
classical FOL fragment) collision guard for the NXF export path. This check
runs AFTER the ASCII sanitisation step above, over the sanitised formulas —
:func:`_sanitize_for_tptp` already avoids colliding with itself (a shared
reservation set covers both already-legal and newly-synthesised names in
each namespace), so in practice this guard only ever fires for the same
kind of pre-existing, already-legal-name case-fold collision it always did
(``Foo``/``foo``); it is not weakened or bypassed by the sanitisation step.

Predicate names and function/constant names are checked as two SEPARATE
namespaces (mirroring how a TPTP-reading prover resolves a bare identifier by
its syntactic position — formula position is a predicate, term position is a
function/constant — rather than by a single shared symbol table), so a
predicate and a function/constant folding to the same string is not itself
flagged; only two DISTINCT names within the SAME namespace colliding is. The
equality/disequality/arithmetic-comparison predicates (``=``, ``≠``, ``<``,
``>``, ``≤``, ``≥``) and the arithmetic functions (``+``, ``-``, ``*``, ``/``)
are excluded from the check entirely — each maps individually and
injectively to a fixed TPTP token (``=``, ``!=``, ``$less``, ``$sum``, ...),
never through the first-letter fold, so they cannot participate in a folding
collision. The same two symbols are excluded from :func:`_sanitize_for_tptp`
for the same reason: ``=`` is not an identifier to begin with, so it is
never a candidate for the "is this already legal?" test in the first place.
"""

import re
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Tuple

from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol.nodes import Atom, Constant, Function, Node
from ._ascii_names import ascii_safe_base, reserve_rendered

__all__ = ["generate_tptp_problem", "generate_tptp_problem_with_mapping",
           "TptpNameMap", "apply_reverse_tptp"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring's second section.
# ---------------------------------------------------------------------------

# A raw kit-level name that is ALREADY safe to hand to Node.to_tptp(): pure
# ASCII, letter-initial (so the fold turns it into a legal lower_word no
# matter its case), and containing only the characters lower_word allows
# after that. Names the widened parser can now produce never contain
# anything outside this (unicode letters/digits/underscore/combining marks
# only), so this is the exact complement of "needs a replacement".
_TPTP_SAFE_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _is_tptp_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_TPTP_SAFE_RE.fullmatch(name))


@dataclass
class _Renamer:
    """One symbol namespace's original->safe-token map, whole-problem-shared.

    Two passes, run over the WHOLE problem before any text is rendered:

    1. :meth:`collect` — called once per occurrence of every name in this
       namespace, in problem order. An already-legal name is reserved
       immediately and unconditionally (R1: it is never touched, so its
       reservation cannot depend on what else is in the problem); anything
       else is queued, deduplicated by first occurrence.
    2. :meth:`finalize` — synthesises a token for every queued name, each
       de-collided (:func:`reserve_rendered`) against ``used`` as it now
       stands: every already-legal name in the WHOLE problem, not just the
       ones that happened to appear earlier in iteration order.

    Doing this in one combined pass (synthesise-as-you-go) would make
    collision-avoidance depend on argument order: a synthesised name could
    legitimately claim a token that a DIFFERENT, already-legal name
    appearing LATER in the same problem also owns — since R1 forbids moving
    the legal name off of it, that is a genuine, unavoidable ambiguity, but
    one this two-pass split avoids ever manufacturing purely from processing
    order (R2: "two different names never collide" holds regardless of
    where in the problem each one appears). :meth:`get` is only valid after
    :meth:`finalize` — every name this namespace will ever be asked about
    must have gone through :meth:`collect` first.
    """

    prefix: str
    render: Callable[[str], str]
    case_fix: Callable[[str], str]
    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: List[str] = field(default_factory=list)

    def collect(self, name: str) -> None:
        if name in self.mapping or name in self._pending:
            return
        if _is_tptp_safe(name):
            self.used.add(self.render(name))
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        for name in self._pending:
            base = self.case_fix(ascii_safe_base(name, self.prefix))
            token = reserve_rendered(base, self.used, self.render)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return self.mapping[name]


def _predicate_base_case(base: str) -> str:
    """Force uppercase-initial — the kit's own PREDICATE convention.

    Necessary for round-tripping, not merely stylistic: TPTP's own fold
    always lower-cases whatever we export, and ``tptp_input.py``'s ``_cap()``
    always UPPER-cases the first letter of whatever text a prover echoes
    back — regardless of what we originally exported. A synthesised
    predicate token therefore has to already BE upper-case-initial, or the
    reverse mapping (keyed by the token we chose) would never match what
    comes back from ``_cap()``. Function/constant names need no such fix:
    neither export nor import case-folds them at all (see
    :func:`_term_base_case`), so any ASCII letter-initial form round-trips
    verbatim.
    """
    return base[0].upper() + base[1:] if base else base


def _term_base_case(base: str) -> str:
    """Force lowercase-initial — the kit's own NAME (function/constant)
    convention, and, since neither export nor import case-folds a
    function/constant name at all, the form that makes ``render(candidate)
    == candidate`` (no fold vs. no-fold asymmetry to reverse)."""
    return base[0].lower() + base[1:] if base else base


@dataclass
class TptpNameMap:
    """The renamings :func:`_sanitize_for_tptp` chose for one problem.

    ``predicate`` and ``term`` are original-kit-name -> raw-token dicts (the
    exact string substituted into the sanitised AST, BEFORE ``Node.to_tptp``'s
    own fold) for the predicate namespace and the shared function/constant
    namespace respectively — mirroring the two-namespace split
    :func:`_check_no_symbol_collisions` already uses. An original name that
    was already TPTP-legal maps to itself (see :class:`_Renamer`), so
    :meth:`reverse` inverts cleanly even for untouched names.
    """

    predicate: Dict[str, str] = field(default_factory=dict)
    term: Dict[str, str] = field(default_factory=dict)

    def reverse(self) -> Tuple[Dict[str, str], Dict[str, str]]:
        """Return ``(predicate_reverse, term_reverse)``: token -> original.

        The token used as the reverse-dict KEY is exactly what a prover's
        own output re-parsed via :func:`~unicode_fol_kit.fol.tptp_input
        .parse_tptp_formula` produces for that symbol — see
        :func:`_predicate_base_case`/:func:`_term_base_case`'s docstrings for
        why that already equals the raw token stored in ``predicate``/
        ``term`` (no extra fold/cap step needed here). Use this for the
        STRUCTURED Rückweg (:func:`apply_reverse_tptp`, and anything that
        goes through it such as :func:`~unicode_fol_kit.atp.tstp
        .reverse_map_derivation`) — never for raw, un-parsed prover text; see
        :meth:`reverse_rendered` for that.
        """
        return ({v: k for k, v in self.predicate.items()},
                {v: k for k, v in self.term.items()})

    def reverse_rendered(self) -> Tuple[Dict[str, str], Dict[str, str]]:
        """Return ``(predicate_reverse, term_reverse)`` keyed by the
        RENDERED token — exactly the text ``Node.to_tptp()`` actually wrote
        into the generated problem, and therefore exactly what a prover
        echoes back UNPARSED (raw stdout, an SZS detail string, and similar
        free text — R3's "Erklärungstexte").

        :meth:`reverse` is keyed by the raw, pre-fold token instead, which is
        the right key for the STRUCTURED Rückweg (:func:`apply_reverse_tptp`
        re-parses a prover's TSTP text via
        :func:`~unicode_fol_kit.fol.tptp_input.parse_tptp_formula` first,
        which re-applies the kit's uppercase-initial predicate convention on
        import — see :func:`_predicate_base_case` — undoing the export-time
        fold before this mapping is ever consulted) but the WRONG key for
        free text that was never re-parsed: a synthesised or already-legal
        predicate token such as ``Human`` renders as ``human`` (only the
        first character is folded, :func:`tptp_fold_first_letter`), so raw
        prover stdout contains ``human``, not ``Human`` — a reverse dict
        keyed by ``Human`` never matches it, and the original name is never
        restored (this is exactly the bug this method fixes). Term
        (function/constant) tokens are unaffected in practice — they are
        already chosen/kept lowercase-initial (:func:`_term_base_case`), so
        rendering them again is a no-op — but this method renders them the
        same way regardless, so it stays correct even for a term name built
        directly (e.g. a bare ``Constant("Foo")``) outside the parser's own
        lowercase-initial NAME convention rather than assuming every caller
        went through it.

        Injective by construction: :class:`_Renamer` already de-collides
        every name in a namespace on its RENDERED form (:func:`reserve_rendered`,
        and the immediate ``self.used.add(self.render(name))`` for an
        already-legal name in :meth:`_Renamer.collect`) before assigning it a
        token, so two distinct original names can never render to the same
        text within one namespace — this dict can never silently drop or
        merge an entry.
        """
        pred_rendered = {tptp_fold_first_letter(v): k for k, v in self.predicate.items()}
        term_rendered = {tptp_fold_first_letter(constant_name_to_ascii(v)): k
                         for k, v in self.term.items()}
        return pred_rendered, term_rendered


def _sanitize_node_for_tptp(node: Node, predicates: _Renamer, terms: _Renamer) -> Node:
    """Rebuild ``node`` with every non-TPTP-legal symbol name replaced.

    Structural recursion via ``Node.map_children`` (see
    :mod:`fol.sanitize`'s ``_rewrite`` for the same pattern); an
    already-legal name comes back as the exact same string, so a node whose
    own name and every descendant's name were already legal is rebuilt with
    identical field values throughout — ``Node.to_tptp()`` on the result is
    therefore byte-identical to ``Node.to_tptp()`` on the original (R1).
    """
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
            pred = node.predicate
        else:
            pred = predicates.get(node.predicate)
        return Atom(pred, [_sanitize_node_for_tptp(a, predicates, terms) for a in node.args])
    if isinstance(node, Function):
        if node.name in Function.TPTP_ARITH_OPS:
            name = node.name
        else:
            name = terms.get(node.name)
        return Function(name, [_sanitize_node_for_tptp(a, predicates, terms) for a in node.args])
    if isinstance(node, Constant):
        return Constant(terms.get(node.name))
    return node.map_children(lambda c: _sanitize_node_for_tptp(c, predicates, terms))


def _collect_names_for_tptp(node: Node, predicates: _Renamer, terms: _Renamer) -> None:
    """First pass (see :class:`_Renamer`): register every predicate/
    function/constant name ``node`` (and its descendants) uses, without
    rewriting anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in Atom.INFIX_PREDS_TPTP and n.predicate not in Atom.PREFIX_PREDS_TPTP:
                predicates.collect(n.predicate)
        elif isinstance(n, Function):
            if n.name not in Function.TPTP_ARITH_OPS:
                terms.collect(n.name)
        elif isinstance(n, Constant):
            terms.collect(n.name)


def _sanitize_for_tptp(formulas: List[Node]) -> Tuple[List[Node], TptpNameMap]:
    """Sanitise every formula's predicate/function/constant names for TPTP.

    Returns ``(sanitised_formulas, mapping)`` — see the module docstring's
    ASCII-sanitisation section. Both namespaces (predicate; function+constant)
    are shared across ALL of ``formulas``, so the same original name maps to
    the same token everywhere (R2), and a synthesised token can never
    collide with any name anywhere in the problem, regardless of where each
    one appears (:class:`_Renamer`'s two-pass collect/finalize split).
    """
    predicates = _Renamer(prefix="p", render=tptp_fold_first_letter,
                         case_fix=_predicate_base_case)
    terms = _Renamer(prefix="n", case_fix=_term_base_case,
                     render=lambda n: tptp_fold_first_letter(constant_name_to_ascii(n)))
    for f in formulas:
        _collect_names_for_tptp(f, predicates, terms)
    predicates.finalize()
    terms.finalize()
    sanitised = [_sanitize_node_for_tptp(f, predicates, terms) for f in formulas]
    mapping = TptpNameMap(predicate=predicates.mapping, term=terms.mapping)
    return sanitised, mapping


def apply_reverse_tptp(node: Node, mapping: TptpNameMap) -> Node:
    """Translate a ``Node`` parsed from a TPTP-family prover's OWN output
    (e.g. one TSTP proof step) back to original kit-level names.

    Walks ``node`` exactly the way :func:`_sanitize_node_for_tptp` walked the
    export direction, looking up each predicate/function/constant name in
    ``mapping.reverse()``'s tables. A name the prover introduced itself (a
    Skolem constant, a CNF-clausification symbol — ``sK1``, ``esk1_0``, and
    similar) was never one of ours to begin with, so it has no entry in
    either table and is left exactly as the prover printed it, not guessed
    at or dropped.
    """
    pred_rev, term_rev = mapping.reverse()
    return _apply_reverse_tptp(node, pred_rev, term_rev)


def _apply_reverse_tptp(node: Node, pred_rev: Dict[str, str], term_rev: Dict[str, str]) -> Node:
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
            pred = node.predicate
        else:
            pred = pred_rev.get(node.predicate, node.predicate)
        return Atom(pred, [_apply_reverse_tptp(a, pred_rev, term_rev) for a in node.args])
    if isinstance(node, Function):
        # A parsed dollar-function statement (Vampire/E echoing $sum(...)
        # etc. back) already comes out of parse_tptp_formula with the
        # KIT-level operator name (tptp_input.py's dollar_func_app maps
        # "$sum" -> "+" before this function ever sees it) — the same
        # names Function.TPTP_ARITH_OPS is keyed by, not its dollar-word
        # values, so this mirrors the forward-direction check exactly.
        if node.name in Function.TPTP_ARITH_OPS:
            name = node.name
        else:
            name = term_rev.get(node.name, node.name)
        return Function(name, [_apply_reverse_tptp(a, pred_rev, term_rev) for a in node.args])
    if isinstance(node, Constant):
        return Constant(term_rev.get(node.name, node.name))
    return node.map_children(lambda c: _apply_reverse_tptp(c, pred_rev, term_rev))


# ---------------------------------------------------------------------------
# Cross-formula case-fold collision guard (pre-existing; now runs on the
# ASCII-sanitised formulas — see the module docstring).
# ---------------------------------------------------------------------------

def _check_symbol_name(seen: Dict[str, str], rendered: str, original: str, kind: str) -> None:
    """Record ``original -> rendered`` in ``seen``, or raise if it collides.

    ``seen`` maps a rendered TPTP identifier to the ONE original kit-level
    name already observed to fold to it; a second, DIFFERENT original name
    folding to the same rendered identifier is the collision this guards
    against (the same original name repeating — the ordinary case of one
    predicate/function/constant used more than once — is not a collision).
    """
    prior = seen.get(rendered)
    if prior is None:
        seen[rendered] = original
    elif prior != original:
        raise NotImplementedError(
            f"generate_tptp_problem: distinct {kind} names {prior!r} and "
            f"{original!r} would both render as the TPTP identifier "
            f"{rendered!r} (Node.to_tptp folds only the first character to "
            "lower-case, so it cannot tell these two apart) — refusing to "
            "silently merge two distinct symbols into one; rename one of "
            "them before exporting this problem."
        )


def _check_no_symbol_collisions(formulas: List[Node]) -> None:
    """Raise ``NotImplementedError`` if any two distinct predicate names, or
    any two distinct function/constant names, across ``formulas`` would fold
    to the same TPTP identifier under :meth:`Node.to_tptp` — see the module
    docstring for why this cannot be checked inside a single node's
    ``to_tptp()`` and must happen once all of a problem's formulas are known.
    """
    predicates_seen: Dict[str, str] = {}
    terms_seen: Dict[str, str] = {}  # Function and Constant share one namespace
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom):
                if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
                    continue
                rendered = tptp_fold_first_letter(node.predicate)
                _check_symbol_name(predicates_seen, rendered, node.predicate, "predicate")
            elif isinstance(node, Function):
                if node.name in Function.TPTP_ARITH_OPS:
                    continue
                rendered = tptp_fold_first_letter(node.name)
                _check_symbol_name(terms_seen, rendered, node.name, "function")
            elif isinstance(node, Constant):
                rendered = tptp_fold_first_letter(constant_name_to_ascii(node.name))
                _check_symbol_name(terms_seen, rendered, node.name, "constant/function")


def generate_tptp_problem_with_mapping(premises: List[Node], conclusion: Node
                                       ) -> Tuple[str, TptpNameMap]:
    """Like :func:`generate_tptp_problem`, but also returns the
    :class:`TptpNameMap` recording every ASCII-legality rename it applied.

    Callers that need to translate a prover's OWN output (a proof, a
    countermodel, an unsat core, ...) back to kit-level names — anything
    reading a TSTP derivation via :mod:`atp.tstp`, for instance — must use
    THIS function (not the plain :func:`generate_tptp_problem`) so they have
    the mapping :func:`apply_reverse_tptp` needs. A caller that only wants
    the problem text (nothing reads the answer's symbol names back) can keep
    using :func:`generate_tptp_problem`.
    """
    sanitised, mapping = _sanitize_for_tptp(list(premises) + [conclusion])
    sanitised_premises, sanitised_conclusion = sanitised[:-1], sanitised[-1]
    _check_no_symbol_collisions(sanitised)
    lines: List[str] = []
    for i, premise in enumerate(sanitised_premises, start=1):
        lines.append(f"fof(premise_{i}, axiom, {premise.to_tptp()}).")
    lines.append(f"fof(goal, conjecture, {sanitised_conclusion.to_tptp()}).")
    return "\n".join(lines) + "\n", mapping


def generate_tptp_problem(premises: List[Node], conclusion: Node) -> str:
    """Build a TPTP ``fof`` problem string from premises and a conclusion.

    Each premise becomes ``fof(premise_<i>, axiom, <tptp>).`` (1-based) and
    the conclusion becomes ``fof(goal, conjecture, <tptp>).``. The bodies
    come from ``Node.to_tptp`` (variables upper-cased TPTP-style, predicate/
    function/constant names folded on their first character only — see the
    module docstring), after every name has been made TPTP-ASCII-legal (see
    the module docstring's sanitisation section) — a name that was already
    legal renders byte-identically to before that step existed. Shared
    verbatim by :mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend`,
    and :mod:`atp.twee_entailment`.

    Before rendering, checks that the export stays injective across every
    premise and the conclusion TOGETHER — see the module docstring's
    soundness-guard section and :func:`_check_no_symbol_collisions`.

    A caller that also needs to translate a prover's response back to
    kit-level symbol names should call
    :func:`generate_tptp_problem_with_mapping` instead, which returns the
    same text plus the :class:`TptpNameMap` :func:`apply_reverse_tptp` needs.

    Raises:
        NotImplementedError: either (a) two distinct predicate names, or two
            distinct function/constant names, would render as the same TPTP
            identifier (the collision guard above), or (b) a premise or the
            conclusion contains a node outside the classical FOL fragment
            ``Node.to_tptp`` covers (modal / second-order / Łukasiewicz /
            lambda) — surfaced by ``to_tptp`` itself, unchanged from before
            this module existed.
    """
    text, _mapping = generate_tptp_problem_with_mapping(premises, conclusion)
    return text
