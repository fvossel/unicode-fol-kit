"""TSTP/SZS: read prover output into the kit's :mod:`atp.protocol` vocabulary.

TPTP-family provers (Vampire, E, Prover9-successors, ...) report their result
through the **SZS ontology** (Sutcliffe's "Standard for Success" status
values) on a single stdout line:

    % SZS status <value> for <problem>[ : <free-text>]

and, when asked for a proof, print the derivation itself as a sequence of
annotated TSTP statements:

    fof(name, role, formula, inference(rule, [status(thm)], [parent, ...])).
    cnf(name, role, formula, inference(rule, [status(thm)], [parent, ...])).

This module is mostly the read side of both: :func:`extract_szs_status` pulls
the first status line out of raw prover output, :func:`szs_to_verdict_fields`
maps an SZS value onto :mod:`atp.protocol`'s ``(status, reason)`` pair, and
:func:`parse_tstp_derivation` turns the annotated fof/cnf lines into a proof
DAG of :class:`TstpStep` records (reusing :mod:`fol.tptp_input` to parse each
step's formula body back into the toolkit AST). :func:`to_tstp` is the write
side's one entry point — see its own docstring for what it serialises and
why that is narrower than "the kit's own resolution search": it turns an
already-:func:`~atp.resolution_check.verify_resolution_proof`-CERTIFIED
:class:`~atp.resolution_check.ResolutionDerivation` into the annotated
``cnf(...).`` text this module's own :func:`parse_tstp_derivation` reads back
(the round trip is the write side's own test oracle), regardless of who
built that derivation.

Sources (verified against the primary spec before writing this module):

* SZS status line syntax and the full ontology of values —
  https://tptp.org/UserDocs/SZSOntology/
* TSTP annotated-formula / ``inference(rule, info, parents)`` derivation
  syntax — https://tptp.org/UserDocs/QuickGuide/Derivations.html

Conjecture vs. refutation framing
----------------------------------
The SZS *success* branch splits into two parallel vocabularies depending on
whether the TPTP problem carries a ``conjecture`` role or not:

* **with a conjecture** (``Ax ⊢ C``): ``Theorem`` (all models of Ax model C),
  ``CounterSatisfiable`` (some model of Ax models ¬C — a genuine
  countermodel), ``ContradictoryAxioms`` (Ax alone has no model, so C follows
  vacuously by ex falso quodlibet).
* **without a conjecture** (a bare clause/axiom set): ``Unsatisfiable`` (Ax
  has no model) / ``Satisfiable`` (Ax has a model).

:func:`szs_to_verdict_fields` takes a ``query`` argument spelling out which
framing produced the SZS value, because the *same* Verdict status can follow
from *different* SZS values depending on it: a resolution-refutation route
that folds ``premises ∧ ¬conclusion`` into one clause set and asks "is this
unsatisfiable?" (``query="refutation"``) proves the entailment on
``Unsatisfiable``, whereas a direct-conjecture route (``query="conjecture"``)
proves it on ``Theorem``. Feeding a conjecture-framing status to a
refutation query (or vice versa) is a mismatch this module refuses to
resolve by guessing — it comes back ``(UNKNOWN, "incomplete")``, and any SZS
value entirely outside the recognised table comes back ``(UNKNOWN, None)``;
either way the raw SZS string itself is never lost — it is whatever the
caller already passed in, only the (status, reason) pair is decided here.
"""

import re
from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterator, List, Optional, Tuple

from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol.nodes import Atom, Constant, Function, Node
from ..fol.naming import ParsingError
from ..fol.tptp_input import parse_tptp_formula
from ._tptp_problem import (
    TptpNameMap, apply_reverse_tptp,
    _check_no_symbol_collisions, _is_tptp_safe,
    _Renamer, _predicate_base_case, _term_base_case,
)
from .protocol import ERROR, PROVED, REFUTED, UNKNOWN
from .resolution_check import ResolutionDerivation, _lit_key, verify_resolution_proof

__all__ = [
    "extract_szs_status", "szs_to_verdict_fields",
    "TstpStep", "TstpDerivation", "parse_tstp_derivation",
    "reverse_map_derivation",
    "relevant_premises_from_tstp",
    "to_tstp",
]

# ---------------------------------------------------------------------------
# extract_szs_status
# ---------------------------------------------------------------------------

# "% SZS status <value> for <problem>[ : free text]" — tolerant of extra
# leading comment characters and surrounding whitespace (some tools double
# the marker or indent it), and deliberately NOT anchored on "for ..." so a
# status line lacking the problem name still yields its value. The comment
# marker set is [%#]: Vampire/Zipperposition print "% SZS status ...",
# E prints "# SZS status ..." (E's TSTP comments use '#').
_SZS_LINE_RE = re.compile(r"(?m)^[ \t]*[%#]+[ \t]*SZS\s+status\s+(\S+)")


def extract_szs_status(output: str) -> Optional[str]:
    """Return the FIRST ``SZS status`` value found in ``output``, or ``None``.

    Args:
        output: raw stdout (or stdout+stderr) from a TPTP-family prover.

    Returns:
        The bare status token (e.g. ``"Theorem"``, ``"CounterSatisfiable"``,
        ``"GaveUp"``) from the first matching line, or ``None`` if the text
        has no ``SZS status`` line at all.
    """
    match = _SZS_LINE_RE.search(output)
    return match.group(1) if match else None


# ---------------------------------------------------------------------------
# szs_to_verdict_fields
# ---------------------------------------------------------------------------

# reason values reused from atp.protocol's UNKNOWN/ERROR vocabulary; see
# that module's docstring for what each one asserts.
_TIMEOUT = "timeout"
_BOUND_HIT = "bound_hit"
_INCOMPLETE = "incomplete"
_UNSUPPORTED = "unsupported"
_INFRA = "infra"

# Values shared by both framings: no-success outcomes and the SZS values
# that mean the same thing regardless of whether a conjecture was posed.
_COMMON = {
    "Timeout": (UNKNOWN, _TIMEOUT),
    "ResourceOut": (UNKNOWN, _BOUND_HIT),
    "GaveUp": (UNKNOWN, _INCOMPLETE),
    "Inappropriate": (UNKNOWN, _UNSUPPORTED),
    "Error": (ERROR, _INFRA),
    "InputError": (ERROR, _INFRA),
    "SyntaxError": (ERROR, _INFRA),
    # "no success value has ever been established for this problem" — the
    # prover said nothing informative; distinct from a hit budget.
    "Unknown": (UNKNOWN, None),
    # Reserved for open mathematical conjectures / accepted-on-faith results
    # (TPTP problem-library ratings, not something a live prover run
    # emits) — never seen from Vampire/E in practice, mapped honestly to
    # UNKNOWN rather than silently dropped.
    "Open": (UNKNOWN, None),
    "Assumed": (UNKNOWN, None),
}

# query="conjecture": Ax ⊢ C was posed directly (a "conjecture" role formula
# in the TPTP problem). See module docstring for the semantics.
_CONJECTURE_TABLE = {
    "Theorem": (PROVED, None),
    "CounterSatisfiable": (REFUTED, None),
    # Ax alone is inconsistent -> Ax ⊢ C holds for EVERY C (ex falso
    # quodlibet); a legitimate, if degenerate, proof of the entailment.
    "ContradictoryAxioms": (PROVED, None),
    # "Satisfiable"/"Unsatisfiable" are the NO-conjecture branch's success
    # values (see docstring); seeing them here means the problem this
    # status came from did not actually carry a conjecture the way the
    # caller's query claims — refuse to guess proved/refuted from it.
    "Satisfiable": (UNKNOWN, _INCOMPLETE),
    "Unsatisfiable": (UNKNOWN, _INCOMPLETE),
}

# query="refutation": the caller already folded premises ∧ ¬conclusion into
# one axiom/clause set with NO conjecture and asked "is this satisfiable?".
_REFUTATION_TABLE = {
    # No model of (premises ∧ ¬conclusion) -> the entailment holds.
    "Unsatisfiable": (PROVED, None),
    # A model of (premises ∧ ¬conclusion) exists -> a genuine countermodel.
    "Satisfiable": (REFUTED, None),
    # "Theorem"/"CounterSatisfiable"/"ContradictoryAxioms" are the
    # WITH-conjecture branch's values; seeing them under a refutation query
    # is the mirror-image mismatch of the case above.
    "Theorem": (UNKNOWN, _INCOMPLETE),
    "CounterSatisfiable": (UNKNOWN, _INCOMPLETE),
    "ContradictoryAxioms": (UNKNOWN, _INCOMPLETE),
}

def szs_to_verdict_fields(szs: str, *, query: str) -> Tuple[str, Optional[str]]:
    """Map an SZS status value onto ``atp.protocol``'s ``(status, reason)``.

    Args:
        szs: a bare SZS status token, e.g. from :func:`extract_szs_status`
            (``"Theorem"``, ``"CounterSatisfiable"``, ``"GaveUp"``, ...).
        query: which framing produced ``szs`` — ``"conjecture"`` (the prover
            was handed premises plus a ``conjecture``-role formula and asked
            to prove it) or ``"refutation"`` (the prover was handed
            ``premises ∧ ¬conclusion`` as one clause/axiom set with no
            conjecture and asked whether it is satisfiable). See the module
            docstring for why the same Verdict status follows from different
            SZS values under the two framings.

    Returns:
        A ``(status, reason)`` pair drawn from :mod:`atp.protocol`'s
        vocabulary. ``reason`` is only ever non-``None`` when
        ``status == UNKNOWN`` or ``status == ERROR``, matching
        :class:`atp.protocol.Verdict`'s contract.

    Raises:
        ValueError: ``query`` is neither ``"conjecture"`` nor ``"refutation"``.

    Any ``szs`` value this table does not recognise — including a
    recognised value fed the WRONG ``query`` (see module docstring) — comes
    back as ``(UNKNOWN, None)`` or ``(UNKNOWN, "incomplete")`` rather than a
    guessed proved/refuted; this function never invents a definitive verdict
    from an unfamiliar or mismatched SZS token.
    """
    if query == "conjecture":
        table, other_table = _CONJECTURE_TABLE, _REFUTATION_TABLE
    elif query == "refutation":
        table, other_table = _REFUTATION_TABLE, _CONJECTURE_TABLE
    else:
        raise ValueError(
            f"szs_to_verdict_fields: query must be 'conjecture' or 'refutation', got {query!r}")

    if szs in table:
        return table[szs]
    if szs in _COMMON:
        return _COMMON[szs]
    if szs in other_table:
        # Recognised, but only under the OTHER framing — an explicit
        # query/status mismatch (see module docstring); reported the same
        # as an unrecognised value except for the reason, so a caller that
        # logs UNKNOWN/incomplete can tell "mismatch" from "no info" apart
        # from the SZS string it already has in hand.
        return (UNKNOWN, _INCOMPLETE)
    return (UNKNOWN, None)


# ---------------------------------------------------------------------------
# TSTP derivation parsing
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TstpStep:
    """One annotated TSTP statement: ``language(name, role, formula, source).``

    Fields:

    ``name``
        the statement's TSTP name (``"f1"``, ``"c_0_7"``, a bare number, …),
        verbatim.
    ``language``
        ``"fof"`` or ``"cnf"`` (the only two this module reads — ``tff`` /
        ``thf`` lines are skipped, see :func:`parse_tstp_derivation`).
    ``role``
        the TSTP role verbatim (``"axiom"``, ``"plain"``,
        ``"negated_conjecture"``, ``"lemma"``, …), not validated against a
        fixed vocabulary.
    ``formula_text``
        the formula's TSTP source text, verbatim, always present regardless
        of whether it parsed.
    ``formula``
        ``formula_text`` parsed into a toolkit :class:`Node` via
        :func:`fol.tptp_input.parse_tptp_formula`, or ``None`` if that parse
        failed (a TSTP formula shape the grammar does not cover, e.g. one
        carrying ``$distinct`` or other constructs outside its scope) — the
        raw text is kept either way, nothing is lost.
    ``rule``
        the inference rule name from an ``inference(rule, info, parents)``
        source record, or ``None`` for a leaf statement (a ``file(…)``
        source, no source field at all, or a source form this module does not
        interpret, e.g. ``introduced(…)``).
    ``parents``
        names of the statements this one was derived from, read from an
        ``inference(…)`` source's parent list; empty for a leaf statement or
        when every parent-list entry is itself a compound term (e.g.
        ``theory(equality)``, or a prover's inline-nested ``inference(…)``
        parent) rather than a bare name/number.
    """

    name: str
    language: str
    role: str
    formula_text: str
    formula: Optional[Node]
    rule: Optional[str]
    parents: Tuple[str, ...] = ()

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (``formula`` via ``Node.to_dict``)."""
        return {
            "name": self.name,
            "language": self.language,
            "role": self.role,
            "formula_text": self.formula_text,
            "formula": self.formula.to_dict() if self.formula is not None else None,
            "rule": self.rule,
            "parents": list(self.parents),
        }


@dataclass(frozen=True)
class TstpDerivation:
    """An ordered sequence of :class:`TstpStep`, in the order they appeared."""

    steps: Tuple[TstpStep, ...]

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {"steps": [s.to_dict() for s in self.steps]}


# A "fof(" / "cnf(" statement start: the keyword must not be preceded by an
# identifier character (so it never fires inside a longer name), matched
# case-sensitively since TPTP keywords are lowercase by the standard.
_STMT_START_RE = re.compile(r"(?<![A-Za-z0-9_])(fof|cnf)\(")

_OPEN = "(["
_CLOSE = ")]"


def _skip_comment(text: str, i: int, n: int) -> int:
    """If ``text[i:]`` starts a ``%`` line comment or ``/* */`` block comment,
    return the index just past it; otherwise return ``i`` unchanged."""
    if text[i] == "%":
        j = text.find("\n", i)
        return n if j == -1 else j + 1
    if text.startswith("/*", i):
        j = text.find("*/", i + 2)
        return n if j == -1 else j + 2
    return i


def _skip_quoted(text: str, i: int, n: int) -> int:
    """If ``text[i]`` opens a ``'...'`` or ``"..."`` TPTP quoted token
    (``\\`` escapes the next character), return the index just past its
    closing quote; otherwise return ``i`` unchanged."""
    quote = text[i]
    if quote not in ("'", '"'):
        return i
    j = i + 1
    while j < n and text[j] != quote:
        j += 2 if text[j] == "\\" else 1
    return min(j + 1, n)


def _iter_tstp_statements(text: str):
    """Yield ``(language, statement_text)`` for every top-level ``fof(...)./
    cnf(...).`` statement in ``text``, comments and quoted tokens skipped.

    ``statement_text`` is the exact source span from the ``fof``/``cnf``
    keyword through the terminating ``.`` inclusive. Bracket depth is
    tracked over BOTH ``()`` and ``[]`` (TPTP variable/argument lists use
    ``[]``, and a naive parens-only count would mis-split on the commas
    inside one) so nested source/inference records are captured whole. A
    statement whose closing bracket is never followed by ``.`` (malformed
    input, or the text was truncated mid-statement) is silently skipped —
    :func:`parse_tstp_derivation` only ever sees whole statements.
    """
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        if c in "%" or text.startswith("/*", i):
            i = _skip_comment(text, i, n)
            continue
        if c.isspace():
            i += 1
            continue
        match = _STMT_START_RE.match(text, i)
        if not match:
            i += 1
            continue
        language = match.group(1)
        start = i
        k = match.end()          # just past the opening '('
        depth = 1
        while k < n and depth > 0:
            c = text[k]
            if c == "%" or text.startswith("/*", k):
                k = _skip_comment(text, k, n)
                continue
            if c in ("'", '"'):
                k = _skip_quoted(text, k, n)
                continue
            if c in _OPEN:
                depth += 1
            elif c in _CLOSE:
                depth -= 1
            k += 1
        p = k
        while p < n and text[p] in " \t":
            p += 1
        if p < n and text[p] == ".":
            yield language, text[start:p + 1]
            i = p + 1
        else:
            i = match.end()       # malformed: resume scanning past the keyword


def _split_top_level(s: str) -> List[str]:
    """Split ``s`` on commas at bracket-depth 0 (``()``/``[]``, quotes-aware)."""
    parts: List[str] = []
    buf: List[str] = []
    n = len(s)
    depth = 0
    i = 0
    while i < n:
        c = s[i]
        if c in ("'", '"'):
            j = _skip_quoted(s, i, n)
            buf.append(s[i:j])
            i = j
            continue
        if c in _OPEN:
            depth += 1
            buf.append(c)
            i += 1
            continue
        if c in _CLOSE:
            depth -= 1
            buf.append(c)
            i += 1
            continue
        if c == "," and depth == 0:
            parts.append("".join(buf))
            buf = []
            i += 1
            continue
        buf.append(c)
        i += 1
    parts.append("".join(buf))
    return [p.strip() for p in parts]


def _parse_source(source_text: Optional[str]) -> Tuple[Optional[str], Tuple[str, ...]]:
    """Read a statement's 4th field into ``(rule, parents)``.

    Only the ``inference(rule, useful_info, parents)`` source form is
    interpreted (rule = its 1st field, parents = the bare-name entries of
    its LAST field, which is the parent list in every arity TSTP writers
    use — 2-field ``inference(rule, parents)`` and 3-field
    ``inference(rule, info, parents)`` alike). Any other source
    (``file(...)``, ``introduced(...)``, absent) yields ``(None, ())`` — this
    module does not guess a rule name for forms it was not asked to parse.
    """
    if not source_text or not source_text.startswith("inference("):
        return None, ()
    inner = source_text[len("inference("):-1]
    fields = _split_top_level(inner)
    if not fields:
        return None, ()
    rule = fields[0].strip() or None
    parents_field = fields[-1].strip()
    if not (parents_field.startswith("[") and parents_field.endswith("]")):
        return rule, ()
    items = _split_top_level(parents_field[1:-1])
    parents = tuple(it for it in (item.strip() for item in items) if it and "(" not in it)
    return rule, parents


def parse_tstp_derivation(output: str) -> TstpDerivation:
    """Parse every top-level ``fof``/``cnf`` statement out of prover output.

    Args:
        output: raw prover stdout containing zero or more TSTP-annotated
            ``fof(...).``/``cnf(...).`` statements (interspersed with SZS
            status lines, banners, timing info, ... — all of that is
            skipped; only lines that are themselves whole ``fof``/``cnf``
            statements become a :class:`TstpStep`).

    Returns:
        A :class:`TstpDerivation` with one :class:`TstpStep` per statement,
        in source order. ``steps`` is empty (not an error) when ``output``
        contains no ``fof``/``cnf`` statement at all — e.g. a bare
        ``SZS status Theorem`` line with proof output not requested.
    """
    steps = []
    for language, stmt_text in _iter_tstp_statements(output):
        inner = stmt_text[stmt_text.index("(") + 1:-2]   # strip 'LANG(' and ').'
        fields = _split_top_level(inner)
        if len(fields) < 3:
            continue                                      # malformed statement
        name, role, formula_text = fields[0], fields[1], fields[2]
        source_text = fields[3] if len(fields) > 3 else None
        try:
            formula: Optional[Node] = parse_tptp_formula(formula_text)
        except ParsingError:
            formula = None
        rule, parents = _parse_source(source_text)
        steps.append(TstpStep(
            name=name, language=language, role=role,
            formula_text=formula_text, formula=formula,
            rule=rule, parents=parents,
        ))
    return TstpDerivation(steps=tuple(steps))


# ---------------------------------------------------------------------------
# Rückweg: translate a derivation's formulas back to kit-level symbol names.
# ---------------------------------------------------------------------------

def reverse_map_derivation(derivation: TstpDerivation, mapping: TptpNameMap) -> TstpDerivation:
    """Return a copy of ``derivation`` with every step's ``formula`` rewritten
    from the sanitised TPTP-ASCII identifiers :func:`atp._tptp_problem
    .generate_tptp_problem_with_mapping` chose back to the original
    kit-level names, via ``mapping`` (see :func:`atp._tptp_problem
    .apply_reverse_tptp`).

    ``formula_text`` — the prover's own verbatim printed form of the step —
    is deliberately left UNTOUCHED: it stays a truthful record of exactly
    what the prover said, while ``formula`` becomes the structured form a
    caller actually wants to read symbol names off of. A step whose formula
    failed to parse (``formula is None``) passes through unchanged, and a
    symbol the prover introduced itself (a Skolem constant, a
    clausification name — ``sK1``, ``esk1_0``, ...) was never one of ours
    to begin with, so :func:`apply_reverse_tptp` leaves it exactly as
    printed rather than guessing at it.
    """
    new_steps = tuple(
        step if step.formula is None else
        TstpStep(name=step.name, language=step.language, role=step.role,
                 formula_text=step.formula_text,
                 formula=apply_reverse_tptp(step.formula, mapping),
                 rule=step.rule, parents=step.parents)
        for step in derivation.steps
    )
    return TstpDerivation(steps=new_steps)


# ---------------------------------------------------------------------------
# Premise relevance: which axiom-role leaves does a derivation's refutation
# actually rest on?
#
# This is a SEPARATE walk from parse_tstp_derivation/TstpStep.parents above,
# deliberately — _parse_source (and therefore TstpStep.parents) intentionally
# DROPS a parent-list entry that is itself a compound term (a prover's own
# unnamed, nested `inference(...)` sub-step, or a `theory(equality)` marker —
# pinned by test_nested_inference_parents_that_are_compound_terms_are_dropped
# in tests/test_tstp.py), which is the right choice for a proof-DAG *display*
# (an unnamed intermediate has nothing else to call it) but would silently
# UNDER-count a derivation's real axiom leaves for a relevance query: E's own
# output nests almost every real inference this way (administrative steps
# like fof_nnf/variable_rename that never get their own c_0_N name — see
# tests/fixtures/eprover_3_5_1_theorem.txt). So the functions below re-scan
# the raw statement text directly (via _iter_tstp_statements/_split_top_level,
# the same low-level splitters parse_tstp_derivation itself uses) rather than
# going through TstpStep at all, and recurse into nested inference(...) parent
# entries instead of dropping them. TstpStep.parents/_parse_source are left
# completely untouched by this section.
# ---------------------------------------------------------------------------

def _iter_statement_fields(output: str) -> Iterator[Tuple[str, str, str, Optional[str]]]:
    """Yield ``(name, role, formula_text, source_text)`` for every top-level
    ``fof``/``cnf`` statement in ``output`` — the same fields
    :func:`parse_tstp_derivation` extracts per :class:`TstpStep`, except
    ``source_text`` is kept RAW (the unparsed 4th field, or ``None``)
    instead of being reduced to ``(rule, parents)`` — :func:`_deep_ancestor_names`
    below needs the raw text to recurse into nested ``inference(...)`` terms.
    """
    for _language, stmt_text in _iter_tstp_statements(output):
        inner = stmt_text[stmt_text.index("(") + 1:-2]   # strip 'LANG(' and ').'
        fields = _split_top_level(inner)
        if len(fields) < 3:
            continue                                      # malformed statement
        name, role, formula_text = fields[0], fields[1], fields[2]
        source_text = fields[3] if len(fields) > 3 else None
        yield name, role, formula_text, source_text


def _deep_ancestor_names(source_text: Optional[str]) -> FrozenSet[str]:
    """Recursively collect every bare leaf name reachable from ``source_text``
    (one statement's raw 4th field), descending into nested ``inference(...)``
    parent-list entries instead of dropping them the way :func:`_parse_source`
    does (see this section's module comment).

    A bare name/number parent-list entry is a leaf name; an
    ``inference(rule, info, parents)`` entry is descended into (its own LAST
    field is ITS parents list, read the same way — arity-agnostic, exactly
    like :func:`_parse_source`); any other compound entry (``theory(equality)``,
    ...) contributes no name of its own but does not stop the REST of the
    list from being read — the difference from :func:`_parse_source`, which
    drops the whole list once any entry is compound.

    Returns an empty set for a non-``inference`` source (``file(...)``, no
    source field at all, ``introduced(...)``, ...) — that statement is a
    leaf itself, with no ancestors to report.
    """
    if not source_text or not source_text.startswith("inference("):
        return frozenset()
    inner = source_text[len("inference("):-1]
    fields = _split_top_level(inner)
    if not fields:
        return frozenset()
    parents_field = fields[-1].strip()
    if not (parents_field.startswith("[") and parents_field.endswith("]")):
        return frozenset()
    names: set = set()
    for item in _split_top_level(parents_field[1:-1]):
        item = item.strip()
        if not item:
            continue
        if item.startswith("inference("):
            names |= _deep_ancestor_names(item)
        elif "(" not in item:
            names.add(item)
        # else: an uninterpreted compound term (theory(equality), a source
        # form this module was not asked to descend into, ...) -- no name
        # to report, matching _parse_source's treatment of the same shape.
    return frozenset(names)


def _is_false_formula(formula_text: str) -> bool:
    """Whether a statement's (raw, unparsed) formula text is ``$false``,
    modulo the surrounding whitespace/parentheses a prover's pretty-printer
    adds (``"($false)"``, ``"(\\n  $false)"``, ...) — the textual marker of
    a resolution refutation's SINK step, independent of whether the text
    happens to parse (:func:`parse_tptp_formula` does understand ``$false``,
    but this check is purely textual so it never depends on that grammar
    staying in sync)."""
    t = formula_text.strip()
    while t.startswith("(") and t.endswith(")"):
        inner = t[1:-1].strip()
        if inner == t:            # no progress -- stop, avoid looping forever
            break
        t = inner
    return t == "$false"


def _walk_axiom_leaves(start_names: List[str],
                       statements: Dict[str, Tuple[str, str, Optional[str]]]
                       ) -> Optional[FrozenSet[str]]:
    """Walk backward from every name in ``start_names`` through
    ``statements``'s (possibly nested) ``inference(...)`` ancestor chains
    down to every reachable ``axiom``-role leaf's NAME.

    Returns ``None`` when the walk reaches a cited name that ``statements``
    does not itself define (an incomplete derivation excerpt) — refuse
    rather than guess, same contract as the caller.
    """
    axioms: set = set()
    stack = list(start_names)
    visited: set = set()
    while stack:
        name = stack.pop()
        if name in visited:
            continue
        visited.add(name)
        entry = statements.get(name)
        if entry is None:
            return None          # a cited name this module cannot resolve
        role, _formula_text, source_text = entry
        ancestors = _deep_ancestor_names(source_text)
        if not ancestors:
            if role == "axiom":
                axioms.add(name)
            continue
        stack.extend(a for a in ancestors if a not in visited)
    return frozenset(axioms)


def _relevant_axiom_names(output: str) -> Optional[FrozenSet[str]]:
    """Walk ``output``'s derivation backward from its sink step(s) through
    the (possibly nested) ``inference(...)`` chain, down to every reachable
    ``axiom``-role leaf's NAME.

    The sinks are the steps whose formula text is ``$false`` — the final
    empty clause of a refutation (both the E-prover and Vampire fixtures in
    tests/test_tstp.py/eprover_3_5_1_*.txt end this way). A text with no
    ``$false`` step is not a refutation at all (E's Saturation report for a
    non-theorem, a truncated excerpt, ...), so there is nothing a premise
    could be relevant *to*: ``None``.

    What a non-``None`` result means: the leaves reachable from the sinks.
    Every ``$false`` step together with its ancestors is a derivation of the
    contradiction from exactly those leaves (plus the negated conjecture), so
    the reachable axioms are SUFFICIENT for the entailment — provided the
    prover's own inferences are sound, which is the trust this route already
    places in the prover's PROVED verdict. When a text holds several
    ``$false`` steps the union of their leaves is reported: each part is
    sufficient on its own, so the union is too. The set is therefore never
    an under-approximation of a sufficient set, but it is not claimed to be
    minimal.

    Returns ``None`` — refuse rather than guess, see this section's module
    comment — when: there is no ``fof``/``cnf`` statement in ``output`` at
    all; no step is ``$false``; or the walk reaches a cited name that is not
    itself defined anywhere in ``output`` (an incomplete derivation excerpt).
    A non-``None`` result is a genuine axiom-name set, even if empty (the
    negated conjecture alone was contradictory).
    """
    statements: Dict[str, Tuple[str, str, Optional[str]]] = {}
    for name, role, formula_text, source_text in _iter_statement_fields(output):
        statements[name] = (role, formula_text, source_text)
    if not statements:
        return None

    sinks = [name for name, (_role, ftext, _src) in statements.items()
            if _is_false_formula(ftext)]
    if not sinks:
        return None
    return _walk_axiom_leaves(sinks, statements)


_PREMISE_NAME_RE = re.compile(r"^premise_(\d+)$")


def relevant_premises_from_tstp(output: str, n_premises: int) -> Optional[Tuple[int, ...]]:
    """Which ``premise_<i>`` axioms (1-based, this module's own naming
    convention — see :func:`atp._tptp_problem.generate_tptp_problem`) does a
    TSTP derivation's refutation actually rest on?

    Walks backward from the derivation's sink step(s) through the (possibly
    nested) ``inference(...)`` chain via :func:`_relevant_axiom_names`, down
    to every reachable ``axiom``-role leaf, then keeps only the leaves named
    ``premise_<i>`` — E's own convention for a route that used
    :func:`atp._tptp_problem.generate_tptp_problem`/
    ``generate_tptp_problem_with_mapping`` (verified live: E's leaf names
    equal ``premise_<i>`` VERBATIM, never renamed). This is genuinely NOT
    the same walk as :func:`parse_tstp_derivation`'s ``TstpStep.parents``
    alone would give (see this section's module comment): a leaf hidden
    behind a prover's own nested, unnamed administrative inference would be
    silently lost by ``.parents`` alone, under-reporting the true premise set.

    Args:
        output: raw prover stdout containing the TSTP derivation.
        n_premises: how many premises the original call had — used only to
            validate every ``premise_<i>`` name found is in range; a name
            outside ``1..n_premises`` makes the whole result untrustworthy
            (this module's own naming convention was not the one actually
            used, so nothing here can be trusted), reported as ``None``.

    Returns:
        A sorted tuple of 0-based indices into the caller's premise list, or
        ``None`` when the walk cannot be trusted — see
        :func:`_relevant_axiom_names`'s ``Returns`` for when THAT happens,
        plus: an axiom-role leaf whose name does not match
        ``premise_<i>``/``1<=i<=n_premises`` (this module's own generator
        was evidently not what produced ``output``). ``None`` is always the
        honest "don't know", never a silently under-approximated subset —
        the kit's refuse-loudly rule; a wrong "premises used" answer is
        worse for an eval pipeline than an honest absence of one.
    """
    axiom_names = _relevant_axiom_names(output)
    if axiom_names is None:
        return None
    indices: set = set()
    for name in axiom_names:
        match = _PREMISE_NAME_RE.match(name)
        if not match or not (1 <= int(match.group(1)) <= n_premises):
            return None
        indices.add(int(match.group(1)) - 1)
    return tuple(sorted(indices))


# ---------------------------------------------------------------------------
# Hinweg: serialise a CERTIFIED ResolutionDerivation as annotated TSTP text —
# the write-side companion to parse_tstp_derivation above.
#
# Scope, precisely: this does NOT let the kit hand off proofs "it discovered"
# — atp.resolution.py's refute()/prove() return a bare bool and build no
# ResolutionDerivation trace, so there is no derivation object of the kit's
# OWN search to export. What this writer does serialise is whatever
# ResolutionDerivation the kit has independently CERTIFIED via
# atp.resolution_check.verify_resolution_proof, regardless of who
# constructed it (today: hand-authored fixtures, or a derivation transcribed
# from elsewhere and checked by the kit) — see :func:`to_tstp`'s Raises.
# ---------------------------------------------------------------------------

# Kit rule name -> TSTP inference-rule token. TSTP does not standardise this
# vocabulary (any stable string is spec-conformant, since it is purely
# informational — see the TPTP QuickGuide's own derivation grammar), so the
# tokens below are chosen to match what atp.tstp_check's VAMPIRE_CHECKED_RULES
# / EPROVER_CHECKED_RULES tables actually dispatch on, NOT the arbitrary
# strings a first pass at this mapping might reach for, because a token
# tstp_check does not recognise makes the emitted step come back "unchecked"
# by the independent second route rather than genuinely re-derived:
#
# - "resolve" -> "resolution": _check_tstp_resolve is a direct, unmodified
#   port of resolution_check._check_resolve_step, so the semantics match
#   exactly, not just generalize it.
# - "factor" -> "factoring": likewise a direct port of
#   resolution_check._check_factor_step.
# - "paramodulate" -> "superposition", NOT the more obvious "paramodulation"
#   (which tstp_check does not register in either checked-rule table at
#   all — it would come back unchecked): _check_tstp_superposition
#   generalizes resolution_check._check_paramodulate_step (same equation/
#   target/direction/position recipe, searched instead of trusted) and tries
#   both parent-role assignments, so it accepts a "paramodulate" step's
#   (equation, target) parent order either way.
# - "demodulate" -> "rw" (E's abbreviation for its rewrite/demodulation
#   rule; "forward_demodulation"/"backward_demodulation" dispatch to the
#   identical checker and would work equally well): _check_tstp_demodulation
#   generalizes resolution_check._check_demodulate_step (one-sided matching,
#   term-order-checked orientation) and, like the superposition checker
#   above, tries both parent orders.
# - "reflexivity" -> "equality_resolution", NOT "eq_resolution" (which does
#   not exist in tstp_check's vocabulary either — TSTP/Vampire's own name for
#   this rule is "equality_resolution", E's abbreviation "er"):
#   _check_tstp_equality_resolution generalizes
#   resolution_check._check_reflexivity_step (search over every negative
#   equality literal instead of trusting a stated eq_literal).
#
# "input" has no entry here: an input step carries no inference(...) source
# at all (see to_tstp), matching how parse_tstp_derivation reads a leaf
# statement (TstpStep.rule is None) and how atp.tstp_check's "leaf" tier
# checks it (alpha-variant of a supplied premise, not a rule re-derivation).
_KIT_RULE_TO_TSTP: Dict[str, str] = {
    "resolve": "resolution",
    "factor": "factoring",
    "paramodulate": "superposition",
    "demodulate": "rw",
    "reflexivity": "equality_resolution",
}


def _collect_name_case_safe(renamer: _Renamer, name: str) -> None:
    """Like :meth:`atp._tptp_problem._Renamer.collect`, but ALSO requires
    ``name`` to already match this namespace's own round-trip-safe case
    convention (``renamer.case_fix(name) == name`` — uppercase-initial for
    predicates, lowercase-initial for terms) before treating it as an
    untouched identity.

    Why :meth:`_Renamer.collect`'s plain :func:`atp._tptp_problem
    ._is_tptp_safe` check is not enough here (a real, reviewer-found
    blocker): that check is case-INSENSITIVE (it only asks "is this ASCII
    and letter-initial", not "is this the case my namespace round-trips"),
    so it happily reserves e.g. a lower-case predicate ``"bar"`` or an
    upper-case-initial constant ``"Foo"`` AS ITSELF. But
    :meth:`~fol.nodes.Node.to_tptp` folds only the FIRST character on
    export, and :func:`fol.tptp_input._cap` UNCONDITIONALLY upper-cases a
    parsed predicate's first character on import (no compensating step
    exists for constants/functions at all) — so an identity-mapped name
    whose real first-letter case does not already match what the reader
    will reconstruct is never recoverable: ``apply_reverse_tptp`` comes back
    with a DIFFERENTLY-cased name than the one actually serialised, with no
    error anywhere (confirmed: a derivation-level ``Atom.predicate``/
    ``Constant.name`` is a plain, case-unchecked ``str`` field, and
    :func:`~atp.resolution_check.verify_resolution_proof` never inspects
    case, so nothing upstream of this function rules the input out).

    A name that fails this stricter test is routed through the exact same
    queued-for-synthesis path :meth:`_Renamer.collect` uses for a genuinely
    illegal name (``self._pending``), so it still gets a properly-cased,
    de-collided token — :meth:`_Renamer.finalize` already runs ``case_fix``
    on every synthesised base, so this only changes WHICH names go through
    that path, not the synthesis logic itself.
    """
    if name in renamer.mapping or name in renamer._pending:
        return
    if _is_tptp_safe(name) and renamer.case_fix(name) == name:
        renamer.used.add(renamer.render(name))
        renamer.mapping[name] = name
    else:
        renamer._pending.append(name)


def _collect_names_for_derivation(node: Node, predicates: _Renamer, terms: _Renamer) -> None:
    """The exact walk :func:`atp._tptp_problem._collect_names_for_tptp` does
    (same infix/prefix/arithmetic exclusions), routed through
    :func:`_collect_name_case_safe` instead of :meth:`_Renamer.collect`
    directly — see that function's docstring for why."""
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in Atom.INFIX_PREDS_TPTP and n.predicate not in Atom.PREFIX_PREDS_TPTP:
                _collect_name_case_safe(predicates, n.predicate)
        elif isinstance(n, Function):
            if n.name not in Function.TPTP_ARITH_OPS:
                _collect_name_case_safe(terms, n.name)
        elif isinstance(n, Constant):
            _collect_name_case_safe(terms, n.name)


def _extend_name_map_for_derivation(
    derivation: ResolutionDerivation, name_map: Optional[TptpNameMap]
) -> TptpNameMap:
    """Return a :class:`TptpNameMap` that covers every predicate/function/
    constant name ``derivation`` actually uses, seeded from ``name_map``
    where the caller supplied one.

    Mirrors :func:`atp._tptp_problem._sanitize_for_tptp`'s own two-pass
    collect/finalize :class:`atp._tptp_problem._Renamer` split — the two
    namespaces (predicate; function+constant), the never-renamed
    infix/prefix/arithmetic exclusions, everything — but *seeds* each
    namespace's ``mapping``/``used`` from ``name_map`` first (a shallow copy;
    the caller's ``TptpNameMap`` is never mutated) instead of starting empty,
    and collects each name via :func:`_collect_name_case_safe` (through
    :func:`_collect_names_for_derivation`) rather than
    :meth:`~atp._tptp_problem._Renamer.collect` directly — see that
    function's docstring for the case-safety blocker this closes.
    ``name_map is None`` seeds nothing, so this reduces to exactly what
    :func:`_sanitize_for_tptp` would build from scratch, MODULO that same
    case-safety fix — the ``name_map`` argument's documented "``None``
    builds a fresh mapping" behaviour is this function's degenerate case,
    not a separate code path.

    This is what makes reusing a caller-supplied ``name_map`` actually SAFE:
    a symbol ``name_map`` already covers keeps exactly that spelling (the
    documented "identical spellings across a problem export and this proof"
    contract), while a symbol ``derivation`` uses that ``name_map`` does
    *not* cover — e.g. a Skolem constant introduced only in the proof, never
    in the problem the map was built from — is collected/finalised exactly
    as a fresh :func:`_sanitize_for_tptp` call would (modulo the case-safety
    fix above): an already-TPTP-legal, already-correctly-cased name passes
    through unchanged; anything else (non-ASCII, digit-leading, wrong-case,
    …) is synthesised a legal, correctly-cased token, de-collided against
    every token ``name_map`` already chose *and* every other symbol
    ``derivation`` uses. Previously :func:`_apply_forward_tptp` passed an
    uncovered name through completely unsanitised, which silently emitted
    illegal TSTP for exactly this scenario (a digit-leading or non-ASCII
    symbol absent from a caller's ``name_map``); this closes that gap before
    any text is ever rendered, so illegal TSTP can no longer reach
    :func:`to_tstp`'s output. A second, more subtle instance of the same
    root cause — a symbol that is TPTP-LEGAL but wrong-case, e.g. a
    lower-case predicate or an upper-case-initial constant — silently broke
    the round trip rather than the raw legality (see
    :func:`_collect_name_case_safe`); both are closed the same way, by
    routing the name through synthesis instead of identity.
    """
    predicates = _Renamer(prefix="p", render=tptp_fold_first_letter,
                         case_fix=_predicate_base_case)
    terms = _Renamer(prefix="n", case_fix=_term_base_case,
                     render=lambda n: tptp_fold_first_letter(constant_name_to_ascii(n)))
    if name_map is not None:
        predicates.mapping = dict(name_map.predicate)
        terms.mapping = dict(name_map.term)
        predicates.used = {predicates.render(token) for token in predicates.mapping.values()}
        terms.used = {terms.render(token) for token in terms.mapping.values()}
    for step in derivation.steps:
        for literal in step.clause:
            _collect_names_for_derivation(literal, predicates, terms)
    predicates.finalize()
    terms.finalize()
    return TptpNameMap(predicate=predicates.mapping, term=terms.mapping)


def _name_map_sentinel_nodes(name_map: TptpNameMap) -> List[Node]:
    """One bare, zero-arity sentinel node per token ``name_map`` assigns —
    an ``Atom`` for each ``predicate`` value, a ``Constant`` for each
    ``term`` value — so :func:`atp._tptp_problem._check_no_symbol_collisions`
    can see every symbol a (possibly caller-supplied) ``name_map`` already
    commits to, not just the ones ``derivation`` happens to repeat.

    Why this is needed (a second reviewer-found gap, distinct from the
    identity/case one above): the collision guard only ever walks actual AST
    nodes, so a token ``name_map`` records for a name that is NOT used
    anywhere in ``derivation`` — the writer's own advertised primary use
    case, reusing a mapping built from an unrelated problem — is otherwise
    invisible to it, even though it still ends up in the rendered text's
    namespace. :func:`_extend_name_map_for_derivation` does correctly seed
    ``used`` from every token a caller-supplied ``name_map`` already
    reserves, so a genuinely NEW symbol ``derivation`` introduces always
    gets de-collided against it via :meth:`~atp._tptp_problem._Renamer
    .finalize`'s ``reserve_rendered`` call — but an already-legal,
    already-correctly-cased identity (the fast path both
    :meth:`atp._tptp_problem._Renamer.collect` and
    :func:`_collect_name_case_safe` above take) is reserved unconditionally,
    without first checking ``used`` — by design (R1 in
    :class:`atp._tptp_problem._Renamer`'s own docstring: "an already-legal
    name is never renamed", so it must never be skipped just because it
    might collide). If ``name_map`` ITSELF already carries a case-UNSAFE
    identity entry for one name (which can legitimately happen today, since
    :mod:`atp._tptp_problem`'s own ``_Renamer.collect`` still has the exact
    ``_is_tptp_safe``-only gap :func:`_collect_name_case_safe` closes for
    THIS module — e.g. ``generate_tptp_problem_with_mapping`` on a
    ``Constant("Foo")`` returns ``mapping.term == {"Foo": "Foo"}``, and
    fixing that is outside this item's file ownership), a derivation that
    separately introduces that entry's correctly-cased counterpart (e.g.
    ``"foo"``) takes the fast identity path on ITS OWN side too — both are
    "already legal, never renamed" in isolation, so neither is ever compared
    to the other unless something also walks ``name_map``'s own tokens.
    This is that something: it is passed to :func:`atp._tptp_problem
    ._check_no_symbol_collisions` alongside the derivation's own sanitised
    literals, so the two are checked together, not merged silently.
    """
    nodes: List[Node] = []
    for token in name_map.predicate.values():
        nodes.append(Atom(token, []))
    for token in name_map.term.values():
        nodes.append(Constant(token))
    return nodes


def _apply_forward_tptp(node: Node, mapping: TptpNameMap) -> Node:
    """Translate ``node``'s predicate/function/constant names from kit-level
    to the sanitised TPTP-ASCII tokens ``mapping`` records — the forward
    companion to :func:`atp._tptp_problem.apply_reverse_tptp`, walking a
    :class:`Node` the exact same way
    :func:`atp._tptp_problem._sanitize_node_for_tptp` does (the infix/prefix
    TPTP predicates and the arithmetic function operators are never renamed,
    matching both that function and :func:`apply_reverse_tptp`).

    A name absent from ``mapping`` is left exactly as it is — safe ONLY
    because :func:`to_tstp` always calls this with a ``mapping`` already
    extended by :func:`_extend_name_map_for_derivation`, which guarantees
    every predicate/function/constant name ``node`` can possibly carry (it
    walks the very same ``derivation.steps`` this ``node`` came from) is
    already present, sanitised (and correctly CASED — see
    :func:`_collect_name_case_safe`) if it needed to be. This passthrough
    branch is exercised only by a name that is both already-TPTP-legal AND
    already in this namespace's own round-trip-safe case (mapped to itself
    by :func:`_collect_name_case_safe`), never by a name genuinely missing
    from ``mapping`` or one whose case would not survive the reader's own
    first-letter fold/cap — do not call this directly with a hand-built or
    otherwise unextended ``mapping``. :func:`to_tstp` also runs
    :func:`atp._tptp_problem._check_no_symbol_collisions` over every
    sanitised literal AND, via :func:`_name_map_sentinel_nodes`, over every
    token the (possibly caller-supplied) ``mapping`` itself already commits
    to — so two distinct symbols that happen to render to the same token are
    still caught, not silently merged, even when one of the two lives only
    in a reused ``name_map`` and never appears in ``derivation`` itself
    (mirroring :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`'s
    own sanitise-then-check-collisions layering, widened to cover a reused
    mapping's own entries too).
    """
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
            pred = node.predicate
        else:
            pred = mapping.predicate.get(node.predicate, node.predicate)
        return Atom(pred, [_apply_forward_tptp(a, mapping) for a in node.args])
    if isinstance(node, Function):
        if node.name in Function.TPTP_ARITH_OPS:
            name = node.name
        else:
            name = mapping.term.get(node.name, node.name)
        return Function(name, [_apply_forward_tptp(a, mapping) for a in node.args])
    if isinstance(node, Constant):
        return Constant(mapping.term.get(node.name, node.name))
    return node.map_children(lambda c: _apply_forward_tptp(c, mapping))


def _render_clause_tptp(clause: FrozenSet[Node], mapping: TptpNameMap) -> List[Node]:
    """Sanitise every literal of ``clause`` via ``mapping``
    (:func:`_apply_forward_tptp`), in :func:`atp.resolution_check._lit_key`
    order — the same deterministic literal ordering
    :func:`atp.resolution_check.render_resolution_proof` already uses, so
    :func:`to_tstp`'s output is reproducible run to run regardless of
    ``frozenset`` iteration order. Returns the sanitised literal Nodes, not
    yet rendered to text — :func:`to_tstp` both joins them with ``Node
    .to_tptp()`` for the emitted line AND collects them (still as Nodes)
    for the whole-derivation collision check, so keeping this a Node list
    avoids parsing the emitted text back just to check it.
    """
    return [_apply_forward_tptp(lit, mapping) for lit in sorted(clause, key=_lit_key)]


def to_tstp(derivation: ResolutionDerivation, *, name_map: Optional[TptpNameMap] = None) -> str:
    """Serialise a CERTIFIED :class:`~atp.resolution_check.ResolutionDerivation`
    as annotated TSTP ``cnf(...).`` text — the write-side companion to
    :func:`parse_tstp_derivation` above (see this section's module comment
    for the precise, narrower-than-it-sounds scope this covers).

    One line per step, in :attr:`~atp.resolution_check.ResolutionDerivation
    .steps` order (already 1-indexed, matching each step's position):

    - ``rule == "input"``: ``cnf(c<index>, plain, <clause>).`` — no source
      annotation at all, matching how :func:`parse_tstp_derivation` treats a
      leaf statement (``TstpStep.rule is None`` for one with no ``source``
      field).
    - otherwise: ``cnf(c<index>, plain, <clause>, inference(<rule>,
      [status(thm)], [c<p>, ...])).``, ``<rule>`` from :data:`_KIT_RULE_TO_TSTP`
      and ``<p>`` ranging over ``step.parents`` in citation order.

    ``<clause>`` is ``$false`` for the empty clause, else its literals in
    :func:`atp.resolution_check._lit_key` order (matching
    :func:`~atp.resolution_check.render_resolution_proof`'s own literal
    ordering, for reproducible output) joined by ``" | "``, each rendered via
    :meth:`~fol.nodes.Node.to_tptp` after its symbols have been made
    TPTP-ASCII-legal exactly as :func:`atp._tptp_problem
    .generate_tptp_problem_with_mapping` does its own premises/conclusion
    (:func:`atp._tptp_problem._sanitize_for_tptp`, then
    :func:`atp._tptp_problem._check_no_symbol_collisions` over the sanitised
    result — see :func:`_apply_forward_tptp`'s docstring).

    Args:
        derivation: the derivation to serialise. MUST already satisfy
            :func:`atp.resolution_check.verify_resolution_proof` (see
            Raises) — this writer never serialises an uncertified
            derivation, loudly.
        name_map: an optional, already-built :class:`atp._tptp_problem
            .TptpNameMap` to reuse instead of sanitising ``derivation``'s own
            symbols from scratch — for a derivation over a problem some
            caller already exported via :func:`atp._tptp_problem
            .generate_tptp_problem_with_mapping`, passing that call's
            returned mapping here keeps every shared symbol's TPTP spelling
            identical between the problem file and this proof (e.g. so a
            caller's own :func:`atp.tstp_check.check_tstp_derivation` call
            can compare against premises in the SAME sanitised namespace).
            A symbol ``derivation`` uses that this mapping does NOT cover
            (e.g. a Skolem constant introduced only in the proof, never in
            the problem the mapping was built from) is still sanitised, not
            passed through unchanged — :func:`_extend_name_map_for_derivation`
            extends a copy of ``name_map`` with exactly those symbols before
            any text is rendered, so an uncovered non-ASCII or digit-leading
            name can never reach the output unsanitised. The same extension
            ALSO re-sanitises a symbol that is TPTP-legal but wrong-case for
            its namespace (a lower-case predicate, an upper-case-initial
            constant/function) instead of passing it through as an identity
            — an already-legal name only ever keeps its exact spelling when
            that spelling would also survive :func:`parse_tstp_derivation`'s
            own read-back unchanged (see :func:`_collect_name_case_safe`),
            so the round trip this module's own docstring advertises holds
            for every symbol, not only already-correctly-cased ones. When
            omitted, a fresh mapping is built from exactly the symbols
            ``derivation.steps`` uses (the same extension function, seeded
            with nothing — equivalent to :func:`atp._tptp_problem
            ._sanitize_for_tptp`, modulo that same case fix) — an
            already-TPTP-legal, already-correctly-cased name (the common
            case for the kit's own ASCII test fixtures, whose predicates are
            conventionally upper-case-initial and whose constants are
            conventionally lower-case-initial) maps to itself, so the
            emitted text is byte-identical to what
            :meth:`~fol.nodes.Node.to_tptp` alone would have produced.

    Returns:
        The derivation's TSTP text, one ``cnf(...).`` statement per line,
        each newline-terminated (``""`` for an empty ``derivation.steps``).

    Raises:
        ValueError: ``verify_resolution_proof(derivation)`` does not accept
            ``derivation`` — this writer serialises only what the kit has
            independently CERTIFIED (see this section's module comment); a
            derivation research code, a human, or another prover produced
            must be checked FIRST, exactly as any other consumer of
            :mod:`atp.resolution_check` is required to.
        NotImplementedError: two distinct kit-level symbol names would
            render as the same TPTP identifier (:func:`atp._tptp_problem
            ._check_no_symbol_collisions`, run over ``derivation``'s own
            sanitised literals AND, via :func:`_name_map_sentinel_nodes`,
            every token ``name_map`` itself already commits to — so a
            collision between a symbol reused from ``name_map`` and one
            ``derivation`` introduces is caught too, not only a collision
            entirely within ``derivation``), naming both — the same guard
            :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`
            raises for a TPTP problem file, reused here verbatim rather than
            silently merging two distinct symbols into one.
    """
    check = verify_resolution_proof(derivation)
    if not check.ok:
        raise ValueError(
            f"to_tstp: derivation is not certified by verify_resolution_proof "
            f"({check.error}); this writer only serialises a derivation the "
            f"kit has independently checked, never an unverified one"
        )

    name_map = _extend_name_map_for_derivation(derivation, name_map)

    sanitised_by_index: Dict[int, List[Node]] = {
        step.index: _render_clause_tptp(step.clause, name_map)
        for step in derivation.steps
    }
    _check_no_symbol_collisions(
        _name_map_sentinel_nodes(name_map) +
        [lit for literals in sanitised_by_index.values() for lit in literals]
    )

    lines: List[str] = []
    for step in derivation.steps:
        literals = sanitised_by_index[step.index]
        clause_text = "$false" if not literals else " | ".join(lit.to_tptp() for lit in literals)
        if step.rule == "input":
            lines.append(f"cnf(c{step.index}, plain, {clause_text}).")
        else:
            rule_name = _KIT_RULE_TO_TSTP[step.rule]
            parents = ", ".join(f"c{p}" for p in step.parents)
            lines.append(
                f"cnf(c{step.index}, plain, {clause_text}, "
                f"inference({rule_name}, [status(thm)], [{parents}]))."
            )
    return "".join(line + "\n" for line in lines)
