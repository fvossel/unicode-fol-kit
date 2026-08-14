"""TSTP/SZS: read prover output into the kit's :mod:`atp.protocol` vocabulary.

TPTP-family provers (Vampire, E, Prover9-successors, ...) report their result
through the **SZS ontology** (Sutcliffe's "Standard for Success" status
values) on a single stdout line:

    % SZS status <value> for <problem>[ : <free-text>]

and, when asked for a proof, print the derivation itself as a sequence of
annotated TSTP statements:

    fof(name, role, formula, inference(rule, [status(thm)], [parent, ...])).
    cnf(name, role, formula, inference(rule, [status(thm)], [parent, ...])).

This module is the read side of both: :func:`extract_szs_status` pulls the
first status line out of raw prover output, :func:`szs_to_verdict_fields`
maps an SZS value onto :mod:`atp.protocol`'s ``(status, reason)`` pair, and
:func:`parse_tstp_derivation` turns the annotated fof/cnf lines into a proof
DAG of :class:`TstpStep` records (reusing :mod:`fol.tptp_input` to parse each
step's formula body back into the toolkit AST).

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
from typing import List, Optional, Tuple

from ..fol.nodes import Node
from ..fol.naming import ParsingError
from ..fol.tptp_input import parse_tptp_formula
from .protocol import ERROR, PROVED, REFUTED, UNKNOWN

__all__ = [
    "extract_szs_status", "szs_to_verdict_fields",
    "TstpStep", "TstpDerivation", "parse_tstp_derivation",
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
