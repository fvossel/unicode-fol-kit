"""Chemistry MCP tools — model-checking feedback for an LLM writing ChEBI FOL.

The setting (see ``unicode_fol_kit.chem``'s own module docstring for the
full brief): an LLM translates a ChEBI class definition to FOL;
classification is MODEL CHECKING that formula against a molecule represented
as a finite structure. The failure modes that loop runs into are what these
six tools exist to close, one each:

* the LLM never SEES what its formula is being checked against
  (:func:`molecule_to_structure` — the structure as JSON, plus a headline
  domain size / nonempty-predicate summary a caller can read without parsing
  the whole extension table);
* a single positive example failing gives no diagnosis, only pass/fail
  (:func:`check_molecule` — ``holds`` plus, on failure, the
  :func:`~unicode_fol_kit.semantics.model_eval.evaluate_detailed` blame trail);
* a whole labelled corpus needs to be re-checked after every definition edit,
  and a definition that is too general (matching far too much, at a precision
  cost invisible until it is measured against a corpus) is exactly the kind
  of thing only visible in aggregate (:func:`check_molecules` — per-molecule
  results plus a holds/fails/unknown/errors summary);
* a failing conjunct alone still does not say what the molecule looks like —
  a counterexample needs explaining, not just reporting
  (:func:`explain_molecule_failure` — the failing conjunct PLUS the
  molecule's atoms-by-type and bond list, so a model can see both halves of
  the mismatch at once);
* redundant pairwise-inequality chains (``hasAtLeast40Carbons`` written as 40
  nested existentials + C(40,2)=780 ``≠`` literals) are a routine timeout
  cause (:func:`simplify_definition`
  — applies :func:`~unicode_fol_kit.fol.simplify_check.simplify_for_checking`
  and reports what shrank, by how much);
* pure-SYNTAX failures, hallucinated predicate names among them, burn a whole
  generation attempt each (:func:`chemical_signature` — the exact
  40-predicate ChemLog vocabulary so a generator never has to guess what it
  is allowed to write).

Conventions (matching :mod:`unicode_fol_kit.mcp.server`, followed exactly so
a client that already talks to that server needs no special-casing for these
six tools)
------------------------------------------------------------------------------
* every tool returns a JSON-compatible dict;
* a bad TEXT argument (an unparseable formula, or a SMILES string that does
  not describe a valid molecule) comes back as
  ``{"ok": False, "argument": <which input — "formula"/"smiles"/
  "smiles[<i>]">, "errors": [...], "spec_topic": <topic>}`` — the SAME shape
  for both, deliberately: from the calling pipeline's perspective a bad
  formula and a bad SMILES are the identical case, "this argument did not
  work", and a generic client checks ``result.get("ok") is False``, full
  stop;
* a documented exception that is not about a bad argument (RDKit not
  installed; a formula that mentions a predicate the structure does not
  interpret; a node type the structural evaluator does not support) comes
  back as ``{"error": {"type": ..., "message": ...}}``, never a traceback.

Chemical formulas MUST be written in TPTP
------------------------------------------
ChemLog's vocabulary is lower-case-led (``c``, ``bDOUBLE``, ...); in the
kit's own unicode surface syntax a lower-case leading letter is a VARIABLE or
FUNCTION, never a predicate, so a chemical class definition can only be
parsed as TPTP. ``dialect="tptp_bare"`` (the default on every tool that takes
a formula) therefore routes through
:func:`unicode_fol_kit.chem.parse_chemlog_tptp`, which additionally repairs
the three recurring LLM syntax failure modes (unbracketed
biimplication, an unquoted invalid predicate name, a free left-hand
variable — see :mod:`unicode_fol_kit.fol.tptp_repair`) BEFORE renaming the
chemical vocabulary back from the TPTP importer's forced-capitalised kit
spelling to ChemLog's own lower-case spelling — without that rename step no
TPTP-derived formula would ever line up with a
:func:`~unicode_fol_kit.chem.mol_to_structure` structure (see
``unicode_fol_kit.chem.interop``'s module docstring for exactly why). Passing
any other ``dialect`` is still honoured (useful for a formula generated
directly in the kit's own unicode syntax with kit-capitalised chemical
predicate names, e.g. ``C(x)`` for carbon) — it is parsed via
:func:`unicode_fol_kit.api.parse_any` and then the SAME chemical-vocabulary
rename is applied, so the resulting :class:`~unicode_fol_kit.fol.nodes.Node`
always ends up chemlog-spelled either way. It is NOT repaired in that branch
(only the ``tptp_bare`` path calls the repair layer — a formula in the kit's
own syntax is repaired by calling
:func:`unicode_fol_kit.fol.repair_formula` explicitly first, which is
deliberate: a rename that happened silently inside a CHECKING tool would
change which predicate was checked without the caller ever seeing it), and
auxiliary/class
predicates outside ChemLog's 40-symbol vocabulary (``carboxylicAcid``,
``organicMolecularEntity``, ...) are left exactly as parsed either way — they
have no ChemLog spelling to rename to.

Why ``all_different`` defaults to ``True`` here (unlike the underlying
evaluator)
------------------------------------------------------------------------------
:func:`unicode_fol_kit.semantics.model_eval.evaluate_detailed` defaults
``all_different=False`` (plain classical semantics: two separately
existentially-bound variables MAY denote the same individual). Every ChemLog
class definition this tool layer exists to check is written under the
OPPOSITE, ChemLog-specific convention — "separately introduced existential
variables are already pairwise distinct" — so every tool below that runs
model checking defaults ``all_different=True`` instead. Pass ``False``
explicitly to check a formula under plain FOL semantics instead.

Never a guessed False
-----------------------
Every model-checking tool exposes an optional ``budget`` (default ``None`` —
unbounded). If a budget is given and exhausted before a definitive answer,
``holds`` comes back ``None`` (never ``False``) — see
:mod:`unicode_fol_kit.semantics.model_eval`'s own "three-valued contract".

Spans (opt-in, ``with_spans=True`` on :func:`check_molecule`,
:func:`check_molecules`, :func:`explain_molecule_failure`)
------------------------------------------------------------------------------
``failing_conjunct`` names the piece of ``formula`` that made the check fail,
but only ever as rendered TEXT (``fc.to_unicode_str()``) — a caller has to
find that text again inside the ORIGINAL ``formula`` string by eye (or by a
substring search that can fail to be unique, or fail outright once
rendering has re-bracketed or re-spaced anything). ``with_spans=True`` adds
a ``"span"`` key beside ``failing_conjunct`` instead: ``{"start": int, "end":
int, "line": int, "column": int, "end_line": int, "end_column": int, "text":
str}`` (a JSON rendering of a :class:`~unicode_fol_kit.fol.spans.Span`) when
one was recovered, else ``None`` — a character range directly into the
``formula`` TEXT this call was given, exact and unambiguous, ready for a
caller to slice or highlight without re-deriving it.

This is built directly on
:meth:`unicode_fol_kit.fol.msflparser.MSFLParser.parse_with_spans` — a new,
additive method alongside ``.parse`` on the SAME instance (``.parse`` itself
is byte-for-byte unchanged) that returns a
:class:`~unicode_fol_kit.fol.spans.SpannedFormula`: ``.formula`` is the
identical AST ``.parse`` would build, ``.spans`` a
:class:`~unicode_fol_kit.fol.spans.SpanMap` from each of that AST's nodes
back to the slice of source text it was parsed from. ``SpanMap`` is keyed by
PATH (a tuple of child indices from the root — see
:mod:`unicode_fol_kit.fol.spans`'s module docstring), NOT by the node's own
value and NOT by Python ``id()``: every
:class:`~unicode_fol_kit.fol.nodes.Node` subclass is a frozen dataclass with
STRUCTURAL equality/hashing (see the kit-wide reason in ``_fol_nodes.py``),
so a value-keyed table would silently collapse two textually-distinct but
structurally-identical subformulas (``c(x) & c(x)``, two separate
occurrences of the same class predicate) onto a single span, and an
id()-keyed one goes stale the moment a node is rebuilt (which
``map_children``-based rewrites, including the rename below, always do).
This module uses the convenience ``.for_node(node)`` lookup — a node object
in hand, resolved by identity against whichever tree the map was last bound
to — rather than the PATH-keyed ``.get(path)`` a caller doing its own
traversal would use.

This module supplies the piece the span layer does not itself cover: every
``check_molecule``/``check_molecules``/``explain_molecule_failure`` call
renames the freshly parsed formula's chemical vocabulary to ChemLog spelling
before evaluating it (see "Chemical formulas MUST be written in TPTP"
above), and that rename reconstructs EVERY node in the tree — including
every ancestor of a renamed leaf, not just the renamed leaf itself, since
:meth:`~unicode_fol_kit.fol.nodes.Node.map_children` always allocates a new
object — so a fresh set of node OBJECTS exists after the rename even though
the tree's SHAPE (and hence every PATH into it) is unchanged
(:func:`~unicode_fol_kit.semantics.model_eval.evaluate_detailed` itself
never rebuilds a node, so identity survives evaluation, just not the rename
that happens first). :func:`unicode_fol_kit.chem.rename_with_spans` closes
exactly that gap, via :func:`unicode_fol_kit.fol.spans.project_spans` (the
span layer's own utility for carrying a ``SpanMap`` across a
shape-preserving rewrite — the rename only ever changes an ``Atom``'s
predicate or a ``Function``'s name, never the shape of the tree around it —
and re-binds the identity index to the renamed tree, so ``.for_node``
resolves against the SAME tree ``failing_conjunct`` is drawn from): a caller
sees a span on ``failing_conjunct`` whenever ``parse_with_spans`` recorded
one for the corresponding source node, all the way through the rename.

Only the dialects that route through ``MSFLParser`` support ``with_spans``
today — the kit's own surface syntax (``"unicode"``, or a specific mode name
such as ``"fol"``/``"msfol"``/...), NOT ``dialect="tptp_bare"`` (this
module's own default): TPTP is parsed by a wholly separate Lark grammar
(:mod:`unicode_fol_kit.fol.tptp_input`) that the span layer above does not
cover. This is not a theoretical restriction: the real external caller of
these tools (the ChEBI campaign) already calls every one of them with
``dialect="unicode"`` throughout its own pipeline (never ``"tptp_bare"``),
specifically so its `check_formula`/`diagnose`/`repair_formula` loop and its
model-checking calls agree on one dialect — ``with_spans=True`` lines up
with that exact usage, not a hypothetical one. Passing ``with_spans=True``
with ``dialect="tptp_bare"`` (or any other non-kit-syntax dialect) is
reported as ``{"error": {"type": "ValueError", ...}}`` — a caller/config
mismatch, not formula data being bad.
"""

from typing import Dict, List, Optional, Tuple

from .. import api, chem
from .. import simplify_for_checking, count_from_existential_chain
from ..fol.nodes import Node
from ..fol.tptp_repair import _render as _render_tptp
from ..semantics.model_eval import (
    evaluate_detailed, EvalResult, UninterpretedSymbol, UnsupportedNode,
)
from ..semantics.structures import FiniteStructure

__all__ = [
    "molecule_to_structure", "check_molecule", "check_molecules",
    "explain_molecule_failure", "simplify_definition", "chemical_signature",
]


# ---------------------------------------------------------------------------
# Shared error shaping (see module docstring's "Conventions")
# ---------------------------------------------------------------------------

def _error(exc: Exception) -> dict:
    """A documented, non-argument exception as ``{"error": {...}}``.

    :class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol`
    additionally carries ``.symbol``/``.arity`` — surfaced here so a caller
    can tell, without parsing the message, exactly which predicate/arity the
    structure did not interpret (almost always a vocabulary typo, or a class
    predicate from a definition this tool never saw).
    """
    payload = {"error": {"type": type(exc).__name__, "message": str(exc)}}
    symbol = getattr(exc, "symbol", None)
    if symbol is not None:
        payload["error"]["symbol"] = symbol
        payload["error"]["arity"] = getattr(exc, "arity", None)
    return payload


def _smiles_error(message: str, argument: str = "smiles") -> dict:
    """A SMILES that does not describe a valid molecule, in the SAME uniform
    ``ok=False``/``argument``/``errors`` shape as a formula parse failure —
    see the module docstring's "Conventions" for why the two are unified."""
    return {"ok": False, "argument": argument,
            "errors": [{"dialect": "smiles", "message": message}],
            "spec_topic": "chemistry"}


# Lowercased substring of a parse-error message -> the syntax_spec topic that
# explains it. A small, honest heuristic (mirrors
# unicode_fol_kit.mcp.server's own, kept independent rather than imported —
# this module owns no dependency on the general-purpose server's private
# helpers): it names where to LOOK, not a diagnosis, which is why the
# fallback is "chemistry" (the topic covering the TPTP-only, 0-ary-
# definition, lowercase-predicate conventions every chemical formula must
# follow) rather than a guess.
_SPEC_HINTS: Tuple[Tuple[str, str], ...] = (
    ("invalid name", "naming"),
    ("invalid variable", "naming"),
    ("invalid name/constant", "naming"),
    ("unexpected character", "naming"),
    ("not bound", "quantifiers"),
    ("free variable", "quantifiers"),
    ("incomplete formula", "operators"),
    ("unexpected token", "operators"),
)


def _spec_topic_for(message: str) -> str:
    low = message.lower()
    for needle, topic in _SPEC_HINTS:
        if needle in low:
            return topic
    return "chemistry"


def _parse_chem(text: str, dialect: str, argument: str = "formula"
                ) -> Tuple[Optional[Node], Optional[dict]]:
    """Parse chemical class-definition TEXT into a ChemLog-spelled
    :class:`~unicode_fol_kit.fol.nodes.Node` — ``(node, None)`` on success,
    ``(None, error_dict)`` on failure (see the module docstring's
    "Conventions" for the error shape).

    ``dialect="tptp_bare"`` (see the module docstring's "Chemical formulas
    MUST be written in TPTP") routes through
    :func:`unicode_fol_kit.chem.parse_chemlog_tptp` (repair + rename, in one
    call). Any other ``dialect`` is parsed via
    :func:`unicode_fol_kit.api.parse_any` (no repair pass) and then renamed
    the identical way via :func:`unicode_fol_kit.chem.to_chemlog_names`, so
    the returned node is ChemLog-spelled either way.
    """
    if dialect == "tptp_bare":
        try:
            node = chem.parse_chemlog_tptp(text)
        except Exception as exc:  # noqa: BLE001 — every TPTP parser raises
            # its own exception type (TptpParsingError et al.), none of them
            # a ValueError; catching broadly and reporting the message is
            # exactly what unicode_fol_kit.api.parse_any's own _try() does
            # for the identical reason.
            message = str(exc)
            return None, {"ok": False, "argument": argument,
                          "errors": [{"dialect": "tptp_bare",
                                     "message": message}],
                          "spec_topic": _spec_topic_for(message)}
        return node, None

    parsed = api.parse_any(text, hint=dialect)
    if not parsed.ok:
        errors = parsed.to_dict()["errors"]
        combined = " ".join(e.get("message", "") for e in errors)
        return None, {"ok": False, "argument": argument, "errors": errors,
                      "spec_topic": _spec_topic_for(combined)}
    return chem.to_chemlog_names(parsed.formula), None


# ---------------------------------------------------------------------------
# Spans (opt-in) -- see the module docstring's "Spans" section for the full
# contract this builds on (unicode_fol_kit.fol.msflparser.MSFLParser
# .parse_with_spans / unicode_fol_kit.fol.spans).
# ---------------------------------------------------------------------------

#: Dialects with_spans=True actually supports: the kit's own MSFLParser-
#: backed surface syntax -- api._UNICODE_HINTS's keys (each a single fixed
#: mode) plus "unicode" itself (the ladder that tries them in the SAME
#: order api._unicode_ladder does). Deliberately reuses api's own table
#: rather than restating the mode list here, the same way fol.dialect_repair
#: reuses fol.tptp_repair's fixes instead of reimplementing them -- two
#: independently-maintained copies of "which modes, which order" could
#: silently drift, and with_spans=True must pick the identical winning mode
#: plain parsing would, or the span-carrying node would not even be the SAME
#: formula. NOT "tptp_bare" (this module's own default): TPTP is parsed by
#: a wholly separate Lark grammar (fol.tptp_input) with no span tracking.
_SPAN_DIALECTS = frozenset(api._UNICODE_HINTS) | {"unicode"}


def _parse_chem_with_spans(text: str, dialect: str, argument: str = "formula"
                           ) -> Tuple[Optional[Node], Optional[chem.SpanMap],
                                      Optional[dict]]:
    """:func:`_parse_chem`, plus a :class:`unicode_fol_kit.chem.SpanMap` for
    the returned node — ``(node, spans, None)`` on success.

    ``(None, None, error_dict)`` on failure, where ``error_dict`` is one of
    two shapes (see the module docstring's "Conventions" and "Spans"):

    * ``{"error": {"type": "ValueError", ...}}`` — ``dialect`` is not in
      :data:`_SPAN_DIALECTS` (a caller/config mistake: ``with_spans=True``
      together with, most commonly, this module's own ``dialect="tptp_bare"``
      default — not formula DATA being bad);
    * the uniform ``{"ok": False, "argument": ..., "errors": [...],
      "spec_topic": ...}`` shape for a genuine syntax error in ``text`` — the
      SAME shape :func:`_parse_chem` reports for the identical input, so a
      caller's ``result.get("ok") is False`` check behaves identically
      whether or not it asked for spans.
    """
    if dialect not in _SPAN_DIALECTS:
        return None, None, _error(ValueError(
            f"chem_tools: with_spans=True is not supported for dialect={dialect!r} "
            f"yet — only the kit's own surface syntax ({sorted(_SPAN_DIALECTS)}) "
            "has a span-tracking parser (not this module's own default, "
            "dialect='tptp_bare'). Call again without with_spans, or with one "
            "of the dialects above."))

    from ..fol.msflparser import MSFLParser

    ladder = (api._UNICODE_MODES if dialect == "unicode"
             else ((dialect, api._UNICODE_HINTS[dialect]),))
    spanned = None
    message = "no unicode-surface mode accepted the text"
    for _name, kwargs in ladder:
        try:
            spanned = MSFLParser(**kwargs).parse_with_spans(text)
            break
        except Exception as exc:  # noqa: BLE001 — mirrors api._try's own catch-all
            message = str(exc)
    if spanned is None:
        return None, None, {"ok": False, "argument": argument,
                            "errors": [{"dialect": dialect, "message": message}],
                            "spec_topic": _spec_topic_for(message)}
    node, spans = chem.to_chemlog_names_with_spans(spanned.formula, spanned.spans)
    return node, spans, None


def _span_dict(span) -> Optional[dict]:
    """JSON rendering of a :class:`unicode_fol_kit.fol.spans.Span`, or
    ``None`` for :data:`~unicode_fol_kit.fol.spans.UNKNOWN` — a node the span
    layer could not recover an exact source range for (see that module's
    docstring for the two documented, narrow cases) is reported as ``None``,
    never a guessed range."""
    from ..fol.spans import UNKNOWN

    if span is UNKNOWN:
        return None
    return {"start": span.start, "end": span.end, "line": span.line,
           "column": span.column, "end_line": span.end_line,
           "end_column": span.end_column, "text": span.text}


# ---------------------------------------------------------------------------
# Structure -> readable summary helpers (shared by molecule_to_structure /
# explain_molecule_failure)
# ---------------------------------------------------------------------------

#: The atom-type letters: ChemLog's own six, then the halogens the kit adds
#: (see chem._naming.ELEMENT_LETTERS — not imported: that module is
#: documented PRIVATE, and this literal tuple is the exact list
#: unicode_fol_kit.mcp.syntax_spec's own "chemistry" topic already
#: publishes, so duplicating it here does not risk drifting from an
#: undocumented internal any more than that existing publication already
#: does). Kept in sync by tests/test_chem.py's vocabulary test.
_ATOM_LETTERS: Tuple[str, ...] = (
    "c", "n", "o", "s", "p", "h", "f", "cl", "br", "i", "at")

_BOND_KINDS: Tuple[str, ...] = ("bSINGLE", "bDOUBLE", "bTRIPLE", "bAROMATIC")


def _atoms_by_type(structure: FiniteStructure) -> Dict[str, List[str]]:
    """Domain individuals grouped by ChemLog atom-type letter — only the
    letters this structure actually interprets (always all six for a
    structure ``mol_to_structure`` built, per its own "always-populated
    predicates" contract; guarded here anyway so this helper stays correct
    for a hand-built or ``naming="paper"`` structure too, where it silently
    returns fewer groups instead of raising)."""
    return {letter: list(structure.individuals_with(letter))
            for letter in _ATOM_LETTERS if structure.interprets(letter, 1)}


def _bonds(structure: FiniteStructure) -> List[dict]:
    """Every stored bond, ONE entry per unordered pair (bond relations are
    stored symmetrically — see chem.mol's module docstring — so naively
    listing both directions would double-count every bond)."""
    seen = set()
    out: List[dict] = []
    for kind in _BOND_KINDS:
        if not structure.interprets(kind, 2):
            continue
        for a in structure.domain:
            for b in structure.neighbors(kind, a):
                pair = frozenset((a, b))
                key = (kind, pair)
                if key in seen:
                    continue
                seen.add(key)
                out.append({"kind": kind, "atoms": sorted(pair)})
    return out


def _atom_notes(structure: FiniteStructure, individual: str) -> List[str]:
    """Every OTHER unary fact about ``individual`` (hydrogen count, charge,
    chirality, and — when ``computed=True`` — ring/aromaticity/connectivity),
    excluding the bare element letter and ``atom`` (already carried by
    :func:`_atoms_by_type`). Read directly off ``structure.signature()``
    rather than a hardcoded predicate list, so it stays correct regardless of
    naming scheme, ``computed=`` choice, or a future vocabulary extension —
    the one thing this helper must never do is silently miss a fact a wider
    hardcoded list happened not to anticipate."""
    skip = set(_ATOM_LETTERS) | {"atom"}
    held = [name for name, arity in structure.signature()
            if arity == 1 and name not in skip
            and structure.holds(name, (individual,))]
    return sorted(held)


def _eval_payload(result: EvalResult,
                  spans: Optional[chem.SpanMap] = None) -> dict:
    """The holds/exhausted/steps/witness/failing_conjunct bookkeeping shared
    by :func:`check_molecule`, :func:`check_molecules` and
    :func:`explain_molecule_failure` — factored out so the three tools report
    the identical shape for the identical :class:`EvalResult` rather than
    three independently rewritten (and driftable) renderings.

    ``witness``/``failing_conjunct`` are populated only when ``holds`` is
    decisively ``True``/``False`` respectively (never both, never either when
    ``holds`` is ``None`` — the budget ran out) — see
    :mod:`unicode_fol_kit.semantics.model_eval`'s own docstring for exactly
    what shape of formula each can explain.

    ``spans``, when given (the caller asked for ``with_spans=True`` and
    parsing succeeded with a span table — see the module docstring's
    "Spans" section), adds a ``"span"`` key beside ``failing_conjunct``: a
    JSON rendering of its EXTENT :class:`~unicode_fol_kit.fol.spans.Span`
    when this exact node has one, else ``None`` (:data:`~unicode_fol_kit.fol.spans.UNKNOWN`
    — never guessed). ``spans is None`` (the default — every caller that
    never passes ``with_spans=True``) omits the key entirely, so the
    returned shape is byte-identical to before this parameter existed.
    :func:`~unicode_fol_kit.semantics.model_eval.evaluate_detailed` never
    rebuilds any node (see that module's ``_find_blame``), so
    ``failing_conjunct`` is always a literal object out of the tree
    ``spans`` was built over —
    :meth:`~unicode_fol_kit.fol.spans.SpanMap.for_node` finds it directly, by
    identity, no re-derivation (``spans`` is already bound to that tree —
    see :func:`_parse_chem_with_spans`, which routes it through
    :func:`unicode_fol_kit.chem.to_chemlog_names_with_spans`).
    """
    payload: dict = {"holds": result.holds, "exhausted": result.exhausted,
                     "steps": result.steps}
    if result.holds is True:
        payload["witness"] = result.witness
    elif result.holds is False:
        fc = result.failing_conjunct
        entry = ({"unicode": fc.to_unicode_str(), "formula": fc.to_dict()}
                 if fc is not None else None)
        if spans is not None and entry is not None:
            entry["span"] = _span_dict(spans.for_node(fc).extent)
        payload["failing_conjunct"] = entry
    return payload


def _build_structure(smiles: str, include_computed: bool
                     ) -> Tuple[Optional[FiniteStructure], Optional[dict]]:
    """:func:`unicode_fol_kit.chem.mol_to_structure` in the fixed
    ``naming="chemlog"`` scheme every model-checking tool below needs (a
    formula parsed via :func:`_parse_chem` is ALWAYS ChemLog-spelled, so the
    structure it is checked against must be too — exposing ``naming`` here
    would let a caller silently break that pairing, which is why it is not a
    parameter on any tool below except :func:`molecule_to_structure` itself,
    whose whole point is inspecting the structure directly).

    ``(structure, None)`` on success; ``(None, error_dict)`` on failure — an
    ``ImportError`` (RDKit missing) is the ``{"error": ...}`` shape (an
    environment problem, not a bad argument); any other exception
    (``mol_to_structure``'s documented ``ValueError`` — unparseable SMILES,
    an unsupported element/bond, a residual hydrogen atom) is the uniform
    ``argument="smiles"`` shape (see the module docstring's "Conventions").

    A ``smiles`` that is not even a ``str`` (an ``int``, ``None``, a list, …
    — plausible in a batch call like :func:`check_molecules`, where one
    caller-side mistake in a long list should not be worse than any other
    per-item error) is caught HERE, before ever reaching
    ``mol_to_structure``, and reported in that SAME uniform
    ``argument="smiles"`` shape rather than as a raw, undocumented
    :class:`TypeError` — ``mol_to_structure`` itself raises exactly that
    :class:`TypeError` for a non-``str``/non-``Mol`` argument (see its own
    docstring), which is correct for a direct caller but WRONG for this
    tool layer's documented contract (see the module docstring's
    "Conventions": every bad argument is ``ok=False``, never a traceback) —
    left uncaught it would have propagated straight out of
    :func:`check_molecules`, aborting every remaining molecule in the batch
    over a single bad list entry.
    """
    if not isinstance(smiles, str):
        return None, _smiles_error(
            f"smiles must be a str, got {type(smiles).__name__}")
    try:
        return chem.mol_to_structure(smiles, naming="chemlog",
                                     computed=include_computed), None
    except ImportError as exc:
        return None, _error(exc)
    except ValueError as exc:
        return None, _smiles_error(str(exc))


# ---------------------------------------------------------------------------
# 1. molecule_to_structure
# ---------------------------------------------------------------------------

def molecule_to_structure(smiles: str, *, naming: str = "chemlog",
                          include_computed: bool = True) -> dict:
    """Translate a SMILES string into the finite structure a definition is
    checked against — lets the caller SEE what it is generating formulas for.

    Args:
        smiles: a SMILES string (e.g. ``"CCO"`` for ethanol).
        naming: ``"chemlog"`` (default — ``c``, ``bSINGLE``, ``has_1_hs``,
            ...; what :func:`check_molecule` and friends require) or
            ``"paper"`` (the human-readable prose spelling — ``c``,
            ``singleBond``, ``has1H``, ...; use this only to reproduce a
            worked example written that way, never to feed a
            ``dialect="tptp_bare"`` formula, which always comes back
            ChemLog-spelled).
        include_computed: attach the five ring/aromaticity/connectivity
            predicates that need transitive closure (not first-order
            expressible over the stored facts — see
            :mod:`unicode_fol_kit.chem.mol`'s module docstring). ``False``
            gives a structure whose entire vocabulary IS first-order
            expressible over what is stored.

    Returns:
        On success: ``{"ok": True, "structure": <FiniteStructure.to_dict()>,
        "domain_size": <int>, "nonempty_predicates": [...],
        "computed_predicates": [...]}`` — ``nonempty_predicates`` (each
        ``"name/arity"``, matching ``structure``'s own key format) is the
        quick answer to "what does this molecule actually have", without
        scanning the full (mostly-empty, canonically-pre-populated —
        see ``mol_to_structure``'s docstring) extension table by hand.

        ``naming`` outside ``{"chemlog", "paper"}`` is a caller/config
        mistake, not molecule data — reported as
        ``{"error": {"type": "ValueError", ...}}``. An unparseable/invalid
        SMILES is reported as ``{"ok": False, "argument": "smiles", ...}``
        (see the module docstring's "Conventions"); RDKit not being
        installed is reported as ``{"error": {"type": "ImportError", ...}}``
        naming the install command.
    """
    if naming not in ("chemlog", "paper"):
        return _error(ValueError(
            f"molecule_to_structure: unknown naming={naming!r}, expected "
            "'chemlog' or 'paper'"))
    if not isinstance(smiles, str):
        # Same contract as _build_structure below (see its own docstring):
        # a non-str smiles is a bad ARGUMENT, not molecule data, and must
        # come back in the uniform ok=False/argument shape rather than as a
        # raw, undocumented TypeError leaking out of mol_to_structure.
        return _smiles_error(
            f"smiles must be a str, got {type(smiles).__name__}")
    try:
        structure = chem.mol_to_structure(smiles, naming=naming,
                                          computed=include_computed)
    except ImportError as exc:
        return _error(exc)
    except ValueError as exc:
        return _smiles_error(str(exc))

    payload = structure.to_dict()
    nonempty = sorted(label for label, rows in payload["extensions"].items()
                      if rows)
    return {
        "ok": True,
        "structure": payload,
        "domain_size": len(payload["domain"]),
        "nonempty_predicates": nonempty,
        "computed_predicates": payload["computed"],
    }


# ---------------------------------------------------------------------------
# 2. check_molecule
# ---------------------------------------------------------------------------

def check_molecule(formula: str, smiles: str, *, all_different: bool = True,
                   dialect: str = "tptp_bare", include_computed: bool = True,
                   budget: Optional[int] = None,
                   with_spans: bool = False) -> dict:
    """Does ``formula`` hold of the molecule ``smiles`` describes?

    Parses ``formula`` (see the module docstring's "Chemical formulas MUST
    be written in TPTP"), builds the molecule's structure, and model-checks
    directly (:func:`unicode_fol_kit.semantics.model_eval.evaluate_detailed`
    — no CNF/prenex normal form, so a negated existential or a top-level
    disjunction never blows up the way it does for a normal-form-requiring
    checker; see that module's own docstring).

    Args:
        formula: a class-definition formula, TEXT (see ``dialect``).
        smiles: the molecule to check it against.
        all_different: the ChemLog convention that separately ∃-bound
            variables are pairwise distinct — see the module docstring for
            why this defaults ``True`` here (opposite of the underlying
            evaluator's own default).
        dialect: ``"tptp_bare"`` (default) or any other
            :func:`unicode_fol_kit.api.parse_any` hint.
        include_computed: attach the ring/aromaticity/connectivity computed
            predicates (see :func:`molecule_to_structure`).
        budget: cap the evaluator's step count. ``None`` (default) is
            unbounded. If given and exhausted, ``holds`` comes back ``None``
            — an honest UNKNOWN, never a guessed ``False``.
        with_spans: add a ``"span"`` byte-offset range beside
            ``failing_conjunct`` — see the module docstring's "Spans"
            section for the shape and its current dialect restriction.
            Default ``False``: byte-identical to every call made before this
            parameter existed.

    Returns:
        On success: ``{"ok": True, "holds": bool|None, "exhausted": bool,
        "steps": int, "witness": {...}}`` (only when ``holds is True`` — a
        variable->individual binding that makes the definition true) or
        ``..., "failing_conjunct": {"unicode": ..., "formula": ...}}`` (only
        when ``holds is False`` — the specific conjunct
        :func:`evaluate_detailed`'s blame trail drilled down to; ``None`` if
        the formula's shape has no natural single-conjunct blame — see that
        function's own docstring for exactly which shapes it can explain).
        With ``with_spans=True``, ``failing_conjunct`` additionally carries
        a ``"span"`` key — see the module docstring's "Spans" section for
        its shape.

        A parse failure or invalid SMILES is the uniform ``ok=False``
        argument/errors shape; a formula mentioning a predicate the
        structure does not interpret
        (:class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol`
        — almost always a vocabulary typo, or a class predicate this call
        never defined), an unsupported node type
        (:class:`~unicode_fol_kit.semantics.model_eval.UnsupportedNode`), a
        free variable, or (``with_spans=True`` only) an unsupported
        ``dialect``/unavailable span layer are the ``{"error": {...}}``
        shape.
    """
    spans = None
    if with_spans:
        node, spans, err = _parse_chem_with_spans(formula, dialect, argument="formula")
    else:
        node, err = _parse_chem(formula, dialect, argument="formula")
    if err is not None:
        return err
    structure, err = _build_structure(smiles, include_computed)
    if err is not None:
        return err
    try:
        result = evaluate_detailed(node, structure,
                                   all_different=all_different, budget=budget)
    except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
        return _error(exc)
    return {"ok": True, **_eval_payload(result, spans)}


# ---------------------------------------------------------------------------
# 3. check_molecules
# ---------------------------------------------------------------------------

def check_molecules(formula: str, smiles_list: List[str], *,
                    all_different: bool = True, dialect: str = "tptp_bare",
                    include_computed: bool = True,
                    budget: Optional[int] = None,
                    with_spans: bool = False) -> dict:
    """:func:`check_molecule`, batched over a corpus — the core feedback
    loop: one call shows which positive examples a definition actually
    covers, without a round trip per molecule.

    ``formula`` is parsed ONCE; a parse failure aborts the whole call (the
    uniform ``ok=False`` shape, ``argument="formula"``). RDKit missing
    likewise aborts the whole call (an environment problem, not a per-
    molecule one). Everything else is per-molecule: one bad SMILES in the
    list does not lose the results for the rest — it gets its own
    ``{"smiles": ..., "ok": False, "error": ...}`` entry and the batch
    continues, because seeing WHICH examples are unusable is itself part of
    the feedback a correction loop needs.

    Args:
        formula: as :func:`check_molecule`.
        smiles_list: the molecules to check it against, in order.
        all_different, dialect, include_computed, budget, with_spans: as
            :func:`check_molecule`.

    Returns:
        ``{"ok": True, "results": [...], "summary": {"total": int,
        "holds": int, "fails": int, "unknown": int, "errors": int}}``.
        Each ``results[i]`` is ``{"smiles": smiles_list[i], "ok": True,
        **check_molecule-style holds/exhausted/steps/witness/
        failing_conjunct}`` on success, or ``{"smiles": ..., "ok": False,
        "error": <message>}`` on a per-molecule failure (bad SMILES, or the
        same ``UninterpretedSymbol``/``UnsupportedNode``/free-variable
        exceptions :func:`check_molecule` reports as ``{"error": ...}`` —
        flattened to a plain message here since these entries already live
        one level below the top-level ``ok``).
    """
    spans = None
    if with_spans:
        node, spans, err = _parse_chem_with_spans(formula, dialect, argument="formula")
    else:
        node, err = _parse_chem(formula, dialect, argument="formula")
    if err is not None:
        return err

    results: List[dict] = []
    counts = {"holds": 0, "fails": 0, "unknown": 0, "errors": 0}
    for smiles in (smiles_list or []):
        structure, build_err = _build_structure(smiles, include_computed)
        if build_err is not None:
            if "error" in build_err and build_err["error"]["type"] == "ImportError":
                return build_err  # environment-wide: abort the whole batch
            message = build_err["errors"][0]["message"]
            results.append({"smiles": smiles, "ok": False, "error": message})
            counts["errors"] += 1
            continue
        try:
            result = evaluate_detailed(node, structure,
                                       all_different=all_different,
                                       budget=budget)
        except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
            results.append({"smiles": smiles, "ok": False, "error": str(exc)})
            counts["errors"] += 1
            continue
        entry = {"smiles": smiles, "ok": True, **_eval_payload(result, spans)}
        results.append(entry)
        if result.holds is True:
            counts["holds"] += 1
        elif result.holds is False:
            counts["fails"] += 1
        else:
            counts["unknown"] += 1

    return {
        "ok": True,
        "results": results,
        "summary": {"total": len(results), **counts},
    }


# ---------------------------------------------------------------------------
# 4. explain_molecule_failure
# ---------------------------------------------------------------------------

def explain_molecule_failure(formula: str, smiles: str, *,
                             all_different: bool = True,
                             dialect: str = "tptp_bare",
                             include_computed: bool = True,
                             budget: Optional[int] = None,
                             with_spans: bool = False) -> dict:
    """The full counterexample-explanation view for ONE molecule — the piece
    a bare classifier does not give you (a plain model checker returns only
    proved/not-proved, never a witness).

    Runs the identical check :func:`check_molecule` does (same holds/
    exhausted/steps/witness/failing_conjunct), plus the molecule's own
    structure rendered for a human/LLM to read at a glance: every atom
    grouped by element type, every other fact about each atom (hydrogen
    count, charge, chirality, and — when ``include_computed=True`` —
    ring/aromaticity/connectivity), and the full bond list. Reading the
    failing conjunct against this is what lets a caller propose a concrete
    fix (e.g. "the definition asks for a nitrogen but this molecule has
    none") instead of just re-generating blind.

    Args: as :func:`check_molecule` (including ``with_spans``).

    Returns:
        On success: ``{"ok": True, "formula_unicode": str, "domain": [...],
        "domain_size": int, "atoms_by_type": {letter: [individuals]},
        "atom_properties": {individual: [other unary facts]}, "bonds":
        [{"kind": ..., "atoms": [a, b]}], **check_molecule-style holds/
        exhausted/steps/witness/failing_conjunct}``. Same failure shapes as
        :func:`check_molecule` for a bad formula/SMILES/vocabulary mismatch.
    """
    spans = None
    if with_spans:
        node, spans, err = _parse_chem_with_spans(formula, dialect, argument="formula")
    else:
        node, err = _parse_chem(formula, dialect, argument="formula")
    if err is not None:
        return err
    structure, err = _build_structure(smiles, include_computed)
    if err is not None:
        return err
    try:
        result = evaluate_detailed(node, structure,
                                   all_different=all_different, budget=budget)
    except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
        return _error(exc)

    return {
        "ok": True,
        "formula_unicode": node.to_unicode_str(),
        "domain": list(structure.domain),
        "domain_size": len(structure.domain),
        "atoms_by_type": _atoms_by_type(structure),
        "atom_properties": {ind: _atom_notes(structure, ind)
                            for ind in structure.domain},
        "bonds": _bonds(structure),
        **_eval_payload(result, spans),
    }


# ---------------------------------------------------------------------------
# 5. simplify_definition
# ---------------------------------------------------------------------------

def simplify_definition(formula: str, *, all_different: bool = True,
                        dialect: str = "tptp_bare") -> dict:
    """Shrink a class definition for model checking, and report exactly what
    changed — the fix for the standard timeout cause (a redundant O(n²)
    pairwise-inequality chain, e.g. 780 literals for "at least 40
    carbons").

    Two independent, differently-scoped rewrites are applied (see
    :mod:`unicode_fol_kit.fol.simplify_check`'s own module docstring for the
    full soundness argument of each):

    1. :func:`~unicode_fol_kit.fol.simplify_check.simplify_for_checking`
       (``all_different=True`` by default here — see the module docstring)
       — a conservative, EVERYWHERE-applicable pass: drops trivial ``t=t``
       conjuncts, duplicate ∧/∨ operands, double negation, vacuous
       quantifiers, and (under ``all_different``) a pairwise ``x≠y`` between
       two separately ∃-bound variables, wherever in the tree it occurs —
       even when interleaved with other content (a real bond literal between
       the same two variables, say). This is what actually shrinks a real
       definition, and is always applied.
    2. :func:`~unicode_fol_kit.fol.simplify_check.count_from_existential_chain`
       — checked against the ORIGINAL (pre-simplification) formula, because
       it recognises only a COMPLETE, EXACT top-level instance of the
       distinct-witnesses pattern (every witness, every C(n,2) inequality,
       nothing else — see that function's own docstring) and the ``≠``
       literals rule (1) already removed would make an already-simplified
       formula fail that exact-shape test even when the original genuinely
       matched. Reported as ``count_pattern`` — separate, informational
       ``diagnostic`` output, not folded into the main simplified formula
       (see "Why the Count form is reported separately" below).

    Why the Count form is reported separately
    -------------------------------------------
    TPTP (what :func:`check_molecule` reparses) has no native counting-
    quantifier syntax — only the kit's own unicode surface syntax does. A
    ``Count`` node can therefore never be rendered back to reusable
    ``tptp_bare`` text, so folding it into the primary ``after_*`` output
    would hand back a formula this same tool's sibling ``check_molecule``
    could not accept. ``count_pattern`` is reported purely for information
    (and for a caller working with a :class:`~unicode_fol_kit.fol.nodes.Node`
    directly rather than through the TPTP round trip).

    Args:
        formula: the class definition to simplify.
        all_different: passed to ``simplify_for_checking`` (default ``True``
            — see the module docstring for why this differs from that
            function's own, plain-FOL-safe default of ``False``).
        dialect: as :func:`check_molecule`.

    Returns:
        ``{"ok": True, "before_unicode": str, "after_unicode": str,
        "after_tptp": str|None, "changed": bool, "removed": [str, ...],
        "removed_count": int, "count_pattern": {"detected": bool,
        "folded_unicode": str, "note": str} | {"detected": False}}``.
        ``after_tptp`` is ``None`` (with an explanatory
        ``after_tptp_note``) only in the — for this rule set, unreachable in
        practice — case that the simplified formula contains a node type
        with no native TPTP rendering (a ``Count`` node, or an operator
        outside classical FOL reached via a non-``tptp_bare`` ``dialect``);
        ``simplify_for_checking`` itself never introduces one.
    """
    node, err = _parse_chem(formula, dialect, argument="formula")
    if err is not None:
        return err

    counted = count_from_existential_chain(node)
    result = simplify_for_checking(node, all_different=all_different)
    simplified = result.simplified

    payload = {
        "ok": True,
        "before_unicode": node.to_unicode_str(),
        "after_unicode": simplified.to_unicode_str(),
        "changed": result.changed,
        "removed": list(result.removed),
        "removed_count": len(result.removed),
    }
    # known_names maps the TPTP importer's forced-capitalised kit spelling
    # back to the true ChemLog original for every symbol IN the declared
    # chemical vocabulary (chem.KIT_TO_CHEMLOG) — Node.to_tptp() lowercases
    # a predicate's ENTIRE name, which would silently corrupt a mixed-case
    # ChemLog name like "bDOUBLE" into "bdouble" (a different, uninterpreted
    # symbol); this is the same case-preserving renderer
    # repair_tptp_formula's own `repaired_text` uses internally. A symbol
    # OUTSIDE the chemical vocabulary (an auxiliary class predicate) falls
    # back to that renderer's own best-effort un-capitalisation, which is
    # exact for the common case (a name that arrived as a bare, TPTP-
    # required-lowercase functor) — see fol.tptp_repair's module docstring
    # for the one documented, narrow residual gap.
    try:
        payload["after_tptp"] = _render_tptp(simplified, dict(chem.KIT_TO_CHEMLOG))
    except NotImplementedError:
        payload["after_tptp"] = None
        payload["after_tptp_note"] = (
            "the simplified formula contains a node type with no native "
            "TPTP rendering (e.g. a Count node, or an operator outside "
            "classical FOL) — use after_unicode for display instead.")

    if counted is not None:
        payload["count_pattern"] = {
            "detected": True,
            "folded_unicode": counted.to_unicode_str(),
            "note": (
                "the ORIGINAL formula is exactly the distinct-witnesses "
                "pattern for this counting quantifier. Reported for "
                "information only — TPTP has no native counting syntax, so "
                "this folded form cannot be re-submitted to check_molecule "
                "as tptp_bare text; after_tptp above (still all_different-"
                "simplified) evaluates the identical set of molecules under "
                "the all_different convention."),
        }
    else:
        payload["count_pattern"] = {"detected": False}
    return payload


# ---------------------------------------------------------------------------
# 6. chemical_signature
# ---------------------------------------------------------------------------

# Grouping of chem.CHEMLOG_SIGNATURE's 35 declared predicates, for a caller
# that wants "which predicates cover charge" rather than a flat 35-entry
# list. Mirrors unicode_fol_kit.mcp.syntax_spec's own "chemistry" topic
# grouping exactly (both are hand-written against the SAME published
# vocabulary, chem.CHEMLOG_SIGNATURE — the assertion in
# chemical_signature() below is what keeps this list from silently drifting
# out of sync with it, rather than a shared import of chem's own PRIVATE
# _naming module).
_COMPUTED_PREDICATES: Tuple[str, ...] = (
    "in_ring", "in_ring_of_size_3", "in_ring_of_size_4", "in_ring_of_size_5",
    "in_ring_of_size_6", "in_ring_of_size_7", "in_ring_of_size_8",
    "aromatic", "same_fragment", "carbon_connected",
)

_SIGNATURE_GROUPS: Dict[str, Tuple[str, ...]] = {
    "atom_types": _ATOM_LETTERS,
    "hydrogen_count": ("has_0_hs", "has_1_hs", "has_2_hs", "has_3_hs"),
    "charge": ("charge0", "charge_m1", "charge_p1"),
    "chirality": ("ChiralR", "ChiralS"),
    "bonds": ("bSINGLE", "bDOUBLE", "bTRIPLE", "bAROMATIC", "bond",
             "has_bond_to"),
    "molecule_global": ("net_charge_neutral", "NetChargePositive",
                        "NetChargeNegative"),
    "computed": _COMPUTED_PREDICATES,
}


def chemical_signature() -> dict:
    """The full ChemLog vocabulary a chemical class definition may use
    (https://github.com/sfluegel05/chemlog-peptides) — so a generator never
    has to GUESS a predicate name or arity (a hallucinated predicate name is
    a pure-SYNTAX failure that burns a whole generation attempt; an
    unknown-predicate/wrong-arity slip is exactly what this catches before a
    definition ever reaches model checking, via
    ``api.check(formula, signature=chem.CHEMLOG_SIGNATURE)``).

    Returns:
        ``{"ok": True, "signature": <chem.CHEMLOG_SIGNATURE.to_dict()>,
        "stored_predicates": [...], "computed_predicates": [...],
        "groups": {"atom_types": [...], "hydrogen_count": [...], "charge":
        [...], "chirality": [...], "bonds": [...], "molecule_global": [...],
        "computed": [...]}, "dialect_note": str}``. ``signature`` is the
        raw, declared ``(name, arity)`` table (40 predicates — see
        :data:`unicode_fol_kit.chem.CHEMLOG_SIGNATURE`'s own docstring for
        exactly what is and is not covered, e.g. only the CANONICAL
        hydrogen-count 0..3 / charge -1/0/+1 range); ``stored_predicates``/
        ``computed_predicates`` split that same set by whether
        :func:`unicode_fol_kit.chem.mol_to_structure` materialises the
        extension up front or decides it algorithmically on demand (see that
        function's own "Why five predicates are COMPUTED" section);
        ``groups`` is the same 40 predicates organised by chemical
        role, for a caller that wants "what covers charge" rather than a
        flat list.
    """
    sig_dict = chem.CHEMLOG_SIGNATURE.to_dict()
    declared = set(sig_dict["predicates"])
    groups = {name: list(names) for name, names in _SIGNATURE_GROUPS.items()}
    grouped_names = {n for names in groups.values() for n in names}
    # Sanity, not a caller-facing failure mode: these groups are hand-
    # written against chem.CHEMLOG_SIGNATURE (see this section's own
    # docstring) rather than derived from it, precisely so this module never
    # imports chem's PRIVATE _naming — an assertion is what keeps that
    # duplication from silently drifting if the declared vocabulary ever
    # changes, per this kit's own "never approximate silently" convention.
    assert grouped_names <= declared, sorted(grouped_names - declared)
    stored = sorted(declared - set(_COMPUTED_PREDICATES))
    return {
        "ok": True,
        "signature": sig_dict,
        "stored_predicates": stored,
        "computed_predicates": list(_COMPUTED_PREDICATES),
        "groups": groups,
        "dialect_note": (
            "This vocabulary uses lowercase predicate names (c, o, n, "
            "bSINGLE, ...); in the kit's own unicode syntax those parse as "
            "variables/functions, never predicates. Write chemical class "
            "definitions in TPTP and pass dialect='tptp_bare' to "
            "check_molecule/check_molecules/explain_molecule_failure/"
            "simplify_definition rather than relying on auto-detection."),
    }
