"""Campaign-scale checking of chemical class definitions against molecules.

:func:`~unicode_fol_kit.eval.datasets.c3po.score_definition` answers "how good
is THIS definition" and returns a confusion matrix. This module answers the
other question a campaign asks — "run these K definitions over these N
molecules and write down everything that happened" — and its contract is
shaped by the two ways such a run fails in practice.

**A run never stops because of data.** One unparseable SMILES in a set of
200 000, or one definition mentioning a predicate no structure interprets,
must not cost the other 199 999 rows. Every such failure becomes a ROW with a
``status``, never an exception. The dividing line is exactly: is this a
property of the input data (row) or of the configuration (raise, immediately,
before the first molecule)? RDKit not installed, an unknown ``naming``, an
unwritable results path — those are configuration, and they fail loudly up
front rather than as 200 000 identical error rows.

**Partial results survive an interrupt.** Rows are flushed to JSONL after each
DEFINITION rather than at the end, so a run killed at 90 % keeps 90 %. With
``resume=True`` a re-run reads back what is already there and skips those
``(definition, molecule)`` pairs — the campaign's own restart mechanism, not
an afterthought.

**The structure is built once per molecule, not once per check.** That is what
:class:`~unicode_fol_kit.chem.cache.StructureCache` is for, and why this
module loops definition-outer/molecule-inner: the inner loop hits the cache.
Measured speed-up on this kit: 1.6× to 59× depending on how fast the formula
short-circuits, around 3–8× for a realistic mix (see the cache module's own
docstring for the numbers and the method).

Statuses a row can carry:

``ok``
    The formula was evaluated; ``holds`` is ``True``/``False``.
``exhausted``
    The evaluation budget ran out. ``holds`` is ``None`` — NEVER ``False``.
    A separate status because counting an undecided check as a negative is
    how an evaluation quietly flatters itself.
``structure_error``
    RDKit refused the SMILES. Cached, so it costs one attempt per molecule
    for the whole run, not one per definition.
``parse_error`` / ``eval_error``
    The definition did not parse (recorded ONCE, on a synthetic row with
    ``smiles=None``, and the definition is then skipped), or the evaluator
    refused this structure/formula pair (per row — typically an
    :class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol` for a
    class predicate that only exists in another definition).
"""

import io
import json
import os
import time
from dataclasses import dataclass, field
from typing import (
    Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple,
    Union,
)

from ..chem.cache import StructureBuildError, StructureCache
from ..fol.nodes import Atom, Node
from ..semantics.model_eval import (
    evaluate_detailed, UninterpretedSymbol, UnsupportedNode,
)

__all__ = ["ChemBatchResult", "check_definitions"]

_STATUSES = ("ok", "exhausted", "structure_error", "parse_error", "eval_error")


#: :meth:`ChemBatchResult.to_markdown`/:meth:`~ChemBatchResult.to_html`
#: default cap on how many non-``ok`` rows are rendered — see their
#: docstrings for why a campaign-scale result must never dump every row.
#: Private (not re-exported): a caller who wants a different cap just passes
#: ``max_rows=`` explicitly rather than importing this default.
_DEFAULT_MAX_ROWS = 25


@dataclass(frozen=True)
class ChemBatchResult:
    """Outcome of :func:`check_definitions`.

    ``rows`` is every row produced BY THIS CALL — rows skipped because a
    resume found them already written are not re-reported, so ``counts`` and
    ``rows`` describe the work this call did, while the JSONL file describes
    the run as a whole. ``skipped`` says how many pairs the resume passed
    over, so the difference is never silent.
    """

    rows: Tuple[dict, ...]
    counts: Dict[str, int]
    cache_stats: Dict[str, Any]
    seconds: float
    skipped: int = 0

    def to_dict(self) -> dict:
        return {"rows": list(self.rows), "counts": dict(self.counts),
                "cache_stats": dict(self.cache_stats),
                "seconds": self.seconds, "skipped": self.skipped}

    def to_markdown(self, max_rows: int = _DEFAULT_MAX_ROWS) -> str:
        """Render a summary as plain-formatted Markdown — NOT a row dump.

        A campaign run is hundreds of thousands of rows; a renderer that
        printed every one would produce multi-hundred-MB output and defeat
        the point of a summary. This renders ``counts``/``cache_stats``/
        ``seconds``/``skipped`` as summary tables, then an explicit, capped
        sample of at most ``max_rows`` non-``ok`` rows (their
        ``error_msg``/``unknown_predicates``/``witness``), and always closes
        with an honest "showing N of M" note — never a silent truncation.

        Every rendered field goes through :func:`_md_cell`, so a hostile
        SMILES/error message (one containing ``|`` or a newline) cannot
        corrupt the table structure. Calling this twice on the same result
        returns the identical string.
        """
        return "\n".join(_chem_markdown_lines(self, max_rows))

    def to_html(self, title: str = "Chem batch result",
               max_rows: int = _DEFAULT_MAX_ROWS) -> str:
        """Render as a self-contained, theme-aware HTML page — same summary
        content and the same ``max_rows`` cap as :meth:`to_markdown`, in the
        idiom :meth:`unicode_fol_kit.fol.derivation.CCGDerivation.to_html`
        established. Every user-supplied string (SMILES, error message,
        witness) is HTML-escaped.
        """
        return _html_page(title, _chem_html_body(self, max_rows), _CHEM_HTML_CSS)


def _resolve(formula: Union[Node, str], dialect: str) -> Node:
    """Definition text -> a ChemLog-spelled :class:`Node`.

    Delegates to :func:`unicode_fol_kit.eval.datasets.c3po._resolve_formula`
    rather than reimplementing the dialect routing and the ChemLog rename:
    two implementations of "which parser, then which rename" is exactly how
    the unicode path silently stopped matching structures once before.
    """
    from .datasets.c3po import _resolve_formula

    return _resolve_formula(formula, dialect)


def _unknown_predicates(formula: Node, structure) -> List[str]:
    """Predicates the formula uses that this structure does not interpret.

    Informational, never fatal. A ChEBI class definition legitimately names
    OTHER class predicates (``carboxylicAcid``, ``lipid``) that no molecule
    structure can decide — they have to be unfolded first — and refusing the
    definition for it would reject most of a real corpus. Reporting them once
    per definition turns a wall of identical per-row ``eval_error``s into one
    actionable line.
    """
    unknown = set()
    for part in formula.walk():
        if isinstance(part, Atom) and part.predicate not in ("=", "≠"):
            if not structure.interprets(part.predicate, len(part.args)):
                unknown.add(f"{part.predicate}/{len(part.args)}")
    return sorted(unknown)


def _existing_pairs(path: str) -> set:
    """``(def_id, smiles)`` pairs already in the results file.

    A truncated final line (the normal shape of an interrupted run) is
    ignored rather than raising: the pair it described simply gets redone.
    """
    pairs = set()
    if not os.path.exists(path):
        return pairs
    with io.open(path, encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except ValueError:
                continue
            pairs.add((row.get("def_id"), row.get("smiles")))
    return pairs


def check_definitions(
    definitions: Iterable[Mapping[str, Any]],
    molecules: Sequence[str],
    *,
    results_path: Optional[str] = None,
    dialect: str = "tptp",
    naming: str = "chemlog",
    aromatic: bool = True,
    computed: bool = True,
    all_different: bool = True,
    budget: Optional[int] = None,
    cache: Optional[StructureCache] = None,
    resume: bool = True,
    progress: Optional[Callable[[str, int, int], None]] = None,
) -> ChemBatchResult:
    """Evaluate every definition against every molecule.

    Args:
        definitions: mappings with ``"id"`` and ``"formula"`` (text in
            ``dialect``, or an already-parsed
            :class:`~unicode_fol_kit.fol.nodes.Node`). Validated up front —
            a missing key is a caller bug, not data, and raises.
        molecules: SMILES strings. Only strings: an already-parsed
            ``rdkit.Chem.Mol`` cannot be a cache key (object identity would
            defeat the cache and the key would be mutable).
        results_path: JSONL to append to, flushed after each definition.
            ``None`` keeps everything in memory only.
        dialect: ``"tptp"`` (the ChemLog format) or ``"unicode"``.
        naming / aromatic / computed: structure-building options, forwarded to
            :func:`~unicode_fol_kit.chem.mol_to_structure` AND part of the
            cache key — see :mod:`unicode_fol_kit.chem.cache`.
        all_different: ChemLog's convention that separately introduced
            existential variables denote distinct individuals. Defaults to
            ``True`` here, matching every other chemical entry point in the
            kit (and unlike the underlying evaluator's plain-FOL default).
        budget: evaluation step budget per check. ``None`` is unbounded; a
            campaign should set one, and an exhausted check is reported as
            ``status="exhausted"`` with ``holds=None``.
        cache: a shared :class:`~unicode_fol_kit.chem.cache.StructureCache`.
            One is created if omitted; pass your own to share it across calls
            (that is where the speed-up lives).
        resume: skip ``(def_id, smiles)`` pairs already present in
            ``results_path``.
        progress: called as ``(def_id, index, total)`` after each definition.

    Returns:
        A :class:`ChemBatchResult`.

    Raises:
        ValueError: a definition without ``id``/``formula``, a non-string
            SMILES, an unknown ``naming``/``dialect``, or an unwritable
            ``results_path`` — all configuration, all detected before the
            first molecule is built.
        ImportError: RDKit is not installed.
    """
    started = time.perf_counter()
    if naming not in ("chemlog", "paper"):
        raise ValueError(f"check_definitions: unknown naming={naming!r}")
    if dialect not in ("tptp", "unicode"):
        raise ValueError(f"check_definitions: unknown dialect={dialect!r}")

    prepared: List[Tuple[str, Any]] = []
    for entry in definitions:
        if "id" not in entry or "formula" not in entry:
            raise ValueError(
                "check_definitions: every definition needs 'id' and 'formula'; "
                f"got keys {sorted(entry)}")
        prepared.append((str(entry["id"]), entry["formula"]))
    for smiles in molecules:
        if not isinstance(smiles, str):
            raise ValueError(
                "check_definitions: molecules must be SMILES strings, got "
                f"{type(smiles).__name__}")

    if results_path:
        directory = os.path.dirname(os.path.abspath(results_path))
        if directory and not os.path.isdir(directory):
            raise ValueError(
                f"check_definitions: results_path directory does not exist: "
                f"{directory}")

    cache = cache if cache is not None else StructureCache()
    # Fail on a missing RDKit here, once, rather than per molecule: it is the
    # environment, not the data. Deliberately NOT through the cache — a
    # pre-warm would count as a hit on the first row and make the reported
    # hit rate flatter than the run actually achieved, which is the one
    # number M2 exists to measure.
    if molecules:
        from ..chem import mol_to_structure

        try:
            mol_to_structure(molecules[0], naming=naming, aromatic=aromatic,
                             computed=computed)
        except ValueError:
            pass    # a bad FIRST molecule is data; it gets its own row below

    done = _existing_pairs(results_path) if (resume and results_path) else set()
    rows: List[dict] = []
    counts: Dict[str, int] = {status: 0 for status in _STATUSES}
    skipped = 0

    def record(row: dict) -> None:
        rows.append(row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1

    for index, (def_id, raw_formula) in enumerate(prepared, 1):
        slab: List[dict] = []
        try:
            formula = _resolve(raw_formula, dialect)
        except Exception as exc:   # noqa: BLE001 — every parser has its own
            row = {"def_id": def_id, "smiles": None, "status": "parse_error",
                   "holds": None, "steps": None, "exhausted": None,
                   "witness": None, "error_kind": type(exc).__name__,
                   "error_msg": str(exc)[:400], "ms": None, "cached": None}
            record(row)
            slab.append(row)
            _flush(results_path, slab)
            if progress:
                progress(def_id, index, len(prepared))
            continue

        reported_unknown = False
        for smiles in molecules:
            if (def_id, smiles) in done:
                skipped += 1
                continue
            cell_started = time.perf_counter()
            before = cache.misses
            structure = cache.structure_for(smiles, naming=naming,
                                            aromatic=aromatic, computed=computed)
            was_cached = cache.misses == before
            row = {"def_id": def_id, "smiles": smiles, "status": "ok",
                   "holds": None, "steps": None, "exhausted": False,
                   "witness": None, "error_kind": None, "error_msg": None,
                   "ms": None, "cached": was_cached}

            if isinstance(structure, StructureBuildError):
                row.update(status="structure_error", exhausted=None,
                           error_kind="StructureBuildError",
                           error_msg=structure.message)
            else:
                if not reported_unknown:
                    unknown = _unknown_predicates(formula, structure)
                    reported_unknown = True
                    if unknown:
                        row["unknown_predicates"] = unknown
                try:
                    result = evaluate_detailed(
                        formula, structure, all_different=all_different,
                        budget=budget)
                except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
                    row.update(status="eval_error", exhausted=None,
                               error_kind=type(exc).__name__,
                               error_msg=str(exc)[:400])
                else:
                    row["steps"] = result.steps
                    row["exhausted"] = result.exhausted
                    if result.exhausted:
                        row["status"] = "exhausted"
                    else:
                        row["holds"] = result.holds
                        row["witness"] = (dict(result.witness)
                                          if result.witness else None)
            row["ms"] = round((time.perf_counter() - cell_started) * 1000, 4)
            record(row)
            slab.append(row)

        _flush(results_path, slab)
        if progress:
            progress(def_id, index, len(prepared))

    return ChemBatchResult(
        rows=tuple(rows), counts=counts, cache_stats=cache.stats(),
        seconds=round(time.perf_counter() - started, 3), skipped=skipped)


def _flush(results_path: Optional[str], slab: List[dict]) -> None:
    """Append one definition's rows and fsync-free close.

    Append mode, one open/close per definition: a campaign run is minutes to
    hours long, and holding one handle open for its whole duration means an
    interrupt loses whatever the OS had buffered.
    """
    if not results_path or not slab:
        return
    with io.open(results_path, "a", encoding="utf-8", newline="\n") as handle:
        for row in slab:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


# ---------------------------------------------------------------------------
# ChemBatchResult.to_markdown() / to_html() — a capped SUMMARY, never a row
# dump (see both docstrings): display only, no new decision-procedure logic,
# so no soundness risk. Pure formatting over already-computed rows/counts.
# ---------------------------------------------------------------------------

def _md_cell(value) -> str:
    """Escape a value for safe embedding in one Markdown table cell.

    A bare ``|`` would be read as a new column and an embedded newline would
    split the row across lines — both routinely occur in campaign data (a
    SMILES cannot contain either, but an ``error_msg`` free-text string can)
    — so both are neutralised here. Mirrors
    :func:`unicode_fol_kit.eval.theory_check._md_cell` exactly (a stable,
    three-line function); duplicated rather than imported the way
    :mod:`unicode_fol_kit.atp._html` documents duplicating ``esc_html`` —
    see :func:`_esc_html` below for the matching HTML-side duplicate and why
    this module does not import ``atp._html`` itself.
    """
    text = _cell(value)
    text = text.replace("|", "\\|")
    return text.replace("\r\n", " ").replace("\n", " ").replace("\r", " ")


def _cell(value) -> str:
    """None-safe stringification shared by the Markdown and HTML table
    builders: a row field genuinely IS ``None`` for every ``parse_error``
    row (:func:`check_definitions` always sets ``smiles=None`` there), and a
    bare ``str(None)`` would render the misleading literal text ``"None"``
    in the cell rather than an empty one.
    """
    return "" if value is None else str(value)


def _gloss_chem_witness(witness: Optional[Mapping[str, Any]]) -> str:
    """A short, honest gloss of a row's ``witness``: which FOL variable was
    bound to which individual, per :func:`~unicode_fol_kit.semantics.model_eval
    .evaluate_detailed`'s own existential search (``EvalResult.witness``).

    Deliberately NOT routed through
    :func:`unicode_fol_kit.eval.explain.explain_countermodel`: that
    function's bare-``{name: value}``-dict branch is documented, and its
    generated text is hardcoded, as a Z3 SMT model ("Z3 found a model ...
    the two sides differ") — a chem row's witness never touched Z3 and
    proves a formula IS satisfied by this structure, not that two sides of
    an implication differ, so routing it through that text would misstate
    both the source and the claim. (Contrast
    :mod:`unicode_fol_kit.eval.theory_check`'s own renderer, where a
    ``SatisfiabilityResult``/``SubsumptionResult`` witness genuinely IS
    shaped like — and produced by the same backend chain as —
    ``Verdict.countermodel``, so reusing ``explain_countermodel`` there is a
    faithful reuse of that function's actual contract.)
    """
    if not witness:
        return ""
    items = sorted(witness.items(), key=lambda kv: str(kv[0]))
    return "witness " + ", ".join(f"{k}={v}" for k, v in items)


def _row_detail(row: Mapping[str, Any]) -> str:
    """The one-line "why" for a non-``ok`` row: its error message, any
    unknown predicates, and a gloss of its witness — whichever are present.

    Note: :func:`check_definitions` only ever populates ``row["witness"]``
    inside the branch that leaves ``status="ok"`` (mirroring
    :func:`~unicode_fol_kit.semantics.model_eval.evaluate_detailed`'s own
    ``EvalResult.witness``, documented "only ever set when ``holds`` is
    ``True``"). :meth:`ChemBatchResult.to_markdown`/:meth:`to_html` only ever
    sample non-``ok`` rows (see :func:`_sample_rows`), so on genuine
    ``check_definitions`` output the witness-gloss branch below is currently
    unreachable from the sample — this function still handles it (a witness
    on a non-``ok`` row is not a contract violation, just not something
    today's row-construction produces) rather than assuming it can't happen.
    """
    parts = []
    error_msg = row.get("error_msg")
    if error_msg:
        parts.append(str(error_msg))
    unknown = row.get("unknown_predicates")
    if unknown:
        parts.append("unknown predicates: " + ", ".join(unknown))
    gloss = _gloss_chem_witness(row.get("witness"))
    if gloss:
        parts.append(gloss)
    return "; ".join(parts)


def _summary_rows(result: ChemBatchResult) -> List[Tuple[str, str]]:
    rows = [("rows", str(len(result.rows))), ("seconds", str(result.seconds)),
            ("skipped", str(result.skipped))]
    for key in sorted(result.cache_stats):
        rows.append((f"cache.{key}", str(result.cache_stats[key])))
    return rows


def _status_rows(result: ChemBatchResult) -> List[Tuple[str, str]]:
    return [(status, str(result.counts[status]))
            for status in sorted(result.counts)]


def _sample_rows(result: ChemBatchResult, max_rows: int) -> Tuple[List[dict], int]:
    """The first ``max_rows`` non-``ok`` rows (row order preserved, so this
    is deterministic), and the total non-``ok`` count they are a sample of.

    ``max_rows`` is clamped to 0 rather than passed straight into a slice: a
    negative value (e.g. computed by a caller as ``limit - offset``) would
    otherwise hit Python's negative-slice semantics, which drop elements
    from the END of the list instead of capping the sample to zero — the
    opposite of what a cap parameter should do, while still letting the
    closing "showing N of M" line look plausible instead of clearly wrong.
    """
    non_ok = [row for row in result.rows if row.get("status") != "ok"]
    max_rows = max(0, max_rows)
    return non_ok[:max_rows], len(non_ok)


def _chem_markdown_lines(result: ChemBatchResult, max_rows: int) -> List[str]:
    lines: List[str] = ["# Chem batch result", ""]
    lines.append(f"**{len(result.rows)}** row(s) in **{result.seconds}s**, "
                 f"**{result.skipped}** skipped.")
    lines.append("")

    lines.append("## Summary")
    lines.append("")
    lines.append("| metric | value |")
    lines.append("|---|---|")
    for metric, value in _summary_rows(result):
        lines.append(f"| {_md_cell(metric)} | {_md_cell(value)} |")
    lines.append("")

    lines.append("## Status breakdown")
    lines.append("")
    lines.append("| status | count |")
    lines.append("|---|---|")
    for status, count in _status_rows(result):
        lines.append(f"| {_md_cell(status)} | {_md_cell(count)} |")
    lines.append("")

    lines.append("## Sample of non-ok rows")
    lines.append("")
    sample, total = _sample_rows(result, max_rows)
    lines.append("| def_id | smiles | status | detail |")
    lines.append("|---|---|---|---|")
    for row in sample:
        lines.append(f"| {_md_cell(row.get('def_id'))} | {_md_cell(row.get('smiles'))} "
                     f"| {_md_cell(row.get('status'))} | {_md_cell(_row_detail(row))} |")
    lines.append("")
    lines.append(f"showing {len(sample)} of {total} non-ok row(s); full data in "
                 "`rows`/the JSONL results file.")
    lines.append("")

    while len(lines) >= 2 and lines[-1] == "" and lines[-2] == "":
        lines.pop()
    return lines


# ---------------------------------------------------------------------------
# HTML: a small, self-contained page-wrapper local to this module. See
# _md_cell's docstring — this duplicates unicode_fol_kit.atp._html's
# esc_html/html_page idiom rather than importing it, because (unlike
# eval.theory_check, which already imports unicode_fol_kit.atp at module
# scope) this module does not otherwise reach into atp, and this batch's own
# working notes ask for a local helper rather than establishing that import
# direction here.
# ---------------------------------------------------------------------------

def _esc_html(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


_CHEM_HTML_CSS = """
:root{--pg:#faf9f6;--ink:#23232a;--muted:#6b6b76;--bar:#3f3f47;--accent:#1c46b0}
@media(prefers-color-scheme:dark){:root{--pg:#15151a;--ink:#e9e8e4;--muted:#a6a6b0;--bar:#c3c3cd;--accent:#84a6ff}}
:root[data-theme=light]{--pg:#faf9f6;--ink:#23232a;--muted:#6b6b76;--bar:#3f3f47;--accent:#1c46b0}
:root[data-theme=dark]{--pg:#15151a;--ink:#e9e8e4;--muted:#a6a6b0;--bar:#c3c3cd;--accent:#84a6ff}
body{margin:0;background:var(--pg);color:var(--ink)}
.rpt{max-width:900px;margin:0 auto;padding:26px 16px;
  font-family:ui-sans-serif,system-ui,"Segoe UI",Arial,sans-serif;
  font-size:14px;line-height:1.5}
.rpt h1{font-size:20px;margin:0 0 8px}
.rpt h2{font-size:16px;margin:22px 0 6px;border-bottom:1.3px solid var(--bar);padding-bottom:3px}
.rpt table{border-collapse:collapse;width:100%;margin:4px 0 10px}
.rpt th,.rpt td{border:1px solid var(--bar);padding:4px 8px;text-align:left;
  vertical-align:top}
.rpt th{color:var(--muted);font-weight:600}
.rpt .note{color:var(--muted);font-size:12.5px}
"""


def _html_page(title: str, body_html: str, extra_css: str) -> str:
    """Wrap ``body_html`` in a self-contained, theme-aware HTML page — the
    same skeleton :meth:`unicode_fol_kit.fol.derivation.CCGDerivation.to_html`
    and :mod:`unicode_fol_kit.atp._html`'s ``html_page`` use."""
    return (
        "<!doctype html>\n<html><head><meta charset=\"utf-8\">\n"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        "<title>%s</title>\n<style>%s</style></head>\n<body>\n%s\n</body></html>\n"
        % (_esc_html(title), extra_css, body_html)
    )


def _html_table(headers: Tuple[str, ...], rows: List[Tuple[str, ...]]) -> str:
    head = "".join("<th>%s</th>" % _esc_html(h) for h in headers)
    body = "".join(
        "<tr>%s</tr>" % "".join("<td>%s</td>" % _esc_html(str(cell)) for cell in row)
        for row in rows
    )
    return "<table><tr>%s</tr>%s</table>" % (head, body)


def _chem_html_body(result: ChemBatchResult, max_rows: int) -> str:
    parts: List[str] = ['<div class="rpt">', "<h1>Chem batch result</h1>",
                        "<p>%d row(s) in %ss, %d skipped.</p>"
                        % (len(result.rows), result.seconds, result.skipped)]

    parts.append("<h2>Summary</h2>")
    parts.append(_html_table(("metric", "value"), _summary_rows(result)))

    parts.append("<h2>Status breakdown</h2>")
    parts.append(_html_table(("status", "count"), _status_rows(result)))

    parts.append("<h2>Sample of non-ok rows</h2>")
    sample, total = _sample_rows(result, max_rows)
    table_rows = [
        (_cell(row.get("def_id")), _cell(row.get("smiles")), _cell(row.get("status")),
         _row_detail(row))
        for row in sample
    ]
    parts.append(_html_table(("def_id", "smiles", "status", "detail"), table_rows))
    parts.append('<p class="note">showing %d of %d non-ok row(s); full data in '
                "<code>rows</code>/the JSONL results file.</p>" % (len(sample), total))

    parts.append("</div>")
    return "".join(parts)
