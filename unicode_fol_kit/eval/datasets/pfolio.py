"""Adapter for P-FOLIO (Han, Simeng, et al., "P-FOLIO: Evaluating and
Improving Logical Reasoning with Abundant Human-Written Reasoning Chains",
Findings of the Association for Computational Linguistics: EMNLP 2024) —
local CSV files only, no network access.

Source and verified schema
---------------------------
Canonical source: https://huggingface.co/datasets/yale-nlp/P-FOLIO (access
gated — a Hugging Face login is required to download it; this loader never
downloads anything itself). P-FOLIO extends FOLIO (Han et al., "FOLIO:
Natural Language Reasoning with First-Order Logic", arXiv:2209.00840; see
also :mod:`~unicode_fol_kit.eval.datasets.folio`, which reads a DIFFERENT,
JSONL, distribution of FOLIO — the ``FOLIO.csv`` this module joins against
is P-FOLIO's OWN bundled spreadsheet export of the same underlying stories,
not that JSONL file, and the two do not share a row format) with a
human-written, step-by-step derivation for every (story, conclusion) pair.
The repository ships the dataset as two CSV files, and this adapter's own
schema assumptions below were checked directly against a real download
(one file each, 2026-09) — not assumed from the paper or the HF card:

``P-FOLIO.csv`` (16071 data rows, columns ``story_id``, ``Truth Value``,
``Premises used``, ``Derivation``, ``Derivation - Corrected``,
``Derivation index``, ``Inference rule``) is a spreadsheet export where **a
row with a non-blank, digit-only ``story_id`` opens one conclusion's
block**: its ``Truth Value`` is that conclusion's gold label, and every
following row with a blank ``story_id`` is one derivation step of that
block (``Derivation index`` ``D1``, ``D2``, ... referencing earlier steps or
``Premises used`` indices into the story's premise list). A story with
several conclusions has several consecutive blocks; **the block's position
among its story's blocks, counted in file order starting at 0, is the only
thing that says WHICH conclusion it is** — the file carries no conclusion
id of its own. Many rows are blank padding between blocks.

``FOLIO.csv`` (487 data rows, columns ``''``, ``Premises - NL``,
``Conclusions - NL``, ``Truth Values``, ``Premises - FOL``,
``Conclusions - FOL``, ``Comments``, ``Verified by Prover``) has one row per
STORY: its unnamed first column is the story id (verified: every id ``0``
… ``486`` present exactly once, matching ``P-FOLIO.csv``'s ``story_id``
range exactly), and ``Premises - NL``/``Conclusions - NL``/
``Truth Values``/``Premises - FOL``/``Conclusions - FOL`` each hold a
NEWLINE-separated list — one entry per premise (first two columns) or per
conclusion (last three), in the SAME order the P-FOLIO blocks for that
story appear in.

This adapter's join, and what it refuses
------------------------------------------
The two files carry no shared conclusion id, so — exactly as this module's
build spec requires — a P-FOLIO block's ``nl_conclusion``/``fol_conclusion``
are resolved by joining ``FOLIO.csv`` on **story id AND the block's
position among its story's blocks**, and every join is CROSS-CHECKED: the
block's own ``Truth Value`` must equal ``FOLIO.csv``'s truth value at that
same position, or the block is refused rather than trusted. This was
verified by hand against several real stories before being encoded as a
blanket check (see ``tests/test_datasets_pfolio.py`` for the same
cross-check run against the small fixture below): story 5's two ``T``
blocks' last derivation steps read, verbatim, "If the Hulk does not wake up,
then Thor is not happy." and "If Thor is happy, then Peter Parker wears a
uniform" — exactly ``FOLIO.csv`` story 5's first two conclusions, in order,
both labelled ``T`` on both sides.

Of the real, once-downloaded ``P-FOLIO.csv``'s 1431 blocks (2026-09), **1420
load cleanly** through :func:`load_pfolio` and **11 are refused** — a 99.2%
yield, all 11 individually accounted for below rather than swallowed into an
aggregate. Re-measured directly through the loader by
``test_the_real_files_join_as_measured`` in ``tests/test_datasets_pfolio.py``
(opt-in, since the source files are access-gated — see below).

A block is REFUSED (excluded from :func:`load_pfolio`'s default strict
pass, listed with a reason by :func:`pfolio_refusals`) — never guessed —
for any of:

* ``"unparseable_truth_value"`` — the block's ``Truth Value`` cell, after
  stripping whitespace, is not exactly ``"T"``/``"F"``/``"U"``. The real
  file's two worst offenders are reviewer notes left IN the truth-value
  cell instead of a real ``T``/``F``/``U``, e.g. ``"F -> should be U?\\n
  rui_comment: F is correct."`` — guessing which of the two conflicting
  reviewers is right is exactly the guessing this adapter declines to do.
  A bare trailing newline (``"T\\n"``, common throughout the real file) is
  NOT an unparseable value — it is stripped, not refused.
* ``"folio_story_ambiguous"`` — that story's ``FOLIO.csv`` row cannot be
  read unambiguously in the first place (see :func:`_read_folio`: its
  conclusions/truth-values/conclusion-FOL lists disagree in length, or its
  premises/premises-FOL lists do, even after trimming wholly-blank leading
  or trailing list entries — a known export artifact, see below). Verified
  in the real file: of 487 stories, only story 249 is genuinely ambiguous
  this way (its ``Conclusions - NL`` column holds 6 lines that read like
  PREMISES, not conclusions, while ``Truth Values``/``Conclusions - FOL``
  hold only 2 — a real upstream data defect, not a formatting artifact).
* ``"story_not_in_folio"`` — the block's ``story_id`` has no row in
  ``FOLIO.csv`` at all (defensive; does not occur in the verified real
  files, where the id ranges match exactly, but a caller-supplied fixture
  or a future release could still have this).
* ``"position_out_of_range"`` — the block's position exceeds how many
  conclusions that story's ``FOLIO.csv`` row actually has. Verified once in
  the real file: story 135 has three P-FOLIO blocks but only two resolved
  FOLIO conclusions.
* ``"truth_value_mismatch"`` — the block's own truth value parses fine and
  the position resolves, but disagrees with ``FOLIO.csv``'s truth value at
  that position. Verified five times in the real file (stories 34, 50
  twice, 258, 409) — genuine annotation disagreements between the two
  files, not something this adapter is in a position to adjudicate.

Three further export artifacts, all handled WITHOUT guessing at their
content, are worth naming explicitly because they could otherwise look like
corruption:

* A handful of rows in ``P-FOLIO.csv`` have a non-blank, non-digit
  ``story_id`` (e.g. a stray ``"("`` character, or a whole comment row like
  ``"Need to change xor"`` sitting alone between blank padding rows). Only
  a BLANK or DIGIT-ONLY ``story_id`` is read as starting a new block; any
  other value is never interpreted as an id OR as a truth value — the row
  is treated exactly like a blank-``story_id`` row, i.e. as one more
  derivation-step candidate of whichever block is currently open (real
  content columns intact) or as ignorable padding (nothing else on the
  row). This is the same "only the recognised column means anything on
  this row" treatment already used for a stray reviewer comment landing in
  a derivation row's ``Truth Value`` cell (see the fixture and
  ``tests/test_datasets_pfolio.py`` for both real-shaped cases).
* Several ``FOLIO.csv`` cells hold one extra wholly-blank leading or
  trailing line inside an otherwise-consistent newline-separated list
  (verified: stories 55, 113, 135). :func:`_split_field` trims ONLY
  wholly-blank entries at the very start/end of such a list — never a
  blank in the middle, and never anything from a non-blank entry — before
  the length cross-check above runs, so these three stories load normally
  rather than being flagged ``folio_story_ambiguous``.
* A block's FIRST derivation step's own content (``Premises used``/
  ``Derivation``/``Derivation - Corrected``/``Derivation index``/
  ``Inference rule``) sometimes sits on the SAME row as the block's own
  ``story_id``/``Truth Value`` header, rather than on a following
  blank-``story_id`` row (verified: real story 246's ``D1``, and 164 of the
  real file's 1431 blocks overall, 33 of them with that step as their ONLY
  one — indistinguishable from a genuinely derivation-less block unless
  this row is also inspected). :func:`_iter_pfolio_blocks` checks a
  header row's own columns 2–6 the same way it checks any other row's, so
  that first step is kept, not silently dropped.

``Derivation`` vs. ``Derivation - Corrected`` are two DIFFERENT upstream
columns (the corrected text is only sometimes present, and sometimes reads
quite differently from the original — both were observed verbatim in the
real file) and this adapter keeps them as two separate keys in every
``meta["proof_steps"]`` entry, never merged into one. ``Premises used`` is
likewise kept VERBATIM as a single string rather than parsed into a list of
indices: real values mix plain premise numbers, ``D``-prefixed references
to earlier steps, comma- and even full-width-comma (``，``)-separated lists
(``"3，5"``) in the same column — parsing that into a clean structure would
be exactly the kind of guess this adapter's build spec forbids.

Truth-value vocabulary — a real, documented difference from
:mod:`~unicode_fol_kit.eval.datasets.folio`
------------------------------------------------------------------------
``FOLIO.csv``'s ``Truth Values`` column (and P-FOLIO's ``Truth Value``
column) use the single letters ``"T"``/``"F"``/``"U"`` (:data:`PFOLIO_TRUTH_VALUES`)
— verified directly, not the ``"True"``/``"False"``/``"Uncertain"`` words
the OTHER FOLIO adapter's JSONL source uses. ``label`` here is that letter,
UNCHANGED — this loader does not translate between the two vocabularies
(that would be presenting an invented value as gold data).

License: **MIT**, per the yale-nlp/P-FOLIO Hugging Face dataset card.

This module never downloads anything — obtain both CSV files yourself from
https://huggingface.co/datasets/yale-nlp/P-FOLIO (a Hugging Face account and
accepted access request are required) and pass their local paths to
:func:`load_pfolio`.
"""

import csv
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, NamedTuple, Optional, Tuple, Union

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_pfolio", "pfolio_refusals", "PFOLIO_TRUTH_VALUES",
          "PFOLIO_REFUSAL_REASONS"]

#: The verified vocabulary of P-FOLIO's/FOLIO.csv's own truth-value tokens
#: (single letters — see the module docstring for how this differs from
#: :mod:`~unicode_fol_kit.eval.datasets.folio`'s word-form labels).
PFOLIO_TRUTH_VALUES = ("T", "F", "U")

#: The reasons :func:`load_pfolio`/:func:`pfolio_refusals` can report for a
#: block that was NOT turned into a :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
#: — see the module docstring's "This adapter's join, and what it refuses"
#: section for what each one means and how often it fires on the real file.
PFOLIO_REFUSAL_REASONS = (
    "unparseable_truth_value", "folio_story_ambiguous", "story_not_in_folio",
    "position_out_of_range", "truth_value_mismatch",
)

_register_dataset_info(
    "pfolio",
    license="MIT, per the yale-nlp/P-FOLIO Hugging Face dataset card.",
    source_url="https://huggingface.co/datasets/yale-nlp/P-FOLIO",
    citation_hint=(
        "Han, Simeng, et al. \"P-FOLIO: Evaluating and Improving Logical "
        "Reasoning with Abundant Human-Written Reasoning Chains.\" Findings "
        "of the Association for Computational Linguistics: EMNLP 2024, "
        "pages 16553-16565. arXiv:2410.09207."
    ),
)


# ---------------------------------------------------------------------------
# FOLIO.csv — one row per story
# ---------------------------------------------------------------------------

_FOLIO_HEADER = (
    "", "Premises - NL", "Conclusions - NL", "Truth Values",
    "Premises - FOL", "Conclusions - FOL", "Comments", "Verified by Prover",
)


class _FolioStory(NamedTuple):
    premises_nl: Tuple[str, ...]
    premises_fol: Tuple[str, ...]
    conclusions_nl: Tuple[str, ...]
    conclusions_fol: Tuple[str, ...]
    truth_values: Tuple[str, ...]
    comments: Optional[str]
    verified_by_prover: Optional[str]


def _lf_cells(row: List[str]) -> List[str]:
    """``row`` with every line break inside a cell rewritten to ``\\n``.

    ``csv`` (read with ``newline=""``, as it must be) hands a quoted cell's
    embedded line breaks through VERBATIM. The real files break lines inside
    cells with a bare ``\\n``, but a copy that went through a CRLF-converting
    tool (a git checkout with ``core.autocrlf``, a Windows editor) carries
    ``\\r\\n`` there, and splitting that on ``\\n`` leaves a ``\\r`` glued
    to every premise and conclusion. A line break inside a cell means the
    same thing in either convention, so both files read identically."""
    return [cell.replace("\r\n", "\n").replace("\r", "\n") for cell in row]


def _split_field(cell: str) -> List[str]:
    """Newline-split ``cell``, trimming only WHOLLY-BLANK leading/trailing
    entries (a verified export artifact — see the module docstring). A
    blank entry anywhere else in the list, or any whitespace inside a
    non-blank entry, is left untouched."""
    lines = cell.split("\n")
    while lines and lines[0].strip() == "":
        lines.pop(0)
    while lines and lines[-1].strip() == "":
        lines.pop()
    return lines


def _read_folio(path: Union[str, Path]) -> Tuple[Dict[int, _FolioStory], Dict[int, str]]:
    """Read ``FOLIO.csv`` into per-story records.

    Returns ``(stories, ambiguous)``: ``stories`` maps a story id to a
    :class:`_FolioStory` for every story whose premise/conclusion lists are
    internally consistent; ``ambiguous`` maps every OTHER story id to a
    human-readable reason it could not be read unambiguously (see the
    module docstring's ``"folio_story_ambiguous"`` entry) — such a story is
    never silently dropped, only excluded from ``stories``.

    Raises:
        ValueError: the header does not match the verified ``FOLIO.csv``
            column layout, a row's own id does not parse as a non-negative
            integer, or a story id repeats — this is STRUCTURAL corruption
            of the reference file itself, refused unconditionally (unlike
            the per-story ambiguity above, there is no safe partial reading
            of a file whose id scheme is broken).
    """
    path = Path(path)
    stories: Dict[int, _FolioStory] = {}
    ambiguous: Dict[int, str] = {}
    with path.open("r", encoding="utf-8-sig", newline="") as fh:
        reader = csv.reader(fh)
        header = tuple(next(reader))
        if header != _FOLIO_HEADER:
            raise ValueError(
                f"pfolio: {path} has header {header!r}, expected "
                f"{_FOLIO_HEADER!r} — is this FOLIO.csv?")

        seen: Dict[int, int] = {}
        for row_no, row in enumerate(reader):
            if len(row) != len(_FOLIO_HEADER):
                raise ValueError(
                    f"pfolio: {path} row {row_no} has {len(row)} fields, "
                    f"expected {len(_FOLIO_HEADER)}")
            row = _lf_cells(row)
            raw_id = row[0].strip()
            if not raw_id.isdigit():
                raise ValueError(
                    f"pfolio: {path} row {row_no} has story id {row[0]!r}, "
                    "not a non-negative integer — is this FOLIO.csv?")
            story_id = int(raw_id)
            if story_id in seen:
                raise ValueError(
                    f"pfolio: {path} has story id {story_id} at both rows "
                    f"{seen[story_id]} and {row_no} — ids must be unique")
            seen[story_id] = row_no

            premises_nl = _split_field(row[1])
            conclusions_nl = _split_field(row[2])
            truth_values = _split_field(row[3])
            premises_fol = _split_field(row[4])
            conclusions_fol = _split_field(row[5])
            comments = row[6].strip() or None
            verified_by_prover = row[7].strip() or None

            if len(premises_nl) != len(premises_fol):
                ambiguous[story_id] = (
                    f"premises-NL/premises-FOL length mismatch "
                    f"({len(premises_nl)} vs {len(premises_fol)})")
                continue
            if not (len(conclusions_nl) == len(truth_values) == len(conclusions_fol)):
                ambiguous[story_id] = (
                    "conclusions-NL/truth-values/conclusions-FOL length "
                    f"mismatch ({len(conclusions_nl)}, {len(truth_values)}, "
                    f"{len(conclusions_fol)})")
                continue
            bad_tv = [t for t in truth_values if t.strip() not in PFOLIO_TRUTH_VALUES]
            if bad_tv:
                ambiguous[story_id] = f"unparseable truth value(s) {bad_tv!r}"
                continue

            stories[story_id] = _FolioStory(
                premises_nl=tuple(premises_nl),
                premises_fol=tuple(premises_fol),
                conclusions_nl=tuple(conclusions_nl),
                conclusions_fol=tuple(conclusions_fol),
                truth_values=tuple(t.strip() for t in truth_values),
                comments=comments,
                verified_by_prover=verified_by_prover,
            )
    return stories, ambiguous


# ---------------------------------------------------------------------------
# P-FOLIO.csv — several derivation-step rows per block, several blocks per story
# ---------------------------------------------------------------------------

_PFOLIO_HEADER = (
    "story_id", "Truth Value", "Premises used", "Derivation",
    "Derivation - Corrected", "Derivation index", "Inference rule",
)


def _none_if_blank(text: str) -> Optional[str]:
    stripped = text.strip()
    return stripped if stripped else None


class _RawBlock(NamedTuple):
    story_id: int
    truth_raw: str
    steps: Tuple[dict, ...]
    header_row_no: int


def _iter_pfolio_blocks(path: Union[str, Path]) -> Iterator[_RawBlock]:
    """Group ``P-FOLIO.csv``'s rows into blocks, in file order.

    A row STARTS a new block iff its ``story_id`` cell, stripped, is
    non-empty and digit-only; every other row either extends the currently
    open block (if it carries any real step content — see the module
    docstring for why a stray non-digit ``story_id`` or a stray comment in
    the ``Truth Value`` column of such a row is never interpreted) or is
    ignored as padding.

    Raises:
        ValueError: the header does not match the verified ``P-FOLIO.csv``
            column layout, or a row has the wrong field count — structural
            corruption of the file itself.
    """
    path = Path(path)
    current: Optional[dict] = None
    with path.open("r", encoding="utf-8-sig", newline="") as fh:
        reader = csv.reader(fh)
        header = tuple(next(reader))
        if header != _PFOLIO_HEADER:
            raise ValueError(
                f"pfolio: {path} has header {header!r}, expected "
                f"{_PFOLIO_HEADER!r} — is this P-FOLIO.csv?")

        for row_no, row in enumerate(reader):
            if len(row) != len(_PFOLIO_HEADER):
                raise ValueError(
                    f"pfolio: {path} row {row_no} has {len(row)} fields, "
                    f"expected {len(_PFOLIO_HEADER)}")
            row = _lf_cells(row)
            story_id_raw = row[0].strip()
            if story_id_raw.isdigit():
                if current is not None:
                    yield _RawBlock(current["story_id"], current["truth_raw"],
                                    tuple(current["steps"]), current["header_row_no"])
                current = {"story_id": int(story_id_raw), "truth_raw": row[1],
                          "steps": [], "header_row_no": row_no}
                if any(cell.strip() for cell in row[2:7]):
                    # A real export artifact: the block's FIRST derivation
                    # step's content sometimes sits on the very same row as
                    # the story_id/Truth Value header, rather than on a
                    # following blank-story_id row (verified: real story
                    # 246's D1). Not capturing it here would silently drop
                    # that step — see the module docstring.
                    current["steps"].append({
                        "premises_used": _none_if_blank(row[2]),
                        "derivation": _none_if_blank(row[3]),
                        "derivation_corrected": _none_if_blank(row[4]),
                        "step_id": _none_if_blank(row[5]),
                        "inference_rule": _none_if_blank(row[6]),
                        "row_no": row_no,
                    })
                continue
            if current is None:
                continue                          # padding before any block
            if any(cell.strip() for cell in row[2:7]):
                current["steps"].append({
                    "premises_used": _none_if_blank(row[2]),
                    "derivation": _none_if_blank(row[3]),
                    "derivation_corrected": _none_if_blank(row[4]),
                    "step_id": _none_if_blank(row[5]),
                    "inference_rule": _none_if_blank(row[6]),
                    "row_no": row_no,
                })
        if current is not None:
            yield _RawBlock(current["story_id"], current["truth_raw"],
                            tuple(current["steps"]), current["header_row_no"])


def _parse_truth_value(raw: str) -> Optional[str]:
    stripped = raw.strip()
    return stripped if stripped in PFOLIO_TRUTH_VALUES else None


# ---------------------------------------------------------------------------
# The join
# ---------------------------------------------------------------------------

def _iter_joined(pfolio_path: Union[str, Path], folio_path: Union[str, Path],
                 known_bad_ids: FrozenSet[str]) -> Iterator[Tuple[str, object]]:
    """Yield ``("ok", DatasetExample)`` or ``("refused", dict)`` per P-FOLIO
    block, in file order — the shared engine behind :func:`load_pfolio` and
    :func:`pfolio_refusals`, so the two never disagree about what loads.

    A refusal dict is ``{"story_id", "position", "reason" (one of
    :data:`PFOLIO_REFUSAL_REASONS`), "detail", "row_no"}`` — ``row_no`` is
    the block's own header row's 0-based data-row number in ``P-FOLIO.csv``,
    for tracing a refusal back to the source file.
    """
    stories, ambiguous = _read_folio(folio_path)
    positions: Dict[int, int] = {}

    for block in _iter_pfolio_blocks(pfolio_path):
        story_id = block.story_id
        position = positions.get(story_id, 0)
        positions[story_id] = position + 1

        def _refused(reason: str, detail: Optional[str]) -> Tuple[str, dict]:
            return ("refused", {"story_id": story_id, "position": position,
                                "reason": reason, "detail": detail,
                                "row_no": block.header_row_no})

        truth_value = _parse_truth_value(block.truth_raw)
        if truth_value is None:
            yield _refused("unparseable_truth_value", block.truth_raw)
            continue
        if story_id in ambiguous:
            yield _refused("folio_story_ambiguous", ambiguous[story_id])
            continue
        story = stories.get(story_id)
        if story is None:
            yield _refused("story_not_in_folio", None)
            continue
        if position >= len(story.conclusions_nl):
            yield _refused(
                "position_out_of_range",
                f"story {story_id} has only {len(story.conclusions_nl)} "
                "FOLIO.csv conclusion(s)")
            continue
        folio_truth_value = story.truth_values[position]
        if folio_truth_value != truth_value:
            yield _refused(
                "truth_value_mismatch",
                f"P-FOLIO.csv={truth_value!r} FOLIO.csv={folio_truth_value!r}")
            continue

        example_id = f"pfolio:{story_id}:{position}"
        proof_steps = [
            {
                "step_id": step["step_id"],
                "premises_used": step["premises_used"],
                "derivation": step["derivation"],
                "derivation_corrected": step["derivation_corrected"],
                "inference_rule": step["inference_rule"],
            }
            for step in block.steps
        ]
        meta = {
            "story_id": story_id,
            "position": position,
            "folio_comments": story.comments,
            "folio_verified_by_prover": story.verified_by_prover,
            "proof_steps": proof_steps,
        }
        yield ("ok", DatasetExample(
            id=example_id,
            nl_premises=story.premises_nl,
            fol_premises=story.premises_fol,
            nl_conclusion=story.conclusions_nl[position],
            fol_conclusion=story.conclusions_fol[position],
            label=folio_truth_value,
            known_bad=example_id in known_bad_ids,
            meta=meta,
        ))


def load_pfolio(pfolio_path: Union[str, Path], folio_path: Union[str, Path], *,
                known_bad_ids: FrozenSet[str] = frozenset(),
                on_refused: str = "raise") -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local pair of P-FOLIO/FOLIO CSV files, joined per the module docstring.

    Field mapping: ``nl_premises``/``fol_premises`` = the joined story's
    ``FOLIO.csv`` premises (repeated across every conclusion of that story,
    the same "several consecutive examples share identical premises"
    situation :mod:`~unicode_fol_kit.eval.datasets.folio`'s docstring
    documents for its own story grouping); ``nl_conclusion``/
    ``fol_conclusion`` = that story's ``FOLIO.csv`` conclusion/FOL at the
    block's position; ``label`` = the (agreeing) truth value, one of
    :data:`PFOLIO_TRUTH_VALUES`. ``meta`` carries ``story_id``, ``position``
    (both 0-based/int), ``folio_comments``/``folio_verified_by_prover``
    (``FOLIO.csv``'s own free-text columns, kept at STORY granularity —
    verified too sparse and inconsistently shaped to align per-conclusion,
    see the module docstring), and ``proof_steps``: the block's derivation
    rows verbatim, each ``{"step_id", "premises_used", "derivation",
    "derivation_corrected", "inference_rule"}`` (``Derivation`` and
    ``Derivation - Corrected`` kept as two distinct keys, never merged;
    ``premises_used`` kept as one raw string, never parsed into indices —
    see the module docstring for why).

    Args:
        pfolio_path: local path to ``P-FOLIO.csv``.
        folio_path: local path to P-FOLIO's own bundled ``FOLIO.csv`` (NOT
            the JSONL file :func:`~unicode_fol_kit.eval.datasets.folio.load_folio`
            reads — see the module docstring).
        known_bad_ids: ids (``f"pfolio:{story_id}:{position}"``) whose gold
            annotation is known to be broken. Every yielded example with a
            matching id gets ``known_bad=True``.
        on_refused: what to do with a block this adapter cannot safely join
            (see the module docstring's refusal reasons). ``"raise"``
            (default): raise :class:`ValueError` naming the story, position
            and reason at the first one reached — the loud, no-guessing
            default. ``"skip"``: drop it from the yielded stream instead
            (use :func:`pfolio_refusals` to see what was dropped and why —
            nothing is silently lost either way, only excluded from this
            call's own output).

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        successfully-joined P-FOLIO block, in file order.

    Raises:
        ValueError: ``on_refused`` is not ``"raise"``/``"skip"``; either CSV
            file has the wrong header or a malformed row (structural
            corruption, refused unconditionally regardless of
            ``on_refused``); or, with ``on_refused="raise"``, the first
            block that cannot be safely joined.
        FileNotFoundError: either path does not exist.
    """
    if on_refused not in ("raise", "skip"):
        raise ValueError(
            f"pfolio: on_refused must be 'raise' or 'skip', got {on_refused!r}")

    for kind, payload in _iter_joined(pfolio_path, folio_path, known_bad_ids):
        if kind == "ok":
            yield payload
            continue
        if on_refused == "raise":
            raise ValueError(
                f"pfolio: story {payload['story_id']} conclusion #"
                f"{payload['position']} (P-FOLIO.csv row {payload['row_no']}) "
                f"refused ({payload['reason']}): {payload['detail']}")
        # on_refused == "skip": drop it, recoverable via pfolio_refusals().


def pfolio_refusals(pfolio_path: Union[str, Path],
                    folio_path: Union[str, Path]) -> List[dict]:
    """Every block :func:`load_pfolio` would refuse, with why — a read-only
    diagnostic pass, never raising for a refusal itself (only for the same
    structural-corruption cases :func:`load_pfolio` always raises for).

    Returns one ``{"story_id", "position", "reason", "detail", "row_no"}``
    dict per refused block, in file order (see :func:`_iter_joined`'s
    docstring for the field meanings, and the module docstring's "This
    adapter's join, and what it refuses" section for what each ``reason``
    means). Empty iff every block in ``pfolio_path`` joins cleanly.
    """
    return [payload for kind, payload
            in _iter_joined(pfolio_path, folio_path, frozenset())
            if kind == "refused"]
