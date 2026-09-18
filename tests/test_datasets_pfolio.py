"""Tests for the P-FOLIO adapter (unicode_fol_kit.eval.datasets.pfolio).

The fixtures (``tests/fixtures/pfolio/pfolio_mini.csv`` and
``.../folio_mini.csv``) are SYNTHETIC — hand-written in the REAL, verified
CSV layout of both files (columns, block/step structure, the newline-joined
per-story lists) — for two reasons: the real dataset is access-gated (a
Hugging Face login and an accepted access request are required), so it is
not committed here, and every documented export artifact and refusal
reason (see ``unicode_fol_kit/eval/datasets/pfolio.py``'s module docstring)
can be put side by side in nine small stories instead of hunted across the
real file's 487.

Every fixture value below, and every expectation against it, was chosen
BY HAND (not derived from the code under test) — including the five
non-obvious export artifacts and five refusal reasons, each of which was
first found and hand-verified against a real, once-downloaded copy of both
CSV files (see ``test_the_real_files_join_as_measured``, skipped unless
``$UFK_PFOLIO_CSV``/``$UFK_FOLIO_CSV`` point at local copies; its expected
counts are the ones the adapter's module docstring documents, arrived at by
manually cross-checking several real stories' derivation chains against
their ``FOLIO.csv`` conclusion text — the same technique
:mod:`~unicode_fol_kit.eval.datasets.logicnli`'s docstring used to
cross-check its own two sources against each other).
"""

import os
from collections import Counter
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import DATASET_INFO, DatasetExample, audit_examples
from unicode_fol_kit.eval.datasets.pfolio import (
    PFOLIO_REFUSAL_REASONS, PFOLIO_TRUTH_VALUES, load_pfolio, pfolio_refusals,
)

_FIXTURES = Path(__file__).parent / "fixtures" / "pfolio"
_PFOLIO = _FIXTURES / "pfolio_mini.csv"
_FOLIO = _FIXTURES / "folio_mini.csv"


def _examples(**kwargs):
    kwargs.setdefault("on_refused", "skip")
    return list(load_pfolio(_PFOLIO, _FOLIO, **kwargs))


def _by_id(examples):
    return {e.id: e for e in examples}


# ---------------------------------------------------------------------------
# Reading — the successful joins
# ---------------------------------------------------------------------------

def test_the_fixture_loads_the_eight_clean_conclusions_in_file_order():
    examples = _examples()
    assert [e.id for e in examples] == [
        "pfolio:0:0", "pfolio:0:1", "pfolio:1:0", "pfolio:1:1",
        "pfolio:2:0", "pfolio:2:1", "pfolio:4:0", "pfolio:8:0",
    ]
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_premises_and_conclusion_come_from_folio_csv_at_the_right_position():
    example = _by_id(_examples())["pfolio:0:0"]
    assert example.nl_premises == ("All ravens are black.", "Rook is a raven.")
    assert example.fol_premises == (
        "∀x (Raven(x) → Black(x))", "Raven(rook)")
    assert example.nl_conclusion == "Rook is black."
    assert example.fol_conclusion == "Black(rook)"
    assert example.label == "T"
    assert example.label in PFOLIO_TRUTH_VALUES

    # The SAME story's second conclusion: same premises, different
    # conclusion/label, taken from position 1 of the same FOLIO.csv row.
    second = _by_id(_examples())["pfolio:0:1"]
    assert second.nl_premises == example.nl_premises
    assert second.nl_conclusion == "Rook is white."
    assert second.fol_conclusion == "White(rook)"
    assert second.label == "F"


def test_derivation_and_derivation_corrected_stay_distinct_never_merged():
    steps = _by_id(_examples())["pfolio:0:0"].meta["proof_steps"]
    assert steps == [
        {"step_id": "D1", "premises_used": "1, 2",
         "derivation": "Rook is a raven that is black.",
         "derivation_corrected": None,
         "inference_rule": "universal instantiation"},
        {"step_id": "D2", "premises_used": "D1",
         "derivation": "Rook is black.",
         "derivation_corrected": "Rook the raven is black.",
         "inference_rule": "conjunction elimination"},
    ]
    # D2's corrected text genuinely differs from the original -- merging
    # them would silently discard one.
    assert (steps[1]["derivation"] != steps[1]["derivation_corrected"])


def test_premises_used_is_kept_verbatim_never_parsed_into_indices():
    # "D1" (a step reference), "1, 2" (premise numbers) and "D1, 1" (mixed)
    # all appear raw, exactly as the source column spells them.
    steps = {e.id: e.meta["proof_steps"] for e in _examples()}
    assert steps["pfolio:0:0"][0]["premises_used"] == "1, 2"
    assert steps["pfolio:0:0"][1]["premises_used"] == "D1"
    assert steps["pfolio:0:1"][1]["premises_used"] == "D1, 1"


def test_a_conclusion_with_no_derivation_loads_with_an_empty_step_list():
    example = _by_id(_examples())["pfolio:1:1"]
    assert example.label == "U"
    assert example.nl_conclusion == "Milo never sleeps."
    assert example.meta["proof_steps"] == []


def test_folio_comments_and_verified_by_prover_are_kept_at_story_granularity():
    # Both conclusions of story 0 carry the SAME story-level comments text
    # -- it is not, and cannot safely be, split one-per-conclusion (see the
    # module docstring: the real file's own comment columns are too sparse
    # and inconsistently shaped to align positionally).
    examples = _by_id(_examples())
    assert examples["pfolio:0:0"].meta["folio_comments"] == (
        "extra brackets?\nsecond note")
    assert examples["pfolio:0:1"].meta["folio_comments"] == (
        "extra brackets?\nsecond note")
    assert examples["pfolio:0:0"].meta["folio_verified_by_prover"] is None


def test_every_step_and_story_id_and_position_are_recorded():
    example = _by_id(_examples())["pfolio:2:1"]
    assert example.meta["story_id"] == 2
    assert example.meta["position"] == 1


# ---------------------------------------------------------------------------
# Export artifacts, handled without guessing
# ---------------------------------------------------------------------------

def test_a_trailing_newline_in_the_truth_value_cell_is_stripped_not_refused():
    # Story 0's and story 1's first blocks both use "T\n" in the fixture,
    # mirroring the real file's most common contamination -- neither is a
    # refusal.
    examples = _by_id(_examples())
    assert examples["pfolio:0:0"].label == "T"
    assert examples["pfolio:1:0"].label == "T"
    assert not any(r["story_id"] in (0, 1) for r in pfolio_refusals(_PFOLIO, _FOLIO))


def test_a_leading_blank_line_in_folio_csvs_lists_is_trimmed():
    # Story 1's Conclusions-NL/Truth-Values cells both start with one
    # wholly-blank line in the fixture; after trimming, position 0 is
    # "Milo sleeps often." (T), not the blank line.
    example = _by_id(_examples())["pfolio:1:0"]
    assert example.nl_conclusion == "Milo sleeps often."
    assert example.label == "T"


def test_a_trailing_blank_line_in_folio_csvs_lists_is_trimmed():
    # Story 2's Truth-Values cell ends with one wholly-blank line in the
    # fixture; after trimming it is ["T", "F"], matching the two real
    # conclusions rather than leaving a dangling empty third slot.
    examples = _by_id(_examples())
    assert examples["pfolio:2:0"].label == "T"
    assert examples["pfolio:2:1"].label == "F"


def test_a_stray_non_digit_story_id_on_a_step_row_extends_the_open_block():
    # The fixture's story-0/F block has a step row whose story_id cell is a
    # stray "(" rather than blank -- it must be read as this block's SECOND
    # step (its real content columns are intact), never as a new block
    # header (its story_id is not digit-only) and never by trying to
    # interpret "(" as anything.
    steps = _by_id(_examples())["pfolio:0:1"].meta["proof_steps"]
    assert len(steps) == 2
    assert steps[1]["step_id"] == "D2"
    assert steps[1]["inference_rule"] == "reductio ad absurdum"


def test_a_comment_in_a_step_rows_truth_value_column_is_never_read():
    # Story-2/F's one step row carries "^shouldn't this be U?" in the
    # column that would be Truth Value on a HEADER row; on a step row that
    # column is simply not consulted, so the step still loads normally and
    # the block's own (correct) label stays "F".
    example = _by_id(_examples())["pfolio:2:1"]
    assert example.label == "F"
    steps = example.meta["proof_steps"]
    assert len(steps) == 1
    assert steps[0]["derivation"] == "Rex does not bark."


def test_a_lone_comment_row_between_blocks_is_ignored():
    # "Need to fix labels" sits alone (every other column blank) between
    # story 0's two blocks; it must neither start a spurious block nor
    # attach itself as a step -- story 0/T keeps exactly its two real steps,
    # and the comment text itself appears nowhere in them.
    steps = _by_id(_examples())["pfolio:0:0"].meta["proof_steps"]
    assert len(steps) == 2
    assert not any(s["derivation"] == "Need to fix labels" for s in steps)
    # Nor did it leak into a spurious extra block for story 0.
    assert [e.id for e in _examples() if e.meta["story_id"] == 0] == [
        "pfolio:0:0", "pfolio:0:1"]


def test_a_derivation_steps_content_on_the_blocks_own_header_row_is_kept():
    # Story 8's block puts D1's own content (Premises used/Derivation/
    # Derivation index/Inference rule) on the SAME row as the block's own
    # story_id + Truth Value header, rather than on a following
    # blank-story_id row -- mirroring the real file's story 246 (verified:
    # 164 of the real file's 1431 blocks have this shape, 33 of them with
    # D1 as their ONLY step). It must still be kept as the block's first
    # step, not silently discarded.
    steps = _by_id(_examples())["pfolio:8:0"].meta["proof_steps"]
    assert len(steps) == 2
    assert steps[0] == {
        "step_id": "D1", "premises_used": "1, 2",
        "derivation": "Milo naps in the afternoon.",
        "derivation_corrected": None,
        "inference_rule": "universal instantiation"}
    assert steps[1]["step_id"] == "D2"
    assert steps[1]["premises_used"] == "D1"
    assert steps[1]["derivation"] == "Milo is asleep."


# ---------------------------------------------------------------------------
# Refusals -- named, not guessed
# ---------------------------------------------------------------------------

def test_every_refusal_reason_fires_exactly_where_hand_designed():
    refusals = {(r["story_id"], r["position"]): r for r in pfolio_refusals(_PFOLIO, _FOLIO)}
    assert set(refusals) == {(3, 0), (4, 1), (6, 0), (7, 0), (99, 0)}
    assert refusals[(3, 0)]["reason"] == "folio_story_ambiguous"
    assert "3, 1, 1" in refusals[(3, 0)]["detail"]
    assert refusals[(4, 1)]["reason"] == "position_out_of_range"
    assert refusals[(6, 0)]["reason"] == "unparseable_truth_value"
    assert "rui_comment" in refusals[(6, 0)]["detail"]
    assert refusals[(7, 0)]["reason"] == "truth_value_mismatch"
    assert "P-FOLIO.csv='T'" in refusals[(7, 0)]["detail"]
    assert "FOLIO.csv='F'" in refusals[(7, 0)]["detail"]
    assert refusals[(99, 0)]["reason"] == "story_not_in_folio"
    assert set(r["reason"] for r in refusals.values()) <= set(PFOLIO_REFUSAL_REASONS)


def test_refused_blocks_never_appear_among_load_pfolios_skip_output():
    ids = {e.id for e in _examples(on_refused="skip")}
    assert not ids & {"pfolio:3:0", "pfolio:4:1", "pfolio:6:0",
                      "pfolio:7:0", "pfolio:99:0"}
    assert len(_examples(on_refused="skip")) == 8


def test_on_refused_raise_is_the_default_and_names_the_first_refusal():
    with pytest.raises(ValueError, match="folio_story_ambiguous"):
        list(load_pfolio(_PFOLIO, _FOLIO))       # on_refused defaults to "raise"


def test_an_unknown_on_refused_mode_is_rejected():
    with pytest.raises(ValueError, match="on_refused"):
        list(load_pfolio(_PFOLIO, _FOLIO, on_refused="ignore"))


# ---------------------------------------------------------------------------
# known_bad_ids / DATASET_INFO / audit_examples
# ---------------------------------------------------------------------------

def test_known_bad_ids_flag_the_story_position_id():
    examples = _by_id(_examples(known_bad_ids=frozenset({"pfolio:1:0"})))
    assert examples["pfolio:1:0"].known_bad is True
    assert examples["pfolio:0:0"].known_bad is False


def test_the_provenance_is_registered():
    info = DATASET_INFO["pfolio"]
    assert info["license"] == "MIT, per the yale-nlp/P-FOLIO Hugging Face dataset card."
    assert info["source_url"] == "https://huggingface.co/datasets/yale-nlp/P-FOLIO"
    assert "P-FOLIO" in info["citation_hint"]
    assert "2410.09207" in info["citation_hint"]


def test_every_loaded_gold_formula_parses_and_checks_clean():
    # An independent second route: run the kit's OWN parser/checker over
    # every gold FOL string the fixture claims -- a typo in a hand-written
    # fixture formula would show up here as a real defect, not a made-up one.
    report = audit_examples(_examples())
    assert len(report) == 8
    assert all(row["ok"] and not row["defects"] for row in report)


# ---------------------------------------------------------------------------
# Structural corruption of the CSV files themselves is refused unconditionally
# ---------------------------------------------------------------------------

def _write_folio(tmp_path, rows, header=None):
    import csv
    header = header or ["", "Premises - NL", "Conclusions - NL",
                        "Truth Values", "Premises - FOL", "Conclusions - FOL",
                        "Comments", "Verified by Prover"]
    path = tmp_path / "folio_bad.csv"
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)
    return path


def _write_pfolio(tmp_path, rows, header=None):
    import csv
    header = header or ["story_id", "Truth Value", "Premises used",
                        "Derivation", "Derivation - Corrected",
                        "Derivation index", "Inference rule"]
    path = tmp_path / "pfolio_bad.csv"
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)
    return path


def test_a_wrong_folio_header_is_refused_by_name(tmp_path):
    bad = _write_folio(tmp_path, [], header=["wrong", "header"])
    with pytest.raises(ValueError, match="header"):
        list(load_pfolio(_PFOLIO, bad))


def test_a_wrong_pfolio_header_is_refused_by_name(tmp_path):
    bad = _write_pfolio(tmp_path, [], header=["wrong", "header"])
    with pytest.raises(ValueError, match="header"):
        list(load_pfolio(bad, _FOLIO))


def test_a_non_digit_folio_story_id_is_refused_by_name(tmp_path):
    bad = _write_folio(tmp_path, [["not-a-number", "p", "c", "T", "P", "C", "", ""]])
    with pytest.raises(ValueError, match="non-negative integer"):
        list(load_pfolio(_PFOLIO, bad))


def test_a_duplicate_folio_story_id_is_refused_by_name(tmp_path):
    bad = _write_folio(tmp_path, [
        ["0", "p", "c", "T", "P", "C", "", ""],
        ["0", "p2", "c2", "F", "P2", "C2", "", ""],
    ])
    with pytest.raises(ValueError, match="duplicate|both rows"):
        list(load_pfolio(_PFOLIO, bad))


def test_a_short_row_is_refused_by_name(tmp_path):
    import csv
    path = tmp_path / "folio_short.csv"
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["", "Premises - NL", "Conclusions - NL", "Truth Values",
                    "Premises - FOL", "Conclusions - FOL", "Comments",
                    "Verified by Prover"])
        f.write("0,p,c,T,P,C\n")          # only 6 fields, header has 8
    with pytest.raises(ValueError, match="fields"):
        list(load_pfolio(_PFOLIO, path))


# ---------------------------------------------------------------------------
# The real, access-gated files -- opt-in only
# ---------------------------------------------------------------------------

_REAL_PFOLIO = os.environ.get("UFK_PFOLIO_CSV")
_REAL_FOLIO = os.environ.get("UFK_FOLIO_CSV")
real_files = pytest.mark.skipif(
    not (_REAL_PFOLIO and _REAL_FOLIO and Path(_REAL_PFOLIO).is_file()
        and Path(_REAL_FOLIO).is_file()),
    reason="set $UFK_PFOLIO_CSV and $UFK_FOLIO_CSV to local copies of the "
           "real, access-gated P-FOLIO.csv/FOLIO.csv")


@real_files
def test_the_real_files_join_as_measured():
    """The adapter's documented numbers, re-measured through the loader."""
    examples = list(load_pfolio(_REAL_PFOLIO, _REAL_FOLIO, on_refused="skip"))
    refusals = pfolio_refusals(_REAL_PFOLIO, _REAL_FOLIO)
    assert len(examples) == 1420
    assert len(refusals) == 11
    assert Counter(r["reason"] for r in refusals) == {
        "truth_value_mismatch": 5, "unparseable_truth_value": 3,
        "folio_story_ambiguous": 2, "position_out_of_range": 1,
    }
    # Story 5's two agreeing "T" conclusions, hand-verified against the
    # real file: their derivation chains' LAST steps read, verbatim, the
    # same two sentences FOLIO.csv gives as story 5's first two conclusions.
    by_id = {e.id: e for e in examples}
    first = by_id["pfolio:5:0"]
    second = by_id["pfolio:5:1"]
    assert first.label == second.label == "T"
    assert first.meta["proof_steps"][-1]["derivation"].strip() == (
        "If the Hulk does not wake up, then Thor is not happy.")
    assert second.meta["proof_steps"][-1]["derivation"].strip() == (
        "If Thor is happy, then Peter Parker wears a uniform")
