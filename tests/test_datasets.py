"""Tests for unicode_fol_kit.eval.datasets (FOLIO / MALLS adapters).

Fixtures used here (``tests/fixtures/folio_mini.jsonl``,
``tests/fixtures/malls_mini.jsonl``) are hand-written SYNTHETIC examples in
the verified upstream field format (see the ``folio.py``/``malls.py`` module
docstrings for how that format was verified) — they are NOT copied from the
real FOLIO/MALLS datasets, only shaped like them, for license hygiene. Each
fixture has one deliberately broken row as its LAST line, chosen to exercise
a different defect class per dataset:

* FOLIO row 4: ``premises-FOL[0]`` is ``"Cat(x) → Mammal(x)"`` — a valid FOL
  string (it PARSES) but has an unbound variable ``x`` (no ``∀x``/``∃x``
  binds it), so it fails ``check()`` with ``is_closed=False``. This exercises
  the "parses but is ill-formed" defect path.
* MALLS row 4: ``"FOL"`` is ``"∀x (Gizmo(x) → Whirs(x)"`` — missing its
  closing parenthesis, so it fails to parse under ANY dialect
  ``parse_any`` tries. This exercises the "does not even parse" defect path.

Together the two fixtures cover both defect classes ``audit_examples`` must
distinguish, each hand-verified below by reasoning through
``unicode_fol_kit.api.parse_any``/``check`` directly (not just re-asserting
whatever the code under test happens to compute).
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import (
    DatasetExample,
    DATASET_INFO,
    audit_examples,
    load_folio,
    load_malls,
)

_FIXTURES = Path(__file__).parent / "fixtures"
_FOLIO_FIXTURE = _FIXTURES / "folio_mini.jsonl"
_MALLS_FIXTURE = _FIXTURES / "malls_mini.jsonl"


# ---------------------------------------------------------------------------
# FOLIO: field mapping and id resolution
# ---------------------------------------------------------------------------

def test_load_folio_yields_one_example_per_line():
    """4 non-blank JSONL lines in the fixture -> 4 examples, in file order."""
    examples = list(load_folio(_FOLIO_FIXTURE))
    assert len(examples) == 4
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_folio_field_mapping_first_example():
    """premises/premises-FOL/conclusion/conclusion-FOL/label map verbatim.

    Row 1 of the fixture has no id field, so the id must fall back to the
    positional form documented in folio.py: f"folio:{line_no}" with line_no=0.
    """
    example = next(load_folio(_FOLIO_FIXTURE))
    assert example.id == "folio:0"
    assert example.nl_premises == ("All cats are mammals.", "Tom is a cat.")
    assert example.fol_premises == ("∀x (Cat(x) → Mammal(x))", "Cat(tom)")
    assert example.nl_conclusion == "Tom is a mammal."
    assert example.fol_conclusion == "Mammal(tom)"
    assert example.label == "True"
    assert example.known_bad is False


def test_load_folio_uses_native_example_id_when_present():
    """Row 3 carries an explicit 'example-id' -> that value is used verbatim,
    not the positional fallback (which would be 'folio:2')."""
    examples = list(load_folio(_FOLIO_FIXTURE))
    third = examples[2]
    assert third.id == "folio-dev-42"
    assert third.meta["source"] == "synthetic"


def test_load_folio_positional_id_fallback_for_id_less_rows():
    """Rows without a native id field get 0-based positional ids."""
    examples = list(load_folio(_FOLIO_FIXTURE))
    assert [e.id for e in examples] == ["folio:0", "folio:1", "folio-dev-42", "folio:3"]


def test_load_folio_known_bad_flag():
    """known_bad_ids flags exactly the matching example, nothing else."""
    examples = list(load_folio(_FOLIO_FIXTURE, known_bad_ids=frozenset({"folio:3"})))
    known_bad = {e.id: e.known_bad for e in examples}
    assert known_bad == {
        "folio:0": False, "folio:1": False,
        "folio-dev-42": False, "folio:3": True,
    }


# ---------------------------------------------------------------------------
# FOLIO: lazy parsing
# ---------------------------------------------------------------------------

def test_folio_parse_premises_and_conclusion_on_good_example():
    """Row 1 is a well-formed example: both premises and the conclusion parse."""
    example = next(load_folio(_FOLIO_FIXTURE))
    premise_results = example.parse_premises()
    assert len(premise_results) == 2
    assert all(pr.ok for pr in premise_results)
    conclusion_result = example.parse_conclusion()
    assert conclusion_result is not None
    assert conclusion_result.ok is True
    assert conclusion_result.formula is not None


def test_folio_parse_premises_broken_example_parses_but_is_not_closed():
    """Row 4's first premise 'Cat(x) → Mammal(x)' PARSES (ParseResult.ok is
    True — it is syntactically a well-formed formula) but 'x' is free, which
    is a semantic (check()) defect, not a parse defect. This is the exact
    distinction audit_examples' all_parsed vs all_checked must preserve."""
    examples = list(load_folio(_FOLIO_FIXTURE))
    broken = examples[3]
    assert broken.id == "folio:3"
    premise_results = broken.parse_premises()
    assert premise_results[0].ok is True
    assert premise_results[1].ok is True                # 'Cat(tom)' is fine

    from unicode_fol_kit import api
    checked = api.check(premise_results[0].formula)
    assert checked.ok is False
    assert checked.is_closed is False
    assert checked.free_variables == ("x",)


def test_parse_conclusion_is_none_when_no_conclusion_field():
    """A hand-built example with fol_conclusion=None must short-circuit to
    None rather than calling parse_any on None (which would raise)."""
    example = DatasetExample(
        id="synthetic:1", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None,
        known_bad=False,
    )
    assert example.parse_conclusion() is None
    assert example.parse_premises() == ()


# ---------------------------------------------------------------------------
# FOLIO: audit_examples finds the deliberately broken row
# ---------------------------------------------------------------------------

def test_audit_examples_finds_exactly_the_broken_folio_example():
    examples = list(load_folio(_FOLIO_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 4

    not_ok = [r for r in report if not r["ok"]]
    assert [r["id"] for r in not_ok] == ["folio:3"]

    broken = not_ok[0]
    assert broken["all_parsed"] is True         # it DID parse
    assert broken["all_checked"] is False        # but failed check()
    assert broken["defects"] == [{
        "kind": "free_variables", "field": "premises",
        "index": 0, "detail": ["x"],
    }]

    good = [r for r in report if r["ok"]]
    assert len(good) == 3
    assert all(r["all_parsed"] and r["all_checked"] and not r["defects"] for r in good)


def test_audit_examples_respects_max_examples():
    """max_examples=2 must stop after the first two, not audit all four."""
    examples = list(load_folio(_FOLIO_FIXTURE))
    report = audit_examples(examples, max_examples=2)
    assert len(report) == 2
    assert [r["id"] for r in report] == ["folio:0", "folio:1"]


def test_audit_examples_accepts_a_generator_not_just_a_list():
    """audit_examples must consume the loader's own iterator directly."""
    report = audit_examples(load_folio(_FOLIO_FIXTURE))
    assert len(report) == 4


# ---------------------------------------------------------------------------
# MALLS: field mapping
# ---------------------------------------------------------------------------

def test_load_malls_yields_one_example_per_line():
    examples = list(load_malls(_MALLS_FIXTURE))
    assert len(examples) == 4


def test_load_malls_field_mapping():
    """MALLS has no premise/conclusion structure: NL/FOL map onto the
    conclusion slot (see malls.py's docstring for the rationale), premises
    stay empty, and there is no entailment label."""
    example = next(load_malls(_MALLS_FIXTURE))
    assert example.id == "malls:0"
    assert example.nl_premises == ()
    assert example.fol_premises == ()
    assert example.nl_conclusion == "All dogs are animals."
    assert example.fol_conclusion == "∀x (Dog(x) → Animal(x))"
    assert example.label is None
    assert example.known_bad is False


def test_load_malls_known_bad_flag():
    examples = list(load_malls(_MALLS_FIXTURE, known_bad_ids=frozenset({"malls:3"})))
    assert [e.known_bad for e in examples] == [False, False, False, True]


# ---------------------------------------------------------------------------
# MALLS: audit_examples finds the unparseable row (different defect class
# than the FOLIO fixture's — see module docstring)
# ---------------------------------------------------------------------------

def test_audit_examples_finds_exactly_the_unparseable_malls_example():
    examples = list(load_malls(_MALLS_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 4

    not_ok = [r for r in report if not r["ok"]]
    assert [r["id"] for r in not_ok] == ["malls:3"]

    broken = not_ok[0]
    assert broken["all_parsed"] is False         # the unbalanced paren never parses
    assert broken["all_checked"] is True          # vacuous: nothing to check() failed
    assert len(broken["defects"]) == 1
    defect = broken["defects"][0]
    assert defect["kind"] == "unparseable"
    assert defect["field"] == "conclusion"
    assert defect["index"] is None

    good = [r for r in report if r["ok"]]
    assert len(good) == 3


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict, malformed-file behaviour
# ---------------------------------------------------------------------------

def test_dataset_info_registry_has_verified_provenance_for_both_datasets():
    assert set(DATASET_INFO) >= {"folio", "malls"}

    folio_info = DATASET_INFO["folio"]
    assert folio_info["license"] == "CC-BY-SA-4.0"
    assert folio_info["source_url"] == "https://github.com/Yale-LILY/FOLIO"
    assert folio_info["citation_hint"]

    malls_info = DATASET_INFO["malls"]
    assert "CC-BY-NC-4.0" in malls_info["license"]
    assert malls_info["source_url"] == "https://huggingface.co/datasets/yuan-yang/MALLS-v0"
    assert malls_info["citation_hint"]


def test_dataset_example_to_dict_is_json_compatible():
    example = next(load_folio(_FOLIO_FIXTURE))
    payload = example.to_dict()
    # json.dumps must not raise — the whole point of to_dict().
    text = json.dumps(payload)
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "folio:0"
    assert round_tripped["fol_premises"] == ["∀x (Cat(x) → Mammal(x))", "Cat(tom)"]
    assert isinstance(round_tripped["fol_premises"], list)   # tuple -> list


def test_load_folio_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_folio(_FIXTURES / "does_not_exist.jsonl"))


def test_load_malls_malformed_json_line_raises_not_silently_skipped():
    """A dataset file with a broken JSON line must fail loudly (this is a
    corrupted-file bug, not a per-example data defect that audit_examples
    is meant to characterise)."""
    bad_path = _FIXTURES / "_tmp_malformed_malls.jsonl"
    bad_path.write_text('{"NL": "ok", "FOL": "P(a)"}\nnot json at all\n', encoding="utf-8")
    try:
        with pytest.raises(json.JSONDecodeError):
            list(load_malls(bad_path))
    finally:
        bad_path.unlink()
