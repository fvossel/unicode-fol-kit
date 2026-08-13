"""Tests for the GROVES adapter (unicode_fol_kit.eval.datasets.groves).

``tests/fixtures/groves_mini.jsonl`` is NOT synthetic like
``folio_mini.jsonl``/``malls_mini.jsonl`` — it is 8 REAL rows copied verbatim
from the ``train`` split of https://huggingface.co/datasets/fvossel/groves
(verified 2026-08-12 via the Hugging Face datasets-server ``/first-rows``
API), at that split's row indices 0, 1, 2, 5, 6, 10, 17, 41 in that order.
This is safe/appropriate here (unlike FOLIO/MALLS, which are third-party
data this repo avoids redistributing) because GROVES is the repo author's
own dataset (CC-BY-NC-4.0), and each row was hand-picked specifically
because it already parses and checks out clean under this kit, so the
fixture doubles as a positive-path regression fixture rather than needing a
deliberately-broken row the way the FOLIO/MALLS fixtures do (see
``groves.py``'s module docstring for the verified schema and the probe that
established every sampled row parses/checks clean).

Each row's FOL was hand-traced against ``unicode_fol_kit.api.parse_any`` /
``unicode_fol_kit.api.check`` before being committed to the fixture:

* row 0 (pharma): ``∀x`` binds every use of ``x``; every ``∃y``/``∃z``/``∃w``
  binds its own variable within its own scope. Closed, arity-consistent
  (each predicate name used with one constant arity throughout), no lambdas.
* row 1 (event): ``∀x`` is the only binder; ``x`` occurs only inside its
  scope. Closed.
* row 2 (bird): ``∀x`` binds both occurrences of ``x`` (the nested
  ``¬Flightless(x) → Flies(x)`` is inside the ``∀x`` scope). Closed.
* row 3 (person/content, biconditional): ``∀x`` binds ``x`` throughout,
  including inside the ``↔``; the inner ``∃y`` binds ``y`` only inside
  ``Has(x, y)``. Closed.
* row 4 (ice cream cone): TWO adjacent existentials ``∃y ∃z`` without
  wrapping parens around each individually -- both bind into the same
  trailing conjunction ``Scoop(y) ∧ WaffleCone(z) ∧ Has(x, y) ∧ Has(x, z)``.
  Closed (exercises the multi-quantifier-prefix syntax this kit's grammar
  supports).
* row 5 (monkeys, XOR): ``∀x`` binds ``x``; ``⊕`` (exclusive or) is a binary
  connective between ``Red(x)`` and ``Blue(x)``, both in scope. Closed.
  Exercises the ``⊕`` connective specifically.
* row 6 (titan): a top-level IMPLICATION with no enclosing quantifier:
  ``¬∀x (Human(x) → Mortal(x)) → ∃y (Titan(y) ∧ ∀z (Titan(z) → Respects(z,
  y)))``. Still closed overall because EACH side is independently closed
  (``¬∀x(...)`` binds its own ``x``; ``∃y(...)`` binds its own ``y``, and the
  nested ``∀z`` binds ``z`` while ``y`` stays bound by the outer ``∃y``).
* row 7 (professor): ``¬∃x (Professor(x) ∧ ∀y (Course(y) ∧ In(y, university)
  → Taught(x, y)))`` -- ``x`` is bound by the outer ``∃x``, ``y`` by the
  inner ``∀y``; ``university`` is a 0-ary constant symbol, not a free
  variable (lowercase identifiers that are never quantifier-bound parse as
  constants, not variables, in this kit's grammar). Closed.

All 8 were confirmed by direct probe (``api.parse_any(fol).ok is True`` and
``api.check(formula)`` giving ``ok=True, is_closed=True,
arity_consistent=True, has_lambdas=False`` for every one) before being
written into the fixture and asserted on below.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import (
    DatasetExample,
    DATASET_INFO,
    audit_examples,
    load_groves,
)

_FIXTURES = Path(__file__).parent / "fixtures"
_GROVES_FIXTURE = _FIXTURES / "groves_mini.jsonl"

# The 8 fixture rows, in file order, as (nl, fol) -- copied verbatim from
# groves_mini.jsonl so the field-mapping test below re-derives its expected
# values independently of however the loader parses the file, rather than
# just re-asserting whatever json.load happens to produce.
_EXPECTED_ROWS = [
    (
        "Every pharmaceutical company researches, develops, and manufactures "
        "drugs that target diseases and medical conditions and improve "
        "patient outcomes.",
        "∀x (PharmaceuticalCompany(x) → ∃y (Drug(y) ∧ Researches(x, y) ∧ "
        "Develops(x, y) ∧ Manufactures(x, y) ∧ ∃z (Disease(z) ∧ Targets(y, "
        "z)) ∧ ∃w (MedicalCondition(w) ∧ Targets(y, w)) ∧ "
        "ImprovesPatientOutcomes(y)))",
    ),
    (
        "Every event is indoors, outdoors, or virtual, but not all three.",
        "∀x (Event(x) → ((Indoors(x) ∨ Outdoors(x) ∨ Virtual(x)) ∧ "
        "¬(Indoors(x) ∧ Outdoors(x) ∧ Virtual(x))))",
    ),
    (
        "A bird flies unless it is flightless.",
        "∀x (Bird(x) → (¬Flightless(x) → Flies(x)))",
    ),
    (
        "A person is content if and only if they are not fit and have "
        "companions.",
        "∀x (Person(x) → (Content(x) ↔ (¬Fit(x) ∧ ∃y (Companion(y) ∧ Has(x, "
        "y)))))",
    ),
    (
        "An ice cream cone has a scoop and a waffle cone.",
        "∀x (IceCreamCone(x) → ∃y ∃z (Scoop(y) ∧ WaffleCone(z) ∧ Has(x, y) ∧ "
        "Has(x, z)))",
    ),
    (
        "All monkeys are either red or blue.",
        "∀x (Monkey(x) → (Red(x) ⊕ Blue(x)))",
    ),
    (
        "There is a titan that every titan respects, presuming not all "
        "humans are mortal.",
        "¬∀x (Human(x) → Mortal(x)) → ∃y (Titan(y) ∧ ∀z (Titan(z) → "
        "Respects(z, y)))",
    ),
    (
        "There isn't a professor who has taught every course in the "
        "university.",
        "¬∃x (Professor(x) ∧ ∀y (Course(y) ∧ In(y, university) → Taught(x, "
        "y)))",
    ),
]


# ---------------------------------------------------------------------------
# Loading and field mapping
# ---------------------------------------------------------------------------

def test_load_groves_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_groves(_GROVES_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_groves_field_mapping_every_row():
    """NL/FOL map onto nl_conclusion/fol_conclusion verbatim, for EVERY row
    (not just the first) -- premises stay empty and there is no label, the
    same translation-pair shape as MALLS (see groves.py's docstring)."""
    examples = list(load_groves(_GROVES_FIXTURE))
    assert len(examples) == len(_EXPECTED_ROWS)
    for line_no, (example, (nl, fol)) in enumerate(zip(examples, _EXPECTED_ROWS)):
        assert example.id == f"groves:{line_no}"
        assert example.nl_premises == ()
        assert example.fol_premises == ()
        assert example.nl_conclusion == nl
        assert example.fol_conclusion == fol
        assert example.label is None
        assert example.known_bad is False
        assert example.meta["line_no"] == line_no


def test_load_groves_positional_id_fallback_for_all_rows():
    """GROVES has no native id field at all (see module docstring) -> every
    row gets the positional fallback, unconditionally."""
    examples = list(load_groves(_GROVES_FIXTURE))
    assert [e.id for e in examples] == [f"groves:{i}" for i in range(8)]


# ---------------------------------------------------------------------------
# known_bad_ids mechanic
# ---------------------------------------------------------------------------

def test_load_groves_known_bad_flag():
    """known_bad_ids flags exactly the matching examples, nothing else."""
    examples = list(load_groves(
        _GROVES_FIXTURE, known_bad_ids=frozenset({"groves:2", "groves:6"}),
    ))
    known_bad = {e.id: e.known_bad for e in examples}
    assert known_bad == {
        "groves:0": False, "groves:1": False, "groves:2": True,
        "groves:3": False, "groves:4": False, "groves:5": False,
        "groves:6": True, "groves:7": False,
    }


def test_load_groves_known_bad_ids_defaults_to_empty():
    """No known_bad_ids given -> every example is known_bad=False."""
    examples = list(load_groves(_GROVES_FIXTURE))
    assert all(e.known_bad is False for e in examples)


# ---------------------------------------------------------------------------
# Lazy parsing: every fixture FOL parses and is well-formed (see module
# docstring for the per-row hand-trace justifying this).
# ---------------------------------------------------------------------------

def test_groves_every_fixture_fol_parses_and_is_wellformed():
    from unicode_fol_kit import api

    examples = list(load_groves(_GROVES_FIXTURE))
    assert len(examples) == 8
    for example in examples:
        # No premises for GROVES -- parse_premises() must be the empty tuple,
        # not attempt to parse anything.
        assert example.parse_premises() == ()

        conclusion_result = example.parse_conclusion()
        assert conclusion_result is not None
        assert conclusion_result.ok is True, (
            f"{example.id} failed to parse: {conclusion_result.errors}"
        )
        checked = api.check(conclusion_result.formula)
        assert checked.ok is True, f"{example.id} failed check(): {checked}"
        assert checked.is_closed is True
        assert checked.arity_consistent is True
        assert checked.has_lambdas is False


# ---------------------------------------------------------------------------
# audit_examples over the fixture
# ---------------------------------------------------------------------------

def test_audit_examples_reports_all_ok_for_groves_fixture():
    """Every fixture row was hand-picked to already be well-formed (see
    module docstring), so audit_examples must report ok=True for all 8, with
    no defects -- unlike the FOLIO/MALLS fixtures, which deliberately carry
    one broken row each. all_checked is True for every row NOT vacuously (as
    it would be if premises were the only checked field, since GROVES's
    fol_premises is always empty) but because the single fol_conclusion each
    row carries genuinely passes check()."""
    examples = list(load_groves(_GROVES_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 8

    for entry, example in zip(report, examples):
        assert entry["id"] == example.id
        assert entry["known_bad"] is False
        assert entry["all_parsed"] is True
        assert entry["all_checked"] is True
        assert entry["ok"] is True
        assert entry["defects"] == []


def test_audit_examples_respects_max_examples_on_groves():
    examples = list(load_groves(_GROVES_FIXTURE))
    report = audit_examples(examples, max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == ["groves:0", "groves:1", "groves:2"]


# ---------------------------------------------------------------------------
# Error / edge cases
# ---------------------------------------------------------------------------

def test_load_groves_missing_fol_field_yields_none_not_exception(tmp_path):
    """A record missing "FOL" gets fol_conclusion=None rather than raising --
    the same documented "missing key -> None default" behaviour load_folio /
    load_malls use (record.get(...) with no default raises nothing; only a
    STRUCTURALLY malformed file, tested below, is a loud failure)."""
    path = tmp_path / "missing_fol.jsonl"
    path.write_text('{"NL": "A statement with no FOL translation."}\n', encoding="utf-8")

    examples = list(load_groves(path))
    assert len(examples) == 1
    assert examples[0].nl_conclusion == "A statement with no FOL translation."
    assert examples[0].fol_conclusion is None
    # parse_conclusion() must short-circuit to None, not call parse_any(None).
    assert examples[0].parse_conclusion() is None


def test_load_groves_missing_nl_field_yields_none_not_exception(tmp_path):
    path = tmp_path / "missing_nl.jsonl"
    path.write_text('{"FOL": "∀x (P(x) → Q(x))"}\n', encoding="utf-8")

    examples = list(load_groves(path))
    assert len(examples) == 1
    assert examples[0].nl_conclusion is None
    assert examples[0].fol_conclusion == "∀x (P(x) → Q(x))"


def test_load_groves_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_groves(_FIXTURES / "does_not_exist_groves.jsonl"))


def test_load_groves_malformed_json_line_raises_not_silently_skipped(tmp_path):
    """A dataset file with a broken JSON line must fail loudly (a corrupted
    file is a bug, not a per-example defect audit_examples characterises)."""
    bad_path = tmp_path / "_tmp_malformed_groves.jsonl"
    bad_path.write_text(
        '{"NL": "ok", "FOL": "P(a)"}\nnot json at all\n', encoding="utf-8",
    )
    with pytest.raises(json.JSONDecodeError):
        list(load_groves(bad_path))


def test_load_groves_honours_opportunistic_id_field(tmp_path):
    """If a downstream re-export DID add an 'id' key, it must be honoured
    verbatim instead of the positional fallback (same defensive stance as
    load_malls; GROVES itself never has this key -- see module docstring)."""
    path = tmp_path / "with_id.jsonl"
    path.write_text(
        '{"id": "custom-7", "NL": "x", "FOL": "P(a)"}\n', encoding="utf-8",
    )
    examples = list(load_groves(path))
    assert examples[0].id == "custom-7"


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict
# ---------------------------------------------------------------------------

def test_groves_dataset_info_registry_has_verified_provenance():
    assert "groves" in DATASET_INFO
    info = DATASET_INFO["groves"]
    assert "CC-BY-NC-4.0" in info["license"]
    assert info["source_url"] == "https://huggingface.co/datasets/fvossel/groves"
    assert info["citation_hint"]


def test_groves_dataset_example_to_dict_is_json_compatible():
    example = next(load_groves(_GROVES_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)          # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "groves:0"
    assert round_tripped["fol_conclusion"] == _EXPECTED_ROWS[0][1]
    assert round_tripped["fol_premises"] == []
    assert isinstance(round_tripped["fol_premises"], list)   # tuple -> list
