"""Tests for the LogicNLI adapter (unicode_fol_kit.eval.datasets.logicnli).

``tests/fixtures/logicnli_mini.jsonl`` is 8 REAL rows built from the
downloaded GitHub original (https://github.com/omnilabNLP/LogicNLI,
``dataset/LogicNLI_sim.zip``, ``dev_language.json``/``dev_logic.json``,
verified 2026-08-12), reshaped into this adapter's own per-example JSONL
schema (see ``logicnli.py``'s module docstring — neither upstream source is
naturally one-JSON-object-per-example). Nothing in the fixture is invented:
every sentence, every ``[subject, attribute, polarity, ...]`` tuple, and
every rule dict is copied verbatim from the real ``dev`` split.

Row layout (hand-picked, not random, so id resolution and story-sharing are
both exercised):

* rows 0-3: story ``"0"``, statements ``"0"``/``"3"``/``"4"``/``"2"`` — one
  per label value (contradiction/entailment/neutral/self_contradiction), all
  four SHARING the same 12 facts + 12 rules (LogicNLI's "one story, several
  statements" shape, the same kind of premise-sharing FOLIO's docstring
  documents for its own story grouping).
* row 4: story ``"1"``, statement ``"0"`` — additionally carries an explicit
  ``"id": "logicnli-dev-custom-7"`` override, to test id precedence.
* rows 5-6: story ``"1"``, statements ``"8"``/``"3"`` — share row 4's
  premises (same story), no id override (story/statement-derived id).
* row 7: story ``"1"`` statement ``"12"``'s premises/hypothesis/label, but
  with ``"story_id"``/``"statement_id"``/``"split"`` deliberately OMITTED
  from the record, to exercise the positional id fallback.

Because this adapter never compiles FOL from LogicNLI's structured symbolic
annotation (see ``logicnli.py``'s module docstring for why), EVERY example's
``fol_premises`` is ``()`` and ``fol_conclusion`` is ``None`` by construction
— there is no "deliberately broken FOL row" here the way the FOLIO/MALLS
fixtures have one, because there is no FOL string in this dataset to break.
``audit_examples`` is accordingly expected to report ``ok=True`` for every
single row, vacuously (nothing to parse or check) — a fact asserted below,
not glossed over.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import (
    DatasetExample,
    DATASET_INFO,
    audit_examples,
    load_logicnli,
)

_FIXTURES = Path(__file__).parent / "fixtures"
_LOGICNLI_FIXTURE = _FIXTURES / "logicnli_mini.jsonl"

# Hand-verified against the downloaded GitHub original (dev_language.json /
# dev_logic.json, stories "0" and "1") independently of logicnli.py's own
# fixture-generation script -- see this file's module docstring for exactly
# which (story, statement) pair each row is.
_EXPECTED_IDS = [
    "logicnli:dev:0:0", "logicnli:dev:0:3", "logicnli:dev:0:4",
    "logicnli:dev:0:2", "logicnli-dev-custom-7", "logicnli:dev:1:8",
    "logicnli:dev:1:3", "logicnli:7",
]
_EXPECTED_HYPOTHESES = [
    "Eli is jittery.", "Patricia is scared.", "Olive is not soft.",
    "Paul is not southern.", "Dan is talkative.", "Rosa is not poised.",
    "Cary is not poised.", "Dan is different.",
]
_EXPECTED_LABELS = [
    "contradiction", "entailment", "neutral", "self_contradiction",
    "contradiction", "entailment", "neutral", "entailment",
]
_EXPECTED_HYPOTHESIS_LOGIC = [
    ["Eli", "jittery", "+", "fact 10"],
    ["Patricia", "scared", "+", "[[fact 2-->6]-->3]"],
    ["Olive", "soft", "-", "none"],
    ["Paul", "southern", "-",
     "[[[fact 2-->6]-->5] + [[[fact 2-->6]-->5]-->10]-->9]|[[[fact 2-->6]-->5]-->6]"],
    ["Dan", "talkative", "+", "[fact 0-->7]"],
    ["Rosa", "poised", "-", "fact 4"],
    ["Cary", "poised", "-", "none"],
    ["Dan", "different", "+", "[[fact 0-->7]-->3]"],
]
_EXPECTED_STORY_IDS = ["0", "0", "0", "0", "1", "1", "1", None]
_EXPECTED_STATEMENT_IDS = ["0", "3", "4", "2", "0", "8", "3", None]


# ---------------------------------------------------------------------------
# Loading and field mapping
# ---------------------------------------------------------------------------

def test_load_logicnli_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_logicnli_field_mapping_every_row():
    """hypothesis_nl/label map onto nl_conclusion/label verbatim; fol_premises
    and fol_conclusion are ALWAYS empty (see module docstring: this adapter
    never compiles FOL from LogicNLI's structured annotation)."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    assert len(examples) == 8
    for i, example in enumerate(examples):
        assert example.id == _EXPECTED_IDS[i]
        assert example.nl_conclusion == _EXPECTED_HYPOTHESES[i]
        assert example.label == _EXPECTED_LABELS[i]
        assert example.fol_premises == ()
        assert example.fol_conclusion is None
        assert example.known_bad is False


def test_load_logicnli_premises_are_facts_then_rules_24_sentences():
    """Rows 0-3 all come from story "0": 12 facts + 12 rules = 24 premise
    sentences, IDENTICAL across all four (same story, different statement) --
    the same "several rows share one premise set" shape FOLIO's own
    docstring documents. Spot-checked at the fact/rule boundary (index 11 is
    the last fact, index 12 the first rule) rather than re-typing all 24."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    for i in range(4):
        assert len(examples[i].nl_premises) == 24
    # All four share the exact same premise tuple (same story "0").
    assert examples[0].nl_premises == examples[1].nl_premises == \
           examples[2].nl_premises == examples[3].nl_premises

    premises = examples[0].nl_premises
    assert premises[0] == "Eli is not soft."             # first fact
    assert premises[11] == "Eli is not poised."           # last fact
    assert premises[12] == (
        "If someone is southern, then he is neither jittery nor soft."
    )                                                      # first rule
    assert premises[23] == (
        "Someone who is not jittery is always both civil and not soft."
    )                                                      # last rule

    # Rows 5-6 share story "1"'s premises instead (different from story "0").
    assert len(examples[5].nl_premises) == 24
    assert examples[5].nl_premises == examples[6].nl_premises
    assert examples[5].nl_premises != examples[0].nl_premises
    assert examples[5].nl_premises[0] == "Adler is angry."


def test_load_logicnli_hypothesis_logic_preserved_verbatim_in_meta():
    """The structured (subject, attribute, polarity, provenance) annotation
    for each hypothesis survives, uninterpreted, in meta -- since it is NOT
    compiled into fol_conclusion (see module docstring)."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    for i, example in enumerate(examples):
        assert example.meta["hypothesis_logic"] == _EXPECTED_HYPOTHESIS_LOGIC[i]


def test_load_logicnli_premises_logic_fact_and_rule_shapes_preserved():
    """meta["premises_logic"] keeps the raw fact 4-tuples and rule dicts,
    same length/order as nl_premises, uninterpreted."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    logic = examples[0].meta["premises_logic"]
    assert len(logic) == 24
    assert logic[0] == ["Eli", "soft", "-", "fact 0"]              # fact
    assert logic[11] == ["Eli", "poised", "-", "fact 11"]           # fact
    assert logic[12] == {                                          # rule
        "p": {"fact": [["all", "southern", "+"]], "conj": "none"},
        "q": {"fact": [["all", "jittery", "-"], ["all", "soft", "-"]],
              "conj": "and"},
        "type": "imp", "reasoning": "AIC", "class": 4,
    }


def test_load_logicnli_story_and_statement_ids_in_meta():
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    for i, example in enumerate(examples):
        assert example.meta["story_id"] == _EXPECTED_STORY_IDS[i]
        assert example.meta["statement_id"] == _EXPECTED_STATEMENT_IDS[i]


# ---------------------------------------------------------------------------
# id resolution
# ---------------------------------------------------------------------------

def test_load_logicnli_ids_story_statement_split_and_positional_fallback():
    """Rows 0-3, 5-6: id built from story_id/statement_id/split. Row 4: an
    explicit "id" key overrides that construction. Row 7: story_id/
    statement_id/split are absent from the record entirely -> falls back to
    the positional id f"logicnli:{line_no}" with line_no=7 (0-based, the
    8th and last line)."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    assert [e.id for e in examples] == _EXPECTED_IDS


def test_load_logicnli_known_bad_flag():
    examples = list(load_logicnli(
        _LOGICNLI_FIXTURE,
        known_bad_ids=frozenset({"logicnli:dev:0:2", "logicnli:7"}),
    ))
    known_bad = {e.id: e.known_bad for e in examples}
    assert known_bad == {
        "logicnli:dev:0:0": False, "logicnli:dev:0:3": False,
        "logicnli:dev:0:4": False, "logicnli:dev:0:2": True,
        "logicnli-dev-custom-7": False, "logicnli:dev:1:8": False,
        "logicnli:dev:1:3": False, "logicnli:7": True,
    }


def test_load_logicnli_known_bad_ids_defaults_to_empty():
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    assert all(e.known_bad is False for e in examples)


# ---------------------------------------------------------------------------
# Lazy parsing -- always vacuous for LogicNLI (no FOL ever compiled)
# ---------------------------------------------------------------------------

def test_logicnli_parse_premises_and_conclusion_are_always_vacuous():
    """fol_premises=() and fol_conclusion=None for every LogicNLI example
    (see module docstring) -> parse_premises() is always the empty tuple and
    parse_conclusion() is always None, never an attempt to call parse_any on
    real content."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    assert len(examples) == 8
    for example in examples:
        assert example.parse_premises() == ()
        assert example.parse_conclusion() is None


# ---------------------------------------------------------------------------
# audit_examples over the fixture
# ---------------------------------------------------------------------------

def test_audit_examples_reports_all_ok_vacuously_for_logicnli_fixture():
    """Every row's fol_premises/fol_conclusion is empty/None by construction,
    so all_parsed and all_checked are vacuously True for all 8 rows, with no
    defects -- NOT evidence the underlying LogicNLI annotation is clean, only
    that this adapter never gives audit_examples anything to check (see
    module docstring's 'What this adapter deliberately does NOT do')."""
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 8
    for entry, example in zip(report, examples):
        assert entry["id"] == example.id
        assert entry["known_bad"] is False
        assert entry["all_parsed"] is True
        assert entry["all_checked"] is True
        assert entry["ok"] is True
        assert entry["defects"] == []


def test_audit_examples_respects_max_examples_on_logicnli():
    examples = list(load_logicnli(_LOGICNLI_FIXTURE))
    report = audit_examples(examples, max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == _EXPECTED_IDS[:3]


# ---------------------------------------------------------------------------
# Error / edge cases
# ---------------------------------------------------------------------------

def test_load_logicnli_missing_label_yields_none_not_exception(tmp_path):
    """A record missing "label" gets label=None rather than raising -- the
    same documented "missing key -> default, not exception" behaviour
    load_folio uses (only a structurally malformed FILE, tested below, is a
    loud failure)."""
    path = tmp_path / "missing_label.jsonl"
    path.write_text(
        json.dumps({"premises_nl": ["P."], "hypothesis_nl": "Q."}) + "\n",
        encoding="utf-8",
    )
    examples = list(load_logicnli(path))
    assert len(examples) == 1
    assert examples[0].label is None
    assert examples[0].nl_premises == ("P.",)
    assert examples[0].nl_conclusion == "Q."


def test_load_logicnli_missing_hypothesis_and_premises_yield_defaults(tmp_path):
    path = tmp_path / "missing_fields.jsonl"
    path.write_text(json.dumps({"label": "neutral"}) + "\n", encoding="utf-8")
    examples = list(load_logicnli(path))
    assert len(examples) == 1
    assert examples[0].nl_conclusion is None
    assert examples[0].nl_premises == ()
    assert examples[0].label == "neutral"
    assert examples[0].id == "logicnli:0"          # positional fallback


def test_load_logicnli_honours_opportunistic_id_field(tmp_path):
    path = tmp_path / "with_id.jsonl"
    path.write_text(
        json.dumps({"id": "custom-42", "story_id": "0", "statement_id": "1",
                    "hypothesis_nl": "x", "label": "neutral"}) + "\n",
        encoding="utf-8",
    )
    examples = list(load_logicnli(path))
    # The explicit "id" wins even though story_id/statement_id are ALSO
    # present (which would otherwise construct "logicnli:0:1").
    assert examples[0].id == "custom-42"


def test_load_logicnli_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_logicnli(_FIXTURES / "does_not_exist_logicnli.jsonl"))


def test_load_logicnli_malformed_json_line_raises_not_silently_skipped(tmp_path):
    """A dataset file with a broken JSON line must fail loudly (a corrupted
    file is a bug, not a per-example defect audit_examples characterises)."""
    bad_path = tmp_path / "_tmp_malformed_logicnli.jsonl"
    bad_path.write_text(
        '{"hypothesis_nl": "ok", "label": "neutral"}\nnot json at all\n',
        encoding="utf-8",
    )
    with pytest.raises(json.JSONDecodeError):
        list(load_logicnli(bad_path))


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict
# ---------------------------------------------------------------------------

def test_logicnli_dataset_info_registry_has_verified_provenance():
    assert "logicnli" in DATASET_INFO
    info = DATASET_INFO["logicnli"]
    assert "Not stated" in info["license"]
    assert info["source_url"] == "https://github.com/omnilabNLP/LogicNLI"
    assert "LogicNLI" in info["citation_hint"]
    assert "EMNLP" in info["citation_hint"]


def test_logicnli_dataset_example_to_dict_is_json_compatible():
    example = next(load_logicnli(_LOGICNLI_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)          # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "logicnli:dev:0:0"
    assert round_tripped["fol_premises"] == []
    assert round_tripped["fol_conclusion"] is None
    assert round_tripped["label"] == "contradiction"
