"""Tests for the ProverQA adapter (unicode_fol_kit.eval.datasets.proverqa).

The fixture (``tests/fixtures/proverqa_mini.jsonl``) holds 8 REAL, VERBATIM
rows (ids 0-7) copied from ``dev/easy.json`` of
https://huggingface.co/datasets/opendatalab/ProverQA, fetched directly on
2026-08-12 (see proverqa.py's module docstring for the full verification
trail) — unlike the FOLIO/MALLS fixtures, these are genuine dataset rows, not
hand-written synthetic ones, per this adapter's own verification requirement
(the low/zero parse rate documented below is a real, dataset-level finding
that a synthetic fixture could not honestly demonstrate).

Every hand-checked value below was read directly off the fixture file (or
computed by a small, shown-in-the-docstring calculation), never invented.
"""

import json

import pytest

from unicode_fol_kit.eval.datasets import DatasetExample, DATASET_INFO, audit_examples
from unicode_fol_kit.eval.datasets.proverqa import (
    load_proverqa, convert_proverqa_formulas, solve_example,
)

from pathlib import Path

_FIXTURES = Path(__file__).parent / "fixtures"
_PROVERQA_FIXTURE = _FIXTURES / "proverqa_mini.jsonl"


# ---------------------------------------------------------------------------
# Field mapping / id resolution
# ---------------------------------------------------------------------------

def test_load_proverqa_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_proverqa_field_mapping_first_example():
    """Row 1 (fixture line 1, source id 0) mapped field-for-field against the
    raw JSON on that line:

        {"id": 0, "options": ["A) True", "B) False", "C) Uncertain"],
         "answer": "B",
         "question": "Based on the above information, is the following
                       statement true, false, or uncertain? Brecken has
                       never experienced heartbreak.",
         "context": "Brecken has experienced heartbreak. Either Brecken has
                      experienced heartbreak or he has never experienced
                      heartbreak, but not both.",
         "nl2fol": {"Brecken has experienced heartbreak.":
                        "has_experienced_heartbreak(Brecken)",
                    "Either Brecken has experienced heartbreak or he has
                     never experienced heartbreak, but not both.":
                        "has_experienced_heartbreak(Brecken) ⊕ "
                        "has_never_experienced_heartbreak(Brecken)"},
         "conclusion_fol": "has_never_experienced_heartbreak(Brecken)"}

    No "tier" kwarg is passed here, so the id is the untiered form
    "proverqa:0" (see proverqa.py's _resolve_id docstring). convert_fol=False
    pins the RAW pass-through mapping; the default conversion pipeline has
    its own test block below.
    """
    example = next(load_proverqa(_PROVERQA_FIXTURE, convert_fol=False))
    assert example.id == "proverqa:0"
    assert example.nl_premises == (
        "Brecken has experienced heartbreak.",
        "Either Brecken has experienced heartbreak or he has never "
        "experienced heartbreak, but not both.",
    )
    assert example.fol_premises == (
        "has_experienced_heartbreak(Brecken)",
        "has_experienced_heartbreak(Brecken) ⊕ "
        "has_never_experienced_heartbreak(Brecken)",
    )
    assert example.nl_conclusion == (
        "Based on the above information, is the following statement true, "
        "false, or uncertain? Brecken has never experienced heartbreak."
    )
    assert example.fol_conclusion == "has_never_experienced_heartbreak(Brecken)"
    assert example.label == "B"          # verbatim "answer", not resolved text
    assert example.known_bad is False
    assert example.meta["options"] == ["A) True", "B) False", "C) Uncertain"]
    assert example.meta["line_no"] == 0
    assert "tier" not in example.meta    # tier=None -> not recorded at all


def test_load_proverqa_tier_namespaces_the_id():
    """Same fixture, tier='easy' this time: the id gains the tier segment,
    and meta records it — this is what lets a caller load all three upstream
    dev/*.json tiers into one corpus without id collisions (every tier's
    native "id" restarts at 0, verified in the module docstring)."""
    example = next(load_proverqa(_PROVERQA_FIXTURE, tier="easy"))
    assert example.id == "proverqa:easy:0"
    assert example.meta["tier"] == "easy"


def test_load_proverqa_rejects_unknown_tier():
    """tier is validated against the three real upstream tiers; a typo must
    fail loudly, not silently produce a wrongly-namespaced id."""
    with pytest.raises(ValueError):
        list(load_proverqa(_PROVERQA_FIXTURE, tier="expert"))


def test_load_proverqa_known_bad_flag():
    """known_bad_ids flags exactly the matching example, nothing else."""
    examples = list(load_proverqa(_PROVERQA_FIXTURE, known_bad_ids=frozenset({"proverqa:3"})))
    known_bad = {e.id: e.known_bad for e in examples}
    assert known_bad["proverqa:3"] is True
    assert sum(1 for v in known_bad.values() if v) == 1


def test_load_proverqa_answer_letter_indexes_its_own_option():
    """Row 3 (source id 2): answer 'C' at options[2] == 'C) Uncertain' —
    hand-checked directly off the fixture JSON, matching the invariant
    verified across all 1,500 real dev rows (see module docstring)."""
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    third = examples[2]
    assert third.label == "C"
    assert third.meta["options"][2] == "C) Uncertain"


def test_load_proverqa_premises_and_conclusion_pair_up_by_position():
    """Row 2 (source id 1) has 4 nl2fol entries; nl_premises[i] must be the
    NL sentence whose gold FOL is fol_premises[i], read straight off the
    fixture's "nl2fol" object (dict key/value iteration order matches)."""
    examples = list(load_proverqa(_PROVERQA_FIXTURE, convert_fol=False))
    second = examples[1]
    assert len(second.nl_premises) == len(second.fol_premises) == 4
    assert second.nl_premises[0] == "Desmond does not study common plants."
    assert second.fol_premises[0] == "¬study_common_plants(Desmond)"
    assert second.nl_premises[3] == "Desmond studies rare plants."
    assert second.fol_premises[3] == "study_rare_plants(Desmond)"


# ---------------------------------------------------------------------------
# Lazy parsing / the notation-mismatch finding
# ---------------------------------------------------------------------------

def test_proverqa_fol_strings_do_not_parse_under_this_kits_grammar():
    """Hand-verified per the module docstring: ProverQA's gold FOL uses
    snake_case predicates (has_experienced_heartbreak) and Capitalized
    constants (Brecken) -- the opposite convention from this kit's grammar
    (unicode_fol_kit/fol/grammars/terminals.lark: PREDICATE must start
    uppercase with no underscore; NAME/constant must start lowercase with no
    underscore). Row 1's first premise 'has_experienced_heartbreak(Brecken)'
    must therefore fail every dialect api.parse_any tries — with
    convert_fol=False, which is what this raw-notation finding is about."""
    example = next(load_proverqa(_PROVERQA_FIXTURE, convert_fol=False))
    premise_results = example.parse_premises()
    assert len(premise_results) == 2
    assert all(pr.ok is False for pr in premise_results)
    conclusion_result = example.parse_conclusion()
    assert conclusion_result is not None
    assert conclusion_result.ok is False


def test_parse_conclusion_is_none_when_no_conclusion_field():
    """A hand-built example with fol_conclusion=None must short-circuit to
    None rather than calling parse_any on None (which would raise) -- same
    contract as the other adapters in this subpackage (see DatasetExample)."""
    example = DatasetExample(
        id="synthetic:1", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None,
        known_bad=False,
    )
    assert example.parse_conclusion() is None
    assert example.parse_premises() == ()


# ---------------------------------------------------------------------------
# audit_examples over the whole fixture: every row fails to parse
# ---------------------------------------------------------------------------

def test_audit_examples_reports_every_proverqa_example_as_unparseable():
    """Expected value reasoned from proverqa.py's module docstring, not just
    re-asserting whatever the code computes: since NONE of the fixture's
    fol_premises/fol_conclusion strings parse (verified above and across all
    17,342 real dev-set formulas during adapter verification), every report
    must have all_parsed=False. Nothing ever reaches check() (a formula that
    fails to parse `continue`s before check() in audit_examples -- see
    _base.py), so all_checked is vacuously True for every row, and ok is
    False for every row.

    Per-row defect counts are exactly len(fol_premises) + 1 (one
    "unparseable" defect per premise, plus one for the conclusion) --
    computed straight from the fixture's own nl2fol lengths:
    [2, 4, 2, 2, 3, 2, 3, 6] premises -> [3, 5, 3, 3, 4, 3, 4, 7] defects.

    convert_fol=False: this test pins the RAW upstream notation's audit
    outcome; the converted default's all-green audit is asserted separately.
    """
    examples = list(load_proverqa(_PROVERQA_FIXTURE, convert_fol=False))
    report = audit_examples(examples)
    assert len(report) == 8

    assert all(r["all_parsed"] is False for r in report)
    assert all(r["all_checked"] is True for r in report)     # vacuous
    assert all(r["ok"] is False for r in report)

    expected_defect_counts = [3, 5, 3, 3, 4, 3, 4, 7]
    assert [len(r["defects"]) for r in report] == expected_defect_counts

    # Every defect is an "unparseable" one -- no formula ever got far enough
    # to trigger a free_variables/arity_conflict/residual_lambda defect.
    for r in report:
        assert all(d["kind"] == "unparseable" for d in r["defects"])

    # The conclusion's defect is always the last one for a row, index None.
    for r in report:
        conclusion_defects = [d for d in r["defects"] if d["field"] == "conclusion"]
        assert len(conclusion_defects) == 1
        assert conclusion_defects[0]["index"] is None


def test_audit_examples_respects_max_examples():
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    report = audit_examples(examples, max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == ["proverqa:0", "proverqa:1", "proverqa:2"]


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict, malformed-file / missing-field behaviour
# ---------------------------------------------------------------------------

def test_dataset_info_registry_has_verified_provenance_for_proverqa():
    assert "proverqa" in DATASET_INFO
    info = DATASET_INFO["proverqa"]
    assert "UNSPECIFIED" in info["license"]
    assert info["source_url"] == "https://huggingface.co/datasets/opendatalab/ProverQA"
    assert info["citation_hint"]


def test_dataset_example_to_dict_is_json_compatible():
    example = next(load_proverqa(_PROVERQA_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)          # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "proverqa:0"
    assert isinstance(round_tripped["fol_premises"], list)   # tuple -> list


def test_load_proverqa_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_proverqa(_FIXTURES / "does_not_exist.jsonl"))


def test_load_proverqa_malformed_json_line_raises_not_silently_skipped():
    """A dataset file with a broken JSON line must fail loudly (a corrupted
    file, not a per-example data defect audit_examples is meant to find)."""
    bad_path = _FIXTURES / "_tmp_malformed_proverqa.jsonl"
    bad_path.write_text(
        '{"id": 0, "nl2fol": {}, "conclusion_fol": "P(a)", "answer": "A"}\n'
        'not json at all\n',
        encoding="utf-8",
    )
    try:
        with pytest.raises(json.JSONDecodeError):
            list(load_proverqa(bad_path))
    finally:
        bad_path.unlink()


# ---------------------------------------------------------------------------
# The ProverQA dialect grammar: default conversion into kit notation
# ---------------------------------------------------------------------------

def test_default_load_converts_every_fixture_row_into_kit_notation():
    """With the default convert_fol=True, all 8 real rows convert cleanly:
    no fol_conversion_error, every formula parses under api.parse_any, and
    audit_examples flips from 0/8 ok (raw notation, pinned above) to 8/8 ok.
    Hand-checked exemplar (row 1 / source id 0):
    'has_experienced_heartbreak(Brecken)' -> 'HasExperiencedHeartbreak(brecken)'.
    """
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    assert len(examples) == 8
    assert all("fol_conversion_error" not in e.meta for e in examples)

    first = examples[0]
    assert first.fol_premises == (
        "HasExperiencedHeartbreak(brecken)",
        "HasExperiencedHeartbreak(brecken) ⊕ HasNeverExperiencedHeartbreak(brecken)",
    )
    assert first.fol_conclusion == "HasNeverExperiencedHeartbreak(brecken)"
    # The verbatim upstream strings stay fully recoverable in meta.
    assert first.meta["original_fol_premises"] == [
        "has_experienced_heartbreak(Brecken)",
        "has_experienced_heartbreak(Brecken) ⊕ has_never_experienced_heartbreak(Brecken)",
    ]
    assert first.meta["original_fol_conclusion"] == \
        "has_never_experienced_heartbreak(Brecken)"
    assert first.meta["fol_name_mapping"] == {
        "predicates": {
            "has_experienced_heartbreak": "HasExperiencedHeartbreak",
            "has_never_experienced_heartbreak": "HasNeverExperiencedHeartbreak",
        },
        "constants": {"Brecken": "brecken"},
    }

    report = audit_examples(examples)
    assert all(r["ok"] for r in report)


def test_converted_quantified_formula_round_trips():
    """The medium/hard tiers quantify; the dialect grammar must handle the
    prefix form. Hand-conversion: ∀x (dedicated_volunteer(x) →
    improves_lives(x)) -> ∀x (DedicatedVolunteer(x) → ImprovesLives(x)),
    closed, and re-parseable by the kit."""
    from unicode_fol_kit import api

    nodes, mapping = convert_proverqa_formulas(
        ["∀x (dedicated_volunteer(x) → improves_lives(x))"])
    rendered = nodes[0].to_unicode_str()
    assert rendered == "∀x (DedicatedVolunteer(x) → ImprovesLives(x))"
    assert api.parse_any(rendered).ok
    assert mapping["predicates"] == {
        "dedicated_volunteer": "DedicatedVolunteer",
        "improves_lives": "ImprovesLives",
    }


def test_conversion_refuses_predicate_name_collision():
    """Injectivity guard, hand-constructed: 'p_a' and 'pA' both convert to
    'PA' — merging two distinct source predicates would change which
    entailments hold, so the converter must refuse."""
    with pytest.raises(ValueError, match="injective"):
        convert_proverqa_formulas(["p_a(Xx) ∧ pA(Xx)"])


def test_conversion_refuses_constant_that_would_become_a_variable():
    """'A' would downcase to 'a', which the kit grammar lexes as a VARIABLE —
    a silent constant→variable change alters quantification semantics and
    must be refused."""
    with pytest.raises(ValueError, match="VARIABLE"):
        convert_proverqa_formulas(["nice(A)"])


def test_conversion_failure_falls_back_to_verbatim_with_recorded_error():
    """A record whose gold FOL cannot be converted (here: conclusion 'P(a)' —
    'a' lexes as a variable, so the converted formula would have a free
    variable) keeps the verbatim strings and records the reason, instead of
    crashing the load or silently dropping the row."""
    bad_path = _FIXTURES / "_tmp_unconvertible_proverqa.jsonl"
    bad_path.write_text(
        '{"id": 5, "nl2fol": {}, "conclusion_fol": "P(a)", "answer": "A"}\n',
        encoding="utf-8",
    )
    try:
        example = next(load_proverqa(bad_path))
        assert example.fol_conclusion == "P(a)"                # verbatim kept
        assert "fol_conversion_error" in example.meta
        assert "free variable" in example.meta["fol_conversion_error"]
    finally:
        bad_path.unlink()


# ---------------------------------------------------------------------------
# solve_example: end-to-end deciding against the gold answer
# ---------------------------------------------------------------------------

def test_solve_example_reproduces_gold_answers_except_the_defective_row():
    """End-to-end over all 8 converted fixture rows via api.prove.

    Rows 0-6 reproduce their gold answer exactly (hand-checked exemplar,
    row 1/source id 0: premises HEB(b) and HEB(b) ⊕ HNEB(b) entail ¬HNEB(b)
    — from HEB(b), the xor forces HNEB(b) false — so premises ⊨ ¬conclusion
    and the prediction is 'B', matching gold).

    Row 8 (source id 7) is the DOCUMENTED upstream annotation defect (module
    docstring): its rule uses resolves_conflict_peacefully (singular) but its
    conclusion resolves_conflictS_peacefully (plural) — two genuinely
    different predicates, so classically NOTHING about the conclusion
    follows and 'C' is the correct verdict; the gold 'B' presupposes the
    two misspellings denote the same predicate. The honest converter keeps
    them distinct, so the mismatch is expected and pinned here.
    """
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    predictions = {e.id: solve_example(e)["predicted"] for e in examples}
    for example in examples[:7]:
        assert predictions[example.id] == example.label, example.id
    assert examples[7].label == "B"            # gold, presupposing the typo
    assert predictions[examples[7].id] == "C"  # classical verdict, typo kept


def test_solve_example_refuses_unconverted_examples():
    """Raw-notation examples (convert_fol=False) cannot be scored — the
    formulas do not parse under the kit grammar, and solve_example must say
    so rather than silently return 'C' for everything."""
    example = next(load_proverqa(_PROVERQA_FIXTURE, convert_fol=False))
    with pytest.raises(ValueError):
        solve_example(example)


def test_on_indefinite_distinguishes_established_uncertain_from_prover_failure():
    """Fixture id 2 (gold 'C': the premises are about Shepherd/Emanuel, the
    conclusion about Munchkin — genuinely unrelated). With z3 both cascade
    legs are definitively REFUTED, so 'C' is ESTABLISHED and even
    on_indefinite='abstain' labels it. With the resolution backend alone,
    both legs are indefinite (bound_hit — resolution cannot refute), so
    'abstain' yields None and 'raise' raises: a prover that merely gave up
    is not credited with a correct 'Uncertain'."""
    examples = list(load_proverqa(_PROVERQA_FIXTURE))
    uncertain = examples[2]
    assert uncertain.label == "C"

    established = solve_example(uncertain, on_indefinite="abstain")
    assert established["predicted"] == "C"
    assert established["verdict"]["status"] == "refuted"
    assert established["verdict_negated"]["status"] == "refuted"

    abstained = solve_example(uncertain, backends=["resolution"],
                              on_indefinite="abstain")
    assert abstained["predicted"] is None
    assert abstained["verdict"]["status"] == "unknown"

    with pytest.raises(ValueError, match="indefinite"):
        solve_example(uncertain, backends=["resolution"],
                      on_indefinite="raise")

    with pytest.raises(ValueError, match="on_indefinite"):
        solve_example(uncertain, on_indefinite="guess")


def test_load_proverqa_record_missing_nl2fol_degrades_to_empty_premises():
    """A record without "nl2fol" at all (e.g. a hand-trimmed/malformed row)
    must not crash -- it degrades to empty premises, documented behaviour
    matching folio.py's own defensive `.get(...) or ()` pattern, not a raise
    (this is NOT the "malformed JSON" case above; the line IS valid JSON,
    it's just missing an expected key). convert_fol=False keeps the test
    about the missing-key behaviour alone."""
    bad_path = _FIXTURES / "_tmp_no_nl2fol_proverqa.jsonl"
    bad_path.write_text(
        '{"id": 99, "conclusion_fol": "P(a)", "answer": "A", '
        '"options": ["A) True", "B) False", "C) Uncertain"]}\n',
        encoding="utf-8",
    )
    try:
        example = next(load_proverqa(bad_path, convert_fol=False))
        assert example.nl_premises == ()
        assert example.fol_premises == ()
        assert example.fol_conclusion == "P(a)"
        assert example.id == "proverqa:99"
    finally:
        bad_path.unlink()
