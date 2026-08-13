"""Tests for the WillowNLtoFOL adapter (unicode_fol_kit.eval.datasets.willow).

Fixture provenance
-------------------
``tests/fixtures/willow_mini.jsonl`` is NOT synthetic (unlike
``folio_mini.jsonl``/``malls_mini.jsonl``, which are hand-written to avoid
share-alike/non-commercial license entanglement) — it is 8 REAL rows copied
verbatim from the ``train`` split of https://huggingface.co/datasets/iedeveci/WillowNLtoFOL,
fetched via the Hugging Face datasets-server ``rows`` API on 2026-08-12. This
is permitted here (and not for FOLIO/MALLS) because WillowNLtoFOL's own card
is verified **CC-BY-4.0** (attribution only, redistribution permitted) — see
``unicode_fol_kit/eval/datasets/willow.py``'s module docstring for the full
verification, including a flagged discrepancy with a different, related
dataset card that claims a more restrictive license for what may be an
earlier state of this same data.

The 8 rows (source ``row_idx`` noted per line) were deliberately chosen, by
running the REAL 16014-row ``train`` split through
``unicode_fol_kit.api.parse_any``/``check`` (a stratified 2100-row sample,
documented in ``willow.py``'s module docstring), to cover every defect class
that sample turned up:

* Lines 1-5 (``row_idx`` 0, 4, 8, 29, 31): parse AND pass ``check()`` cleanly.
* Line 6 (``row_idx`` 148): ``"∀y (Bird(y) ∧ Predator(y) ↔ (Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)))"``
  FAILS TO PARSE — ``Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)`` mixes ∧/∨ at the
  same nesting depth without disambiguating parentheses, which this kit's
  ``fol`` grammar deliberately refuses to guess a precedence for (the
  dominant real failure mode found in the sample).
* Line 7 (``row_idx`` 1554): ``"∀x (Device(x) → (Android(x) ∨ iOS(x)))"``
  FAILS TO PARSE — ``iOS`` starts with a lowercase letter, so this kit's
  ``fol`` grammar (predicate names match ``[A-Z][a-zA-Z0-9]*``) parses it as
  a TERM position, not a predicate, and the formula is left incomplete.
* Line 8 (``row_idx`` 15947): ``"∃x (Chef(x) ∧ ∃y (Cook(y) ∧ ∀z (Meal(z) ∧ CookedBy(z, y) → Cook(x, z))))"``
  PARSES FINE but fails ``check()`` — the predicate ``Cook`` is used at two
  different arities in the same formula (``Cook(y)`` unary, ``Cook(x, z)``
  binary), a genuine annotation defect in the source data, reported as an
  ``arity_conflict``.

Every assertion below was hand-verified by reading the formula directly (see
comments), not by trusting whatever the code under test happens to compute.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import DatasetExample, DATASET_INFO, audit_examples
from unicode_fol_kit.eval.datasets.willow import load_willow

_FIXTURES = Path(__file__).parent / "fixtures"
_WILLOW_FIXTURE = _FIXTURES / "willow_mini.jsonl"


# ---------------------------------------------------------------------------
# Field mapping and id resolution
# ---------------------------------------------------------------------------

def test_load_willow_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_willow(_WILLOW_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_willow_field_mapping_first_example():
    """NL_sentence/FOL_expression map onto nl_conclusion/fol_conclusion (the
    translation-pair convention shared with MALLS); premises stay empty and
    there is no entailment label, because WillowNLtoFOL has no such structure
    (verified against the primary source's schema, see willow.py)."""
    example = next(load_willow(_WILLOW_FIXTURE))
    assert example.id == "willow:0"
    assert example.nl_premises == ()
    assert example.fol_premises == ()
    assert example.nl_conclusion == "A baby is playing with a toy in the playroom."
    assert example.fol_conclusion == "∃x ∃y (Baby(x) ∧ Toy(y) ∧ Playing(x, y) ∧ InThePlayroom(x))"
    assert example.label is None
    assert example.known_bad is False


def test_load_willow_positional_ids_for_every_row():
    """WillowNLtoFOL has no native id field at all (verified schema has only
    NL_sentence/FOL_expression) -> every row falls back to the positional
    f"willow:{line_no}" id, 0-based, in file order."""
    examples = list(load_willow(_WILLOW_FIXTURE))
    assert [e.id for e in examples] == [f"willow:{i}" for i in range(8)]


def test_load_willow_known_bad_flag():
    """known_bad_ids flags exactly the matching example, nothing else."""
    examples = list(load_willow(_WILLOW_FIXTURE, known_bad_ids=frozenset({"willow:7"})))
    known_bad = {e.id: e.known_bad for e in examples}
    expected = {f"willow:{i}": False for i in range(8)}
    expected["willow:7"] = True
    assert known_bad == expected


# ---------------------------------------------------------------------------
# Lazy parsing
# ---------------------------------------------------------------------------

def test_willow_parse_premises_is_always_empty():
    """No premise/conclusion structure exists in the source -> parse_premises()
    is the empty tuple for every example, never called with anything to parse."""
    for example in load_willow(_WILLOW_FIXTURE):
        assert example.parse_premises() == ()


def test_willow_parse_conclusion_on_good_example():
    """Line 1 (row_idx 0) is a well-formed translation: the conclusion parses.
    Hand-check: '∃x ∃y (Baby(x) ∧ Toy(y) ∧ Playing(x, y) ∧ InThePlayroom(x))'
    binds both x and y under the leading existentials, Playing/2 is the only
    binary predicate and it is used consistently -> parses and is closed."""
    example = next(load_willow(_WILLOW_FIXTURE))
    result = example.parse_conclusion()
    assert result is not None
    assert result.ok is True
    assert result.formula is not None


def test_willow_parse_conclusion_mixed_connective_row_fails_to_parse():
    """Line 6 (row_idx 148): 'Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)' mixes ∧ and
    ∨ at the same depth with no parentheses to disambiguate -> this kit's fol
    grammar raises SYNTAX_ERROR (it does not guess a precedence), so
    ParseResult.ok is False for every dialect parse_any tries.
    convert_fol=False: this pins the RAW notation finding; the repair-dialect
    default has its own test block below."""
    examples = list(load_willow(_WILLOW_FIXTURE, convert_fol=False))
    row = examples[5]
    assert row.id == "willow:5"
    result = row.parse_conclusion()
    assert result is not None
    assert result.ok is False


def test_willow_parse_conclusion_lowercase_predicate_row_fails_to_parse():
    """Line 7 (row_idx 1554): 'iOS(x)' starts with a lowercase letter, so this
    kit's fol grammar (predicate names match [A-Z][a-zA-Z0-9]*) parses 'iOS'
    as a term head, not a predicate -> the formula is left incomplete and
    ParseResult.ok is False. convert_fol=False pins the raw finding."""
    examples = list(load_willow(_WILLOW_FIXTURE, convert_fol=False))
    row = examples[6]
    assert row.id == "willow:6"
    result = row.parse_conclusion()
    assert result is not None
    assert result.ok is False


def test_willow_parse_conclusion_arity_conflict_row_parses_but_fails_check():
    """Line 8 (row_idx 15947): 'Cook' appears as both Cook(y) (unary) and
    Cook(x, z) (binary) in the same formula -> it PARSES (syntactically
    well-formed) but api.check() reports an arity_conflict for 'Cook' with
    arities [1, 2]. This is the exact "parses but is ill-formed" distinction
    audit_examples' all_parsed vs all_checked must preserve (mirrors the
    FOLIO fixture's free-variable row in test_datasets.py)."""
    examples = list(load_willow(_WILLOW_FIXTURE))
    row = examples[7]
    assert row.id == "willow:7"
    result = row.parse_conclusion()
    assert result is not None
    assert result.ok is True

    from unicode_fol_kit import api
    checked = api.check(result.formula)
    assert checked.ok is False
    assert checked.arity_consistent is False
    assert checked.arity_conflicts == (
        {"namespace": "pred", "symbol": "Cook", "arities": [1, 2]},
    )
    assert checked.is_closed is True   # x, y, z are all bound -- not the defect here


# ---------------------------------------------------------------------------
# audit_examples finds exactly the three real defects
# ---------------------------------------------------------------------------

def test_audit_examples_finds_exactly_the_three_broken_willow_rows():
    """convert_fol=False — the raw-notation audit outcome; the repair-dialect
    default drops the two unparseable rows to leave ONLY the genuine Cook
    arity defect (asserted in the repair test block below)."""
    examples = list(load_willow(_WILLOW_FIXTURE, convert_fol=False))
    report = audit_examples(examples)
    assert len(report) == 8

    not_ok = [r for r in report if not r["ok"]]
    assert [r["id"] for r in not_ok] == ["willow:5", "willow:6", "willow:7"]

    unparseable_148, unparseable_1554, arity_15947 = not_ok

    # Both unparseable rows: never reached check() -> all_checked is vacuously
    # True (nothing parsed to run check() on), all_parsed is False.
    for r in (unparseable_148, unparseable_1554):
        assert r["all_parsed"] is False
        assert r["all_checked"] is True
        assert len(r["defects"]) == 1
        defect = r["defects"][0]
        assert defect["kind"] == "unparseable"
        assert defect["field"] == "conclusion"
        assert defect["index"] is None

    # The arity-conflict row: DID parse, failed check().
    assert arity_15947["all_parsed"] is True
    assert arity_15947["all_checked"] is False
    assert arity_15947["defects"] == [{
        "kind": "arity_conflict", "field": "conclusion", "index": None,
        "detail": [{"namespace": "pred", "symbol": "Cook", "arities": [1, 2]}],
    }]

    good = [r for r in report if r["ok"]]
    assert len(good) == 5
    assert all(r["all_parsed"] and r["all_checked"] and not r["defects"] for r in good)


def test_audit_examples_respects_max_examples_on_willow():
    """max_examples=3 must stop after the first three (all clean), not reach
    any of the three broken rows at the end of the fixture."""
    examples = list(load_willow(_WILLOW_FIXTURE))
    report = audit_examples(examples, max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == ["willow:0", "willow:1", "willow:2"]
    assert all(r["ok"] for r in report)


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict, malformed-file behaviour
# ---------------------------------------------------------------------------

def test_dataset_info_registry_has_verified_provenance_for_willow():
    assert "willow" in DATASET_INFO
    info = DATASET_INFO["willow"]
    assert "CC-BY-4.0" in info["license"]
    assert info["source_url"] == "https://huggingface.co/datasets/iedeveci/WillowNLtoFOL"
    assert info["citation_hint"]


def test_dataset_example_to_dict_is_json_compatible():
    example = next(load_willow(_WILLOW_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)          # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "willow:0"
    assert round_tripped["fol_conclusion"] == "∃x ∃y (Baby(x) ∧ Toy(y) ∧ Playing(x, y) ∧ InThePlayroom(x))"
    assert round_tripped["nl_premises"] == []
    assert isinstance(round_tripped["nl_premises"], list)   # tuple -> list


def test_load_willow_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_willow(_FIXTURES / "does_not_exist.jsonl"))


def test_load_willow_malformed_json_line_raises_not_silently_skipped():
    """A dataset file with a broken JSON line must fail loudly (a corrupted
    file is a loader bug to surface, not a per-example defect for
    audit_examples to characterise)."""
    bad_path = _FIXTURES / "_tmp_malformed_willow.jsonl"
    bad_path.write_text(
        '{"NL_sentence": "ok", "FOL_expression": "P(a)"}\nnot json at all\n',
        encoding="utf-8",
    )
    try:
        with pytest.raises(json.JSONDecodeError):
            list(load_willow(bad_path))
    finally:
        bad_path.unlink()


# ---------------------------------------------------------------------------
# The repair dialect grammar: default conversion of the kit-refused tail
# ---------------------------------------------------------------------------

def test_default_load_repairs_the_two_unparseable_rows_only():
    """With the default convert_fol=True, the ~98.8% that already parse stay
    byte-for-byte verbatim (no meta additions), and ONLY the two kit-refused
    rows are repaired:

    - willow:5 (row_idx 148) gets the NLTK-precedence reading — hand-derived:
      ↔ binds loosest, ∧ tighter than ∨, so the unparenthesised
      'Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)' clause becomes
      Or(Hunt(y), And(EatMeat(y), ¬EatSeeds(y))) — exactly the reading
      nltk.sem.logic (the dataset's own filter) assigns.
    - willow:6 (row_idx 1554) renames the out-of-class predicate iOS → IOS,
      recorded in the mapping.
    - willow:7 (the Cook arity defect) PARSES already, so it is untouched —
      an arity defect is data, not notation, and stays visible to audit.
    """
    from unicode_fol_kit import api

    raw = list(load_willow(_WILLOW_FIXTURE, convert_fol=False))
    examples = list(load_willow(_WILLOW_FIXTURE))
    assert len(examples) == 8

    for pos in (0, 1, 2, 3, 4, 7):
        assert examples[pos].fol_conclusion == raw[pos].fol_conclusion
        assert "original_fol_conclusion" not in examples[pos].meta
        assert "fol_conversion_error" not in examples[pos].meta

    repaired_prec = examples[5]
    assert repaired_prec.meta["original_fol_conclusion"] == raw[5].fol_conclusion
    assert repaired_prec.fol_conclusion == (
        "∀y (Bird(y) ∧ Predator(y) ↔ Hunt(y) ∨ (EatMeat(y) ∧ ¬EatSeeds(y)))")
    assert repaired_prec.meta["fol_name_mapping"] == {
        "predicates": {}, "terms": {}}
    assert api.parse_any(repaired_prec.fol_conclusion).ok

    repaired_name = examples[6]
    assert repaired_name.meta["original_fol_conclusion"] == raw[6].fol_conclusion
    assert repaired_name.fol_conclusion == "∀x (Device(x) → Android(x) ∨ IOS(x))"
    assert repaired_name.meta["fol_name_mapping"] == {
        "predicates": {"iOS": "IOS"}, "terms": {}}
    assert api.parse_any(repaired_name.fol_conclusion).ok


def test_default_audit_leaves_only_the_genuine_arity_defect():
    """After repair, audit_examples must flag exactly willow:7 (Cook at two
    arities — a data defect no notation repair may hide)."""
    examples = list(load_willow(_WILLOW_FIXTURE))
    report = audit_examples(examples)
    not_ok = [r["id"] for r in report if not r["ok"]]
    assert not_ok == ["willow:7"]


def test_repair_willow_formula_transliterates_accented_predicates():
    """The other real naming-failure class (row_idx 15071's 'Café'): NFKD
    folds é → e, first letter is already uppercase, result parses."""
    from unicode_fol_kit import api
    from unicode_fol_kit.eval.datasets.willow import repair_willow_formula

    node, mapping = repair_willow_formula("∃y (Café(y) ∧ Nice(y))")
    rendered = node.to_unicode_str()
    assert rendered == "∃y (Cafe(y) ∧ Nice(y))"
    assert mapping == {"predicates": {"Café": "Cafe"}, "terms": {}}
    assert api.parse_any(rendered).ok


def test_repair_willow_formula_refuses_name_collision():
    """Injectivity guard: a formula using BOTH 'Café' and 'Cafe' as
    predicates cannot be repaired — folding é→e would merge two distinct
    source predicates."""
    from unicode_fol_kit.eval.datasets.willow import repair_willow_formula

    with pytest.raises(ValueError, match="injective"):
        repair_willow_formula("∃y (Café(y) ∧ Cafe(y))")


def test_repair_willow_formula_refuses_free_variables():
    """A repaired formula must be closed — the repair grammar's tight
    quantifier binding must never silently produce an open formula."""
    from unicode_fol_kit.eval.datasets.willow import repair_willow_formula

    with pytest.raises(ValueError, match="free variable"):
        repair_willow_formula("Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)")


def test_unrepairable_row_keeps_verbatim_string_and_records_the_error():
    """A formula neither the kit grammar nor the repair dialect can read
    keeps its verbatim string plus a recorded fol_conversion_error — the
    load never crashes and never silently drops a row."""
    bad_path = _FIXTURES / "_tmp_unrepairable_willow.jsonl"
    bad_path.write_text(
        '{"NL_sentence": "Broken.", "FOL_expression": "∀x (Foo(x) →"}\n',
        encoding="utf-8",
    )
    try:
        example = next(load_willow(bad_path))
        assert example.fol_conclusion == "∀x (Foo(x) →"
        assert "fol_conversion_error" in example.meta
    finally:
        bad_path.unlink()
