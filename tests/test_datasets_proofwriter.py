"""Tests for the ProofWriter adapter (unicode_fol_kit.eval.datasets.proofwriter).

``tests/fixtures/proofwriter_mini.jsonl`` mixes two things, distinguished by
provenance (see ``proofwriter.py``'s module docstring for how the schema
below was verified):

* Rows 0-7 are 8 REAL rows copied verbatim from the ``train`` split of
  https://huggingface.co/datasets/tasksource/proofwriter (verified
  2026-08-12 via the Hugging Face datasets-server ``/first-rows`` API), at
  that split's row indices 20, 21, 22, 23, 28, 29, 30, 31 in that order —
  rows 20-23 all share ONE theory (about Anne/Dave) with four different
  questions against it (covering all three ``answer`` values); rows 28-31
  share a SECOND theory (about the cat/cow/mouse) the same way. This
  deliberately exercises the documented "one theory id, several question
  rows" shape (see "Id resolution" in the module docstring) with two
  independent theories, not just one.
* Row 8 is SYNTHETIC (hand-written for this test, not from the source) —
  ``{"question": "The unicorn is magical.", "config": "depth-0"}`` — missing
  every field except ``question``/``config``, to exercise the documented
  "missing key -> None/()/empty default" behaviour rather than a broken-FOL
  defect path (ProofWriter carries no FOL to break in the first place — see
  the module docstring's "Honesty" section on why ``audit_examples`` is
  vacuous for this dataset).

The two real theories' sentence counts were hand-checked against
``NFact + NRule`` (see ``test_split_theory_sentences_matches_nfact_plus_nrule``
below) rather than just re-asserting whatever ``_split_theory_sentences``
happens to compute.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import (
    DatasetExample,
    DATASET_INFO,
    audit_examples,
    load_proofwriter,
)
from unicode_fol_kit.eval.datasets.proofwriter import _split_theory_sentences

_FIXTURES = Path(__file__).parent / "fixtures"
_PROOFWRITER_FIXTURE = _FIXTURES / "proofwriter_mini.jsonl"

_ANNE_DAVE_THEORY = (
    "Anne is smart. Dave is round. If someone is cold then they are blue. "
    "If someone is round and not cold then they are smart."
)
_ANNE_DAVE_SENTENCES = (
    "Anne is smart.",
    "Dave is round.",
    "If someone is cold then they are blue.",
    "If someone is round and not cold then they are smart.",
)
_CAT_COW_THEORY = (
    "The cat is not green. The cow likes the mouse. The mouse eats the cat. "
    "If someone needs the cow and the cow does not eat the cat then the cow "
    "does not need the cat."
)
_CAT_COW_SENTENCES = (
    "The cat is not green.",
    "The cow likes the mouse.",
    "The mouse eats the cat.",
    "If someone needs the cow and the cow does not eat the cat then the cow "
    "does not need the cat.",
)


# ---------------------------------------------------------------------------
# Loading and field mapping
# ---------------------------------------------------------------------------

def test_load_proofwriter_yields_one_example_per_line():
    """9 non-blank JSONL lines (8 real + 1 synthetic broken) -> 9 examples."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert len(examples) == 9
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_proofwriter_field_mapping_first_row():
    """Row 0: Anne/Dave theory, question 'Dave is round.', answer True."""
    example = next(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert example.id == "proofwriter:0"
    assert example.nl_premises == _ANNE_DAVE_SENTENCES
    assert example.fol_premises == ()
    assert example.nl_conclusion == "Dave is round."
    assert example.fol_conclusion is None
    assert example.label == "True"
    assert example.known_bad is False
    assert example.meta["theory_id"] == "AttNeg-OWA-D0-1778"
    assert example.meta["theory"] == _ANNE_DAVE_THEORY   # raw string preserved
    assert example.meta["maxD"] == 0
    assert example.meta["NFact"] == 2
    assert example.meta["NRule"] == 2
    assert example.meta["QDep"] == 0
    assert example.meta["QLen"] == 1.0
    assert example.meta["config"] == "depth-0"
    assert example.meta["line_no"] == 0


def test_load_proofwriter_field_mapping_all_real_rows():
    """All 8 real rows: nl_conclusion/label match the source verbatim, and
    both real theories map onto the SAME split sentences across every row
    that shares them (rows 0-3 share the Anne/Dave theory, rows 4-7 share
    the cat/cow/mouse theory)."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    expected = [
        ("Dave is round.", "True", _ANNE_DAVE_SENTENCES),
        ("Anne is not smart.", "False", _ANNE_DAVE_SENTENCES),
        ("Anne is not blue.", "Unknown", _ANNE_DAVE_SENTENCES),
        ("Anne is green.", "Unknown", _ANNE_DAVE_SENTENCES),
        ("The cow likes the mouse.", "True", _CAT_COW_SENTENCES),
        ("The cow does not like the mouse.", "False", _CAT_COW_SENTENCES),
        ("The mouse does not need the mouse.", "Unknown", _CAT_COW_SENTENCES),
        ("The cat needs the cat.", "Unknown", _CAT_COW_SENTENCES),
    ]
    for example, (question, answer, sentences) in zip(examples[:8], expected):
        assert example.nl_conclusion == question
        assert example.label == answer
        assert example.nl_premises == sentences
        assert example.fol_premises == ()
        assert example.fol_conclusion is None


def test_load_proofwriter_qlen_null_iff_answer_unknown_in_fixture():
    """Observed correlation in the fetched sample (see module docstring):
    QLen is null (-> None) exactly on the Unknown-labelled rows, 1.0 on the
    True/False-labelled ones. Hand-checked against the fixture content."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    for example in examples[:8]:
        if example.label == "Unknown":
            assert example.meta["QLen"] is None
        else:
            assert example.meta["QLen"] == 1.0


def test_load_proofwriter_theory_id_repeats_across_grouped_questions():
    """Rows 0-3 all came from the SAME generated theory upstream (id
    'AttNeg-OWA-D0-1778') and rows 4-7 from a second, different theory ('id'
    'RelNeg-OWA-D0-3762') -- meta['theory_id'] must preserve that grouping
    verbatim even though example.id itself is positional/unique per row."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert [e.meta["theory_id"] for e in examples[:4]] == ["AttNeg-OWA-D0-1778"] * 4
    assert [e.meta["theory_id"] for e in examples[4:8]] == ["RelNeg-OWA-D0-3762"] * 4


# ---------------------------------------------------------------------------
# Id resolution: ALWAYS positional (never the source "id", which repeats)
# ---------------------------------------------------------------------------

def test_load_proofwriter_ids_are_always_positional():
    """Unlike FOLIO/MALLS, this loader NEVER honours a record's own 'id'
    field for example.id (it is a non-unique theory id -- see module
    docstring's "Id resolution") -- every row, real or synthetic, gets the
    positional f"proofwriter:{line_no}" form unconditionally."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert [e.id for e in examples] == [f"proofwriter:{i}" for i in range(9)]


# ---------------------------------------------------------------------------
# known_bad_ids mechanic
# ---------------------------------------------------------------------------

def test_load_proofwriter_known_bad_flag():
    examples = list(load_proofwriter(
        _PROOFWRITER_FIXTURE, known_bad_ids=frozenset({"proofwriter:2", "proofwriter:8"}),
    ))
    known_bad = {e.id: e.known_bad for e in examples}
    assert known_bad["proofwriter:2"] is True
    assert known_bad["proofwriter:8"] is True
    assert sum(known_bad.values()) == 2


def test_load_proofwriter_known_bad_ids_defaults_to_empty():
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert all(e.known_bad is False for e in examples)


# ---------------------------------------------------------------------------
# _split_theory_sentences: the local heuristic, hand-checked directly
# ---------------------------------------------------------------------------

def test_split_theory_sentences_matches_nfact_plus_nrule():
    """The split's sentence COUNT must equal NFact + NRule for both real
    fixture theories -- hand-counted: Anne/Dave has NFact=2, NRule=2 (4
    sentences); cat/cow/mouse has NFact=3, NRule=1 (4 sentences)."""
    assert len(_split_theory_sentences(_ANNE_DAVE_THEORY)) == 2 + 2
    assert _split_theory_sentences(_ANNE_DAVE_THEORY) == _ANNE_DAVE_SENTENCES
    assert len(_split_theory_sentences(_CAT_COW_THEORY)) == 3 + 1
    assert _split_theory_sentences(_CAT_COW_THEORY) == _CAT_COW_SENTENCES


def test_split_theory_sentences_single_sentence_no_split_needed():
    assert _split_theory_sentences("Anne is smart.") == ("Anne is smart.",)


def test_split_theory_sentences_none_or_empty_yields_empty_tuple():
    assert _split_theory_sentences(None) == ()
    assert _split_theory_sentences("") == ()


# ---------------------------------------------------------------------------
# Lazy parsing: fol_premises/fol_conclusion are ALWAYS empty -- ProofWriter
# has no FOL gold annotation (see module docstring's "Honesty" section).
# ---------------------------------------------------------------------------

def test_proofwriter_parse_premises_and_conclusion_are_always_trivially_empty():
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    assert len(examples) == 9
    for example in examples:
        assert example.parse_premises() == ()
        assert example.parse_conclusion() is None


# ---------------------------------------------------------------------------
# audit_examples: VACUOUS ok=True for every row (nothing FOL to audit)
# ---------------------------------------------------------------------------

def test_audit_examples_is_vacuously_ok_for_every_proofwriter_row():
    """Because fol_premises is always () and fol_conclusion is always None,
    audit_examples has nothing to parse or check for ANY row -- including
    the synthetic broken row 8, which is 'broken' only in its NL/meta
    fields, not in any FOL string (there is none). This is the exact
    'audit_examples is not a meaningful signal here' point flagged in the
    module docstring's Honesty section, verified directly."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 9
    for entry in report:
        assert entry["all_parsed"] is True
        assert entry["all_checked"] is True
        assert entry["ok"] is True
        assert entry["defects"] == []


def test_audit_examples_respects_max_examples_on_proofwriter():
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    report = audit_examples(examples, max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == ["proofwriter:0", "proofwriter:1", "proofwriter:2"]


# ---------------------------------------------------------------------------
# Error / edge cases
# ---------------------------------------------------------------------------

def test_load_proofwriter_synthetic_broken_row_missing_fields_documented_behaviour():
    """Row 8 ({"question": ..., "config": ...}) is missing 'id', 'theory',
    'answer', 'maxD', 'NFact', 'NRule', 'QDep', 'QLen', 'allProofs' -- every
    missing field must map to its documented None/()/absent-key default,
    never raise."""
    examples = list(load_proofwriter(_PROOFWRITER_FIXTURE))
    broken = examples[8]
    assert broken.id == "proofwriter:8"
    assert broken.nl_premises == ()             # no "theory" -> no sentences
    assert broken.fol_premises == ()
    assert broken.nl_conclusion == "The unicorn is magical."
    assert broken.fol_conclusion is None
    assert broken.label is None                  # no "answer" field at all
    assert broken.meta["theory_id"] is None       # no "id" field at all
    assert broken.meta["config"] == "depth-0"
    assert "maxD" not in broken.meta              # never defaulted into meta
    assert "theory" not in broken.meta            # was never present to keep


def test_load_proofwriter_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_proofwriter(_FIXTURES / "does_not_exist_proofwriter.jsonl"))


def test_load_proofwriter_malformed_json_line_raises_not_silently_skipped(tmp_path):
    """A dataset file with a broken JSON line must fail loudly (a corrupted
    file is a bug, not a per-example defect audit_examples characterises)."""
    bad_path = tmp_path / "_tmp_malformed_proofwriter.jsonl"
    bad_path.write_text(
        '{"theory": "A is B.", "question": "A is B.", "answer": "True"}\n'
        'not json at all\n',
        encoding="utf-8",
    )
    with pytest.raises(json.JSONDecodeError):
        list(load_proofwriter(bad_path))


# ---------------------------------------------------------------------------
# Cross-cutting: DATASET_INFO, to_dict
# ---------------------------------------------------------------------------

def test_proofwriter_dataset_info_registry_has_verified_provenance():
    assert "proofwriter" in DATASET_INFO
    info = DATASET_INFO["proofwriter"]
    assert "UNVERIFIED" in info["license"]
    assert info["source_url"] == "https://huggingface.co/datasets/tasksource/proofwriter"
    assert "Tafjord" in info["citation_hint"]
    assert "2012.13048" in info["citation_hint"]


def test_proofwriter_dataset_example_to_dict_is_json_compatible():
    example = next(load_proofwriter(_PROOFWRITER_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)          # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "proofwriter:0"
    assert round_tripped["nl_premises"] == list(_ANNE_DAVE_SENTENCES)
    assert round_tripped["fol_premises"] == []
    assert isinstance(round_tripped["fol_premises"], list)   # tuple -> list
    assert round_tripped["label"] == "True"


# ---------------------------------------------------------------------------
# Structured OWA route: deterministic FOL generation from the triple/rule
# representations (fixture: tests/fixtures/proofwriter_owa_mini.jsonl — 2 REAL
# rows fetched verbatim from hitachi-nlp/proofwriter_processed_OWA depth-2
# train on 2026-08-12: AttNoneg-OWA-D2-1960 [attribute theory, 12 questions]
# and RelNoneg-OWA-D2-471 [relational theory, 12 questions])
# ---------------------------------------------------------------------------

from unicode_fol_kit.eval.datasets.proofwriter import (   # noqa: E402
    load_proofwriter_structured, parse_proofwriter_representation,
    solve_structured_example,
)

_OWA_FIXTURE = _FIXTURES / "proofwriter_owa_mini.jsonl"


def test_representation_attribute_fact_hand_converted():
    """("Anne" "is" "white" "+"): the RuleTaker attribute reading is the
    unary atom White(anne) — predicate = capitalised attribute, entity in
    kit constant casing."""
    node = parse_proofwriter_representation('("Anne" "is" "white" "+")')
    assert node.to_unicode_str() == "White(anne)"


def test_representation_negative_polarity_hand_converted():
    """("Charlie" "is" "cold" "-"): polarity '-' is negation."""
    node = parse_proofwriter_representation('("Charlie" "is" "cold" "-")')
    assert node.to_unicode_str() == "¬Cold(charlie)"


def test_representation_rule_with_placeholder_hand_converted():
    """The 'something' placeholder is a universally quantified variable:
    ((("something" "is" "young" "+")) -> ("something" "is" "white" "+"))
    is exactly ∀x (Young(x) → White(x))."""
    node = parse_proofwriter_representation(
        '((("something" "is" "young" "+")) -> ("something" "is" "white" "+"))')
    assert node.to_unicode_str() == "∀x (Young(x) → White(x))"


def test_representation_relational_rule_hand_converted():
    """Mixed relational/attribute rule from the REAL RelNoneg row:
    conditions conjoin, the relation triple is binary, and the ONE distinct
    placeholder yields ONE quantifier even though it occurs twice."""
    node = parse_proofwriter_representation(
        '((("something" "chases" "bear" "+") ("bear" "is" "round" "+")) '
        '-> ("something" "sees" "bear" "+"))')
    assert node.to_unicode_str() == \
        "∀x (Chases(x, bear) ∧ Round(bear) → Sees(x, bear))"


def test_representation_ground_rule_stays_unquantified():
    """A rule naming only entities (real rule2 of the AttNoneg row) is a
    ground implication — no placeholder, no quantifier."""
    node = parse_proofwriter_representation(
        '((("Fiona" "is" "big" "+") ("Fiona" "is" "round" "+")) '
        '-> ("Fiona" "is" "green" "+"))')
    assert node.to_unicode_str() == \
        "Big(fiona) ∧ Round(fiona) → Green(fiona)"


def test_representation_rejects_malformed_input():
    """Unknown polarity, unbalanced parens, and single-letter entities (which
    would lex as kit VARIABLES) are refused loudly, never guessed at."""
    with pytest.raises(ValueError, match="polarity"):
        parse_proofwriter_representation('("Anne" "is" "white" "?")')
    with pytest.raises(ValueError, match="unbalanced"):
        parse_proofwriter_representation('(("Anne" "is" "white" "+")')
    with pytest.raises(ValueError, match="single-letter"):
        parse_proofwriter_representation('("A" "is" "white" "+")')


def test_structured_loader_yields_one_example_per_question():
    """2 fixture theories x 12 non-null questions each = 24 examples; ids are
    proofwriter:<row id>:<Qn>; premises are the fact+rule sentence texts of
    the owning theory (AttNoneg row: 7 triples + 3 rules = 10)."""
    examples = list(load_proofwriter_structured(_OWA_FIXTURE))
    assert len(examples) == 24
    assert examples[0].id == "proofwriter:AttNoneg-OWA-D2-1960:Q1"
    assert len(examples[0].nl_premises) == 10
    assert examples[0].nl_premises[0] == "Anne is white."
    assert examples[0].nl_premises[7] == "Young things are white."
    assert all(e.label in ("True", "False", "Unknown") for e in examples)


def test_structured_loader_generates_parsing_wellformed_fol():
    """Every generated formula parses and validates: audit 24/24 ok, every
    example carries the fol_generated marker plus its verbatim source
    representations — the honesty contract for KIT-GENERATED (not
    upstream-authored) FOL."""
    examples = list(load_proofwriter_structured(_OWA_FIXTURE))
    assert all(e.meta.get("fol_generated") is True for e in examples)
    assert all(e.meta["premise_representations"] for e in examples)
    report = audit_examples(examples)
    assert len(report) == 24
    assert all(r["ok"] for r in report)


def test_structured_loader_convert_fol_false_skips_generation():
    examples = list(load_proofwriter_structured(_OWA_FIXTURE, convert_fol=False))
    assert len(examples) == 24
    assert all(e.fol_premises == () and e.fol_conclusion is None
               for e in examples)
    assert all("fol_generated" not in e.meta for e in examples)


def test_solve_structured_reproduces_every_owa_label():
    """End-to-end over ALL 24 real questions: the OWA three-way label aligns
    exactly with classical entailment over the generated FOL — hand-checked
    exemplar (AttNoneg Q2): the theory contains the fact Cold(charlie), the
    question representation is ¬Cold(charlie), premises ⊨ ¬(¬Cold(charlie)),
    so the prediction is 'False', matching gold. 24/24 was verified once by
    hand-run before being pinned here; a regression to anything less means
    either the generation or the OWA-classical alignment broke."""
    examples = list(load_proofwriter_structured(_OWA_FIXTURE))
    for example in examples:
        result = solve_structured_example(example)
        assert result["predicted"] == example.label, example.id


def test_solve_structured_refuses_unconverted_examples():
    example = next(iter(load_proofwriter_structured(_OWA_FIXTURE,
                                                    convert_fol=False)))
    with pytest.raises(ValueError):
        solve_structured_example(example)


# ---------------------------------------------------------------------------
# semantics="cwa": two-valued closed-model checking (ordinary FOL evaluation
# in the minimal model, ATP as the per-atom derivability oracle)
# ---------------------------------------------------------------------------

def _hand_example(premises, conclusion, example_id="synthetic:cwa"):
    """A converted-shape example built by hand (kit-notation FOL strings)."""
    return DatasetExample(
        id=example_id, nl_premises=(), fol_premises=tuple(premises),
        nl_conclusion=None, fol_conclusion=conclusion, label=None,
        known_bad=False, meta={"fol_generated": True},
    )


def test_cwa_underdetermined_positive_atom_is_false_not_unknown():
    """THE defining CWA/OWA divergence, from a hand-built two-question
    theory (premise: ¬Green(alice)):

        Blue(alice):  OWA → Unknown (neither it nor its negation follows),
                      CWA → False   (not derivable → false in the closed model)
        Green(alice): OWA → False, CWA → False (both: ¬Green(alice) given).

    CWA is two-valued classical FOL — evaluation in the closed model — so
    'Unknown' never appears."""
    blue = _hand_example(["¬Green(alice)"], "Blue(alice)")
    green = _hand_example(["¬Green(alice)"], "Green(alice)")

    assert solve_structured_example(blue)["predicted"] == "Unknown"      # OWA
    assert solve_structured_example(blue, semantics="cwa")["predicted"] == "False"
    assert solve_structured_example(green)["predicted"] == "False"       # OWA
    assert solve_structured_example(green, semantics="cwa")["predicted"] == "False"


def test_cwa_negated_conclusion_is_true_iff_atom_underivable():
    """Real fixture question AttNoneg Q7 'Fiona is not big' (¬Big(fiona),
    OWA gold: Unknown). Hand-derivation of the closed model: Fiona is white
    (triple7); rule3 needs White ∧ Round, but Round(fiona) is not derivable,
    so Big(fiona) is NOT in the closed model — hence ¬Big(fiona) is TRUE
    under CWA. Exactly the first-branch-per-atom reading with the negation
    handled compositionally on top."""
    examples = {e.meta["question_key"]: e
                for e in load_proofwriter_structured(_OWA_FIXTURE)
                if e.meta["row_id"] == "AttNoneg-OWA-D2-1960"}
    q7 = examples["Q7"]
    assert q7.label == "Unknown"                       # the OWA gold label
    result = solve_structured_example(q7, semantics="cwa")
    assert result["predicted"] == "True"
    # The oracle call trail is on the record: exactly the Big(fiona) atom.
    assert [c["atom"] for c in result["atom_calls"]] == ["Big(fiona)"]
    assert result["atom_calls"][0]["derivable"] is False


def test_cwa_derived_atoms_stay_true():
    """AttNoneg Q5 'Erin is big' (OWA gold: True — derivable via young→white,
    white∧round→big): the closed model contains Big(erin), so CWA agrees."""
    examples = {e.meta["question_key"]: e
                for e in load_proofwriter_structured(_OWA_FIXTURE)
                if e.meta["row_id"] == "AttNoneg-OWA-D2-1960"}
    assert solve_structured_example(examples["Q5"],
                                    semantics="cwa")["predicted"] == "True"


def test_cwa_quantified_conclusion_ranges_over_the_constants():
    """Quantifiers in the QUERY are model checking over the finite constant
    set: with facts Red(a-const...) for exactly alice and bob, ∀x Red(x) is
    TRUE in the closed model (its domain is {alice, bob}) while ∃x Blue(x)
    is FALSE. Hand-built; classical entailment would call BOTH unknown."""
    example_forall = _hand_example(["Red(alice)", "Red(bob)"], "∀x Red(x)")
    example_exists = _hand_example(["Red(alice)", "Red(bob)"], "∃x Blue(x)")
    assert solve_structured_example(example_forall,
                                    semantics="cwa")["predicted"] == "True"
    assert solve_structured_example(example_exists,
                                    semantics="cwa")["predicted"] == "False"


def test_cwa_naf_rule_fires_via_stratification():
    """∀x (¬Red(x) → Big(x)) is negation-as-failure INSIDE the theory, and
    stratified evaluation handles it exactly: Red (stratum 0) has no rules,
    so its extension is finally EMPTY; the Big rule (stratum 1) then reads
    Red(alice)'s absence and fires — Big(alice) is TRUE in the perfect
    model. Hand-derived; a classical prover could never conclude this (the
    review's earlier refusal behaviour is now upgraded to the standard
    perfect-model semantics)."""
    example = _hand_example(["∀x (¬Red(x) → Big(x))"], "Big(alice)")
    assert solve_structured_example(example,
                                    semantics="cwa")["predicted"] == "True"


def test_cwa_stratified_chain_hand_derived():
    """Two strata + a positive chain, evaluated by hand:
    facts: Red(bob); rules: ∀x (¬Red(x) → Big(x)), ∀x (Big(x) → Huge(x)).
    Closed model over {alice, bob}: Red = {bob} (stratum 0, final);
    Big = {alice} (bob is Red, alice is not); Huge = {alice}.
    So Huge(alice) True, Huge(bob) False, ¬Big(bob) True."""
    premises = ["Red(bob)", "∀x (¬Red(x) → Big(x))", "∀x (Big(x) → Huge(x))"]
    assert solve_structured_example(
        _hand_example(premises, "Huge(alice)"),
        semantics="cwa")["predicted"] == "True"
    assert solve_structured_example(
        _hand_example(premises, "Huge(bob)"),
        semantics="cwa")["predicted"] == "False"
    assert solve_structured_example(
        _hand_example(premises, "¬Big(bob)"),
        semantics="cwa")["predicted"] == "True"


def test_cwa_refuses_a_cycle_through_negation():
    """∀x (¬P(x) → P(x)) has no stratification (P depends negatively on
    itself) — its NAF semantics is not defined by stratified chaining
    (well-founded semantics would be needed), so the route refuses loudly."""
    example = _hand_example(["∀x (¬P(x) → P(x))"], "P(alice)")
    with pytest.raises(ValueError, match="stratif"):
        solve_structured_example(example, semantics="cwa")


def test_cwa_refuses_an_inconsistent_theory():
    """A theory deriving Green(alice) both positively and negatively is
    inconsistent under the closed-world reading — refusing beats answering
    arbitrarily (and beats the classical prover's ex falso everything)."""
    example = _hand_example(["Green(alice)", "¬Green(alice)"], "Blue(alice)")
    with pytest.raises(ValueError, match="inconsistent"):
        solve_structured_example(example, semantics="cwa")


# ---------------------------------------------------------------------------
# Real CWA gold labels (fixture: tests/fixtures/proofwriter_cwa_mini.jsonl —
# 2 REAL rows copied verbatim from the original AllenAI release
# proofwriter-dataset-V2020.12.3.zip, CWA/depth-2/meta-dev.jsonl, on
# 2026-08-12: AttNoneg-CWA-D2-1286 [definite attribute theory, 12 questions]
# and RelNeg-CWA-D2-1420 [relational theory WITH negated rule bodies, 12
# questions — its predicate graph cycles through negation, its ground graph
# does not, so it exercises LOCAL stratification])
# ---------------------------------------------------------------------------

_CWA_FIXTURE = _FIXTURES / "proofwriter_cwa_mini.jsonl"


def test_cwa_real_gold_fixture_reproduced_24_of_24():
    """Every question of both real AllenAI CWA rows is reproduced exactly.
    The CWA answer field is boolean in the original release (no "Unknown"
    exists under CWA), so gold comparison is str(label). The AttNoneg
    theory is definite (per-atom z3 cross-check active); the RelNeg theory
    has NAF rules (fixpoint only, by design)."""
    examples = list(load_proofwriter_structured(_CWA_FIXTURE))
    assert len(examples) == 24
    for example in examples:
        assert example.label in (True, False)   # CWA gold is two-valued
        result = solve_structured_example(example, semantics="cwa",
                                          backends=["z3"])
        assert result["predicted"] == str(example.label), example.id


def test_cwa_local_stratification_accepts_predicate_level_cycle():
    """¬Likes(mouse, dog) → Likes(dog, rabbit): the PREDICATE graph has a
    negative self-loop on Likes, but the GROUND graph is acyclic — the atom
    Likes(dog, rabbit) depends negatively on the DIFFERENT atom
    Likes(mouse, dog). Local stratification decides both directions, each
    hand-derived:

    * with the fact Likes(mouse, dog): the body ¬Likes(mouse, dog) fails,
      the rule never fires, Likes(dog, rabbit) is NOT in the closed model;
    * without that fact: Likes(mouse, dog) is underivable (stratum 0,
      final), the rule fires, Likes(dog, rabbit) IS in the closed model."""
    blocked = _hand_example(["Likes(mouse, dog)",
                             "¬Likes(mouse, dog) → Likes(dog, rabbit)"],
                            "Likes(dog, rabbit)")
    fires = _hand_example(["Likes(mouse, tiger)",
                           "¬Likes(mouse, dog) → Likes(dog, rabbit)"],
                          "Likes(dog, rabbit)")
    assert solve_structured_example(blocked,
                                    semantics="cwa")["predicted"] == "False"
    assert solve_structured_example(fires,
                                    semantics="cwa")["predicted"] == "True"


def test_cwa_relneg_1420_naf_rules_hand_derived():
    """The theory predicate-level stratification refused, answered by hand:

    Q4 asks ¬Visits(tiger, mouse) (gold: False). rule6 is
    ¬Sees(mouse, tiger) → Visits(tiger, mouse); no fact or rule ever derives
    Sees(mouse, tiger) (the only Sees rule produces Sees(x, rabbit)), so its
    absence is final at a lower stratum, rule6 fires, Visits(tiger, mouse)
    is TRUE in the perfect model — hence the negated question is False.

    Q5 asks Round(rabbit) (gold: True). Sees(rabbit, mouse) is a fact;
    rule5 Sees(x, mouse) → Sees(x, rabbit) gives Sees(rabbit, rabbit);
    with the fact Likes(rabbit, tiger), rule2
    Sees(x, rabbit) ∧ Likes(x, tiger) → Round(x) fires for x=rabbit."""
    examples = {e.meta["question_key"]: e
                for e in load_proofwriter_structured(_CWA_FIXTURE)
                if e.meta["row_id"] == "RelNeg-CWA-D2-1420"}
    q4 = solve_structured_example(examples["Q4"], semantics="cwa")
    assert examples["Q4"].label is False
    assert q4["predicted"] == "False"
    q5 = solve_structured_example(examples["Q5"], semantics="cwa")
    assert examples["Q5"].label is True
    assert q5["predicted"] == "True"


def test_solver_backend_is_caller_selectable():
    """The ATP is the caller's choice: prove_kwargs go verbatim to api.prove
    — here the z3-only chain must reproduce the default result."""
    examples = list(load_proofwriter_structured(_OWA_FIXTURE))
    result = solve_structured_example(examples[0], backends=["z3"])
    assert result["predicted"] == examples[0].label
    result_cwa = solve_structured_example(examples[0], semantics="cwa",
                                          backends=["z3"])
    assert result_cwa["predicted"] in ("True", "False")


def test_solve_structured_rejects_unknown_semantics():
    examples = list(load_proofwriter_structured(_OWA_FIXTURE))
    with pytest.raises(ValueError, match="semantics"):
        solve_structured_example(examples[0], semantics="nwa")


# ---------------------------------------------------------------------------
# on_indefinite: established Unknown vs prover-couldn't-tell
# ---------------------------------------------------------------------------

def _q8_anne_is_big():
    """AttNoneg Q8 'Anne is big' — gold Unknown; hand-derivation: Anne is
    white and young (facts), White(anne) re-derivable via rule1, but rule3
    needs White ∧ Round and Round(anne) is underivable — so Big(anne) is
    not entailed, and neither is ¬Big(anne) (nothing derives negations in
    this theory). The default z3 chain REFUTES both directions
    (countermodels exist), i.e. underdetermination is ESTABLISHED."""
    examples = {e.meta["question_key"]: e
                for e in load_proofwriter_structured(_OWA_FIXTURE)
                if e.meta["row_id"] == "AttNoneg-OWA-D2-1960"}
    q8 = examples["Q8"]
    assert q8.label == "Unknown"
    return q8


def test_on_indefinite_abstain_still_labels_established_unknown():
    """With z3, both cascade legs come back definitively REFUTED — the
    'Unknown' is proven, so even abstain/raise modes label it."""
    q8 = _q8_anne_is_big()
    result = solve_structured_example(q8, on_indefinite="abstain")
    assert result["predicted"] == "Unknown"
    assert result["verdict"]["status"] == "refuted"
    assert result["verdict_negated"]["status"] == "refuted"
    assert solve_structured_example(
        q8, on_indefinite="raise")["predicted"] == "Unknown"


def test_on_indefinite_separates_prover_failure_from_unknown():
    """The same question decided by the resolution backend ALONE: resolution
    is refutation-only-for-proving (its False means bound hit, never a
    countermodel), so both legs are INDEFINITE (unknown/bound_hit) — 'label'
    still scores the dataset label, 'abstain' refuses to, 'raise' raises.
    This is exactly the distinction the parameter exists for: a timeout or
    bound must not be silently creditable as a correct 'Unknown'."""
    q8 = _q8_anne_is_big()
    labelled = solve_structured_example(q8, backends=["resolution"])
    assert labelled["predicted"] == "Unknown"                 # default mode
    # The surfaced verdict is the chain summary (nothing definitive); the
    # member's honest bound_hit reason is on the record in its detail line.
    assert labelled["verdict"]["status"] == "unknown"
    assert labelled["verdict"]["backend"] == "chain"
    assert "resolution:unknown/bound_hit" in labelled["verdict"]["detail"]

    abstained = solve_structured_example(q8, backends=["resolution"],
                                         on_indefinite="abstain")
    assert abstained["predicted"] is None

    with pytest.raises(ValueError, match="indefinite"):
        solve_structured_example(q8, backends=["resolution"],
                                 on_indefinite="raise")


def test_on_indefinite_rejects_unknown_value():
    q8 = _q8_anne_is_big()
    with pytest.raises(ValueError, match="on_indefinite"):
        solve_structured_example(q8, on_indefinite="ignore")
