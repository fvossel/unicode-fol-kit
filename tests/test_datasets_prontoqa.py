"""Tests for unicode_fol_kit.eval.datasets.prontoqa.

``tests/fixtures/prontoqa_mini.jsonl`` holds 8 REAL rows fetched verbatim
from https://huggingface.co/datasets/renma/ProntoQA (config "default", split
"validation", via the Hugging Face ``datasets-server`` ``rows`` API,
2026-08-12) -- ids ``ProntoQA_4``, ``ProntoQA_9``, ``ProntoQA_18``,
``ProntoQA_22``, ``ProntoQA_31``, ``ProntoQA_39``, ``ProntoQA_45``,
``ProntoQA_52``. Unlike the FOLIO/MALLS fixtures, this one is NOT hand-written
synthetic data shaped like the source: the ``prontoqa.py`` module docstring
documents that this dataset's real defects live INSIDE the LLM-generated
``raw_logic_programs`` DSL text itself (naming inconsistencies that break the
forward-chained derivation, or rows where a clean derivation still disagrees
with the gold ``answer`` for unknown reasons), so a hand-authored synthetic
example could not exercise or demonstrate that -- only a genuine row can. The
8 rows above were deliberately selected, out of a 100-row sample fetched
while building this adapter, to be free of both defect classes (verified by
running :func:`solve_example` -- see ``prontoqa.py``'s module docstring for
the full accounting: only 76/100 sampled rows satisfy this cleanly).

Field-mapping and polarity assertions below are hand-checked against the raw
JSON text in the fixture file, not against whatever the code under test
happens to compute.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.eval.datasets import DatasetExample, DATASET_INFO, audit_examples
from unicode_fol_kit.eval.datasets.prontoqa import (
    load_prontoqa,
    parse_logic_program,
    solve_example,
)
from unicode_fol_kit.fol.nodes import Atom, Not, And, Implies, Quantifier, Variable, Constant
from unicode_fol_kit.atp.protocol import PROVED, REFUTED

_FIXTURES = Path(__file__).parent / "fixtures"
_PRONTOQA_FIXTURE = _FIXTURES / "prontoqa_mini.jsonl"

# The 8 fixture ids, in file order, with their hand-verified gold answers and
# the Query:'s own stated boolean (read directly off the fixture's raw JSON;
# see prontoqa.py's module docstring for the ProntoQA_45 derivation worked by
# hand, and the "Honesty" section for why these 8 -- and not just any 8 --
# were chosen).
_FIXTURE_IDS = [
    "ProntoQA_4", "ProntoQA_9", "ProntoQA_18", "ProntoQA_22",
    "ProntoQA_31", "ProntoQA_39", "ProntoQA_45", "ProntoQA_52",
]
_FIXTURE_ANSWERS = {
    "ProntoQA_4": "B", "ProntoQA_9": "A", "ProntoQA_18": "B", "ProntoQA_22": "B",
    "ProntoQA_31": "A", "ProntoQA_39": "B", "ProntoQA_45": "A", "ProntoQA_52": "A",
}
_FIXTURE_QUERY_POLARITY = {
    # Sour/Small/etc(Entity, <this>) -- the Query: line's own boolean, read
    # directly from the fixture text (e.g. ProntoQA_4's Query: is
    # "Small(Alex, False)").
    "ProntoQA_4": False, "ProntoQA_9": True, "ProntoQA_18": True, "ProntoQA_22": False,
    "ProntoQA_31": False, "ProntoQA_39": False, "ProntoQA_45": True, "ProntoQA_52": True,
}


# ---------------------------------------------------------------------------
# load_prontoqa: field mapping and id resolution
# ---------------------------------------------------------------------------

def test_load_prontoqa_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_prontoqa(_PRONTOQA_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)
    assert [e.id for e in examples] == _FIXTURE_IDS


def test_load_prontoqa_field_mapping_first_example():
    """context/question/answer/options/raw_logic_programs map as documented
    in prontoqa.py's module docstring.

    Row 1 of the fixture is ProntoQA_4: context is the single-paragraph
    story about Alex, question asks about "Alex is not small", answer is
    "B", options are the two fixed strings, and raw_logic_programs is a
    1-tuple holding the full DSL text verbatim (checked here only by its
    Query: tail and Facts: head, not the whole ~800-character string, since
    that exact byte-for-byte match is already exercised transitively by
    every other test that parses it).
    """
    example = next(load_prontoqa(_PRONTOQA_FIXTURE))
    assert example.id == "ProntoQA_4"
    assert example.nl_premises == (
        "Rompuses are spicy. Every rompus is an impus. Yumpuses are not "
        "small. Impuses are orange. Impuses are zumpuses. Zumpuses are not "
        "hot. Zumpuses are numpuses. Numpuses are metallic. Numpuses are "
        "wumpuses. Every wumpus is not kind. Each wumpus is a dumpus. Each "
        "dumpus is not bright. Every dumpus is a jompus. Jompuses are "
        "small. Jompuses are vumpuses. Each vumpus is not shy. Every "
        "vumpus is a tumpus. Alex is a zumpus.",
    )
    assert example.fol_premises == ()
    assert example.nl_conclusion == "Is the following statement true or false? Alex is not small."
    assert example.fol_conclusion is None
    assert example.label == "B"
    assert example.known_bad is False
    assert example.meta["options"] == ("A) True", "B) False")
    assert example.meta["line_no"] == 0
    assert len(example.meta["raw_logic_programs"]) == 1
    program = example.meta["raw_logic_programs"][0]
    assert program.startswith("Predicates:\nSpicy($x, bool)")
    assert program.rstrip().endswith("Query:\nSmall(Alex, False)")


def test_load_prontoqa_ids_are_the_source_native_ids():
    """Every fixture row carries its own 'id' field (verified: renma/ProntoQA
    rows always do) -- none of them should fall back to the positional
    'prontoqa:<line_no>' form."""
    examples = list(load_prontoqa(_PRONTOQA_FIXTURE))
    assert [e.id for e in examples] == _FIXTURE_IDS
    assert all(not e.id.startswith("prontoqa:") for e in examples)


def test_load_prontoqa_positional_id_fallback_for_id_less_rows(tmp_path):
    """A record without an 'id' field falls back to f'prontoqa:{line_no}'
    (0-based), mirroring folio.py's own fallback -- exercised here with a
    hand-built record since every real renma/ProntoQA row carries an id."""
    path = tmp_path / "id_less.jsonl"
    path.write_text(
        json.dumps({
            "answer": "A", "context": "Foo.", "question": "Is foo a bar?",
            "options": ["A) True", "B) False"],
            "raw_logic_programs": ["Facts:\nFoo(Bar, True)\n\nRules:\n\nQuery:\nFoo(Bar, True)"],
        }) + "\n",
        encoding="utf-8",
    )
    examples = list(load_prontoqa(path))
    assert len(examples) == 1
    assert examples[0].id == "prontoqa:0"


def test_load_prontoqa_known_bad_flag():
    """known_bad_ids flags exactly the matching example, nothing else."""
    examples = list(load_prontoqa(_PRONTOQA_FIXTURE, known_bad_ids=frozenset({"ProntoQA_45"})))
    known_bad = {e.id: e.known_bad for e in examples}
    expected = {eid: (eid == "ProntoQA_45") for eid in _FIXTURE_IDS}
    assert known_bad == expected


def test_load_prontoqa_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_prontoqa(_FIXTURES / "does_not_exist.jsonl"))


def test_load_prontoqa_malformed_json_line_raises_not_silently_skipped(tmp_path):
    """A dataset file with a broken JSON line must fail loudly (mirrors
    test_load_malls_malformed_json_line_raises_not_silently_skipped in
    test_datasets.py)."""
    bad_path = tmp_path / "_tmp_malformed_prontoqa.jsonl"
    bad_path.write_text(
        '{"id": "ok", "answer": "A", "context": "c", "question": "q", '
        '"options": [], "raw_logic_programs": []}\nnot json at all\n',
        encoding="utf-8",
    )
    with pytest.raises(json.JSONDecodeError):
        list(load_prontoqa(bad_path))


# ---------------------------------------------------------------------------
# audit_examples: vacuously ok, by construction (see module docstring)
# ---------------------------------------------------------------------------

def test_audit_examples_is_vacuously_ok_for_every_prontoqa_example():
    """fol_premises is always () and fol_conclusion always None for this
    adapter (the DSL is not a parseable FOL string -- see prontoqa.py's
    module docstring), so audit_examples has nothing to parse or check for
    any example: every report must come back ok=True with no defects. This
    is a real, reasoned expected value (not "whatever the code computes"):
    audit_examples' own docstring defines all_checked as "vacuously True if
    nothing parsed", and all_parsed as True when there is nothing in
    fol_premises/fol_conclusion to fail parsing.
    """
    examples = list(load_prontoqa(_PRONTOQA_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 8
    assert all(r["ok"] is True for r in report)
    assert all(r["all_parsed"] is True and r["all_checked"] is True for r in report)
    assert all(r["defects"] == [] for r in report)


def test_audit_examples_respects_max_examples():
    report = audit_examples(load_prontoqa(_PRONTOQA_FIXTURE), max_examples=3)
    assert len(report) == 3
    assert [r["id"] for r in report] == _FIXTURE_IDS[:3]


# ---------------------------------------------------------------------------
# DATASET_INFO / to_dict
# ---------------------------------------------------------------------------

def test_dataset_info_registry_has_verified_provenance_for_prontoqa():
    assert "prontoqa" in DATASET_INFO
    info = DATASET_INFO["prontoqa"]
    assert info["license"] == "MIT"
    assert info["source_url"] == "https://huggingface.co/datasets/renma/ProntoQA"
    assert "Saparov" in info["citation_hint"]
    assert "Logic-LM" in info["citation_hint"]


def test_dataset_example_to_dict_is_json_compatible():
    example = next(load_prontoqa(_PRONTOQA_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)         # must not raise
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "ProntoQA_4"
    assert round_tripped["fol_premises"] == []
    assert round_tripped["fol_conclusion"] is None
    assert round_tripped["label"] == "B"


# ---------------------------------------------------------------------------
# parse_logic_program: the DSL -> AST converter
# ---------------------------------------------------------------------------

def _program_for(example_id: str) -> str:
    for e in load_prontoqa(_PRONTOQA_FIXTURE):
        if e.id == example_id:
            return e.meta["raw_logic_programs"][0]
    raise AssertionError(f"fixture id not found: {example_id}")


def test_parse_logic_program_hand_worked_prontoqa_45():
    """ProntoQA_45 -- the example worked by hand in prontoqa.py's module
    docstring (solve_example) and the shortest fixture row (11 rules, 1
    fact), reproduced here structurally.

    Facts: Dumpus(Fae, True) -> Atom("Dumpus", (Constant("fae"),)).
    11 Rules lines -> 11 Quantifier(forall, x, Implies(...)) nodes, so
    12 premises total (1 fact + 11 rules).
    Query: Wooden(Fae, True) -> positive atom, query_polarity=True.
    """
    program = _program_for("ProntoQA_45")
    premises, query, query_polarity = parse_logic_program(program)

    assert len(premises) == 1 + 11
    assert premises[0] == Atom("Dumpus", (Constant("fae"),))
    assert query_polarity is True
    assert query == Atom("Wooden", (Constant("fae"),))

    # The rule "Impus($x, True) >>> Wooden($x, True)" (the 10th Rules: line,
    # 0-indexed 9 among the rule premises which start at premises[1]) is the
    # one that actually derives the Query -- check its exact shape.
    x = Variable("x")
    impus_to_wooden = Quantifier(
        "∀", x,
        Implies(Atom("Impus", (x,)), Atom("Wooden", (x,))),
    )
    assert impus_to_wooden in premises

    # And the OTHER Wooden rule is a genuine negation, structurally distinct.
    tumpus_to_not_wooden = Quantifier(
        "∀", x,
        Implies(Atom("Tumpus", (x,)), Not(Atom("Wooden", (x,)))),
    )
    assert tumpus_to_not_wooden in premises


def test_parse_logic_program_query_polarity_false_and_negated_rule_bodies():
    """ProntoQA_4 -- Query: Small(Alex, False) must parse to a NEGATED atom
    with query_polarity=False, and a rule like
    'Dumpus($x, True) >>> Bright($x, False)' must produce
    Implies(Atom(Dumpus,x), Not(Atom(Bright,x))), not two separate positive
    atoms."""
    program = _program_for("ProntoQA_4")
    premises, query, query_polarity = parse_logic_program(program)

    assert query_polarity is False
    assert query == Not(Atom("Small", (Constant("alex"),)))

    x = Variable("x")
    dumpus_to_not_bright = Quantifier(
        "∀", x,
        Implies(Atom("Dumpus", (x,)), Not(Atom("Bright", (x,)))),
    )
    assert dumpus_to_not_bright in premises
    # Fact: Zumpus(Alex, True) is ground and positive.
    assert Atom("Zumpus", (Constant("alex"),)) in premises


def test_parse_logic_program_entity_names_are_lowercased():
    """'Alex' -> Constant('alex'); 'Fae' -> Constant('fae') -- the documented
    convention (task/docstring: 'Max' -> 'max')."""
    _, query4, _ = parse_logic_program(_program_for("ProntoQA_4"))
    assert query4.formula.args == (Constant("alex"),)   # query4 is Not(Atom(...))

    _, query45, _ = parse_logic_program(_program_for("ProntoQA_45"))
    assert query45.args == (Constant("fae"),)


def test_parse_logic_program_rejects_missing_section_marker():
    with pytest.raises(ValueError, match="Rules:"):
        parse_logic_program("Predicates:\nFoo($x, bool) ::: ?\n\nFacts:\nFoo(Bar, True)\n\nQuery:\nFoo(Bar, True)")


def test_parse_logic_program_rejects_malformed_fact_line():
    program = "Predicates:\n\nFacts:\nthis is not an atom\n\nRules:\n\nQuery:\nFoo(Bar, True)"
    with pytest.raises(ValueError, match="cannot parse fact/query line"):
        parse_logic_program(program)


def test_parse_logic_program_rejects_variable_in_fact_line():
    """A Facts:/Query: line must be GROUND -- '$x' there is a Rules:-only
    placeholder and must raise, not silently become a constant named '$x'."""
    program = "Predicates:\n\nFacts:\nFoo($x, True)\n\nRules:\n\nQuery:\nFoo(Bar, True)"
    with pytest.raises(ValueError, match="variable placeholder"):
        parse_logic_program(program)


def test_parse_logic_program_rejects_unsupported_rule_variable():
    program = (
        "Predicates:\n\nFacts:\nFoo(Bar, True)\n\n"
        "Rules:\nFoo($y, True) >>> Baz($y, True)\n\nQuery:\nFoo(Bar, True)"
    )
    with pytest.raises(ValueError, match="unsupported rule variable"):
        parse_logic_program(program)


def test_parse_logic_program_rejects_multiple_query_lines():
    program = (
        "Predicates:\n\nFacts:\nFoo(Bar, True)\n\nRules:\n\n"
        "Query:\nFoo(Bar, True)\nBaz(Bar, True)"
    )
    with pytest.raises(ValueError, match="exactly one Query"):
        parse_logic_program(program)


def test_parse_logic_program_rejects_rule_without_arrow():
    program = (
        "Predicates:\n\nFacts:\nFoo(Bar, True)\n\n"
        "Rules:\nFoo($x, True) Baz($x, True)\n\nQuery:\nFoo(Bar, True)"
    )
    with pytest.raises(ValueError, match="no '>>>'"):
        parse_logic_program(program)


# ---------------------------------------------------------------------------
# solve_example: end to end via unicode_fol_kit.api.prove
# ---------------------------------------------------------------------------

def test_solve_example_reproduces_gold_answer_for_every_fixture_example():
    """The main test: for every one of the 8 curated real fixture rows,
    solve_example's predicted answer matches the gold 'answer' field, and
    the verdict is always definitive (PROVED or REFUTED, never UNKNOWN) --
    exactly the deductive-closure property prontoqa.py's module docstring
    claims for a DSL row free of the documented naming defect."""
    for example in load_prontoqa(_PRONTOQA_FIXTURE):
        result = solve_example(example)
        assert result["predicted"] == example.label == _FIXTURE_ANSWERS[example.id]
        assert result["verdict"]["status"] in (PROVED, REFUTED)
        assert result["query_polarity"] == _FIXTURE_QUERY_POLARITY[example.id]


def test_solve_example_hand_worked_prontoqa_45():
    """ProntoQA_45 worked by hand (see prontoqa.py's solve_example
    docstring): Facts: Dumpus(Fae, True); chasing Dumpus->Numpus->Zumpus->
    Wumpus->Impus, the rule Impus($x, True) >>> Wooden($x, True) fires,
    giving the unique derived literal Wooden(Fae, True) -- exactly the
    Query:, so premises |= query classically (PROVED), predicted 'A',
    matching the gold answer."""
    example = next(e for e in load_prontoqa(_PRONTOQA_FIXTURE) if e.id == "ProntoQA_45")
    result = solve_example(example)
    assert result["verdict"]["status"] == PROVED
    assert result["predicted"] == "A"
    assert result["query_polarity"] is True
    assert example.label == "A"


def test_solve_example_hand_worked_prontoqa_4_refuted_case():
    """ProntoQA_4: Facts: Zumpus(Alex, True); chasing Zumpus->Numpus->
    Wumpus->Dumpus->Jompus, the rule Jompus($x, True) >>> Small($x, True)
    fires, deriving Small(Alex, True) -- the OPPOSITE polarity of
    Query: Small(Alex, False). Since Small(Alex, True) is classically
    entailed, its negation (the literal Query) is REFUTED (a countermodel --
    in fact every model of the premises -- falsifies it), so predicted='B',
    matching the gold answer."""
    example = next(e for e in load_prontoqa(_PRONTOQA_FIXTURE) if e.id == "ProntoQA_4")
    result = solve_example(example)
    assert result["verdict"]["status"] == REFUTED
    assert result["predicted"] == "B"
    assert result["query_polarity"] is False
    assert example.label == "B"


def test_solve_example_raises_for_missing_raw_logic_programs():
    example = DatasetExample(
        id="synthetic:1", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None,
        known_bad=False, meta={},
    )
    with pytest.raises(ValueError, match="exactly one raw_logic_programs entry"):
        solve_example(example)


def test_solve_example_raises_for_empty_raw_logic_programs_tuple():
    example = DatasetExample(
        id="synthetic:2", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None,
        known_bad=False, meta={"raw_logic_programs": ()},
    )
    with pytest.raises(ValueError, match="exactly one raw_logic_programs entry"):
        solve_example(example)


def test_solve_example_raises_for_multiple_raw_logic_programs():
    example = DatasetExample(
        id="synthetic:3", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None,
        known_bad=False,
        meta={"raw_logic_programs": (
            "Predicates:\n\nFacts:\nFoo(Bar, True)\n\nRules:\n\nQuery:\nFoo(Bar, True)",
            "Predicates:\n\nFacts:\nFoo(Bar, True)\n\nRules:\n\nQuery:\nFoo(Bar, True)",
        )},
    )
    with pytest.raises(ValueError, match="exactly one raw_logic_programs entry"):
        solve_example(example)


def test_solve_example_underivable_query_is_none_not_b():
    """Soundness fix pinned (found by adversarial review): a query whose atom
    is UNRELATED to the facts (here: facts say Foo(bar), query asks Baz(bar))
    is neither provable nor is its negation — the honest answer is None. The
    old single-call mapping coerced the entailment's REFUTED (which only
    witnesses a countermodel to premises ⊨ query, NOT a proof of ¬query)
    into 'B'."""
    example = DatasetExample(
        id="synthetic:underivable", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None, known_bad=False,
        meta={"raw_logic_programs": [
            "Predicates:\nFoo($x, bool) ::: test\nBaz($x, bool) ::: test\n\n"
            "Facts:\nFoo(Bar, True)\n\nRules:\n\nQuery:\nBaz(Bar, True)",
        ]},
    )
    result = solve_example(example)
    assert result["predicted"] is None
    assert result["verdict_negated"] is not None      # the second call ran


def test_on_indefinite_raise_mode_distinguishes_established_from_failure():
    """Same underivable-query example: with z3 both directions are
    definitively REFUTED — 'provably neither entailed' is an established
    outcome, so on_indefinite='raise' does NOT raise (predicted stays None,
    ProntoQA has no third label). With the resolution backend alone the legs
    are indefinite (bound_hit), and 'raise' must raise."""
    example = DatasetExample(
        id="synthetic:underivable", nl_premises=(), fol_premises=(),
        nl_conclusion=None, fol_conclusion=None, label=None, known_bad=False,
        meta={"raw_logic_programs": [
            "Predicates:\nFoo($x, bool) ::: test\nBaz($x, bool) ::: test\n\n"
            "Facts:\nFoo(Bar, True)\n\nRules:\n\nQuery:\nBaz(Bar, True)",
        ]},
    )
    established = solve_example(example, on_indefinite="raise")
    assert established["predicted"] is None
    assert established["verdict"]["status"] == "refuted"
    assert established["verdict_negated"]["status"] == "refuted"

    with pytest.raises(ValueError, match="indefinite"):
        solve_example(example, backends=["resolution"], on_indefinite="raise")

    with pytest.raises(ValueError, match="on_indefinite"):
        solve_example(example, on_indefinite="maybe")
