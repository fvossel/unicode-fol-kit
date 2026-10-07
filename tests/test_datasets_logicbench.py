"""Tests for the LogicBench adapter (unicode_logic_kit.eval.datasets.logicbench).

The fixtures under ``tests/fixtures/logicbench/`` are REAL rows copied
verbatim from a local clone of ``https://github.com/Mihir3009/LogicBench``
(MIT-licensed — see ``logicbench.py``'s module docstring for why this is
MIT and not the CC BY 4.0 an earlier, unverified roadmap entry assumed),
trimmed to 1-2 samples per file so the interesting structural cases (a BQA
sample's ``qa_pairs`` flattening into several examples, one with 2 pairs and
one with 4, and each of the three ``logic_type`` values under both BQA and
MCQA) sit side by side instead of scattered across 24 axiom files of 20
samples each.

Every ``solve_example`` expectation below was independently confirmed
against the real backend chain / ``semantics.nonmonotonic`` before being
pinned here (see the inline comments for the by-hand derivation) — nothing
here is invented, and the non-monotonic-vs-classical divergence test is the
same ``{P(a)→Q(a)}`` pattern ``tests/test_nonclassical.py`` already pins for
``semantics.nonmonotonic`` itself, just under LogicBench-shaped names, which
is the "cross-check against its existing behavior" the build spec asks for.
"""

from pathlib import Path
from dataclasses import replace

import pytest

from unicode_logic_kit.eval.datasets import DATASET_INFO, DatasetExample, audit_examples
from unicode_logic_kit.eval.datasets.logicbench import (
    LOGIC_TYPES, NM_LOGIC_TYPE, load_logicbench, solve_example,
)

_FIXTURES = Path(__file__).parent / "fixtures" / "logicbench"


def _examples(name, **kwargs):
    return list(load_logicbench(_FIXTURES / name, **kwargs))


def _by_id(examples):
    return {e.id: e for e in examples}


# ---------------------------------------------------------------------------
# Reading — BQA
# ---------------------------------------------------------------------------

def test_a_bqa_sample_flattens_into_one_example_per_qa_pair():
    examples = _examples("bqa_propositional_modus_tollens.json", split="BQA")
    assert [e.id for e in examples] == [
        "logicbench:BQA:propositional_logic:modus_tollens:1:0",
        "logicbench:BQA:propositional_logic:modus_tollens:1:1",
        "logicbench:BQA:propositional_logic:modus_tollens:2:0",
        "logicbench:BQA:propositional_logic:modus_tollens:2:1",
    ]
    assert all(isinstance(e, DatasetExample) for e in examples)
    # Both examples from sample 1 share the SAME premises (the one context
    # paragraph), but ask about different propositions with different labels.
    by_id = _by_id(examples)
    first, second = (by_id["logicbench:BQA:propositional_logic:modus_tollens:1:0"],
                     by_id["logicbench:BQA:propositional_logic:modus_tollens:1:1"])
    assert first.nl_premises == second.nl_premises
    assert first.nl_premises == (
        "Liam had finished his work early for the day, which meant that he "
        "would typically have ordered pizza for dinner. However, on this "
        "particular day, he decided against ordering pizza and opted for "
        "something else instead.",)
    assert first.nl_conclusion == "Does this imply that liam didn't finish his work early?"
    assert first.label == "yes"
    assert second.nl_conclusion == "Does this entail that liam finished his work early?"
    assert second.label == "no"


def test_bqa_meta_carries_axiom_logic_type_task_and_qa_index_verbatim():
    example = _by_id(_examples("bqa_first_order_modus_ponens.json", split="BQA"))[
        "logicbench:BQA:first_order_logic:modus_ponens:1:0"]
    assert example.meta["axiom"] == "modus_ponens"
    assert example.meta["logic_type"] == "first_order_logic"
    assert example.meta["task"] == "BQA"
    assert example.meta["sample_id"] == 1
    assert example.meta["qa_index"] == 0


def test_nm_logic_type_is_the_json_value_not_the_directory_name():
    # The upstream DIRECTORY is called "nm_logic", but every real file's own
    # "type" field says "non_monotonic_logic" — this is the exact deviation
    # from the roadmap build spec's assumed literal "nm_logic" string.
    examples = _examples("bqa_nm_default_reasoning_default.json", split="BQA")
    assert {e.meta["logic_type"] for e in examples} == {"non_monotonic_logic"}
    assert examples[0].meta["logic_type"] == NM_LOGIC_TYPE
    assert NM_LOGIC_TYPE in LOGIC_TYPES
    assert "nm_logic" not in LOGIC_TYPES


def test_a_sample_with_four_qa_pairs_yields_four_examples():
    examples = _examples("bqa_propositional_bidirectional_dilemma.json", split="BQA")
    assert [e.id for e in examples] == [
        f"logicbench:BQA:propositional_logic:bidirectional_dilemma:1:{i}"
        for i in range(4)
    ]
    assert [e.meta["qa_index"] for e in examples] == [0, 1, 2, 3]
    assert [e.label for e in examples] == ["yes", "no", "no", "no"]


# ---------------------------------------------------------------------------
# Reading — MCQA
# ---------------------------------------------------------------------------

def test_an_mcqa_sample_yields_one_example_with_choices_in_meta():
    examples = _examples("mcqa_first_order_universal_instantiation.json", split="MCQA")
    assert [e.id for e in examples] == [
        "logicbench:MCQA:first_order_logic:universal_instantiation:1",
        "logicbench:MCQA:first_order_logic:universal_instantiation:2",
    ]
    first = examples[0]
    assert first.nl_conclusion == "Based on the context, what conclusion would be deemed most suitable?"
    assert first.label == "choice_4"
    assert first.meta["choices"] == {
        "choice_1": "reema has already completed all the requirements for her degree",
        "choice_2": "reema is responsible for fulfilling the requirements for someone else's degree",
        "choice_3": "reema is exempted from taking the exam to complete her degree",
        "choice_4": "reema need to take an exam to complete her degree",
    }
    # The gold answer is always a key of that same sample's own choices.
    assert all(e.label in e.meta["choices"] for e in examples)


def test_an_mcqa_propositional_sample_yields_two_examples_with_choices_in_meta():
    # Distinct from test_an_mcqa_sample_yields_one_example_with_choices_in_meta
    # (first_order_logic) and test_mcqa_meta_carries_axiom_logic_type_and_task
    # (non_monotonic_logic): this exercises the propositional_logic MCQA
    # fixture, which until now sat unused in tests/fixtures/logicbench/.
    examples = _examples("mcqa_propositional_modus_tollens.json", split="MCQA")
    assert [e.id for e in examples] == [
        "logicbench:MCQA:propositional_logic:modus_tollens:1",
        "logicbench:MCQA:propositional_logic:modus_tollens:2",
    ]
    first, second = examples
    assert first.nl_conclusion == "Based on the context, what conclusion would be deemed most suitable?"
    assert first.label == "choice_1"
    assert first.meta["choices"] == {
        "choice_1": "Liam didn't finish his work early.",
        "choice_2": "Sarah had already ordered Chinese takeout.",
        "choice_3": "Rebecca finished her work early.",
        "choice_4": "Liam decided to order sushi instead.",
    }
    assert first.meta["axiom"] == "modus_tollens"
    assert first.meta["logic_type"] == "propositional_logic"
    assert second.label == "choice_1"
    # The gold answer is always a key of that same sample's own choices.
    assert all(e.label in e.meta["choices"] for e in examples)
    # And, as with any other MCQA row, solve_example refuses it by name --
    # this fixture's rows are not exempt from that contract either.
    with pytest.raises(ValueError, match="MCQA"):
        solve_example(first, translate=lambda s: "P(a)")


def test_mcqa_meta_carries_axiom_logic_type_and_task():
    example = _by_id(_examples("mcqa_nm_default_reasoning_default.json", split="MCQA"))[
        "logicbench:MCQA:non_monotonic_logic:default_reasoning_default:1"]
    assert example.meta["axiom"] == "default_reasoning_default"
    assert example.meta["logic_type"] == "non_monotonic_logic"
    assert example.meta["task"] == "MCQA"
    assert example.meta["sample_id"] == 1
    assert "qa_index" not in example.meta


# ---------------------------------------------------------------------------
# known_bad_ids and the no-FOL contract
# ---------------------------------------------------------------------------

def test_known_bad_ids_flag_the_composite_id():
    flagged = "logicbench:BQA:propositional_logic:modus_tollens:1:0"
    examples = _by_id(_examples("bqa_propositional_modus_tollens.json", split="BQA",
                                known_bad_ids=frozenset({flagged})))
    assert examples[flagged].known_bad is True
    assert examples["logicbench:BQA:propositional_logic:modus_tollens:1:1"].known_bad is False


def test_no_example_carries_gold_fol_and_the_audit_says_so_vacuously():
    examples = (_examples("bqa_propositional_modus_tollens.json", split="BQA")
               + _examples("mcqa_first_order_universal_instantiation.json", split="MCQA"))
    assert all(e.fol_premises == () for e in examples)
    assert all(e.fol_conclusion is None for e in examples)
    report = audit_examples(examples)
    assert all(row["ok"] and not row["defects"] for row in report)


def test_the_provenance_is_registered_as_mit_not_cc_by_40():
    # The roadmap build spec assumed CC BY 4.0 -- verified wrong against the
    # cloned repository's own LICENSE file and README.md.
    info = DATASET_INFO["logicbench"]
    assert "MIT" in info["license"]
    assert "CC BY" not in info["license"] or "NOT CC BY" in info["license"]
    assert info["source_url"] == "https://github.com/Mihir3009/LogicBench"
    assert "2404.15522" in info["citation_hint"]


# ---------------------------------------------------------------------------
# Malformed inputs and split mismatches are refused by name
# ---------------------------------------------------------------------------

def test_an_unknown_split_is_refused():
    with pytest.raises(ValueError, match="split"):
        _examples("bqa_propositional_modus_tollens.json", split="TQA")


def test_a_bqa_file_read_with_split_mcqa_is_refused():
    with pytest.raises(ValueError, match="question"):
        _examples("bqa_propositional_modus_tollens.json", split="MCQA")


def test_an_mcqa_file_read_with_split_bqa_is_refused():
    with pytest.raises(ValueError, match="qa_pairs"):
        _examples("mcqa_first_order_universal_instantiation.json", split="BQA")


def _write(tmp_path, obj, name="bad.json"):
    import json
    path = tmp_path / name
    path.write_text(json.dumps(obj), encoding="utf-8")
    return path


@pytest.mark.parametrize("obj,split,fragment", [
    ({"axiom": "x", "samples": []}, "BQA", "type"),
    ({"type": "propositional_logic", "samples": []}, "BQA", "axiom"),
    ({"type": "propositional_logic", "axiom": "", "samples": []}, "BQA", "axiom"),
    ({"type": "made_up_logic", "axiom": "x", "samples": []}, "BQA", "outside"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c", "qa_pairs": []}]}, "BQA", "qa_pairs"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "", "qa_pairs": [{"question": "q", "answer": "yes"}]}]},
     "BQA", "context"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c",
       "qa_pairs": [{"question": "q", "answer": "maybe"}]}]}, "BQA", "outside"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c", "qa_pairs": [{"answer": "yes"}]}]}, "BQA", "question"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c", "qa_pairs": [{"question": "q", "answer": "yes"}]},
      {"id": 1, "context": "c2", "qa_pairs": [{"question": "q2", "answer": "no"}]}]},
     "BQA", "duplicate"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"context": "c", "qa_pairs": [{"question": "q", "answer": "yes"}]}]}, "BQA", "id"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c", "question": "q",
       "choices": {"choice_1": "a"}, "answer": "choice_9"}]},
     "MCQA", "choices"),
    ({"type": "propositional_logic", "axiom": "x", "samples":
     [{"id": 1, "context": "c", "question": "q", "choices": {}, "answer": "choice_1"}]},
     "MCQA", "choices"),
])
def test_a_malformed_file_is_refused_by_name(tmp_path, obj, split, fragment):
    with pytest.raises(ValueError, match=fragment):
        list(load_logicbench(_write(tmp_path, obj), split=split))


# ---------------------------------------------------------------------------
# solve_example -- classical routes (propositional_logic / first_order_logic)
# ---------------------------------------------------------------------------

#: Hand-written translations of the fixtures' sentences, confirmed against
#: api.prove directly (not just derived from what solve_example happens to
#: compute) before being used as expectations below:
#:   (FinishedEarly(liam) → OrdersPizza(liam)) ∧ ¬OrdersPizza(liam)  [premise]
#:   ⊢ ¬FinishedEarly(liam)  [modus tollens -- proved]
#:   ⊬ FinishedEarly(liam)   [refuted: the countermodel is the premise's own
#:                            forced valuation]
_PROP_TRANSLATION = {
    "Liam had finished his work early for the day, which meant that he "
    "would typically have ordered pizza for dinner. However, on this "
    "particular day, he decided against ordering pizza and opted for "
    "something else instead.":
        "(FinishedEarly(liam) → OrdersPizza(liam)) ∧ ¬OrdersPizza(liam)",
    "Does this imply that liam didn't finish his work early?": "¬FinishedEarly(liam)",
    "Does this entail that liam finished his work early?": "FinishedEarly(liam)",
}

#: ∀x (Tired(x) → Rests(x)) ∧ Tired(jack) ⊢ Rests(jack)  [modus ponens +
#: universal instantiation -- proved]; ⊬ ¬Rests(jack)  [refuted].
_FOL_TRANSLATION = {
    "If someone is extremely tired, then they will seek some rest and "
    "relaxation. Today, Jack finds himself utterly exhausted.":
        "∀x (Tired(x) → Rests(x)) ∧ Tired(jack)",
    "Does this entail that he will take rest?": "Rests(jack)",
    "Does this entail that he won't take rest?": "¬Rests(jack)",
}


def test_a_propositional_modus_tollens_row_is_decided_correctly():
    examples = _by_id(_examples("bqa_propositional_modus_tollens.json", split="BQA"))
    translate = lambda s: _PROP_TRANSLATION[s]

    yes = solve_example(
        examples["logicbench:BQA:propositional_logic:modus_tollens:1:0"],
        translate=translate)
    assert yes["route"] == "classical"
    assert yes["verdict"]["status"] == "proved"
    assert yes["predicted"] == "yes" == yes["label"]

    no = solve_example(
        examples["logicbench:BQA:propositional_logic:modus_tollens:1:1"],
        translate=translate)
    assert no["verdict"]["status"] == "refuted"
    assert no["predicted"] == "no" == no["label"]


def test_a_first_order_modus_ponens_row_is_decided_correctly():
    examples = _by_id(_examples("bqa_first_order_modus_ponens.json", split="BQA"))
    translate = lambda s: _FOL_TRANSLATION[s]

    yes = solve_example(
        examples["logicbench:BQA:first_order_logic:modus_ponens:1:0"],
        translate=translate)
    assert yes["predicted"] == "yes" == yes["label"]
    assert yes["verdict"]["status"] == "proved"

    no = solve_example(
        examples["logicbench:BQA:first_order_logic:modus_ponens:1:1"],
        translate=translate)
    assert no["predicted"] == "no" == no["label"]
    assert no["verdict"]["status"] == "refuted"


def test_an_inconclusive_classical_verdict_predicts_none_not_a_guessed_label():
    # LogicBench's label space is only {"yes", "no"} -- unlike FraCaS there
    # is no third "unknown" to fall back on, so an UNKNOWN verdict must not
    # be silently forced into either binary label. "Some checks are strict"
    # does not classically settle "all checks are strict" either way; with
    # the default chain (which includes the finite model finder) a
    # countermodel is found and this comes back REFUTED, so -- exactly as
    # tests/test_datasets_fracas.py's own on_indefinite test does -- the
    # resolution-only chain is used here to force a genuinely indefinite
    # verdict (confirmed directly against api.prove above: "unknown" with
    # backends=["resolution"], "refuted" with the default chain).
    example = _by_id(_examples("bqa_propositional_modus_tollens.json", split="BQA"))[
        "logicbench:BQA:propositional_logic:modus_tollens:2:0"]
    translation = {
        example.nl_premises[0]: "∃x (Check(x) ∧ Strict(x))",
        example.nl_conclusion: "∀x (Check(x) → Strict(x))",
    }
    result = solve_example(example, translate=lambda s: translation[s],
                           backends=["resolution"])
    assert result["verdict"]["status"] == "unknown"
    assert result["predicted"] is None


# ---------------------------------------------------------------------------
# solve_example -- MCQA rows are refused, not silently mis-decided
# ---------------------------------------------------------------------------

def test_solve_example_refuses_an_mcqa_row_by_name():
    example = _examples("mcqa_first_order_universal_instantiation.json", split="MCQA")[0]
    with pytest.raises(ValueError, match="MCQA"):
        solve_example(example, translate=lambda s: "P(a)")


def test_solve_example_refuses_an_unsupported_logic_type():
    example = _examples("bqa_propositional_modus_tollens.json", split="BQA")[0]
    weird = replace(example, meta=dict(example.meta, logic_type="modal_logic"))
    with pytest.raises(ValueError, match="unsupported"):
        solve_example(weird, translate=lambda s: "P(a)")


@pytest.mark.parametrize("translate,fragment", [
    (lambda s: "∀x (", "does not parse"),
    (lambda s: 17, "expected a formula"),
])
def test_solve_example_refuses_what_it_cannot_decide(translate, fragment):
    example = _examples("bqa_propositional_modus_tollens.json", split="BQA")[0]
    with pytest.raises(ValueError, match=fragment):
        solve_example(example, translate=translate)


# ---------------------------------------------------------------------------
# solve_example -- the non-monotonic route, and its divergence from classical
# ---------------------------------------------------------------------------

#: The real Jenny/Anna row, translated with the "exception" resolved to
#: EXPLICIT ground facts for every named individual (¬Ab(jenny), Ab(anna)) --
#: the discipline the module docstring documents: only ``Bk`` (the default
#: rule's consequent) is left for circumscription to decide, so there is
#: exactly ONE minimal model up to the domain's constant-labelling symmetry.
#: Confirmed directly against semantics.nonmonotonic.minimal_models before
#: being pinned here: minimal_entails(..., Bk(jenny), circumscribed={"Bk"})
#: is True, and minimal_entails(..., ¬Bk(jenny), circumscribed={"Bk"}) is
#: False.
_NM_TRANSLATION = {
    "Jenny and Anna are known for their tall stature, which is often "
    "associated with playing basketball. However, Anna might be an "
    "exception to this norm.":
        "Tall(jenny) ∧ Tall(anna) ∧ ¬Ab(jenny) ∧ Ab(anna) ∧ "
        "∀x (Tall(x) ∧ ¬Ab(x) → Bk(x))",
    "does this entail that jenny plays basketball?": "Bk(jenny)",
    "does this mean that jenny doesn't play basketball?": "¬Bk(jenny)",
}


def test_a_default_reasoning_row_is_routed_through_nonmonotonic():
    examples = _by_id(_examples("bqa_nm_default_reasoning_default.json", split="BQA"))
    translate = lambda s: _NM_TRANSLATION[s]

    yes = solve_example(
        examples["logicbench:BQA:non_monotonic_logic:default_reasoning_default:1:0"],
        translate=translate, circumscribed={"Bk"})
    assert yes["route"] == "nonmonotonic"
    assert yes["predicted"] == "yes" == yes["label"]
    assert yes["minimal_model_count"] >= 1

    no = solve_example(
        examples["logicbench:BQA:non_monotonic_logic:default_reasoning_default:1:1"],
        translate=translate, circumscribed={"Bk"})
    assert no["predicted"] == "no" == no["label"]


def test_no_minimal_model_found_is_refused_not_reported_as_a_vacuous_yes():
    # minimal_entails([P(a) ∧ ¬P(a)], anything, ...) would return True
    # VACUOUSLY (an empty for-loop) -- the route must catch this itself and
    # refuse, rather than ever surface that vacuous "yes".
    example = _by_id(_examples("bqa_nm_default_reasoning_default.json", split="BQA"))[
        "logicbench:BQA:non_monotonic_logic:default_reasoning_default:1:0"]
    with pytest.raises(ValueError, match="no minimal model|NO minimal model"):
        solve_example(example, translate=lambda s: "P(a) ∧ ¬P(a)",
                      circumscribed={"P"})


#: The exact {P(a)→Q(a)} pattern tests/test_nonclassical.py already pins for
#: semantics.nonmonotonic.minimal_entails directly (test_circumscription_is_
#: non_monotonic), reused here under Bird/Flies names and wrapped as
#: DatasetExamples, to show solve_example's ROUTING reproduces that same
#: cross-checked behavior end to end -- and that it genuinely diverges from
#: what the classical route would say for the identical translated premises.
def _bird_example(logic_type, nl_conclusion, label, extra_premise_sentence=None):
    sentences = ["Birds imply flying."]
    if extra_premise_sentence:
        sentences.append(extra_premise_sentence)
    return DatasetExample(
        id="logicbench:BQA:test:bird:1:0",
        nl_premises=tuple(sentences),
        fol_premises=(),
        nl_conclusion=nl_conclusion,
        fol_conclusion=None,
        label=label,
        known_bad=False,
        meta={"axiom": "default_reasoning_default", "logic_type": logic_type,
             "task": "BQA", "sample_id": 1, "qa_index": 0},
    )


_BIRD_TRANSLATION = {
    "Birds imply flying.": "Bird(tweety) → Flies(tweety)",
    "Tweety is a bird.": "Bird(tweety)",
    "Does tweety not fly?": "¬Flies(tweety)",
    "Does tweety fly?": "Flies(tweety)",
}


def test_nonmonotonic_route_diverges_from_classical_on_the_same_translation():
    # Nothing says Tweety IS a bird: circumscriptively Bird and Flies are
    # both minimally empty, so "Tweety does not fly" is the DEFAULT
    # conclusion (minimal_entails(..., ¬Flies, circumscribed={Bird,Flies})
    # is True, confirmed directly against semantics.nonmonotonic above).
    nm_example = _bird_example(NM_LOGIC_TYPE, "Does tweety not fly?", "yes")
    nm_result = solve_example(nm_example, translate=lambda s: _BIRD_TRANSLATION[s],
                              circumscribed={"Bird", "Flies"})
    assert nm_result["route"] == "nonmonotonic"
    assert nm_result["predicted"] == "yes"

    # The SAME translated premise, decided classically: {Bird→Flies} does
    # NOT classically entail ¬Flies (a model with Bird=Flies=True satisfies
    # the premise and refutes the goal) -- confirmed directly against
    # api.prove above (status "refuted", i.e. NOT entailed).
    classical_example = _bird_example("propositional_logic", "Does tweety not fly?", "yes")
    classical_result = solve_example(classical_example,
                                     translate=lambda s: _BIRD_TRANSLATION[s])
    assert classical_result["route"] == "classical"
    assert classical_result["verdict"]["status"] == "refuted"
    assert classical_result["predicted"] == "no"

    # Genuine divergence on the identical translated premises/hypothesis.
    assert nm_result["predicted"] != classical_result["predicted"]


def test_nonmonotonic_conclusion_is_retracted_when_bird_is_asserted():
    # Non-monotonicity itself: asserting "Tweety is a bird" FLIPS the
    # circumscriptive answer -- the earlier "does not fly" default is
    # retracted, and "flies" becomes entailed instead (confirmed directly
    # against semantics.nonmonotonic above; this is the SAME pattern
    # test_nonclassical.py's test_circumscription_is_non_monotonic pins).
    example = _bird_example(NM_LOGIC_TYPE, "Does tweety fly?", "yes",
                            extra_premise_sentence="Tweety is a bird.")
    result = solve_example(example, translate=lambda s: _BIRD_TRANSLATION[s],
                           circumscribed={"Bird", "Flies"})
    assert result["predicted"] == "yes"

    retracted = _bird_example(NM_LOGIC_TYPE, "Does tweety not fly?", "no",
                              extra_premise_sentence="Tweety is a bird.")
    retracted_result = solve_example(retracted, translate=lambda s: _BIRD_TRANSLATION[s],
                                     circumscribed={"Bird", "Flies"})
    assert retracted_result["predicted"] == "no"


#: The module docstring's "Honest limitations" case: an abnormality
#: predicate ("Ab") left FREE for jenny -- no explicit ground fact, positive
#: or negative -- with only "Bk" circumscribed (Ab stays FIXED and
#: unconstrained). Confirmed directly against semantics.nonmonotonic before
#: being pinned here: minimal_models([Tall(jenny) ∧ ∀x(Tall(x) ∧ ¬Ab(x) →
#: Bk(x))], {"Bk"}, max_size=2, extra_signature=[Bk(jenny)]) finds 18 minimal
#: models that genuinely DISAGREE on Bk(jenny) (some with Ab(jenny) true,
#: which blocks the implication and lets Bk(jenny) minimise to false; some
#: with Ab(jenny) false, which forces Bk(jenny) true -- both truth values
#: {False, True} occur), not an empty set -- this is the ambiguous case, not
#: the vacuous-entailment case test_no_minimal_model_found_is_refused_... above
#: covers. minimal_entails(...) over those same models is False (skeptical:
#: not true in EVERY minimal model found).
_AMBIGUOUS_NM_TRANSLATION = {
    "jenny is tall; whether she is an exception is not stated":
        "Tall(jenny) ∧ ∀x (Tall(x) ∧ ¬Ab(x) → Bk(x))",
    "does this entail that jenny plays basketball?": "Bk(jenny)",
}


def test_nonmonotonic_route_answers_without_flagging_disagreeing_minimal_models():
    # Documents (and pins) that solve_example does NOT detect or refuse the
    # disagreeing-minimal-models case -- only the fully-empty-model-set case
    # is refused (see test_no_minimal_model_found_is_refused_... above). A
    # translation that leaves an abnormality predicate unpinned gets a
    # confident-looking answer out of this route with no signal that the
    # question was underspecified; this test exists so the module docstring
    # and this behavior cannot silently drift apart again.
    from unicode_logic_kit import api
    from unicode_logic_kit.semantics.nonmonotonic import minimal_entails, minimal_models
    from unicode_logic_kit.semantics.tarski import models as tarski_models

    example = DatasetExample(
        id="logicbench:BQA:test:ambiguous:1:0",
        nl_premises=("jenny is tall; whether she is an exception is not stated",),
        fol_premises=(),
        nl_conclusion="does this entail that jenny plays basketball?",
        fol_conclusion=None,
        label="yes",
        known_bad=False,
        meta={"axiom": "default_reasoning_default", "logic_type": NM_LOGIC_TYPE,
             "task": "BQA", "sample_id": 1, "qa_index": 0},
    )

    result = solve_example(example, translate=lambda s: _AMBIGUOUS_NM_TRANSLATION[s],
                           circumscribed={"Bk"}, max_size=2)

    # solve_example must NOT raise here -- it silently reports a definite
    # answer, exactly as the corrected docstring says.
    assert result["route"] == "nonmonotonic"
    assert result["predicted"] in ("yes", "no")

    # Cross-check directly against semantics.nonmonotonic: the minimal
    # models genuinely disagree on the goal (both truth values occur among
    # more than one model), confirming this is the ambiguous case and that
    # solve_example's answer is exactly minimal_entails's own skeptical bool.
    prem = api.parse_any(_AMBIGUOUS_NM_TRANSLATION[example.nl_premises[0]]).formula
    goal = api.parse_any(_AMBIGUOUS_NM_TRANSLATION[example.nl_conclusion]).formula
    found = minimal_models([prem], {"Bk"}, max_size=2, extra_signature=[goal])
    assert len(found) > 1
    assert {tarski_models(goal, m) for m in found} == {False, True}
    assert result["minimal_model_count"] == len(found)
    assert result["predicted"] == (
        "yes" if minimal_entails([prem], goal, {"Bk"}, max_size=2) else "no")
    assert result["predicted"] == "no"  # skeptical: false in at least one minimal model
