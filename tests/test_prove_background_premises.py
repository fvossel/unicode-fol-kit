# -*- coding: utf-8 -*-
"""The premises ``api.prove`` reports as relevant are the caller's own: side axioms are background.

A :class:`~unicode_logic_kit.logic.Sentence` that is handed to ``api.prove`` brings its side axioms with it
(the non-emptiness of a sort, the membership atom of a sorted constant, a frame condition); they are
appended to the premises of every backend, after the caller's own. Like the sentences of ``signature=``
they are background, not premises the caller gave, and an index that comes back is an index into the
CALLER's list: ``relevant_premises`` and the premise tags of the Z3 core name nothing past it.

By hand: the premises ``Bird(tweety)`` (index 0) and the sentence whose term is
``∀x (Human(x) → Mortal(x))`` (index 1) and whose side axiom is ``Human(socrates)`` entail
``Mortal(socrates)``, and what the proof needs is the rule (index 1) and the side axiom; the bird is
irrelevant. The relevant premises are ``(1,)`` -- the side axiom is needed, and it is not a premise.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import PROVED, get_backend
from unicode_logic_kit.fol.signature import Signature
from unicode_logic_kit.logic import Sentence


def F(text):
    parsed = api.parse_any(text)
    assert parsed.ok, (text, parsed)
    return parsed.formula


BIRD = F("Bird(tweety)")
RULE = F("∀x (Human(x) → Mortal(x))")
MEMBERSHIP = F("Human(socrates)")
GOAL = F("Mortal(socrates)")
SENTENCE = Sentence(term=RULE, logic="fol", axioms=(MEMBERSHIP,))


def available(name):
    try:
        return get_backend(name).available()
    except Exception:
        return False


def test_the_side_axiom_of_a_sentence_is_not_reported_as_a_premise():
    verdict = api.prove(GOAL, [BIRD, SENTENCE], backends=["z3"], relevant_premises=True)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (1,)


def test_the_indices_follow_the_callers_order():
    verdict = api.prove(GOAL, [SENTENCE, BIRD], backends=["z3"], relevant_premises=True)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (0,)
    verdict = api.prove(GOAL, [SENTENCE], backends=["z3"], relevant_premises=True)
    assert verdict.relevant_premises == (0,)


def test_the_z3_core_names_only_the_callers_premises():
    verdict = api.prove(GOAL, [BIRD, SENTENCE], backends=["z3"])
    assert verdict.status == PROVED
    assert sorted(verdict.proof["core"]) == ["goal", "p1"]


def test_a_sentence_in_the_conclusion_brings_its_axioms_and_they_are_not_premises_either():
    # the goal Mortal(socrates) as a sentence that carries Human(socrates); the rule is the one premise
    goal = Sentence(term=GOAL, logic="fol", axioms=(MEMBERSHIP,))
    verdict = api.prove(goal, [BIRD, RULE], backends=["z3"], relevant_premises=True)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (1,)


def test_the_sentences_of_a_signature_are_background_next_to_those_of_a_sentence():
    # carl is declared in A, and the sentence says every A is a P; the premise Q(ann) is irrelevant
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    sentence = Sentence(term=F("∀x (A(x) → P(x))"), logic="fol", axioms=(F("B(dora)"),))
    verdict = api.prove(F("P(carl)"), [F("Q(ann)"), sentence], backends=["z3"],
                        signature=signature, relevant_premises=True)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (1,)


def test_a_call_without_background_reports_what_the_backend_found():
    verdict = api.prove(GOAL, [BIRD, RULE, MEMBERSHIP], backends=["z3"], relevant_premises=True)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (1, 2)


@pytest.mark.parametrize("backend", ["vampire", "eprover"])
def test_a_prover_that_names_its_axioms_reports_only_the_callers_premises(backend):
    if not available(backend):
        pytest.skip(f"{backend} is not available on this machine")
    verdict = api.prove(GOAL, [BIRD, SENTENCE], backends=[backend], relevant_premises=True,
                        timeout=30000)
    assert verdict.status == PROVED
    assert verdict.relevant_premises == (1,)
