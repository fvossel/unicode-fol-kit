"""The linear-time tableau on a sorted constant, and its deadline.

``c:S`` denotes an element of ``S`` at EVERY position of the word (a constant is a rigid designator), and
``Mortal(c:S)`` and ``Mortal(c)`` are one letter. Standard linear time, the first position anchoring the
formula (``mode="initial"``). Expectations derived by hand:

* ``Human(carl:Human)``, ``Ⓧ Human(carl:Human)``, ``Ⓖ Human(carl:Human)``, ``Ⓕ Human(carl:Human)`` and
  ``Mortal(carl:Human) → Human(carl:Human)`` are VALID: carl is a Human at every position.
* ``Human(carl)`` is NOT valid (a word without Human(carl) falsifies it) and neither is
  ``¬Human(carl:Human)`` (false at every position).
* With past operators and ``mode="floating"`` the anchor may have a history, and carl was a Human there
  too: ``Ⓗ Human(carl:Human)`` (historically) is valid. Without the membership of the PAST positions it
  would not be.
* A countermodel of ``P → Mortal(carl:Human)`` makes carl a Human at every position it lists.
"""

import time

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.ltl_tableau import (
    ltl_countermodel, ltl_decide, ltl_tableau_closed, ltl_valid,
)
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_fol_kit.fol.nodes import (
    And, Always, Atom, Constant, Eventually, Historically, Implies, Next, Not, Or, SortedConstant,
)

CARL_H = SortedConstant("carl", "Human")
CARL = Constant("carl")
human = lambda t: Atom("Human", [t])
mortal = lambda t: Atom("Mortal", [t])

# name -> (formula, valid by hand)
FORMULAS = {
    "Human(carl:Human)": (human(CARL_H), True),
    "Ⓧ Human(carl:Human)": (Next(human(CARL_H)), True),
    "Ⓖ Human(carl:Human)": (Always(human(CARL_H)), True),
    "Ⓕ Human(carl:Human)": (Eventually(human(CARL_H)), True),
    "Mortal(carl:Human) → Human(carl:Human)": (Implies(mortal(CARL_H), human(CARL_H)), True),
    "Mortal(carl) → Mortal(carl:Human)": (Implies(mortal(CARL), mortal(CARL_H)), True),
    "Human(carl)": (human(CARL), False),
    "¬Human(carl:Human)": (Not(human(CARL_H)), False),
}


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_the_entry_points_read_the_membership(name):
    formula, valid = FORMULAS[name]
    assert ltl_valid(formula) is valid
    assert ltl_decide(formula) == ("valid" if valid else "invalid")
    assert ltl_tableau_closed([Not(formula)]) is valid
    assert (ltl_countermodel(formula) is None) is valid


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_the_backend_answers_as_the_definition_says(name):
    # it used to REFUTE the valid ones: a word in which carl is no Human
    formula, valid = FORMULAS[name]
    verdict = api.prove(formula, [], backends=["ltl-tableau"], logic="modal")
    assert verdict.status == (PROVED if valid else REFUTED)


def test_a_premise_brings_its_membership():
    # Mortal(carl:Human) ⊢ Human(carl): one constant, annotated in the premise
    assert ltl_valid(human(CARL), [mortal(CARL_H)]) is True
    assert ltl_valid(human(CARL), [mortal(SortedConstant("carl", "Animal"))]) is False


def test_floating_mode_gives_the_membership_to_the_past_too():
    formula = Historically(human(CARL_H))
    assert ltl_valid(formula, mode="floating") is True
    assert ltl_valid(Historically(human(CARL)), mode="floating") is False


def test_a_countermodel_is_a_word_in_which_the_constant_is_in_its_sort_everywhere():
    formula = Implies(Atom("P", []), mortal(CARL_H))
    trace = ltl_countermodel(formula)
    assert trace is not None
    assert all("Human(carl)" in valuation for valuation in trace.prefix + trace.cycle)
    assert "Mortal(carl)" not in trace.at(trace.witness_position)


def _hard_formula(n):
    parts = [Or(Atom(f"P{i}", []), Next(Atom(f"P{i}", []))) for i in range(n)]
    conjunction = parts[0]
    for part in parts[1:]:
        conjunction = And(conjunction, part)
    return Not(Always(Eventually(conjunction)))


def test_the_deadline_ends_the_construction():
    # five atoms and their Next terms: a few thousand elementary atoms and their graph, seconds of work
    formula = _hard_formula(5)
    start = time.perf_counter()
    assert ltl_decide(formula, timeout=100) == "unknown"
    assert time.perf_counter() - start < 5.0
    assert ltl_valid(formula, timeout=100) is False
    assert ltl_tableau_closed([Not(formula)], timeout=100) is False


def test_the_backend_reports_a_used_up_limit_as_a_timeout():
    start = time.perf_counter()
    verdict = get_backend("ltl-tableau").decide(_hard_formula(5), [], timeout=100)
    assert time.perf_counter() - start < 5.0
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def test_a_small_instance_is_decided_within_a_generous_limit():
    assert ltl_decide(_hard_formula(3), timeout=60000) == "invalid"
