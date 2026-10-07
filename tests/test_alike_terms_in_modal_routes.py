"""A modal route that files a valuation or a relation by a written name does not merge two terms.

A valuation is keyed by the text an atom prints as, and the relation of an agent's operator is
named after the agent (``"K:" + name``). Two different terms that print alike would be ONE key,
and a route that read them as one would answer about another problem:

* ``□P(1) → □P('1')`` (the numeral ``1`` and a constant named ``1``) has the countermodel "one
  reflexive world, ``P`` true of the numeral and false of the constant", so a search that ends
  with "no countermodel" has not looked at the formula;
* ``K_1 P → K_'1' P`` is about two agents, so it is not valid: worlds {0, 1}, the relation of
  agent ``1`` empty, the relation of agent ``'1'`` is {(0, 1)}, ``P`` false at 1. A tableau that
  files both operators under one relation closes the branch and calls the formula valid.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.kripke_enum import modal_enum_search
from unicode_logic_kit.atp.modal_tableau import modal_decide, modal_prove
from unicode_logic_kit.fol._msfl_nodes import SortedConstant
from unicode_logic_kit.fol.modal_translation import hybrid_is_valid, standard_translation
from unicode_logic_kit.fol.nodes import (
    Atom, Believes, Box, Constant, Implies, Knows, Number, Variable)
from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal

P = Atom("P", [])


def p(term):
    return Atom("P", [term])


ALIKE = {
    "numeral and constant": (Number(1), Constant("1")),
    "free variable and constant": (Variable("x"), Constant("x")),
}
alike = pytest.mark.parametrize("left, right", list(ALIKE.values()), ids=list(ALIKE))


# ---------------------------------------------------------------------------
# The enumerator of finite models does not say "no countermodel" about a formula it cannot read
# ---------------------------------------------------------------------------

@alike
def test_the_enumerator_does_not_exhaust_a_formula_with_two_atoms_that_print_alike(left, right):
    result = modal_enum_search(Implies(Box(p(left)), Box(p(right))))
    assert result.model is None
    assert result.exhausted is False
    assert result.unsupported is not None and "two different atoms" in result.unsupported


@alike
def test_the_enumerator_does_not_exhaust_a_formula_with_two_agents_that_print_alike(left, right):
    result = modal_enum_search(Implies(Knows(left, P), Knows(right, P)))
    assert result.model is None and result.exhausted is False
    assert result.unsupported is not None and "two different agents" in result.unsupported


def test_the_enumerator_still_refutes_and_exhausts_a_formula_without_such_a_pair():
    # P(1) → □P(1) is not valid: two worlds, world 0 has P(1) and an edge to world 1 without it
    invalid = modal_enum_search(Implies(p(Number(1)), Box(p(Number(1)))))
    assert invalid.model is not None
    # □P(1) -> □P(1.0): the numeral has one spelling, so this is valid and the search is exhausted
    valid = modal_enum_search(Implies(Box(p(Number(1))), Box(p(Number(1.0)))))
    assert valid.model is None and valid.exhausted is True and valid.unsupported is None


# ---------------------------------------------------------------------------
# The labelled tableau does not close a branch for two agents it files under one relation
# ---------------------------------------------------------------------------

@alike
def test_the_tableau_refuses_a_formula_about_two_agents_that_print_alike(left, right):
    with pytest.raises(NotImplementedError, match="two different agents"):
        modal_decide(Implies(Knows(left, P), Knows(right, P)))
    with pytest.raises(NotImplementedError, match="two different agents"):
        modal_prove([Knows(left, P)], Knows(right, P))


@alike
def test_api_prove_does_not_prove_the_conclusion_of_another_agent(left, right):
    for backends in (None, ["modal-tableau"]):
        kwargs = {"backends": backends} if backends else {}
        verdict = api.prove(Knows(right, P), [Knows(left, P)], timeout=8000, **kwargs)
        assert verdict.status != "proved", backends


def test_two_agents_of_different_names_are_two_agents_and_one_agent_is_one():
    a, b = Constant("a"), Constant("b")
    assert modal_decide(Implies(Knows(a, P), Knows(a, P))) == "valid"
    assert modal_decide(Implies(Knows(a, P), Knows(b, P))) == "invalid"
    # the same agent under two operators is one agent
    assert modal_decide(Implies(Knows(a, Believes(a, P)), Knows(a, Believes(a, P)))) == "valid"


# ---------------------------------------------------------------------------
# The first-order image of a modal formula names one relation per agent
# ---------------------------------------------------------------------------

@alike
def test_the_standard_translation_refuses_two_agents_that_print_alike(left, right):
    formula = Implies(Knows(left, P), Knows(right, P))
    with pytest.raises(NotImplementedError, match="two different agents"):
        standard_translation(formula)
    # it is the hybrid route's only path to a verdict: K_1 P → K_'1' P is not valid (two agents)
    with pytest.raises(NotImplementedError, match="two different agents"):
        hybrid_is_valid(formula)


def test_the_hybrid_route_still_tells_two_agents_of_different_names_apart():
    a, b = Constant("a"), Constant("b")
    assert hybrid_is_valid(Implies(Knows(a, P), Knows(a, P))) is True
    assert hybrid_is_valid(Implies(Knows(a, P), Knows(b, P))) is False


# ---------------------------------------------------------------------------
# A sorted constant is the constant: one key in a graded model as well
# ---------------------------------------------------------------------------

def test_a_graded_model_reads_a_sorted_constant_at_the_key_of_the_plain_constant():
    model = FuzzyKripkeModel(worlds={0}, valuation={0: {"Tall(alice)": 0.7}})
    plain = Atom("Tall", [Constant("alice")])
    sorted_atom = Atom("Tall", [SortedConstant("alice", "Person")])
    assert satisfies_fuzzy_modal(plain, model, 0) == pytest.approx(0.7)
    assert satisfies_fuzzy_modal(sorted_atom, model, 0) == pytest.approx(0.7)
    # the key with the sort is no key
    other = FuzzyKripkeModel(worlds={0}, valuation={0: {"Tall(alice:Person)": 0.7}})
    assert satisfies_fuzzy_modal(sorted_atom, other, 0) == 0.0
