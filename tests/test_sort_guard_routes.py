"""A sorted constant ``c:S`` lies in ``S``: the routes that decide sorted input through the guard reading.

``to_fol`` writes ``∀x:S φ`` as ``∀x (S(x) → φ)`` and the sorted constant ``c:S`` as the plain
constant ``c``; ``nonempty_sort_axioms`` says every sort is non-empty. The fact the annotation of a
constant states, ``S(c)``, comes from ``sort_axioms`` (``sort_membership_axioms``). Every route that
decides sorted input adds ``sort_axioms`` as background premises: never inside the per-formula
translation, never under the negation of the goal, and for every formula the question involves.

The definition the expectations are derived from: ONE universe; a sort is the non-empty extension of
the unary predicate of its name; sorts may overlap; ``c:S`` denotes an element of ``S`` (and ``c:S``
here and a plain ``c`` there are one constant); an unsorted constant, an unsorted variable and the
value of a function may be any element of the universe.

* ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is VALID: socrates is a Human, every Human is Mortal.
* ``∀x:Human Mortal(x) ⊢ Mortal(socrates)`` is NOT: universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1.
* ``⊢ Mortal(socrates:Human)`` is NOT: universe {0}, Human = {0}, Mortal = {}, socrates = 0. The
  membership fact is a premise, never part of what is proved.
* ``⊢ ∃x:Human x = socrates:Human`` is VALID: the sorted constant is its own witness.
* ``∀x:Foo R(x), ¬R(kay:Foo)`` is UNSATISFIABLE: kay is a Foo, so R(kay).
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.incremental import IncrementalSession
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, Z3Backend, z3_relevant_premises
from unicode_fol_kit.atp.resolution import prove as resolution_prove
from unicode_fol_kit.atp.resolution import to_clauses
from unicode_fol_kit.atp.z3_arith import (
    get_model_arith, is_satisfiable_arith, is_valid_arith,
)
from unicode_fol_kit.atp.z3_equivalence import formulas_are_equivalent
from unicode_fol_kit.atp.z3_models import get_model, is_satisfiable, is_valid
from unicode_fol_kit.eval.equivalence import equivalent
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Implies, Not, Number, SortedCardinality, SortedCount,
    Variable,
)
from unicode_fol_kit.logic import FOL, MSFOL as MSFOL_LOGIC

def F(text):
    parsed = api.parse_any(text)
    assert parsed.ok, (text, parsed)
    return parsed.formula


ALL_MORTAL = F("∀x:Human Mortal(x)")
GOAL = F("Mortal(socrates:Human)")
TAUTOLOGY = F("P ∨ ¬P")


# ---------------------------------------------------------------------------------------------
# Z3Backend and the api
# ---------------------------------------------------------------------------------------------
def test_z3_proves_that_a_sorted_constant_is_in_its_sort():
    assert api.prove(GOAL, [ALL_MORTAL], backends=["z3"]).status == PROVED


def test_the_default_chain_proves_it_too_instead_of_refuting_it():
    # z3 is the first member of the chain; before the membership fact it said "refuted".
    assert api.prove(GOAL, [ALL_MORTAL]).status == PROVED


def test_an_unsorted_constant_is_not_in_the_sort():
    verdict = api.prove(F("Mortal(socrates)"), [ALL_MORTAL], backends=["z3"])
    assert verdict.status == REFUTED          # universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1


def test_the_membership_fact_is_a_premise_and_not_part_of_the_conclusion():
    # Nothing follows about a sorted constant from nothing ...
    assert api.prove(GOAL, [], backends=["z3"]).status == REFUTED
    # ... but the constant is its own witness. Were S(c) conjoined onto the goal (and so negated with
    # it) the second would fail; were it absent the second would fail as well.
    assert api.prove(F("∃x:Human x = socrates:Human"), [], backends=["z3"]).status == PROVED


def test_membership_atoms_are_never_part_of_the_reported_unsat_core():
    verdict = Z3Backend().decide(GOAL, [ALL_MORTAL])
    assert verdict.status == PROVED
    # Neither the premise alone nor the negated goal alone is unsatisfiable, so the core is exactly
    # these two tags; Human(socrates) and "some Human exists" are untracked background.
    assert verdict.proof["core"] == ["goal", "p0"]


def test_membership_atoms_are_never_part_of_the_relevant_premise_indices():
    assert z3_relevant_premises(GOAL, [ALL_MORTAL]) == (0,)
    irrelevant = F("Bird(tweety)")
    assert z3_relevant_premises(GOAL, [irrelevant, ALL_MORTAL]) == (1,)
    assert z3_relevant_premises(GOAL, [ALL_MORTAL, irrelevant]) == (0,)
    # the same question asked through the api
    verdict = api.prove(GOAL, [ALL_MORTAL, irrelevant], backends=["z3"], relevant_premises=True)
    assert verdict.status == PROVED and verdict.relevant_premises == (0,)


# ---------------------------------------------------------------------------------------------
# z3_models
# ---------------------------------------------------------------------------------------------
def test_z3_models_validity_with_a_sorted_constant():
    assert is_valid(Implies(ALL_MORTAL, GOAL)) is True
    assert is_valid(GOAL) is False                                    # universe {0}, Mortal = {}
    assert is_valid(Implies(ALL_MORTAL, F("Mortal(socrates)"))) is False
    assert is_valid(F("∃x:Human x = socrates:Human")) is True


def test_z3_models_satisfiability_and_models_with_a_sorted_constant():
    clash = And(F("∀x:Foo R(x)"), F("¬R(kay:Foo)"))
    assert is_satisfiable(clash) is False
    assert get_model(clash) is None
    # the unsorted twin is satisfiable: universe {0, 1}, Foo = {0}, R = {0}, kay = 1
    assert is_satisfiable(And(F("∀x:Foo R(x)"), F("¬R(kay)"))) is True
    # a model of a negated goal is asked for under a Not: membership is asserted outside it
    assert get_model(Not(GOAL)) is not None
    assert get_model(Not(Implies(ALL_MORTAL, GOAL))) is None


# ---------------------------------------------------------------------------------------------
# IncrementalSession
# ---------------------------------------------------------------------------------------------
def test_incremental_session_asserts_membership():
    session = IncrementalSession([ALL_MORTAL])
    assert session.decide(GOAL).status == PROVED
    assert session.decide(F("Mortal(socrates)")).status == REFUTED


def test_incremental_session_recomputes_membership_when_a_premise_is_retracted():
    # One constant: the premise Q(socrates:Human) puts socrates in Human, so the UNSORTED goal
    # Mortal(socrates) follows from ∀x:Human Mortal(x). Retract that premise and nothing puts
    # socrates in Human any more: universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1.
    session = IncrementalSession([ALL_MORTAL])
    goal = F("Mortal(socrates)")
    assert session.decide(goal).status == REFUTED
    session.assert_premise(F("Q(socrates:Human)"))
    assert session.decide(goal).status == PROVED
    session.retract()
    assert session.decide(goal).status == REFUTED
    session.assert_premise(F("Q(socrates:Human)"))
    assert session.decide(goal).status == PROVED


# ---------------------------------------------------------------------------------------------
# equivalence: the facts of BOTH formulas
# ---------------------------------------------------------------------------------------------
def test_formulas_are_equivalent_uses_the_membership_facts_of_both_formulas():
    assert formulas_are_equivalent(F("(∀x:Human Mortal(x)) → Mortal(socrates:Human)"), TAUTOLOGY) is True
    assert formulas_are_equivalent(TAUTOLOGY, F("(∀x:Human Mortal(x)) → Mortal(socrates:Human)")) is True
    assert formulas_are_equivalent(GOAL, TAUTOLOGY) is False          # universe {0}, Mortal = {}
    # f1 says "if socrates is Human he is Mortal", f2 says he is Mortal and puts him in Human.
    # Equivalent over the structures of the pair: f2's annotation makes socrates a Human, so f1
    # reduces to Mortal(socrates). The fact comes from f2 in one order and from f1's partner in the
    # other; a route that read the facts of one formula only would miss it in one of the two.
    plain = F("Human(socrates) → Mortal(socrates)")
    assert formulas_are_equivalent(plain, GOAL) is True
    assert formulas_are_equivalent(GOAL, plain) is True


def test_the_eval_equivalence_check_uses_the_membership_facts_of_both_formulas():
    plain = F("Human(socrates) → Mortal(socrates)")
    for first, second in ((plain, GOAL), (GOAL, plain)):
        result = equivalent(first, second, method="solver")
        assert result.equivalent is True
    assert equivalent(F("(∀x:Human Mortal(x)) → Mortal(socrates:Human)"), TAUTOLOGY,
                      method="solver").equivalent is True
    refuted = equivalent(GOAL, TAUTOLOGY, method="solver")
    assert refuted.equivalent is False and refuted.counterexample is not None


# ---------------------------------------------------------------------------------------------
# the msfol -> fol comorphism edge
# ---------------------------------------------------------------------------------------------
def test_the_msfol_to_fol_edge_returns_the_membership_atoms_as_axioms():
    result = api.translate(GOAL, "msfol", "fol")
    assert [a.to_unicode_str() for a in result.axioms] == ["∃x0 Human(x0)", "Human(socrates)"]
    assert result.result.to_unicode_str() == "Mortal(socrates)"       # the image forgets the sort
    assert result.guarantee == "faithful"


def test_the_composed_translate_and_prove_path_proves_the_sorted_constant_fact():
    premise = api.translate(ALL_MORTAL, "msfol", "fol")
    goal = api.translate(GOAL, "msfol", "fol")
    background = [*premise.axioms, *goal.axioms]
    assert api.prove(goal.result, [premise.result, *background], backends=["z3"]).status == PROVED
    # Without the goal's axioms the image is the question about an unsorted constant: refuted.
    assert api.prove(goal.result, [premise.result, *premise.axioms], backends=["z3"]).status == REFUTED


def test_a_sentence_carries_the_membership_axioms_into_prove():
    premise = FOL(MSFOL_LOGIC(ALL_MORTAL))
    goal = FOL(MSFOL_LOGIC(GOAL))
    assert api.prove(goal, [premise], backends=["z3"]).status == PROVED


# ---------------------------------------------------------------------------------------------
# z3_arith
# ---------------------------------------------------------------------------------------------
def test_z3_arith_accepts_a_sorted_constant_inside_an_atom():
    assert is_valid_arith(Implies(ALL_MORTAL, GOAL)) is True
    assert is_valid_arith(GOAL) is False
    assert is_satisfiable_arith(GOAL) is True
    assert is_valid_arith(Implies(ALL_MORTAL, F("Mortal(socrates)"))) is False
    assert is_valid_arith(F("∃x:Human x = socrates:Human")) is True
    assert get_model_arith(GOAL) is not None


def test_z3_arith_reads_a_sorted_and_a_plain_constant_of_one_name_as_one_symbol():
    assert is_satisfiable_arith(And(F("P(carl:S)"), F("¬P(carl)"))) is False
    assert is_satisfiable_arith(And(F("P(carl:S)"), F("¬P(dora)"))) is True


def test_z3_arith_decides_a_sorted_constant_next_to_arithmetic():
    # kay is a Foo, every Foo is below 3, so kay < 3 (kay is one real number)
    assert is_valid_arith(Implies(F("∀x:Foo x < 3"), F("kay:Foo < 3"))) is True
    assert is_valid_arith(Implies(F("∀x:Foo x < 3"), F("kay < 3"))) is False        # kay = 5, Foo = {0}


def test_z3_arith_lowers_a_sorted_count_and_refuses_a_sorted_cardinality_by_name():
    x, y = Variable("x"), Variable("y")
    at_least_two = SortedCount("ge", Number(2), x, "S", Atom("P", [x]))
    assert is_satisfiable_arith(at_least_two) is True                  # two distinct numbers in S, both P
    one_element = F("∀x:S ∀y:S x = y")
    assert is_satisfiable_arith(And(at_least_two, one_element)) is False
    cardinality = Atom("=", [SortedCardinality(x, "S", Atom("P", [x])), Number(3)])
    with pytest.raises(NotImplementedError, match="SortedCardinality"):
        is_valid_arith(cardinality)
    with pytest.raises(NotImplementedError, match="SortedCardinality"):
        is_satisfiable_arith(cardinality)
    assert y.name == "y"          # keep the unused-variable linter quiet about the second binder


# ---------------------------------------------------------------------------------------------
# the resolution prover: a sorted constant keeps its identity, the prover gets sort_axioms
# ---------------------------------------------------------------------------------------------
def test_resolution_proves_a_sorted_constant_across_formulas():
    premises = [F("P(carl:S)"), F("∀x (P(x) → Q(x))")]
    assert resolution_prove(premises, F("Q(carl:S)"), max_steps=2000) is True


def test_resolution_clausifies_a_sorted_constant_under_its_own_name():
    # Two independently clausified formulas must talk about the SAME constant: the sorted constant
    # used to be renamed to a fresh Skolem name per formula (_sk0), and the two never met.
    assert to_clauses(F("P(carl:S)")) == {frozenset({Atom("P", [Constant("carl")])})}
    assert to_clauses(F("Q(carl:S)")) == {frozenset({Atom("Q", [Constant("carl")])})}


def test_resolution_proves_that_a_sorted_constant_is_in_its_sort():
    assert resolution_prove([ALL_MORTAL], GOAL, max_steps=2000) is True
    assert api.prove(GOAL, [ALL_MORTAL], backends=["resolution"]).status == PROVED


def test_resolution_gets_the_non_emptiness_of_a_sort():
    # ∀x:Ghost P(x) ⊢ ∃x:Ghost P(x) holds because Ghost is not empty
    assert resolution_prove([F("∀x:Ghost P(x)")], F("∃x:Ghost P(x)"), max_steps=2000) is True


def test_resolution_does_not_prove_what_the_definition_does_not_entail():
    # universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1
    assert resolution_prove([ALL_MORTAL], F("Mortal(socrates)"), max_steps=3000) is False
    # universe {0}, Human = {0}, Mortal = {}, socrates = 0: the fact is a premise, not the goal's work
    assert resolution_prove([], GOAL, max_steps=3000) is False
    # a sort with no sorted constant and no premise about it proves nothing about Mortal
    assert resolution_prove([F("∀x:Human Mortal(x)")], F("Mortal(plato:Greek)"), max_steps=3000) is False
