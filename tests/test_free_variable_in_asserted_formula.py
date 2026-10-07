"""An exporter that writes one formula as an ASSERTED axiom does not close a free variable.

A free variable is a parameter of the problem: one unknown individual, the same in every formula.
Closing it universally is the same thing as the parameter reading only for a formula that stands
alone as a goal (the formula is valid for the parameter iff it is valid for every individual).
An axiom is a premise of a larger problem, and there the two readings part:

* the premise ``∀x P(x)`` entails ``P(a)`` (instantiate ``x := a``);
* the premise ``P(x)`` does not: universe ``{0, 1}``, ``x`` ↦ 1, ``a`` ↦ 0, ``P`` = ``{1}``.

So ``to_thf_fol`` / ``to_thf_msfol`` / ``to_lean_fol`` / ``to_lean_msfol`` with ``conjecture=False``
refuse a formula with a free variable by name, and say how to state the parameter (a constant,
or a quantifier). With ``conjecture=True`` (the default) the closure stays: for one formula with
no premise it is the parameter reading itself. The Isabelle writer states a lemma, which is a
goal, and has no asserted role.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Implies, Quantifier, SortedQuantifier, Variable,
)
from unicode_logic_kit.hol.classical import (
    to_isabelle_fol, to_isabelle_msfol, to_thf_fol, to_thf_msfol,
)
from unicode_logic_kit.hol.lean import to_lean_fol, to_lean_msfol

x, y = Variable("x"), Variable("y")
alpha = Constant("alpha")


def P(term):
    return Atom("P", [term])


def forall(var, body):
    return Quantifier("∀", var, body)


WRITERS = [to_thf_fol, to_thf_msfol, to_lean_fol, to_lean_msfol]
IDS = [w.__name__ for w in WRITERS]


def test_the_premise_with_a_free_variable_is_not_the_closed_premise():
    # the reason for the refusal, by Z3: ∀x P(x) ⊢ P(alpha) but P(x) ⊬ P(alpha)
    assert api.prove(P(alpha), [forall(x, P(x))], backends=["z3"]).status == "proved"
    assert api.prove(P(alpha), [P(x)], backends=["z3"]).status == "refuted"


@pytest.mark.parametrize("writer", WRITERS, ids=IDS)
def test_an_asserted_formula_with_a_free_variable_is_refused_by_name(writer):
    with pytest.raises(NotImplementedError) as info:
        writer(P(x), conjecture=False)
    message = str(info.value)
    assert message.startswith(writer.__name__ + ":")
    assert "free variable 'x'" in message
    assert "conjecture=True" in message                 # how to get the goal reading
    assert "constant" in message and "quantifier" in message   # how to state the parameter


@pytest.mark.parametrize("writer", WRITERS, ids=IDS)
def test_every_free_variable_of_an_asserted_formula_is_named(writer):
    formula = Implies(P(x), forall(Variable("z"), Atom("Q", [y, Variable("z")])))
    with pytest.raises(NotImplementedError, match="'x', 'y'"):
        writer(formula, conjecture=False)


@pytest.mark.parametrize("writer", WRITERS, ids=IDS)
def test_a_variable_free_outside_a_quantifier_that_binds_its_name_is_refused(writer):
    # P(x) ∧ ∀x P(x): the first x is free
    formula = And(P(x), forall(x, P(x)))
    with pytest.raises(NotImplementedError, match="free variable 'x'"):
        writer(formula, conjecture=False)


@pytest.mark.parametrize("writer", WRITERS, ids=IDS)
def test_a_closed_asserted_formula_is_written(writer):
    assert "axiom" in writer(forall(x, P(x)), conjecture=False)
    assert "axiom" in writer(P(alpha), conjecture=False)


@pytest.mark.parametrize("writer", WRITERS, ids=IDS)
def test_a_goal_with_a_free_variable_keeps_its_closure(writer):
    # one formula, no premise: the closure is the parameter reading
    text = writer(P(x))
    if writer in (to_thf_fol, to_thf_msfol):
        assert "thf(goal, conjecture, ( ! [X: $i] : ( p @ X ) ))." in text
    else:
        assert "theorem goal : (∀ x : Ind, (p x)) := by" in text


def test_the_asserted_closed_formula_text_is_the_one_it_was():
    assert "thf(goal, axiom, ( ! [X: $i] : ( p @ X ) ))." in to_thf_fol(
        forall(x, P(x)), conjecture=False)
    assert "axiom goal : (∀ x : Ind, (p x))" in to_lean_fol(forall(x, P(x)), conjecture=False)


def test_a_many_sorted_asserted_formula_with_a_free_variable_is_refused():
    formula = Implies(P(x), SortedQuantifier("∃", y, "Thing", P(y)))
    with pytest.raises(NotImplementedError, match="to_thf_msfol: .*free variable 'x'"):
        to_thf_msfol(formula, conjecture=False)
    with pytest.raises(NotImplementedError, match="to_lean_msfol: .*free variable 'x'"):
        to_lean_msfol(formula, conjecture=False)


def test_the_isabelle_writers_state_a_lemma_whatever_the_formula_has_free():
    for writer in (to_isabelle_fol, to_isabelle_msfol):
        assert 'lemma goal: "(p x)"' in writer(P(x))
