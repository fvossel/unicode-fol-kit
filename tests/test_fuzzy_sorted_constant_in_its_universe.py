"""The fuzzy routes refuse a sorted constant that the universe given for its sort does not hold.

``c:S`` denotes an element of ``S``, and on the fuzzy routes an element of a universe is named by its constant.
So ``(∀x:Person Tall(x)) → Tall(alice:Person)`` is valid: the infimum over Person is at most the degree at
``alice``, an element of Person. A caller who gives ``sort_universes = {"Person": {"carol"}}`` has given a
universe that contradicts the formula's own constant. Decided anyway, the quantifier ranges over ``carol``
only, ``Tall(carol) = 1`` and ``Tall(alice) = 0`` make the implication ``1 → 0``, degree 0, and the valid
formula comes out not valid. The routes refuse the input by name instead.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.z3_fuzzy import fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid
from unicode_fol_kit.semantics.fuzzy import check_sorted_constants, evaluate

PARSER = MSFLParser(many_sorted=True, fuzzy=True)
FORMULA = PARSER.parse("(∀x:Person Tall(x)) → Tall(alice:Person)")
WITH_ALICE = {"Person": {"alice", "carol"}}
WITHOUT_ALICE = {"Person": {"carol"}}
REFUSAL = r"the sorted constant alice:Person names an element that sort_universes\['Person'\] = \['carol'\] does not hold"


@pytest.mark.parametrize("tnorm", ["lukasiewicz", "godel"])
def test_the_formula_is_valid_over_a_universe_that_holds_the_constant(tnorm):
    assert fuzzy_is_valid(FORMULA, tnorm=tnorm, sort_universes=WITH_ALICE) is True
    assert fuzzy_is_valid(FORMULA, tnorm=tnorm, sort_universes={"Person": {"alice"}}) is True


@pytest.mark.parametrize("decide", [fuzzy_is_valid, fuzzy_is_satisfiable, fuzzy_get_model])
def test_the_deciders_refuse_a_universe_without_the_constant(decide):
    with pytest.raises(ValueError, match=REFUSAL):
        decide(FORMULA, sort_universes=WITHOUT_ALICE)


def test_the_evaluator_refuses_it_too():
    valuation = {"Tall(carol)": 1.0, "Tall(alice)": 0.0}
    with pytest.raises(ValueError, match=REFUSAL):
        evaluate(FORMULA, valuation, sort_universes=WITHOUT_ALICE)
    # with alice in the universe the degree is 1: min(1.0, 0.0) = 0.0 ≤ 0.0
    assert evaluate(FORMULA, valuation, sort_universes=WITH_ALICE) == 1.0


def test_a_sort_without_a_universe_puts_no_condition_on_its_constants():
    ground = PARSER.parse("Tall(alice:Person)")
    check_sorted_constants(ground, None, "here")
    check_sorted_constants(ground, {}, "here")
    check_sorted_constants(ground, {"Animal": {"rex"}}, "here")
    assert evaluate(ground, {"Tall(alice)": 0.25}) == 0.25
    assert evaluate(ground, {"Tall(alice)": 0.25}, sort_universes={"Animal": {"rex"}}) == 0.25
