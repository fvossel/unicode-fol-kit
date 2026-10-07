"""A cardinality ``|{x : φ}|`` is a natural number, never an individual of the domain.

The evaluator counts the elements that satisfy ``φ``. That count compares with a number (a numeral
or another count) and with nothing else: as the argument of a predicate or of a function it would
have to be read as the element of the domain that happens to share its value, which is another
statement (the count 1 as the element 1) and one that changes when the domain is named differently.
The ASP encoding, the MiniZinc encoding and ``model_eval`` refuse these forms by name; the Tarski
evaluator and the finite model finder refuse them too, instead of answering with a structure of a
question nobody asked.

Every expectation is derived by hand.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.clingo_backend import ClingoBackend
from unicode_logic_kit.fol.nodes import (
    And, Atom, Cardinality, Constant, Function, Implies, Number, Quantifier, SortedCardinality,
    Variable,
)
from unicode_logic_kit.semantics import modelfinder, nonmonotonic, secondorder
from unicode_logic_kit.semantics.tarski import Structure, models, satisfies, term_value

x, y = Variable("x"), Variable("y")
alice = Constant("alice")


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


def R(*terms):
    return Atom("R", list(terms))


COUNT_P = Cardinality(x, P(x))
COUNT_Q = Cardinality(y, Q(y))
FORALL_R = Quantifier("∀", y, R(y))

# domain {0, 1, 2}; P = {0, 1} so |P| = 2; Q = {2} so |Q| = 1; alice is the element 2
WORLD = Structure([0, 1, 2], constants={"alice": 2},
                  predicates={("P", 1): {(0,), (1,)}, ("Q", 1): {(2,)}, ("R", 1): {(2,)}})


# --------------------------------------------------------------------------- #
# the arithmetic reading is kept
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("formula,expected", [
    (Atom("=", [COUNT_P, Number(2)]), True),
    (Atom("=", [Number(2), COUNT_P]), True),
    (Atom("=", [COUNT_P, Number(1)]), False),
    (Atom("≠", [COUNT_P, Number(1)]), True),
    (Atom(">", [COUNT_P, COUNT_Q]), True),           # 2 > 1
    (Atom("≥", [COUNT_Q, Number(2)]), False),        # 1 >= 2
    (Atom("<", [COUNT_Q, Number(2)]), True),         # 1 < 2
    (Atom("≤", [COUNT_P, COUNT_P]), True),
    (Atom("=", [COUNT_P, COUNT_P]), True),
])
def test_a_cardinality_compared_with_a_number_is_counted(formula, expected):
    assert satisfies(formula, WORLD) is expected
    assert models(formula, WORLD) is expected


def test_a_comparison_inside_the_matrix_of_a_cardinality_is_a_comparison_too():
    # the x with exactly one Q: there are no x satisfying "|Q| = 1 and P(x)" other than 0 and 1
    inner = Cardinality(x, And(Atom("=", [COUNT_Q, Number(1)]), P(x)))
    assert satisfies(Atom("=", [inner, Number(2)]), WORLD) is True


def test_the_model_finder_still_finds_a_structure_with_a_given_count():
    structure = modelfinder.find_model([Atom("=", [COUNT_P, Number(2)])], max_size=3)
    assert structure is not None
    assert sum(1 for d in structure.domain if (d,) in structure.predicates[("P", 1)]) == 2
    # and a count that no structure of the searched sizes has is not found
    assert modelfinder.find_model([Atom("≥", [COUNT_P, Number(4)])], max_size=3) is None


# --------------------------------------------------------------------------- #
# a cardinality as an individual is refused by name
# --------------------------------------------------------------------------- #

def test_the_model_finder_refuses_a_cardinality_as_the_argument_of_a_predicate():
    # ∀y R(y) ⊢ R(|{x : P(x)}|): a countermodel here would make the count an element of the domain
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        modelfinder.find_countermodel([FORALL_R], R(COUNT_P), max_size=3)
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        modelfinder.is_valid_finite(Implies(FORALL_R, R(COUNT_P)), max_size=3)
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        modelfinder.find_model([R(COUNT_P)], max_size=3)


def test_the_prove_surface_does_not_refute_it():
    verdict = api.prove(R(COUNT_P), [FORALL_R], backends=["modelfinder"], timeout=10000, max_size=3)
    assert verdict.status == "unknown"
    assert "modelfinder:unknown/unsupported" in (verdict.detail or "")
    assert "argument of the predicate 'R'" in (verdict.detail or "")


def test_the_refusal_comes_before_the_search_whatever_the_bounds():
    # a size bound under which nothing is searched must not turn the refusal into "no model found"
    with pytest.raises(NotImplementedError):
        modelfinder.find_model([R(COUNT_P)], max_size=1, max_candidates=0)
    with pytest.raises(NotImplementedError):
        modelfinder.is_size_exhaustive([R(COUNT_P)], 2)


def test_the_refusal_names_the_cardinality_and_what_to_do():
    with pytest.raises(NotImplementedError) as refused:
        modelfinder.find_model([R(COUNT_P)])
    message = str(refused.value)
    assert "|{x : P(x)}|" in message and "natural number" in message
    assert "compared with a number" in message or "compare it" in message.lower()


def test_a_cardinality_as_the_argument_of_a_function_is_refused():
    with pytest.raises(NotImplementedError, match="argument of the function 'f'"):
        modelfinder.find_model([R(Function("f", [COUNT_P]))], max_size=2)


def test_a_sorted_cardinality_is_a_number_too():
    counted = SortedCardinality(x, "S", P(x))
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        modelfinder.find_model([R(counted)], max_size=2)
    structure = modelfinder.find_model([Atom("=", [counted, Number(1)])], max_size=2)
    assert structure is not None


def test_the_evaluator_refuses_the_count_read_as_the_element_that_shares_its_value():
    # |P| = 2 and alice is the element 2: R holds of alice. Read as an individual the count 2
    # would be alice, and R(|P|) would come out true; no domain naming makes it so.
    formula = R(COUNT_P)
    assert not any(isinstance(d, str) for d in WORLD.domain)
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        satisfies(formula, WORLD)
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        models(formula, WORLD)
    # the same structure with the elements renamed would have answered otherwise
    renamed = Structure(["a", "b", "c"], constants={"alice": "c"},
                        predicates={("P", 1): {("a",), ("b",)}, ("R", 1): {("c",)}})
    with pytest.raises(NotImplementedError):
        satisfies(formula, renamed)


@pytest.mark.parametrize("predicate", ["=", "≠", ">", "<", "≥", "≤"])
def test_a_cardinality_compared_with_an_individual_is_refused(predicate):
    # alice is the element 2 and |P| is 2: "|P| = alice" would be true and "|P| > alice" false
    for formula in (Atom(predicate, [COUNT_P, alice]), Atom(predicate, [alice, COUNT_P]),
                    Atom(predicate, [COUNT_P, x]),
                    Atom(predicate, [COUNT_P, Function("f", [alice])])):
        with pytest.raises(NotImplementedError, match="compares a cardinality with"):
            satisfies(formula, WORLD, {"x": 2})
    with pytest.raises(NotImplementedError, match="compares a cardinality with"):
        modelfinder.find_model([Atom(predicate, [COUNT_P, alice])], max_size=3)


def test_the_evaluator_asked_directly_for_the_value_of_a_cardinality_refuses():
    with pytest.raises(NotImplementedError, match="evaluated as an individual"):
        term_value(COUNT_P, WORLD, {})


def test_the_check_does_not_touch_a_formula_without_a_cardinality():
    assert satisfies(And(R(alice), Quantifier("∃", x, P(x))), WORLD) is True


# --------------------------------------------------------------------------- #
# the other routes that read the same evaluator
# --------------------------------------------------------------------------- #

def test_the_second_order_search_refuses_it():
    sentence = Implies(FORALL_R, R(COUNT_P))
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        secondorder.so_is_valid_finite(sentence, max_size=3)
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        secondorder.so_find_model(R(COUNT_P), max_size=2)


def test_circumscription_refuses_it():
    with pytest.raises(NotImplementedError, match="argument of the predicate 'R'"):
        nonmonotonic.minimal_entails([FORALL_R], R(COUNT_P), {"P"}, max_size=3)


def test_the_clingo_route_refuses_it_by_name_too():
    pytest.importorskip("clingo")
    verdict = ClingoBackend().decide(R(COUNT_P), [FORALL_R], max_size=3)
    assert verdict.status == "unknown" and verdict.reason == "unsupported"


@pytest.mark.parametrize("make", [
    lambda: R(COUNT_P),
    lambda: R(Function("f", [COUNT_P])),
    lambda: Atom("=", [COUNT_P, alice]),
])
def test_the_finite_routes_agree_on_what_they_refuse(make):
    formula = make()
    with pytest.raises(NotImplementedError):
        modelfinder.find_model([formula], max_size=2)
    pytest.importorskip("clingo")
    verdict = ClingoBackend().decide(formula, [], max_size=2)
    assert verdict.status == "unknown" and verdict.reason == "unsupported"
