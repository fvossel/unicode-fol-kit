"""``parameterize``: every free variable of a problem becomes one constant, the same everywhere.

A free variable is a parameter of the problem (see ``tests/test_free_variables_are_parameters.py``):
``Γ(x) ⊨ φ(x)`` assignment-wise iff ``Γ(c) ⊨ φ(c)`` for a constant ``c`` that no symbol of the
problem has. The expectations are written down in each test.
"""

import pytest

from unicode_logic_kit.fol._free_parameters import free_parameter_names, parameterize
from unicode_logic_kit.fol._identifiers import symbol_names
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Number, Quantifier, SortedQuantifier,
    Variable, free_variables,
)

x, y = Variable("x"), Variable("y")
alpha = Constant("alpha")


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


def forall(var, body):
    return Quantifier("∀", var, body)


def test_one_constant_per_variable_the_same_in_every_formula():
    first, second = P(x), Atom("R", [x, y])
    closed, parameters = parameterize([first, second])
    assert set(parameters) == {"x", "y"}
    assert parameters["x"] != parameters["y"]
    assert closed[0] == P(parameters["x"])
    assert closed[1] == Atom("R", [parameters["x"], parameters["y"]])
    assert all(not free_variables(formula) for formula in closed)


def test_an_occurrence_bound_inside_a_formula_is_left_alone():
    bound = forall(x, P(x))
    closed, parameters = parameterize([P(x), bound])
    assert closed[1] == bound                      # x is bound there: not a free occurrence
    assert closed[0] == P(parameters["x"])


def test_a_formula_without_a_free_variable_comes_back_unchanged():
    sentence = forall(x, Implies(P(x), P(alpha)))
    closed, parameters = parameterize([sentence])
    assert closed == [sentence] and parameters == {}


def test_a_name_bound_in_one_formula_and_free_in_another_is_free_once():
    closed, parameters = parameterize([forall(x, P(x)), Q(x)])
    assert set(parameters) == {"x"}
    assert closed[0] == forall(x, P(x)) and closed[1] == Q(parameters["x"])


def test_the_minted_parameters_are_fresh_against_every_name_of_the_problem():
    # the spellings the minting would try first are taken: as constants, a predicate, a
    # function and a variable
    taken = [Atom("_p0", [Constant("_p1")]), Atom("S", [Function("_p2", [Constant("c")])]),
             forall(Variable("_p3"), Atom("T", [Variable("_p3")])), P(x), Q(y)]
    closed, parameters = parameterize(taken)
    names = symbol_names(*taken)
    for constant in parameters.values():
        assert constant.name not in names
    assert len({c.name for c in parameters.values()}) == 2


def test_the_avoid_argument_keeps_the_parameters_off_a_vocabulary_that_is_added_later():
    _, plain = parameterize([P(x)])
    _, avoiding = parameterize([P(x)], avoid={plain["x"].name})
    assert avoiding["x"] != plain["x"]


def test_named_after_the_variable():
    closed, parameters = parameterize([P(x), Q(y)], after_variables=True)
    assert parameters == {"x": Constant("x"), "y": Constant("y")}
    assert closed == [P(Constant("x")), Q(Constant("y"))]


def test_a_parameter_that_would_be_a_constant_of_the_problem_is_refused_by_name():
    clash = Atom("R", [x, Constant("x")])          # the text ``R(x, c_x)``
    with pytest.raises(NotImplementedError, match="free variable 'x' and a constant 'x'"):
        parameterize([clash], after_variables=True)
    closed, parameters = parameterize([clash])     # minted names never clash
    assert closed[0].args[1] == Constant("x") and closed[0].args[0] == parameters["x"]


def test_a_counting_binder_and_a_sorted_binder_bind_their_variable():
    counted = Count("ge", Number(2), x, P(x))
    sorted_ = SortedQuantifier("∀", x, "S", P(x))
    assert free_parameter_names([counted, sorted_]) == ()
    assert free_parameter_names([counted, Q(x)]) == ("x",)
    assert free_parameter_names([And(P(x), Q(y))]) == ("x", "y")
