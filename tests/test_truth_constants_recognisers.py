"""The recognisers of the two truth constants (``unicode_fol_kit.fol._truth_constants``).

``$true`` and ``$false`` are the NULLARY atoms. The same name WITH arguments is an
ordinary predicate that happens to be spelled like a reserved word, and is neither
constant.
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Constant, And, Or, Implies
from unicode_fol_kit.fol._truth_constants import (
    TRUE, FALSE, truth_value, is_true_constant, is_false_constant, is_truth_constant,
    truth_constants_in, refuse_truth_constants,
)

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())


def test_recognisers():
    assert truth_value(T) is True and truth_value(F) is False
    assert truth_value(P) is None
    assert is_true_constant(T) and not is_true_constant(F)
    assert is_false_constant(F) and not is_false_constant(T)
    assert is_truth_constant(T) and is_truth_constant(F) and not is_truth_constant(P)
    assert TRUE == T and FALSE == F


def test_a_node_that_is_not_an_atom_is_no_constant():
    assert truth_value(And(T, F)) is None
    assert truth_value(Constant("a")) is None


def test_the_name_with_arguments_is_an_ordinary_predicate():
    # `$true(a)` is a predicate that happens to be spelled like the constant
    odd = Atom("$true", [Constant("a")])
    assert truth_value(odd) is None
    assert not is_truth_constant(odd)


def test_truth_constants_in_collects_each_once_in_order():
    formula = Implies(And(F, T), Or(F, P))
    assert truth_constants_in([formula]) == (F, T)
    assert truth_constants_in([P]) == ()


def test_refusal_names_the_route_the_constant_and_the_reason():
    with pytest.raises(NotImplementedError) as info:
        refuse_truth_constants([Or(P, T)], "some_route", "because of the reason given")
    message = str(info.value)
    assert "some_route" in message
    assert "$true" in message
    assert "because of the reason given" in message


def test_refusal_names_every_constant_that_occurs():
    with pytest.raises(NotImplementedError) as info:
        refuse_truth_constants([Implies(F, T)], "some_route", "why")
    assert "$false" in str(info.value) and "$true" in str(info.value)


def test_refusal_uses_the_error_class_it_is_given():
    with pytest.raises(TypeError):
        refuse_truth_constants([F], "some_route", "why", error=TypeError)
    # and says nothing when there is no constant
    assert refuse_truth_constants([P, And(P, P)], "some_route", "why") is None
