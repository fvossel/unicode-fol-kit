"""The Isabelle free-logic writer keeps a numeral and a constant spelled like it apart.

A numeral is a constant of its own, identified by its value (``Number(1)`` is ``Number(1.0)``),
and the higher-order writers name it ``n1``. A user constant spelled ``n1`` is another symbol, so
a writer that gave both the name ``n1`` (ONE ``consts n1 :: "e"`` used for both) would make
``P(1)`` and ``Q(n1)`` talk about one element: a theory that proves things about the constant
that are false of the numeral. Every writer (``to_isabelle_fol``, ``to_thf_free``,
``to_isabelle_free``, ...) refuses the pair by name.

The expectations are the definition above, applied by hand to the text the writer returns.
"""

import pytest

from unicode_fol_kit.fol.nodes import And, Atom, Constant, Number
from unicode_fol_kit.hol import free_theory, to_isabelle_free, to_thf_free


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


@pytest.mark.parametrize("writer", [to_isabelle_free, free_theory, to_thf_free])
def test_a_numeral_next_to_a_constant_spelled_like_it_is_refused_by_name(writer):
    clash = And(P(Number(1)), Q(Constant("n1")))
    with pytest.raises(NotImplementedError) as raised:
        writer(clash)
    message = str(raised.value)
    assert "number 1" in message and "'n1'" in message and "alike" in message


def test_the_refusal_names_the_writer():
    with pytest.raises(NotImplementedError, match="to_isabelle_free"):
        to_isabelle_free(And(P(Number(1)), Q(Constant("n1"))))


def test_a_fractional_numeral_is_refused_next_to_its_spelling_too():
    with pytest.raises(NotImplementedError, match="2.5"):
        to_isabelle_free(And(P(Number(2.5)), Q(Constant("n2.5"))))


def test_the_bare_spelling_of_a_numeral_is_refused_too():
    # The canonical text of the numeral is '1': a constant of that name is a clash as well.
    with pytest.raises(NotImplementedError):
        to_isabelle_free(And(P(Number(1)), Q(Constant("1"))))


def test_a_constant_spelled_like_no_numeral_of_the_formula_is_accepted():
    # Number(1.0) is Number(1), so the numeral is n1; a constant n2 is no numeral of the formula.
    text = to_isabelle_free(And(P(Number(1.0)), Q(Constant("n2"))))
    assert text.count('consts n1 :: "e"') == 1
    assert text.count('consts n2 :: "e"') == 1


def test_a_numeral_is_one_constant_per_value():
    one = to_isabelle_free(P(Number(1)))
    assert one == to_isabelle_free(P(Number(1.0)))
    assert one.count('consts n1 :: "e"') == 1
    assert "(p n1)" in one
    two = to_isabelle_free(And(P(Number(1)), Q(Number(2))))
    assert two.count('consts n1 :: "e"') == 1
    assert two.count('consts n2 :: "e"') == 1
    assert "(p n1)" in two and "(q n2)" in two


def test_a_numeral_that_is_not_a_number_is_a_value_error():
    with pytest.raises(ValueError):
        to_isabelle_free(P(Number(float("inf"))))
