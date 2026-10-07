# -*- coding: utf-8 -*-
"""Under the integer sort a numeral that is not an integer is refused by name, never read as its integer part.

No integer is ``2.5``. Z3's ``IntVal(2.5)`` takes the integer part, so ``2.5 = 2`` was valid under
``sort="int"`` and ``2.5 = c`` had the model ``c = 2``: both wrong. By hand:

* under ``sort="int"`` the numeral ``2.5`` has no literal, so each function of the module refuses a formula
  that holds one (``NotImplementedError``), and does not answer a question about another formula;
* under ``sort="real"`` the same formulas are decided as they always were: ``2.5 = 2`` is not valid (5/2 is
  not 2) and ``2.5 = c`` has exactly the model ``c = 5/2``;
* a whole numeral is an integer under both sorts, whatever way it was written: ``Number(2.0)`` is
  ``Number(2)``, so ``2.0 = c`` has the model ``c = 2`` under ``sort="int"``.
"""

import pytest
import z3

from unicode_logic_kit.atp.z3_arith import (
    ArithEnv, get_model_arith, is_satisfiable_arith, is_valid_arith, to_z3_arith,
)
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Number, Quantifier, Variable

EQ_25_2 = Atom("=", [Number(2.5), Number(2)])
EQ_25_C = Atom("=", [Number(2.5), Constant("cc")])
SOME_ABOVE = Quantifier("∃", Variable("x"), Atom(">", [Variable("x"), Number(2.5)]))
INSIDE_A_TERM = Atom("=", [Function("+", [Constant("cc"), Number(0.5)]), Number(3)])


@pytest.mark.parametrize("formula", [EQ_25_2, EQ_25_C, SOME_ABOVE, INSIDE_A_TERM])
def test_every_function_refuses_a_fractional_numeral_under_the_integer_sort(formula):
    for function in (is_valid_arith, is_satisfiable_arith, get_model_arith):
        with pytest.raises(NotImplementedError, match="2.5|0.5"):
            function(formula, sort="int")
    with pytest.raises(NotImplementedError):
        to_z3_arith(formula, sort="int")


def test_the_refusal_names_the_numeral_and_the_way_out():
    with pytest.raises(NotImplementedError) as refused:
        is_valid_arith(EQ_25_2, sort="int")
    message = str(refused.value)
    assert "2.5" in message and "sort='real'" in message


def test_the_environment_refuses_it_where_the_literal_is_made():
    env = ArithEnv("int")
    assert env.num(3).as_long() == 3
    with pytest.raises(NotImplementedError):
        env.num(2.5)


def test_the_same_formulas_are_decided_under_the_real_sort():
    assert is_valid_arith(EQ_25_2, sort="real") is False          # 5/2 is not 2
    assert get_model_arith(EQ_25_C, sort="real") == {"cc": "5/2"}   # c must be 5/2
    assert is_satisfiable_arith(SOME_ABOVE, sort="real") is True    # 3 is above 2.5
    assert is_satisfiable_arith(INSIDE_A_TERM, sort="real") is True  # c = 2.5
    assert z3.is_true(z3.simplify(to_z3_arith(Atom("=", [Number(2.5), Number(2.5)]), sort="real")))


def test_a_whole_numeral_is_an_integer_however_it_was_written():
    assert Number(2.0) == Number(2)
    assert get_model_arith(Atom("=", [Number(2.0), Constant("cc")]), sort="int") == {"cc": "2"}
    assert is_valid_arith(Atom("=", [Number(4.0), Function("+", [Number(2), Number(2)])]), sort="int") is True


def test_integers_are_decided_under_the_integer_sort():
    # x + 1 = 2 ∧ x > 0 has the model x = 1, and x + x = 1 has none among the integers
    assert is_satisfiable_arith(Atom("=", [Function("+", [Constant("cc"), Constant("cc")]), Number(1)]),
                                sort="int") is False
    assert is_satisfiable_arith(Atom("=", [Function("+", [Constant("cc"), Constant("cc")]), Number(1)]),
                                sort="real") is True
