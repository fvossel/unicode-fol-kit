# -*- coding: utf-8 -*-
"""A function of no arguments is written as the constant of its name in TPTP.

TPTP has no empty argument list: ``f()`` is no term, and a prover stops at it with a parse error. The kit
defines a function of no arguments as the constant of its name (the problem writers write it that way), so
the text of one formula writes it that way too: ``Function('f', []).to_tptp()`` is the text of
``Constant('f').to_tptp()``, with every refusal of a constant, and the single-formula collision guard sees
it as the constant it is written as.
"""

import pytest

from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Variable
from unicode_logic_kit.fol.tptp_input import parse_tptp_formula


@pytest.mark.parametrize("name, word", [
    ("f", "f"),
    ("Foo", "foo"),            # the first letter is folded, as for a constant
    ("hasBond", "hasBond"),    # the rest of the name is kept
    ("θ", "theta"),            # a Greek letter is transliterated, as for a constant
])
def test_a_function_of_no_arguments_is_written_as_the_constant_of_its_name(name, word):
    assert Function(name, []).to_tptp() == word
    assert Function(name, []).to_tptp() == Constant(name).to_tptp()


def test_no_empty_argument_list_is_ever_written():
    atom = Atom("P", [Function("f", []), Function("g", [Function("h", [])])])
    text = atom.to_tptp()
    assert text == "p(f,g(h))"
    assert "()" not in text


def test_the_text_is_read_back_as_the_constant():
    atom = Atom("P", [Function("f", [])])
    assert parse_tptp_formula(atom.to_tptp()) == Atom("P", [Constant("f")])


def test_a_function_with_arguments_is_written_as_before():
    assert Function("f", [Constant("a")]).to_tptp() == "f(a)"
    assert Function("f", [Constant("a"), Variable("x")]).to_tptp() == "f(a,X)"


@pytest.mark.parametrize("name", ["+", "-", "*", "/", "$sum", "9lives", "a b", ""])
def test_a_name_that_is_no_constant_is_refused_by_name_not_written_as_a_call(name):
    with pytest.raises(NotImplementedError, match="constant name"):
        Function(name, []).to_tptp()


def test_a_nullary_function_and_a_constant_of_one_word_are_two_symbols_and_refused():
    # Foo and foo are two distinct names of one namespace, written as the one word ``foo``: the atom
    # R(Foo, foo) would be written r(foo,foo), which says R holds of one element, a different formula
    atom = Atom("R", [Function("Foo", []), Constant("foo")])
    with pytest.raises(NotImplementedError):
        atom.to_tptp()


def test_a_nullary_function_and_a_constant_of_one_name_are_one_symbol():
    assert Atom("R", [Function("c", []), Constant("c")]).to_tptp() == "r(c,c)"
