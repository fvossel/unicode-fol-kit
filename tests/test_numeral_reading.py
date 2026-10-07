# -*- coding: utf-8 -*-
"""A decimal numeral is read as the number it is written as: whole values are exact integers.

A reader that builds the number of a text with a point through ``float`` gives
``100000000000000000000000.0`` the double nearest to it, ``99999999999999991611392``, which is another
integer: the text of that integer is then read as the same numeral as the text with the point, and the text
with the point as another numeral than the one with its integer digits.

What is derived by hand:

* a text whose fractional digits are all zero is the integer of its whole part, however large:
  ``100000000000000000000000.0`` is ``10**23``, ``1.0`` is ``1``, ``100.0`` is ``100``, ``-0.0`` is ``0``;
* it is therefore the same numeral as the text ``100000000000000000000000`` (``P`` of the one is the atom
  ``P`` of the other, with the same printed text), and another numeral than ``99999999999999991611392``;
* a numeral that is not whole keeps the float it is: ``0.10`` is ``0.1`` and ``2.5`` is ``2.5``;
* a numeral with a fractional part is the float it spells only when it has at most 15 significant digits
  (``tests/test_decimal_reading_exact.py`` derives why), and is refused by name when it has more:
  ``9007199254740993.5`` (17 digits) would be the float ``9007199254740994.0``, a whole number, and another
  numeral than the one written;
* two numerals of different value are two constants that may denote different elements, so
  ``P(100000000000000000000000.0) ⊬ P(99999999999999991611392)`` (universe {0, 1}, the first ↦ 0, the second
  ↦ 1, ``P`` = {0}), and ``P(100000000000000000000000.0) ⊢ P(100000000000000000000000)``.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.twee_entailment import _parse_term
from unicode_logic_kit.fol.latex_input import parse_latex
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.naming import ParsingError
from unicode_logic_kit.fol.nodes import Atom, Number
from unicode_logic_kit.fol.prolog_input import parse_prolog_clause
from unicode_logic_kit.fol.prover9_input import Prover9ParsingError, parse_prover9
from unicode_logic_kit.fol.qmltp_input import parse_qmltp_formula
from unicode_logic_kit.fol.tptp_input import parse_tptp, parse_tptp_formula

TEN_TO_23 = 10 ** 23
NEAREST_DOUBLE = 99999999999999991611392            # int(float(10 ** 23))

_UNICODE = MSFLParser()


def _argument(atom):
    assert isinstance(atom, Atom) and len(atom.args) == 1
    return atom.args[0]


READERS = {
    "unicode": lambda t: _argument(_UNICODE.parse(f"P({t})")),
    "latex": lambda t: _argument(parse_latex(f"P({t})")),
    "tptp": lambda t: _argument(parse_tptp_formula(f"p({t})")),
    "tptp problem": lambda t: _argument(parse_tptp(f"fof(a, axiom, p({t})).")[0].formula),
    "qmltp": lambda t: _argument(parse_qmltp_formula(f"p({t})")),
    "prover9": lambda t: _argument(parse_prover9(f"P({t})")),
    "twee": _parse_term,
}


def _numbers(clause):
    """Every Number in a parsed Prolog clause."""
    seen = []
    stack = [clause]
    while stack:
        node = stack.pop()
        if isinstance(node, Number):
            seen.append(node)
        elif hasattr(node, "_child_nodes"):
            stack.extend(node._child_nodes())
    return seen


def _prolog_number(text):
    clause = parse_prolog_clause(f"p({text}).")
    numbers = _numbers(clause)
    assert len(numbers) == 1, clause
    return numbers[0]


READERS["prolog"] = _prolog_number


@pytest.fixture(params=sorted(READERS))
def read(request):
    return READERS[request.param]


@pytest.mark.parametrize("text, value", [
    ("1.0", 1),
    ("100.0", 100),
    ("-0.0", 0),
    ("100000000000000000000000.0", TEN_TO_23),
    ("100000000000000000000000", TEN_TO_23),
    ("99999999999999991611392", NEAREST_DOUBLE),
    ("99999999999999991611392.0", NEAREST_DOUBLE),
    ("0.0", 0),
])
def test_a_whole_numeral_is_the_integer_it_is_written_as(read, text, value):
    number = read(text)
    assert isinstance(number, Number)
    assert number.value == value and type(number.value) is int


# "0.30000000000000004" used to be in this list. It has 17 significant digits, so it is refused (see the
# module docstring), and "3.14159265358979" (15 digits) takes its place as the longest decimal that is read.
@pytest.mark.parametrize("text, value", [("0.10", 0.1), ("2.5", 2.5), ("-1.5", -1.5), ("3.14159265358979", 3.14159265358979)])
def test_a_numeral_that_is_not_whole_keeps_its_float(read, text, value):
    number = read(text)
    assert isinstance(number, Number)
    assert number.value == value and type(number.value) is float


def test_the_two_spellings_of_ten_to_the_23_are_one_numeral(read):
    assert read("100000000000000000000000.0") == read("100000000000000000000000")
    assert read("100000000000000000000000.0").value == TEN_TO_23


def test_ten_to_the_23_and_the_integer_nearest_to_it_as_a_double_are_two_numerals(read):
    assert read("100000000000000000000000.0") != read("99999999999999991611392")
    assert read("100000000000000000000000") != read("99999999999999991611392.0")


def test_the_atoms_of_the_two_spellings_print_alike_and_the_atom_of_the_other_numeral_does_not():
    same_a = _UNICODE.parse("P(100000000000000000000000.0)")
    same_b = _UNICODE.parse("P(100000000000000000000000)")
    other = _UNICODE.parse("P(99999999999999991611392)")
    assert same_a == same_b
    assert same_a.to_unicode_str() == same_b.to_unicode_str() == "P(100000000000000000000000)"
    assert same_a != other and other.to_unicode_str() == "P(99999999999999991611392)"


@pytest.mark.parametrize("name", sorted(READERS))
def test_a_fraction_that_no_float_of_its_size_holds_is_refused_by_name(name):
    # The message used to name "a fractional part that no float of its size can hold"; the rule is now the
    # number of significant digits (17 here), which is what the message says.
    with pytest.raises((ParsingError, ValueError)) as refused:
        READERS[name]("9007199254740993.5")
    assert "9007199254740993.5" in str(refused.value) and "significant digits" in str(refused.value)


# -- what it means for a prover ---------------------------------------------------------------------

def test_the_numeral_with_a_point_is_the_numeral_without_it():
    premise = _UNICODE.parse("P(100000000000000000000000.0)")
    goal = _UNICODE.parse("P(100000000000000000000000)")
    assert api.prove(goal, [premise], backends=["z3"]).status == "proved"


def test_the_integer_nearest_to_it_as_a_double_is_another_numeral():
    premise = _UNICODE.parse("P(100000000000000000000000.0)")
    goal = _UNICODE.parse("P(99999999999999991611392)")
    verdict = api.prove(goal, [premise], backends=["z3"])
    assert verdict.status == "refuted"


# -- Prover9 keeps two spellings apart, so a text that has both is refused, and two values are not --------

def test_prover9_text_with_both_spellings_of_one_value_is_refused():
    with pytest.raises(Prover9ParsingError, match="written in one text"):
        parse_prover9("P(100000000000000000000000.0) & Q(100000000000000000000000)")


def test_prover9_text_with_two_values_that_a_double_cannot_tell_apart_is_read():
    both = parse_prover9("P(100000000000000000000000.0) & Q(99999999999999991611392)")
    left, right = both.left, both.right
    assert _argument(left).value == TEN_TO_23 and _argument(right).value == NEAREST_DOUBLE


def test_a_quoted_numeral_with_a_point_is_not_the_canonical_spelling_of_its_value():
    with pytest.raises(Prover9ParsingError, match="canonical"):
        parse_prover9('P("100000000000000000000000.0")')
    assert _argument(parse_prover9('P("100000000000000000000000")')).value == TEN_TO_23
