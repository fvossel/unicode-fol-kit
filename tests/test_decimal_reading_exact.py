# -*- coding: utf-8 -*-
"""A decimal numeral is read as exactly the number it spells, or refused by name.

A numeral is a constant identified by its VALUE, so two different decimal texts must never become one
numeral. ``Number`` holds an ``int`` or a ``float``, and a text is read as the ``float`` it spells only when
no other decimal text of at most that many digits spells the same float.

What is derived by hand:

* a double has 53 significant bits, so two neighbouring doubles are at most 2**-52 (2.2e-16) of their size
  apart. Two different decimals of at most 15 significant digits differ by at least a unit of the 15th digit
  of the smaller one, which is at least 5e-16 of the larger one: more than a double's spacing, so they are
  two doubles, and a double of such a decimal prints back as that decimal;
* with 16 digits the unit of the last digit can be below the spacing: the doubles in [8, 16) are 2**-49 =
  1.78e-15 apart, so ``8.000000000000001`` (8 plus 1e-15, nearer to 8 + 1.78e-15 than to 8) and
  ``8.000000000000002`` (8 plus 2e-15, 0.22e-15 from 8 + 1.78e-15) are ONE double. ``0.30000000000000004`` and
  ``0.30000000000000005`` are one double too;
* so the digits of a decimal are counted (after the sign, the leading zeros and the trailing zeros of the
  fraction are dropped: ``0.1`` and ``0.10`` are one numeral), a text with at most 15 is read, and a text
  with more is refused, in every reader. A text whose fraction is all zeros is the integer of its whole part,
  as before;
* a decimal below the smallest normal double has fewer than 15 digits of precision (and a text with ``400``
  zeros after the point is the double ``0.0``, another numeral than the one written), so it is refused too;
* a numeral that Z3 holds as the fraction ``p/q`` is the decimal text it spells when ``q`` has no prime factor
  but 2 and 5, and is read by the same rule: ``1/10`` is ``0.1``, ``1/8`` is ``0.125``, ``1/3`` has no decimal
  text and is refused;
* an OWL decimal literal (``"0.1"^^xsd:decimal``) and the ``real(...)`` of an ACE DRS are read by the same rule;
* the inverse of the name a writer gives a numeral reads exactly the names the writer produces and refuses any
  other, so two names are never one value.
"""

import random
from decimal import Decimal

import pytest
import z3

from unicode_fol_kit import api
from unicode_fol_kit.ace.drs_reader import AceDrsUnreadError, parse_ape_drs
from unicode_fol_kit.atp.twee_entailment import _parse_term
from unicode_fol_kit.atp.z3_input import from_z3, parse_smtlib
from unicode_fol_kit.fol._fol_nodes import _numeral_from_text
from unicode_fol_kit.fol.latex_input import parse_latex
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.naming import ParsingError
from unicode_fol_kit.fol.nodes import Atom, Number
from unicode_fol_kit.fol.prolog_input import parse_prolog_clause
from unicode_fol_kit.fol.prover9_input import parse_prover9
from unicode_fol_kit.fol.qmltp_input import parse_qmltp_formula
from unicode_fol_kit.fol.tptp_input import parse_tptp, parse_tptp_formula

_UNICODE = MSFLParser()


def _argument(atom):
    assert isinstance(atom, Atom) and len(atom.args) == 1
    return atom.args[0]


def _prolog_number(text):
    clause = parse_prolog_clause(f"p({text}).")
    seen, stack = [], [clause]
    while stack:
        node = stack.pop()
        if isinstance(node, Number):
            seen.append(node)
        elif hasattr(node, "_child_nodes"):
            stack.extend(node._child_nodes())
    assert len(seen) == 1, clause
    return seen[0]


def _smtlib_number(text):
    # SMT-LIB has no negative literal: a negative numeral is the negation of a positive one
    negative = text.startswith("-")
    literal = f"(- {text[1:]})" if negative else text
    [assertion] = parse_smtlib(f"(declare-fun p (Real) Bool)(assert (p {literal}))")
    term = _argument(assertion)
    if negative:
        assert (term.name, len(term.args)) == ("-", 1), term
        return Number(-term.args[0].value)
    return term


#: every text reader of the kit that reads a decimal numeral, as ``text -> Number``
READERS = {
    "unicode": lambda t: _argument(_UNICODE.parse(f"P({t})")),
    "latex": lambda t: _argument(parse_latex(f"P({t})")),
    "tptp": lambda t: _argument(parse_tptp_formula(f"p({t})")),
    "tptp problem": lambda t: _argument(parse_tptp(f"fof(a, axiom, p({t})).")[0].formula),
    "qmltp": lambda t: _argument(parse_qmltp_formula(f"p({t})")),
    "prover9": lambda t: _argument(parse_prover9(f"P({t})")),
    "twee": _parse_term,
    "prolog": _prolog_number,
    "smtlib": _smtlib_number,
}


@pytest.fixture(params=sorted(READERS))
def read(request):
    return READERS[request.param]


# ---------------------------------------------------------------------------------------------
# What is read: at most 15 significant digits
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("text, value", [
    ("0.1", 0.1),
    ("0.10", 0.1),                      # trailing zero of the fraction: one significant digit
    ("0.1000000000000000000", 0.1),
    ("-0.5", -0.5),                     # the sign is no digit
    ("3.14159265358979", 3.14159265358979),                 # 15 digits
    ("0.123456789012345", 0.123456789012345),               # 15 digits
    ("99999999999999.9", 99999999999999.9),                 # 14 + 1 digits
    ("0.000000000000001", 1e-15),       # one significant digit
    ("0.00000000000000012345", 1.2345e-16),                 # five significant digits
    ("0." + "0" * 307 + "3", 3e-308),   # above the smallest normal double 2.2250738585072014e-308
])
def test_a_decimal_of_at_most_15_significant_digits_is_the_float_it_spells(read, text, value):
    number = read(text)
    assert isinstance(number, Number)
    assert number.value == value and type(number.value) is float


def test_two_spellings_of_one_decimal_are_one_numeral(read):
    assert read("0.1") == read("0.10") == read("0.1000000000000000")


@pytest.mark.parametrize("text, value", [("1.0", 1), ("123456789012345.0", 123456789012345),
                                         ("100000000000000000000000.0", 10 ** 23)])
def test_a_text_with_an_all_zero_fraction_is_still_the_integer_of_its_whole_part(read, text, value):
    number = read(text)
    assert number.value == value and type(number.value) is int


@pytest.mark.parametrize("text, value", [("000.5", 0.5), ("0012.50", 12.5), ("-007.25", -7.25),
                                         ("0.000000000000000500000", 5e-16)])
def test_leading_zeros_and_trailing_zeros_of_the_fraction_are_no_significant_digits(text, value):
    assert _numeral_from_text(text) == value


# ---------------------------------------------------------------------------------------------
# What is refused: more than 15 significant digits, or too close to zero
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("text, digits", [
    ("0.30000000000000004", 17),
    ("0.30000000000000005", 17),
    ("3.141592653589793", 16),
    ("123456789012345.5", 16),
    ("1234567890123456.5", 17),
    ("9007199254740993.5", 17),
    ("0.1234567890123456", 16),
    ("-0.1234567890123456", 16),                # the sign is no digit
    ("8.000000000000001", 16),
    ("1.000000000000001", 16),
    ("1" + "0" * 20 + ".5", 22),                # a whole part that is not a double
    ("0.10000000000000000001", 20),             # one tenth and a hair: the double of 0.1, another numeral
])
def test_a_decimal_of_more_than_15_significant_digits_is_refused_by_name(read, text, digits):
    with pytest.raises((ParsingError, ValueError)) as refused:
        read(text)
    message = str(refused.value)
    assert text.lstrip("-") in message and f"{digits} significant digits" in message


def test_the_refusal_says_why():
    with pytest.raises(ValueError) as refused:
        _numeral_from_text("0.30000000000000004")
    message = str(refused.value)
    # two different decimals of that length can be one float, and a numeral is identified by its value
    assert "can be one float" in message and "identified by its value" in message
    assert "0.30000000000000005" in message


@pytest.mark.parametrize("zeros", [309, 330, 400])
def test_a_decimal_below_the_smallest_normal_double_is_refused_not_read_as_zero(read, zeros):
    text = "0." + "0" * zeros + "1"          # one significant digit, and a value that is not 0
    with pytest.raises((ParsingError, ValueError)) as refused:
        read(text)
    assert "close to zero" in str(refused.value)


def test_a_refused_text_is_no_formula_of_the_front_door():
    result = api.parse_any("P(0.30000000000000004)")
    assert result.formula is None
    assert any("significant digits" in error["message"] for error in result.errors)


# ---------------------------------------------------------------------------------------------
# Why 15 and not 16
# ---------------------------------------------------------------------------------------------

def test_two_different_decimals_of_16_digits_can_be_one_float():
    # hand-derived in the module docstring: the doubles in [8, 16) are 2**-49 apart
    assert float("8.000000000000001") == float("8.000000000000002")
    assert Decimal("8.000000000000001") != Decimal("8.000000000000002")
    assert float("0.30000000000000004") == float("0.30000000000000005")
    for text in ("8.000000000000001", "8.000000000000002"):
        with pytest.raises(ValueError):
            _numeral_from_text(text)


def _scaled_text(k: int, places: int) -> str:
    """The text of the integer ``k`` scaled down by ``10**places``, with ``places`` fractional digits."""
    whole, fraction = divmod(k, 10 ** places)
    return f"{whole}.{fraction:0{places}d}"


def test_neighbouring_decimals_of_15_significant_digits_are_never_one_numeral():
    rng = random.Random(20261005)
    ks = [10 ** 14, 10 ** 14 + 1, 10 ** 15 - 3, 8 * 10 ** 13 * 10 + 1, 9 * 10 ** 14, 9 * 10 ** 14 - 1]
    ks += [rng.randrange(10 ** 14, 10 ** 15 - 2) for _ in range(1500)]
    for k in ks:
        for places in (1, 4, 9, 14):
            first, second = _scaled_text(k, places), _scaled_text(k + 1, places)
            a, b = _numeral_from_text(first), _numeral_from_text(second)
            assert a != b, (first, second)


def test_a_decimal_of_at_most_15_digits_prints_back_as_itself():
    rng = random.Random(7)
    for _ in range(3000):
        digits = rng.randrange(1, 16)
        k = rng.randrange(10 ** (digits - 1), 10 ** digits)
        places = rng.randrange(1, 25)
        text = _scaled_text(k, places)
        value = _numeral_from_text(text)
        if isinstance(value, float):
            assert Decimal(repr(value)) == Decimal(text), (text, value)
        else:
            assert value == Decimal(text)


# ---------------------------------------------------------------------------------------------
# What it means for a prover
# ---------------------------------------------------------------------------------------------

def test_two_spellings_of_one_decimal_are_one_numeral_for_z3():
    premise, goal = _UNICODE.parse("P(0.1)"), _UNICODE.parse("P(0.10)")
    assert api.prove(goal, [premise], backends=["z3"]).status == "proved"


def test_two_different_decimals_of_15_digits_are_two_numerals_for_z3():
    # P(first) does not give P(second): universe {0, 1}, first at 0, second at 1, P = {0}
    premise, goal = _UNICODE.parse("P(0.300000000000004)"), _UNICODE.parse("P(0.300000000000005)")
    assert premise != goal
    assert api.prove(goal, [premise], backends=["z3"]).status == "refuted"


# ---------------------------------------------------------------------------------------------
# The SMT-LIB reader: a numeral that Z3 holds as a fraction
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("fraction, value", [("1/10", 0.1), ("1/8", 0.125), ("-3/4", -0.75), ("5/2", 2.5),
                                             ("1/1024", 0.0009765625)])
def test_a_fraction_with_a_decimal_text_is_the_number_that_text_spells(fraction, value):
    number = from_z3(z3.RealVal(fraction))
    assert number == Number(value) and type(number.value) is float


def test_a_fraction_with_no_decimal_text_is_refused_by_name():
    # 1/3 = 0.333..., no finite decimal and no float; the nearest float would be another numeral
    with pytest.raises(ValueError, match="1/3.*no decimal text"):
        from_z3(z3.RealVal("1/3"))


def test_a_fraction_that_is_a_decimal_of_more_than_15_digits_is_refused_by_name():
    # 18014398509481987/2 = 9007199254740993.5, which a float reads as the whole number 9007199254740994
    with pytest.raises(ValueError, match="17 significant digits"):
        from_z3(z3.RealVal("18014398509481987/2"))


def test_the_smtlib_reader_reads_a_whole_real_as_an_integer():
    assert _smtlib_number("100000000000000000000000.0") == Number(10 ** 23)
    assert _smtlib_number("2.0") == Number(2) and type(_smtlib_number("2.0").value) is int


def test_a_quotient_of_two_numerals_is_not_a_numeral_and_is_read_as_the_application():
    [assertion] = parse_smtlib("(declare-fun p (Real) Bool)(assert (p (/ 1.0 3.0)))")
    term = _argument(assertion)
    assert (term.name, term.args) == ("/", (Number(1), Number(3)))


# ---------------------------------------------------------------------------------------------
# The inverses of the kit's own writers are not text readers and read the name back exactly
# ---------------------------------------------------------------------------------------------

def test_the_name_a_writer_gives_a_float_numeral_is_read_back_as_that_float():
    # A node can hold a float with a 17-digit text (0.1 + 0.2). The writers name it by that text, and
    # the inverse of the name (a name map, a Z3 symbol) reads exactly the float that was written: it
    # reads names the kit wrote, never a text a person typed, so the digit rule does not apply to it.
    from unicode_fol_kit.fol._numeral_symbols import numeral_name, numeral_value

    value = 0.1 + 0.2
    assert numeral_name(value) == "0.30000000000000004"
    assert numeral_value(numeral_name(value)) == value
    assert from_z3(Number(value).to_z3()) == Number(value)


@pytest.mark.parametrize("name", ["1.0", "007", "-0", "1e3", "0.30000000000000005", "0.10", "+5", " 5", "2.50"])
def test_a_name_the_writer_does_not_give_a_numeral_is_not_read_as_a_value(name):
    # numeral_name(float(name)) is another text ("1", "7", "0", ..., "0.30000000000000004", "0.1", "2.5"), so the
    # name is not one numeral_name produces and two names would read as one value if it were accepted
    from unicode_fol_kit.fol._numeral_symbols import numeral_value

    with pytest.raises(ValueError, match="not a name numeral_name produces|invalid literal"):
        numeral_value(name)


@pytest.mark.parametrize("value", [0, 1, -3, 10 ** 30, 0.5, -2.25, 1e-07, 0.1 + 0.2, 123456789012345.5])
def test_every_name_the_writer_gives_a_value_is_read_back_as_that_value(value):
    from unicode_fol_kit.fol._numeral_symbols import numeral_name, numeral_value

    assert numeral_value(numeral_name(value)) == value
    assert type(numeral_value(numeral_name(value))) is type(Number(value).value)


# ---------------------------------------------------------------------------------------------
# The OWL reader: a decimal literal
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("lexical, value", [("0.1", 0.1), ("0.10", 0.1), ("-1.50", -1.5), ("+2.5", 2.5),
                                            (".5", 0.5), ("3.14159265358979", 3.14159265358979),
                                            ("0.00001", 1e-05), ("1.0", 1), ("100000000000000000000000.0", 10 ** 23)])
def test_an_owl_decimal_of_at_most_15_significant_digits_is_the_number_it_spells(lexical, value):
    from unicode_fol_kit.dl.datatypes import Literal

    term = Literal(lexical, "xsd:decimal").to_term()
    assert term == Number(value) and type(term.value) is type(Number(value).value)


@pytest.mark.parametrize("lexical", ["0.30000000000000004", "0.30000000000000005", "3.141592653589793",
                                     "123456789012345.5", "1234567890123456.5", "0.10000000000000000001"])
def test_an_owl_decimal_of_more_than_15_significant_digits_is_refused_by_name(lexical):
    from unicode_fol_kit.dl.datatypes import Literal, UnsupportedDatatypeError

    with pytest.raises(UnsupportedDatatypeError, match="significant digits") as refused:
        Literal(lexical, "xsd:decimal").to_term()
    assert lexical in str(refused.value)


def test_the_smallest_normal_double_the_reader_uses_is_the_one_of_the_platform():
    import sys

    from unicode_fol_kit.fol import _fol_nodes

    assert _fol_nodes._SMALLEST_NORMAL_DOUBLE == sys.float_info.min
    assert _fol_nodes._DECIMAL_DIGITS_READ_EXACTLY == 15


# ---------------------------------------------------------------------------------------------
# The ACE reader: a real(...) of a DRS
# ---------------------------------------------------------------------------------------------

def _ace_real(text):
    drs = parse_ape_drs(f"drs([],[formula(int(1),=,{text})-1/2])")
    return drs.conditions[0].args[2]


@pytest.mark.parametrize("text, value", [("real(0.1)", 0.1), ("real(3.14159265358979)", 3.14159265358979),
                                         ("-0.5", -0.5), ("real(3.0)", 3.0)])
def test_the_ace_reader_reads_a_real_exactly(text, value):
    term = _ace_real(text)
    assert getattr(term, "value", term) == value


def test_the_ace_reader_keeps_a_whole_real_beyond_a_double_as_the_integer_it_is():
    term = _ace_real("real(100000000000000000000000.0)")
    assert term.value == 10 ** 23 and type(term.value) is int
    # the double nearest to 10**23 is another integer, 99999999999999991611392
    assert Number(term.value).value != 99999999999999991611392


@pytest.mark.parametrize("text", ["real(0.30000000000000004)", "real(0.30000000000000005)",
                                  "-0.30000000000000004", "real(3.141592653589793)"])
def test_the_ace_reader_refuses_a_real_of_more_than_15_significant_digits(text):
    with pytest.raises(AceDrsUnreadError, match="significant digits"):
        _ace_real(text)
