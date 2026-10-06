"""A counting quantifier's bound is a non-negative integer, and a
bound that is not one is a PARSE ERROR, not a raw lark ``VisitError``.

The NUMBER terminal reads an optional ``-`` and a decimal point because TERMS
need them (``P(-3)``, ``x < 2.5``). A count is neither: ``∃≥n x φ`` says "at
least n witnesses", and n is a natural number. Before the terminal was widened
``∃≥-2 x P(x)`` was a one-line ``SYNTAX_ERROR`` (the ``-`` was an unexpected
character); once it lexes, the COUNT RULE has to refuse it, and it has to refuse
it the same way: with the kit's ``ParsingError``, which ``MSFLParser.parse``
hands to the caller and the CLI reports in one line. ``∃≥2.5 x P(x)`` is the
same defect (it escaped as a traceback too) and is refused alike.

Hand-derived expectations, one clause each:

* the bound token is ``-2`` or ``2.5``; the integers allowed are 0, 1, 2, ...;
  -2 < 0 and 2.5 has a decimal point, so both are refused; the position
  reported is the 1-based column of the bound's first character: ``∃`` is
  column 1, the relation glyph ``≥``/``≤``/``=`` column 2, the bound column 3;
* ``-0`` equals 0 as a number but is not the numeral ``0``: a count bound is an UNSIGNED
  numeral, so a sign is refused whatever follows it, ``-0`` like ``-2`` (``-0`` used to be
  read as 0, which made ``∃=-0 x P(x)`` a count of zero witnesses by an accident of
  ``int("-0")``). ``+3`` never reaches the count rule: the NUMBER terminal has no ``+``,
  so the lexer refuses it with the unexpected-character message;
* ``∃≥0``, ``∃≥2`` etc. are unchanged.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.__main__ import main
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.naming import ParsingError
from unicode_fol_kit.fol.nodes import Count, Number, SortedCount

#: The parsers that read the UNSORTED counting quantifier (``Count``) ...
_UNSORTED = {
    "fol": {},
    "modal": {"modal": True},
    "second_order": {"second_order": True},
}
#: ... and the one that reads the SORTED one (``SortedCount``).
_SORTED = {"msfol": {"many_sorted": True}}

_BAD_UNSORTED = [
    ("∃≥-2 x P(x)", "-2"),
    ("∃≤-1 x P(x)", "-1"),
    ("∃=-3 x P(x)", "-3"),
    ("∃≥2.5 x P(x)", "2.5"),
    ("∃≥-2.5 x P(x)", "-2.5"),
    ("∃≥2.0 x P(x)", "2.0"),           # spelled with a point: not an integer literal
    ("∃=-0 x P(x)", "-0"),             # a sign, though -0 == 0: not an unsigned numeral
    ("∃≥-0 x P(x)", "-0"),
    ("∃≤-0 x P(x)", "-0"),
]
_BAD_SORTED = [
    ("∃≥-2 x:S P(x)", "-2"),
    ("∃=-1 x:S P(x)", "-1"),
    ("∃≥2.5 x:S P(x)", "2.5"),
    ("∃=-0 x:S P(x)", "-0"),
    ("∃≤-0 x:S P(x)", "-0"),
]


def _refusal(parse):
    with pytest.raises(ParsingError) as caught:
        parse()
    return str(caught.value)


@pytest.mark.parametrize("mode", sorted(_UNSORTED))
@pytest.mark.parametrize("text, bound", _BAD_UNSORTED)
def test_a_bad_count_bound_is_a_parsing_error_not_a_lark_visit_error(mode, text, bound):
    message = _refusal(lambda: MSFLParser(**_UNSORTED[mode]).parse(text))
    assert message.startswith("SYNTAX_ERROR")
    assert "\n" not in message                      # one line, as the CLI prints it
    assert f"got {bound!r}" in message               # names the bound
    assert "non-negative integer" in message         # and what a bound must be
    assert "at position 3" in message                # ∃ ≥ then the bound: column 3


@pytest.mark.parametrize("text, bound", _BAD_SORTED)
def test_a_bad_sorted_count_bound_is_refused_alike(text, bound):
    message = _refusal(lambda: MSFLParser(many_sorted=True).parse(text))
    assert message.startswith("SYNTAX_ERROR")
    assert f"got {bound!r}" in message
    assert "non-negative integer" in message


def test_the_spans_route_refuses_it_the_same_way():
    # parse_with_spans builds the tree with a second transformer; it must not
    # leak the raw lark wrapper either.
    message = _refusal(lambda: MSFLParser().parse_with_spans("∃≥-2 x P(x)"))
    assert message.startswith("SYNTAX_ERROR") and "got '-2'" in message


def test_parse_any_reports_the_bound_in_every_dialect_that_reads_a_count():
    parsed = api.parse_any("∃≥-2 x P(x)")
    assert not parsed.ok
    counted = [e for e in parsed.errors if e["dialect"] in _UNSORTED]
    assert {e["dialect"] for e in counted} == set(_UNSORTED)
    for error in counted:
        assert error["message"].startswith("SYNTAX_ERROR"), error
        assert "got '-2'" in error["message"], error
        assert "VisitError" not in error["message"] and "Error trying" not in error["message"]
    # pinned to one dialect the result is the same single, readable error
    pinned = api.parse_any("∃≥2.5 x P(x)", hint="fol")
    assert not pinned.ok and len(pinned.errors) == 1
    assert pinned.errors[0]["message"].startswith("SYNTAX_ERROR")
    assert "got '2.5'" in pinned.errors[0]["message"]


def test_the_cli_reports_a_bad_bound_in_one_line_and_exits_1(capsys):
    for argv in (["∃≥-2 x P(x)"], ["∃≤-1 x P(x)"], ["∃=-3 x P(x)"], ["∃≥2.5 x P(x)"],
                 ["∃≥-2 x:S P(x)", "--mode", "msfol"]):
        assert main(argv) == 1, argv
        captured = capsys.readouterr()
        lines = captured.err.strip().splitlines()
        assert len(lines) == 1, (argv, captured.err)
        assert lines[0].startswith("SYNTAX_ERROR"), (argv, lines)
        assert "non-negative integer" in lines[0], (argv, lines)
        assert captured.out == ""


def test_the_bounds_that_are_counts_still_read():
    assert MSFLParser().parse("∃≥2 x P(x)").n == Number(2)
    assert MSFLParser().parse("∃≥0 x P(x)").n == Number(0)
    assert isinstance(MSFLParser().parse("∃=3 x P(x)"), Count)
    assert isinstance(MSFLParser(many_sorted=True).parse("∃≥2 x:S P(x)"), SortedCount)
    assert api.parse_any("∃≥2 x P(x)").ok


def test_a_signed_zero_is_not_a_count_in_any_reader():
    # An unsigned numeral is the only count bound. -0 equals 0 but carries a sign, so
    # "∃=-0 x P(x)" is refused (it used to read as "∃=0 x P(x)", a count of zero), in
    # every grammar that reads a count: the three unsorted ones, the sorted one, and
    # through api.parse_any. The unsigned zero still reads.
    from unicode_fol_kit.fol._fol_nodes import CountBoundError
    for kwargs in ({}, {"modal": True}, {"second_order": True}):
        with pytest.raises(CountBoundError, match="got '-0'"):
            MSFLParser(**kwargs).parse("∃=-0 x P(x)")
        assert MSFLParser(**kwargs).parse("∃=0 x P(x)").n == Number(0)
    with pytest.raises(CountBoundError, match="got '-0'"):
        MSFLParser(many_sorted=True).parse("∃=-0 x:S P(x)")
    assert MSFLParser(many_sorted=True).parse("∃=0 x:S P(x)").n == Number(0)
    parsed = api.parse_any("∃=-0 x P(x)")
    assert not parsed.ok and all("got '-0'" in e["message"] for e in parsed.errors
                                 if e["dialect"] in _UNSORTED)


def test_a_plus_sign_is_refused_by_the_lexer_before_the_count_rule():
    # "+3" has never been a count bound: the NUMBER terminal has no "+", so the lexer stops
    # at it (no sign is accepted, which is the rule; only "-" reaches the count rule, as
    # part of the terminal that terms such as P(-3) need).
    from unicode_fol_kit.fol.naming import NamingError
    for text in ("∃≤+3 x P(x)", "∃=+0 x P(x)"):
        with pytest.raises(NamingError) as caught:
            MSFLParser().parse(text)
        message = str(caught.value)
        assert message.startswith("SYNTAX_ERROR") and "'+'" in message, message
