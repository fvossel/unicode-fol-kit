r"""B6: the LALR fast path, and the permanent proof that it agrees with Earley.

``unicode_logic_kit.fol.tptp_input`` now parses with an LALR(1) parser first and
falls back to the original Earley one on ``UnexpectedInput``. The win is
measured: on a real 1,367,212-byte, 4291-formula TPTP translation of an
ontology, ``load_tptp_problem`` takes 68.3 s through Earley and 1.7 s through
LALR, with BYTE-IDENTICAL item lists for all 4291 records. A ``cProfile`` run
attributes 98 % of the Earley cost to lark's dynamic-lexer chart, so this is
the only lever that matters, and splitting the file per statement is worth 0 %
(measured: 6.75 s against 7.19 s for 600 formulas).

The fallback makes the change safe in ONE direction only: if LALR refuses a
text, Earley re-parses and Earley raises, so nothing that parsed before stops
parsing and every syntax-error message stays byte-identical. It does NOT stop
LALR from ACCEPTING something Earley would reject, because LALR uses lark's
contextual lexer and Earley the dynamic one. Every terminal in the grammar is
disjoint by first character and every operator is a longest-match literal, so
a divergence would need a GRAMMAR edit to introduce — and this battery is the
only thing standing between such an edit and a silently widened language.
Keep it parametrised; never xfail it.
"""

import pytest
from lark import Lark
from lark.exceptions import UnexpectedToken

from unicode_logic_kit.fol import tptp_input
from unicode_logic_kit.fol.tptp_input import (
    _FILE_PARSER,
    _FILE_PARSER_FAST,
    _FORMULA_PARSER,
    _FORMULA_PARSER_FAST,
    _GRAMMAR,
    _TRANSFORMER,
    TptpParsingError,
    parse_tptp,
)

# --- 31 feature-coverage probes: the full operator ladder, quantifiers,
# equality, dollar words, quoted atoms, cnf, numeric names, the optional 4th
# and 5th annotation fields, all four tff type-declaration shapes, includes
# with and without a selection list, both comment forms, negative and
# decimal numbers.
FEATURE_PROBES = [
    "fof(a, axiom, p <=> q).",
    "fof(a, axiom, p <~> q).",
    "fof(a, axiom, p => q).",
    "fof(a, axiom, p <= q).",
    "fof(a, axiom, p | q).",
    "fof(a, axiom, p ~| q).",
    "fof(a, axiom, p & q).",
    "fof(a, axiom, p ~& q).",
    "fof(a, axiom, ~p).",
    "fof(a, axiom, ! [X] : p(X)).",
    "fof(a, axiom, ? [X] : p(X)).",
    "tff(a, axiom, ! [X: t] : p(X)).",
    "tff(a, axiom, ? [X: t, Y: t] : r(X, Y)).",
    "fof(a, axiom, a = b).",
    "fof(a, axiom, a != b).",
    "fof(a, axiom, $true).",
    "fof(a, axiom, $less(c, d)).",
    "fof(a, axiom, 'http://example.org/x#y'(c)).",
    "fof(a, axiom, 'http://example.org/x#y').",
    "cnf(a, axiom, p | ~q).",
    "fof(42, axiom, p).",
    "fof(a, axiom, p, file('x.p', y)).",
    "fof(a, axiom, p, file('x.p', y), [a, b]).",
    "tff(t, type, foo: $tType).",
    "tff(t, type, c: t).",
    "tff(t, type, f: (t * t) > t).",
    "tff(t, type, g: t > t).",
    "include('x.p').",
    "include('x.p', [a, b]).",
    "% a line comment\nfof(a, axiom, p).",
    "/* a block\n   comment */\nfof(a, axiom, p(-1, 1.5)).",
]

# --- 15 adversarial LEXING probes: keywords used as names, unspaced
# operators, nested quantifiers, two statements on one line, an escaped
# backslash and an escaped quote inside a quoted atom, and $tType where only
# a DOLLARWORD is legal (both parsers must agree that it fails).
LEXING_PROBES = [
    "fof(include, axiom, p).",
    "fof(a, axiom, include(X)).",
    "fof(fof, axiom, fof(a)).",
    "fof(a, axiom, p($tType)).",
    "fof(a, axiom, a=b).",
    "fof(a,axiom,p).",
    "fof(a, axiom, ~~q).",
    "fof(a, axiom, ?[X]:![Y]:p(X,Y)).",
    "fof(a, axiom, p). fof(b, axiom, q).",
    r"fof(a, axiom, 'a\'b'(c)).",
    r"fof(a, axiom, 'a\\b'(c)).",
    "fof(a, axiom, p) .",
    "fof(a, axiom, $false | $true).",
    "fof(a, axiom, p(X) & ~p(Y)).",
    "fof(a, axiom, X = Y).",
]

# --- 14 MINUS-SIGN probes. The TPTP grammar's NUMBER terminal already
# accepts a leading '-' (`/-?[0-9]+(\.[0-9]+)?/`), and '-' is not an operator
# anywhere in this grammar, so it is the one character that could plausibly
# lex differently under the contextual lexer than under the dynamic one. Every
# position it can appear in is probed here: inside a number, separated from
# one, between two terms, between two variables, in a statement name, inside a
# quoted atom, in a TFF type-declaration name, alone, and doubled. Measured:
# 0 divergences. This is the ambiguity audit for this file, kept as a test so
# it is re-run rather than remembered.
MINUS_PROBES = [
    "fof(a, axiom, p(-1)).",
    "fof(a, axiom, p(- 1)).",
    "fof(a, axiom, p(1-2)).",
    "fof(a, axiom, p(-1.5)).",
    "fof(a, axiom, -1 = -1).",
    "fof(a, axiom, p(-0)).",
    "fof(a, axiom, p(a-b)).",
    "fof(a, axiom, p(X-Y)).",
    "fof(a, axiom, p(-1, -2.5, 3)).",
    "fof(a-b, axiom, p).",
    "fof(a, axiom, 'x-y'(c)).",
    "fof(a, axiom, p(-)).",
    "tff(t, type, 'a-b': t).",
    "fof(a, axiom, p(--1)).",
]

FILE_PROBES = FEATURE_PROBES + LEXING_PROBES + MINUS_PROBES

# --- 8 bare-formula probes, for the start="formula" parser pair.
FORMULA_PROBES = [
    "p",
    "~p",
    "p & q | r",
    "! [X] : (p(X) => q(X))",
    "a = b",
    "$true",
    "'quoted atom'",
    "p(f(g(X)), c)",
]

# --- the LF / CRLF / bare-CR trio (the 0.28.1 line-ending work).
_TWO_STATEMENTS = "fof(a, axiom, p).\nfof(b, axiom, q)."
NEWLINE_PROBES = [
    _TWO_STATEMENTS,
    _TWO_STATEMENTS.replace("\n", "\r\n"),
    _TWO_STATEMENTS.replace("\n", "\r"),
]


def _outcome(parser, text):
    """``("ok", items)`` or ``("raised", type name)`` — never a half result."""
    try:
        tree = parser.parse(text)
    except Exception as exc:                 # noqa: BLE001 - comparing failures
        return "raised", type(exc).__name__
    try:
        return "ok", _TRANSFORMER.transform(tree)
    except Exception as exc:                 # noqa: BLE001
        return "transform-raised", type(exc).__name__


def _assert_agree(fast, slow, text):
    fast_outcome = _outcome(fast, text)
    slow_outcome = _outcome(slow, text)
    if fast_outcome[0] == "raised" and slow_outcome[0] == "raised":
        # Both refuse. The exception CLASS may differ (contextual vs dynamic
        # lexer), and that is fine: _parse re-parses with Earley on any
        # UnexpectedInput, so the message a caller sees is always Earley's.
        return
    assert fast_outcome[0] == slow_outcome[0], (
        f"parsers disagree on whether {text!r} parses: "
        f"LALR {fast_outcome[0]}, Earley {slow_outcome[0]}")
    assert fast_outcome[1] == slow_outcome[1], (
        f"parsers disagree on the result for {text!r}")


@pytest.mark.parametrize("text", FILE_PROBES + NEWLINE_PROBES,
                         ids=range(len(FILE_PROBES) + len(NEWLINE_PROBES)))
def test_the_two_file_parsers_agree(text):
    _assert_agree(_FILE_PARSER_FAST, _FILE_PARSER, text)


@pytest.mark.parametrize("text", FORMULA_PROBES, ids=range(len(FORMULA_PROBES)))
def test_the_two_formula_parsers_agree(text):
    _assert_agree(_FORMULA_PARSER_FAST, _FORMULA_PARSER, text)


def test_the_battery_is_the_size_it_claims_to_be():
    """A guard against a probe being deleted to make a failure go away."""
    assert len(FEATURE_PROBES) == 31
    assert len(LEXING_PROBES) == 15
    assert len(MINUS_PROBES) == 14
    assert len(FORMULA_PROBES) == 8
    assert len(NEWLINE_PROBES) == 3


def test_the_grammar_is_still_lalr1():
    """lark raises GrammarError on any shift/reduce or reduce/reduce conflict.

    Asserted explicitly so a future grammar edit that introduces one fails
    HERE, with lark's own diagnostic, instead of silently making every parse
    fall back to Earley and quietly restoring the 68 s.
    """
    assert Lark(_GRAMMAR, start="file", parser="lalr") is not None
    assert Lark(_GRAMMAR, start="formula", parser="lalr") is not None


# =============================================================================
# The fallback itself.
# =============================================================================

def test_earley_takes_over_when_lalr_refuses(monkeypatch):
    """A text LALR cannot handle is still parsed, by Earley."""
    def refuse(text, *args, **kwargs):
        raise UnexpectedToken(token="x", expected=set())

    monkeypatch.setattr(_FILE_PARSER_FAST, "parse", refuse)
    assert parse_tptp("fof(a, axiom, p).")[0].name == "a"


def test_a_genuinely_broken_input_still_gets_earleys_exact_message(monkeypatch):
    """Every TptpParsingError message stays byte-identical to the old one."""
    before = None
    try:
        parse_tptp("fof(a, axiom, ).")
    except TptpParsingError as exc:
        before = str(exc)
    assert before is not None and "could not parse TPTP problem" in before

    def refuse(text, *args, **kwargs):
        raise UnexpectedToken(token="x", expected=set())

    monkeypatch.setattr(_FILE_PARSER_FAST, "parse", refuse)
    with pytest.raises(TptpParsingError) as caught:
        parse_tptp("fof(a, axiom, ).")
    assert str(caught.value) == before


def test_the_transform_is_never_retried(monkeypatch):
    """A TF0-scope refusal surfaces ONCE, with its own type, not wrapped.

    The refusals come out of the shared transformer, so they are identical
    whichever parser produced the tree; retrying would only double the work
    and could turn a NotImplementedError into a SYNTAX_ERROR.
    """
    calls = []
    original = _TRANSFORMER.transform

    def counting_transform(tree):
        calls.append(tree)
        raise NotImplementedError("scope refusal")

    monkeypatch.setattr(_TRANSFORMER, "transform", counting_transform)
    try:
        with pytest.raises(NotImplementedError, match="scope refusal"):
            parse_tptp("fof(a, axiom, p).")
    finally:
        monkeypatch.setattr(_TRANSFORMER, "transform", original)
    assert len(calls) == 1


def test_the_fast_path_is_the_one_actually_used(monkeypatch):
    """Without this, a silently-never-called fast parser would look fine."""
    seen = []
    original = _FILE_PARSER_FAST.parse

    def recording(text, *args, **kwargs):
        seen.append(text)
        return original(text, *args, **kwargs)

    monkeypatch.setattr(_FILE_PARSER_FAST, "parse", recording)
    parse_tptp("fof(a, axiom, p).")
    assert seen == ["fof(a, axiom, p)."]


def test_every_parse_call_site_passes_its_fast_twin():
    """A new call site that forgets ``fast=`` would silently stay slow."""
    import inspect

    source = inspect.getsource(tptp_input)
    for call in ("_parse(text, _FILE_PARSER, \"problem\"",
                 "_parse(sub_text, _FILE_PARSER, \"problem\"",
                 "_parse(text, _FORMULA_PARSER, \"formula\""):
        assert call in source
    # Exactly as many `fast=` arguments as `_parse(` call sites that take one.
    call_sites = source.count("_parse(text, _FILE_PARSER") \
        + source.count("_parse(sub_text, _FILE_PARSER") \
        + source.count("_parse(text, _FORMULA_PARSER")
    assert source.count("fast=_FILE_PARSER_FAST") \
        + source.count("fast=_FORMULA_PARSER_FAST") == call_sites
