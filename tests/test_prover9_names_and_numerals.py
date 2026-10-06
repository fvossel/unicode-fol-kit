r"""What the Prover9 renderers write for a name, a `$`-word and a numeral; what the reader
makes of a symbol written two ways; and how the backend reads Prover9's banner.

**A name Prover9 cannot read (``to_prover9`` of a single node).** Prover9 reads a bare word of
ASCII letters, digits and underscores as ONE symbol, and a double-quoted word as another; a
name with a space, a dot, a hyphen or a non-ASCII letter is neither, so any text for it is read
as several symbols or refused. Such a name is refused BY NAME, for a proposition, a predicate and
a function at every arity, and for a constant; the problem writer renames it instead.

**`$`-words.** Prover9 keeps the words that begin with ``$`` for itself (``$T``, ``$F``,
``$ANSWER``). The nullary atoms ``$true`` and ``$false`` are its truth constants and are written
``$T`` and ``$F``; any other ``$``-word is refused by name, by the single renderers and the writer.

**Numerals.** Prover9 has no arithmetic and neither has the Z3 route: ``Number.to_z3`` is an
uninterpreted constant named by the number's VALUE, so ``⊢ 1 ≠ 2`` is not valid for Z3 (a model may
give both numerals one value) and must not be proved by Prover9 either. A numeral is ONE constant
per value, written in double quotes: ``"1"`` for ``1`` and for ``1.0`` (equal nodes), ``"2.5"``,
``"-1"``. Bare ``2.5`` is refused by Prover9 (the ``.`` ends the statement), bare ``-1`` is the
function ``-`` applied to the constant ``1``, and Mace4 reads a bare integer as a domain element of
its own, all of them distinct, which is not what a numeral of the kit is. Prover9 has no infix minus
either: ``(a - b)`` is a syntax error there, so a binary ``-`` is written ``-(a, b)``, the same
uninterpreted function that ``-(a)`` is at one argument.

**The reader.** A quoted numeral is a number, in the one spelling of its value (``"1"``, never
``"1.0"``); ``-(a, b)`` is the function ``-``; and a symbol that a text writes both quoted and bare
(``"rain"`` and ``rain``) is refused by name, because Prover9 reads two symbols and the reader has
one name per symbol.

**The banner.** Prover9 has no ``--version``; ``-h`` prints ``Prover9 (64) version 2026-8A, August
2026.`` first and exits 0. The backend reads that line, through ``wsl.exe`` where the binary lives
inside WSL, with the null device for standard input.

Every expectation is derived by hand from those rules. The live tests run the real Prover9 where
there is one and skip, with a reason, where there is none.
"""

import os
import random
import re
import subprocess
import sys

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import protocol as proto
from unicode_fol_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
from unicode_fol_kit.atp.protocol import Prover9Backend, get_backend
from unicode_fol_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Not, Number, Or, Variable,
)
from unicode_fol_kit.fol.prover9_input import (
    Prover9ParsingError, parse_prover9, parse_prover9_problem,
)

x = Variable("x")
a, b, c = Constant("a"), Constant("b"), Constant("c")


def P(*args):
    return Atom("P", list(args))


def _strict(node):
    """A structural key that tells ``Number(1)`` from ``Number(1.0)`` (the nodes compare equal)."""
    return repr(node)


# --------------------------------------------------------------------------- #
# Names that can be written neither bare nor quoted.
# --------------------------------------------------------------------------- #

_NOT_WORDS = ["A b", "a b", "a.b", "a-b", "a%b", 'a"b', "", " ", "a\nb", "a(b)", "a,b", "a'b", "é b"]
_NON_ASCII = ["é", "Ünï", "Größe", "α"]


@pytest.mark.parametrize("name", _NOT_WORDS + _NON_ASCII)
def test_an_atom_whose_name_is_no_word_is_refused_by_name_at_every_arity(name):
    for node in (Atom(name, []), Atom(name, [a]), Atom(name, [a, b])):
        with pytest.raises(NotImplementedError) as refused:
            node.to_prover9()
        message = str(refused.value)
        assert repr(name) in message and "cannot be written for Prover9" in message
        assert "generate_prover9_input_with_mapping" in message       # the writer renames such a name


@pytest.mark.parametrize("name", _NOT_WORDS + _NON_ASCII)
def test_a_function_with_arguments_whose_name_is_no_word_is_refused_by_name(name):
    for node in (Function(name, [a]), Function(name, [a, b]), P(Function(name, [a]))):
        with pytest.raises(NotImplementedError) as refused:
            node.to_prover9()
        assert repr(name) in str(refused.value)


@pytest.mark.parametrize("name", _NOT_WORDS)
def test_a_constant_whose_name_is_no_word_is_refused_by_name(name):
    # (A non-ASCII letter is transliterated first, so only a name that stays no word is refused.)
    for node in (Constant(name), SortedConstant(name, "S"), Function(name, []), P(Constant(name))):
        with pytest.raises(NotImplementedError) as refused:
            node.to_prover9()
        assert repr(name) in str(refused.value) or repr(name.strip()) in str(refused.value)


def test_a_non_ascii_constant_is_still_transliterated_not_refused():
    assert Constant("é").to_prover9() == "u00e9" and Constant("θ").to_prover9() == "theta"
    assert Function("θ", []).to_prover9() == "theta"


@pytest.mark.parametrize("node, name", [
    (Atom("=", [a]), "="), (Atom("=", [a, b, c]), "="), (Atom("<", []), "<"), (Atom("≠", [a]), "≠"),
])
def test_a_comparison_at_a_number_of_arguments_other_than_two_is_refused(node, name):
    # Written infix it needs two operands; `=(a)` is text Prover9 reads as something else.
    with pytest.raises(NotImplementedError) as refused:
        node.to_prover9()
    assert repr(name) in str(refused.value)


def test_a_name_that_is_a_word_is_written_as_before():
    assert Atom("Rain", [x]).to_prover9() == "Rain(X)"
    assert Atom("2nd", [x]).to_prover9() == "2nd(X)"         # Prover9 reads a digit-leading word
    assert Atom("p_1", [a, b]).to_prover9() == "p_1(a, b)"
    assert Atom("_p", []).to_prover9() == '"_p"'
    assert Function("Mother", [a]).to_prover9() == "Mother(a)"
    assert Constant("c_Liquid").to_prover9() == "c_Liquid"
    assert Atom("=", [a, b]).to_prover9() == "(a = b)"


def test_the_writer_renames_every_such_name_instead_of_refusing_it():
    # a b / a.b / a-b are each written as the word of their characters, `a` + the escape of the
    # character (u0020, u002e, u002d) + `b`; the empty name is `s`. All distinct, all words.
    premises = [Atom("a b", [a]), Atom("a.b", []), P(Constant("a-b")), P(Function("a b", [a, a])),
                Atom("", [b])]
    text, names = generate_prover9_input_with_mapping(premises, Atom("é", [c]))
    lines = [line.strip() for line in text.splitlines()]
    assert lines[lines.index("formulas(assumptions).") + 1:lines.index("end_of_list.")] == [
        "au0020b(a).", "au002eb.", "P(au002db).", "P(au0020b2(a, a)).", "s(b)."]
    assert lines[lines.index("formulas(goals).") + 1] == "u00e9(c)."
    assert names.get_symbol("predicate", "a b", 1) == "au0020b"
    assert names.get_symbol("function", "a b", 2) == "au0020b2"      # the function of that name is the second symbol
    assert names.reverse()["au002db"] == "a-b"


# --------------------------------------------------------------------------- #
# $-words.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("node, name", [
    (Atom("$foo", []), "$foo"), (Atom("$less", [a, b]), "$less"), (Atom("$true", [a]), "$true"),
    (Atom("$false", [a, b]), "$false"), (P(Function("$sum", [a, b])), "$sum"),
    (P(Constant("$c")), "$c"), (P(SortedConstant("$c", "S")), "$c"), (Function("$f", []), "$f"),
    (P(Constant("$true")), "$true"),
])
def test_a_dollar_word_is_refused_by_name_by_every_single_renderer(node, name):
    with pytest.raises(NotImplementedError) as refused:
        node.to_prover9()
    message = str(refused.value)
    assert f"'{name}' is a '$'-word" in message and "$T and $F" in message


def test_the_truth_constants_are_still_written_as_prover9s_own():
    assert Atom("$true", []).to_prover9() == "$T" and Atom("$false", []).to_prover9() == "$F"
    assert And(Atom("$true", []), P(a)).to_prover9() == "($T & P(a))"
    text, _ = generate_prover9_input_with_mapping([Atom("$false", [])], Atom("Goal", []))
    assert "  $F." in text and "  goal." in text


@pytest.mark.parametrize("premises, conclusion, name", [
    ([Atom("$foo", [])], Atom("Goal", []), "$foo"),
    ([], Atom("$foo", [a]), "$foo"),
    ([P(Constant("$c"))], Atom("Goal", []), "$c"),
    ([], P(Function("$f", [a])), "$f"),
    ([P(SortedConstant("$c", "S"))], Atom("Goal", []), "$c"),
])
def test_the_writer_refuses_a_dollar_word_wherever_it_stands(premises, conclusion, name):
    with pytest.raises(NotImplementedError) as refused:
        generate_prover9_input_with_mapping(premises, conclusion)
    assert str(refused.value).startswith("generate_prover9_input_with_mapping: ")
    assert f"'{name}' is a '$'-word" in str(refused.value)


def test_the_backend_reports_a_dollar_word_as_unsupported_not_as_an_error():
    verdict = get_backend("prover9").decide(Atom("$foo", []), [Atom("$foo", [])], prover9_path="no-such-prover9",
                                            use_wsl=False)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "'$foo' is a '$'-word" in verdict.detail


# --------------------------------------------------------------------------- #
# Numerals.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("value, text", [
    (1, '"1"'), (0, '"0"'), (42, '"42"'), (10 ** 20, '"100000000000000000000"'),
    (-1, '"-1"'), (-42, '"-42"'), (2.5, '"2.5"'), (1.0, '"1"'), (-0.0, '"0"'), (0.1, '"0.1"'),
    (1e-07, '"0.0000001"'), (1e16, '"10000000000000000"'), (-2.5, '"-2.5"'),
    (100.0, '"100"'), (1e23, '"99999999999999991611392"'),
])
def test_a_numeral_is_its_value_in_double_quotes(value, text):
    # One quoted symbol per VALUE: an integral float is the integer it equals (the exact one:
    # the double nearest 10**23 is 99999999999999991611392), -0.0 is 0, anything else is the
    # positional text of the number. Every numeral is quoted, a non-negative integer too, because
    # Mace4 reads a bare integer as a distinct domain element of its own.
    assert Number(value).to_prover9() == text
    assert P(Number(value)).to_prover9() == f"P({text})"


def test_one_and_one_point_zero_are_one_numeral():
    # Number(1) == Number(1.0), so the two are one constant, one symbol.
    assert Number(1) == Number(1.0)
    assert Number(1).to_prover9() == Number(1.0).to_prover9() == '"1"'
    assert Number(0).to_prover9() == Number(-0.0).to_prover9() == '"0"'
    assert Number(2.5).to_prover9() != Number(2).to_prover9()


def test_a_numeral_inside_an_infix_term_is_written_the_same_way():
    assert Function("+", [Number(1), Number(2.5)]).to_prover9() == '("1" + "2.5")'
    assert Atom("<", [Number(-1), Number(0)]).to_prover9() == '("-1" < "0")'


def test_a_binary_minus_is_written_in_functional_notation():
    # Prover9 reads `-(a, b)`; `(a - b)` is a syntax error there. The unary minus is as before.
    assert Function("-", [a, b]).to_prover9() == "-(a, b)"
    assert Function("-", [a]).to_prover9() == "-(a)"
    assert Function("-", [Function("-", [a, b]), Number(1)]).to_prover9() == '-(-(a, b), "1")'
    assert Function("+", [a, b]).to_prover9() == "(a + b)" and Function("*", [a, b]).to_prover9() == "(a * b)"
    assert Function("/", [a, b]).to_prover9() == "(a / b)"


def test_an_arithmetic_symbol_at_a_number_of_arguments_without_a_notation_is_refused():
    for node in (Function("+", [a]), Function("*", [a, b, c]), Function("/", [])):
        with pytest.raises(NotImplementedError):
            node.to_prover9()


def test_the_writer_records_and_writes_each_numeral_once():
    # 1 and 1.0 are one numeral: both are written "1" and the map holds one entry for them.
    text, names = generate_prover9_input_with_mapping(
        [P(Number(2.5)), P(Number(1)), P(Number(-1)), P(Number(1.0)), P(Number(2.5))], P(Number(2.5)))
    lines = [line.strip() for line in text.splitlines()]
    assert lines[lines.index("formulas(assumptions).") + 1:lines.index("end_of_list.")] == [
        'P("2.5").', 'P("1").', 'P("-1").', 'P("1").', 'P("2.5").']
    assert names.numerals == {"2.5": '"2.5"', "1": '"1"', "-1": '"-1"'}


def test_a_number_and_a_constant_spelled_like_it_are_refused_by_name():
    # Number(1) and Constant('1') are ONE symbol for Z3 (both are named "1") and the TPTP writers
    # refuse the pair. This writer would write the number as "1" and the constant under another
    # word, two symbols, so it refuses too. A numeral is its VALUE, so Number(1.0) is the numeral
    # 1 and the constant '1' is spelled like it (it was written under two names, before).
    for premises, conclusion in (([P(Number(1))], P(Constant("1"))), ([P(Constant("1"))], P(Number(1))),
                                 ([P(Number(2.5))], P(Constant("2.5"))), ([P(Number(-1)), P(Constant("-1"))],
                                                                          P(a)),
                                 ([P(Number(1.0))], P(Constant("1")))):
        with pytest.raises(NotImplementedError) as refused:
            generate_prover9_input_with_mapping(premises, conclusion)
        assert " are spelled alike" in str(refused.value) and "the constant" in str(refused.value)
    # Not the same text as the number, so not the same symbol. Number(1.0) IS Number(1) (a value has
    # one spelling), written 1; the constant '1.0' is spelled like no numeral of the problem.
    generate_prover9_input_with_mapping([P(Number(1))], P(Constant("1.0")))
    generate_prover9_input_with_mapping([P(Number(1.0))], P(Constant("1.0")))
    generate_prover9_input_with_mapping([P(Number(1))], P(Constant("one")))


def test_the_backend_reports_a_number_spelled_like_a_constant_as_unsupported():
    verdict = get_backend("prover9").decide(P(Constant("1")), [P(Number(1))], prover9_path="no-such-prover9",
                                            use_wsl=False)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")


# -- the reader -------------------------------------------------------------- #

@pytest.mark.parametrize("text, expected", [
    ('P("2.5")', P(Number(2.5))), ('P("-1")', P(Number(-1))), ('P("0")', P(Number(0))),
    ('P("1")', P(Number(1))), ('(a = "-2.5")', Atom("=", [a, Number(-2.5)])),
    ('P(f("3"))', P(Function("f", [Number(3)]))),
    ("P(-(a, b))", P(Function("-", [a, b]))), ("P(-(a, b, c))", P(Function("-", [a, b, c]))),
    ("(-(a, b) = c)", Atom("=", [Function("-", [a, b]), c])),
    ("P(-(a, -(b, c)))", P(Function("-", [a, Function("-", [b, c])]))),
])
def test_the_reader_reads_a_quoted_numeral_and_the_functional_minus(text, expected):
    node = parse_prover9(text)
    assert _strict(node) == _strict(expected), (node, expected)


@pytest.mark.parametrize("text", ['P("2.50")', 'P("007")', 'P("-0")', 'P("+1")', 'P("1e5")', 'P("1.")',
                                  'P("1.0")', 'P("-0.0")', 'P("100.0")'])
def test_the_reader_refuses_a_quoted_numeral_that_is_not_the_canonical_spelling(text):
    # Prover9 keeps "2.50" and "2.5" apart, and "1.0" from "1"; a Number node is identified by its
    # value and has one text, so reading both spellings would merge two Prover9 symbols.
    with pytest.raises(Prover9ParsingError):
        parse_prover9(text)


def test_a_file_that_keeps_one_and_one_point_zero_apart_is_refused_not_merged():
    # Prover9 reads "1" and "1.0" as two constants; the kit's Number(1) and Number(1.0) are one,
    # so P("1") & Q("1.0") would say about one thing what the file says about two.
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9('P("1") & Q("1.0")')
    # The refusal names the two spellings it keeps apart.
    assert "the numerals 1 and 1.0 are written in one text" in str(refused.value)


def test_the_reader_reads_a_prefix_minus_as_the_term_Prover9_reads():
    # Prover9's prefix minus has priority 350, tighter than the comparisons (700) and the sums (500), so
    # `-(a)` in an argument is the term -(a) (Prover9 echoes `P(-a)`). The reader refused it before, on
    # the ground that `-(a)` at the start of an atom cannot be told from the negation of `(a)`: true
    # there, and in no other place a term can stand.
    assert parse_prover9("P(-(a))") == P(Function("-", [a]))
    assert parse_prover9("P(-a)") == P(Function("-", [a]))
    assert parse_prover9("P(-(-(a)))") == P(Function("-", [Function("-", [a])]))
    # The negation of a parenthesised formula is what it always was.
    assert parse_prover9("-(P(a) & Q(a))") == Not(And(P(a), Atom("Q", [a])))
    assert parse_prover9("-P(a) | Q(a)") == Or(Not(P(a)), Atom("Q", [a]))


@pytest.mark.parametrize("text, expected", [
    # Prover9 2026-8A echoes each of these as the comparison of TERMS (``-alpha = beta.``): the minus
    # belongs to the operand and the comparison to the whole.
    ("-(alpha) = beta", Atom("=", [Function("-", [Constant("alpha")]), Constant("beta")])),
    ("(-(alpha) = beta)", Atom("=", [Function("-", [Constant("alpha")]), Constant("beta")])),
    ("-alpha = beta", Atom("=", [Function("-", [Constant("alpha")]), Constant("beta")])),
    ("- f(alpha) = beta", Atom("=", [Function("-", [Function("f", [Constant("alpha")])]), Constant("beta")])),
    ("-alpha < beta", Atom("<", [Function("-", [Constant("alpha")]), Constant("beta")])),
    ("- - a = b", Atom("=", [Function("-", [Function("-", [a])]), b])),
    ("-(-(a)) = b", Atom("=", [Function("-", [Function("-", [a])]), b])),
    ("-a + b = c", Atom("=", [Function("+", [Function("-", [a]), b]), c])),
    ("-a * b = c", Atom("=", [Function("*", [Function("-", [a]), b]), c])),
    ("x = -(a)", Atom("=", [Constant("x"), Function("-", [a])])),
    # the bare numeral -1 is the number, also in front of a comparison
    ("-1 < x", Atom("<", [Number(-1), Constant("x")])),
    ("-3 + a = b", Atom("=", [Function("+", [Number(-3), a]), b])),
    # what is a negation stays one: a parenthesised comparison, and an atom with arguments
    ("-(alpha = beta)", Not(Atom("=", [Constant("alpha"), Constant("beta")]))),
    ("-(-(a) = b)", Not(Atom("=", [Function("-", [a]), b]))),
    ("alpha != beta", Atom("≠", [Constant("alpha"), Constant("beta")])),
    ("-P(a)", Not(P(a))),
    ("-a", Not(Atom("a", []))),
])
def test_a_prefix_minus_in_front_of_a_comparison_belongs_to_the_term(text, expected):
    assert parse_prover9(text) == expected


def test_the_text_of_a_unary_minus_equation_is_read_back_as_that_equation():
    node = Atom("=", [Function("-", [Constant("alpha")]), Constant("beta")])
    assert node.to_prover9() == "(-(alpha) = beta)"
    assert parse_prover9(node.to_prover9()) == node


def test_a_file_that_says_minus_alpha_is_beta_and_alpha_is_beta_is_consistent():
    # {-(alpha) = beta, alpha = beta} read as the contradiction {¬ alpha = beta, alpha = beta} proves
    # everything. It is consistent: U={0}, every constant 0, -(0) = 0, Q empty. So Q(alpha) is not valid
    # from it, and Z3 finds that structure.
    records = parse_prover9_problem("formulas(assumptions).\n  -(alpha) = beta.\n  alpha = beta.\nend_of_list.\n")
    premises = [record.formula for record in records]
    assert not any(isinstance(premise, Not) for premise in premises)
    assert api.prove(Atom("Q", [Constant("alpha")]), premises, backends=["z3"], timeout=20000).status == "refuted"


def _random_term(rng, depth):
    roll = rng.random()
    if depth == 0 or roll < 0.4:
        return rng.choice([Number(rng.choice([0, 1, 7, -1, -42, 2.5, -2.5, 1.0, 0.1, 1e-07, 1e16, -0.0])), a, b,
                           Variable("x")])
    if roll < 0.65:
        return Function("-", [_random_term(rng, depth - 1), _random_term(rng, depth - 1)])
    if roll < 0.77:
        # a one-argument minus, written -(t): in front of a comparison it must not be read as a negation
        return Function("-", [_random_term(rng, depth - 1)])
    if roll < 0.88:
        return Function(rng.choice("+*/"), [_random_term(rng, depth - 1), _random_term(rng, depth - 1)])
    return Function("f", [_random_term(rng, depth - 1) for _ in range(rng.randint(1, 3))])


def test_a_numeral_or_a_minus_survives_the_round_trip_through_the_text():
    # The text holds one symbol per VALUE, so Number(1.0) is read back as the equal node Number(1):
    # the round trip is exact up to node equality, and exact in repr for every other value.
    rng = random.Random(20261004)
    for _ in range(1500):
        node = Atom(rng.choice(["P", "R"]), [_random_term(rng, 3), _random_term(rng, 2)])
        assert parse_prover9(node.to_prover9()) == node, node.to_prover9()


def test_a_comparison_whose_left_side_is_a_minus_survives_the_round_trip_through_the_text():
    # The atom the reader got wrong: a comparison written infix, with a one-argument minus on the left.
    rng = random.Random(20261005)
    for _ in range(1500):
        node = Atom(rng.choice(["=", "≠", "<", ">", "≤", "≥"]),
                    [Function("-", [_random_term(rng, 2)]), _random_term(rng, 2)])
        assert parse_prover9(node.to_prover9()) == node, node.to_prover9()
        negated = Not(node)
        assert parse_prover9(negated.to_prover9()) == negated, negated.to_prover9()


def test_a_problem_with_numerals_is_read_back_by_the_reader():
    text, _ = generate_prover9_input_with_mapping(
        [P(Number(2.5), Number(1)), Atom("<", [Number(-1), Function("-", [a, b])])], Atom("Q", [Number(1.0)]))
    records = parse_prover9_problem(text)
    assert [r.role for r in records] == ["assumptions", "assumptions", "goals"]
    assert _strict(records[0].formula) == _strict(P(Number(2.5), Number(1)))
    assert _strict(records[1].formula) == _strict(Atom("<", [Number(-1), Function("-", [a, b])]))
    # Q(1.0) is written Q("1"), the one symbol of the value, and read back as Q(1): an equal node.
    assert records[2].formula == Atom("Q", [Number(1.0)])
    assert _strict(records[2].formula) == _strict(Atom("Q", [Number(1)]))


# -- the two spellings of one symbol ---------------------------------------- #

@pytest.mark.parametrize("text, what", [
    ('P("rain") & Q(rain)', "constant"),                       # one constant, two spellings
    ('"rain" & rain', "proposition"),                           # one proposition, two spellings
    ('"P"(a) & P(b)', "predicate"),                             # one predicate (arity 1), two spellings
    ('(f(a) = "f"(b))', "function"),                            # one function, two spellings
    ('P("g") & Q(g)', "constant"),
    ('(a = "1") & P(1)', "number"),                             # a numeral, quoted and bare
    ('P("2.5") & Q(2.5)', "number"),
])
def test_a_symbol_written_both_quoted_and_bare_is_refused_by_name(text, what):
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9(text)
    message = str(refused.value)
    assert f"the {what} " in message and "both with and without double quotes" in message


def test_the_two_spellings_are_refused_across_the_statements_of_a_file_too():
    # A file is one text: `rain` in one list and "rain" in another are two symbols to Prover9.
    text = 'formulas(assumptions).\n  P("rain").\nend_of_list.\nformulas(goals).\n  P(rain).\nend_of_list.\n'
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9_problem(text)
    assert "'rain'" in str(refused.value) and "both with and without double quotes" in str(refused.value)


@pytest.mark.parametrize("text", [
    '"Rain" & Rain(x)',                  # a proposition and a predicate: two symbols here too
    'P("Rain") & Q(Rain)',               # a quoted constant and a bare VARIABLE (upper case, term position)
    'P("rain") & Q("rain")',             # the same spelling twice
    "P(rain) & Q(rain)",
    '"Mother"(a) & Mother(a, b)',         # a quoted predicate of one argument and a bare one of two
    '"Mother"(a) & Q("Mother")',          # the quoted predicate and a quoted constant of its name
    'P("a", "b") & Q(c)',                 # different names
    '(a = "a"(b))',                      # a constant a and a function a of one argument: two symbols
    '"f"(a) & Q(f(a))',                  # a quoted predicate f and a bare FUNCTION f
])
def test_what_is_not_one_symbol_in_two_spellings_is_read(text):
    parse_prover9(text)


def test_the_text_the_single_renderers_write_is_never_refused_for_two_spellings():
    # The renderers quote exactly the variable-shaped constants and propositions, so one name is
    # never written both ways at one arity; the round trip over a name in every role is the proof.
    node = And(And(Atom("Rain", []), Atom("Rain", [Constant("Rain")])),
               Atom("=", [Function("Rain", [a]), Constant("Rain")]))
    assert parse_prover9(node.to_prover9()) == node


# --------------------------------------------------------------------------- #
# The banner.
# --------------------------------------------------------------------------- #

_BANNER = "Prover9 (64) version 2026-8A, August 2026."
_HELP = ("============================== Prover9 ===============================\n"
         + _BANNER + "\n"
         "Process 371 was started by someone on somewhere,\n"
         "Sun Oct  4 21:51:17 2026\n"
         'The command was "/mnt/d/prover9/Prover9-LADR-2026-8A/bin/prover9 -h".\n'
         "============================== end of head ===========================\n"
         "\nUsage: prover9 [-h] [-x] [-p] [-t <n>] [-m] [-r <dir>] [-f <files>]\n")


class _Run:
    """``subprocess.run`` stand-in: one canned outcome, every call recorded."""

    def __init__(self, stdout="", stderr="", returncode=0, raises=None):
        self.calls = []
        self.stdout, self.stderr, self.returncode, self.raises = stdout, stderr, returncode, raises

    def __call__(self, cmd, *args, **kwargs):
        self.calls.append((list(cmd), kwargs))
        if self.raises is not None:
            raise self.raises
        return subprocess.CompletedProcess(cmd, self.returncode, stdout=self.stdout, stderr=self.stderr)


@pytest.fixture()
def probe(monkeypatch):
    """A fake binary `fake-p9`, no cached version, no ambient WSL setting."""
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    monkeypatch.setenv("UFK_PROVER9", "fake-p9")
    monkeypatch.delenv("UFK_PROVER9_WSL", raising=False)
    return monkeypatch


def test_the_backend_reads_the_banner_line_from_help_not_from_version(probe):
    run = _Run(stdout=_HELP)
    probe.setattr(subprocess, "run", run)
    assert get_backend("prover9").solver_version() == _BANNER
    (command, kwargs), = run.calls
    assert command == ["fake-p9", "-h"]                         # Prover9 has no --version
    assert kwargs["stdin"] is subprocess.DEVNULL                  # it would read the caller's stdin
    assert kwargs["timeout"] and kwargs["timeout"] <= 10          # and the probe has a time limit


def test_the_banner_is_asked_for_once(probe):
    run = _Run(stdout=_HELP)
    probe.setattr(subprocess, "run", run)
    backend = get_backend("prover9")
    assert backend.solver_version() == backend.solver_version() == _BANNER
    assert len(run.calls) == 1


def test_the_banner_is_read_through_wsl_when_the_binary_lives_there(probe):
    run = _Run(stdout=_HELP)
    probe.setattr(subprocess, "run", run)
    probe.setenv("UFK_PROVER9_WSL", "1")
    assert get_backend("prover9").solver_version() == _BANNER
    assert [command for command, _ in run.calls] == [["wsl.exe", "fake-p9", "-h"]]


def test_the_banner_of_an_older_build_is_read_the_same_way(probe):
    run = _Run(stdout="=== Prover9 ===\nProver9 (64) version 2009-11A, November 2009.\nProcess 5 was started\n")
    probe.setattr(subprocess, "run", run)
    assert get_backend("prover9").solver_version() == "Prover9 (64) version 2009-11A, November 2009."


@pytest.mark.parametrize("stdout, stderr", [
    ("", ""), ("usage: prover9 [-h]\n", ""), ("============ Prover9 ============\n", ""),
    ("Fatal error:  Resume: no input file\n", ""),
])
def test_no_banner_is_no_version_and_is_not_an_error(probe, stdout, stderr):
    probe.setattr(subprocess, "run", _Run(stdout=stdout, stderr=stderr, returncode=1))
    assert get_backend("prover9").solver_version() is None


def test_a_banner_printed_with_a_failing_exit_is_still_the_banner(probe):
    probe.setattr(subprocess, "run", _Run(stdout=_HELP, returncode=1))
    assert get_backend("prover9").solver_version() == _BANNER


def test_the_banner_may_come_on_standard_error(probe):
    probe.setattr(subprocess, "run", _Run(stdout="", stderr=_HELP))
    assert get_backend("prover9").solver_version() == _BANNER


@pytest.mark.parametrize("failure", [
    FileNotFoundError("no such file"), subprocess.TimeoutExpired(["fake-p9", "-h"], 10),
    UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1, "invalid start byte"), PermissionError("denied"),
])
def test_a_probe_that_fails_is_no_version_and_never_raises(probe, failure):
    run = _Run(raises=failure)
    probe.setattr(subprocess, "run", run)
    backend = get_backend("prover9")
    assert backend.solver_version() is None
    assert backend.solver_version() is None and len(run.calls) == 1       # a miss is cached too


def test_the_verdict_carries_the_banner_of_the_binary_it_was_given(probe):
    import unicode_fol_kit.atp.prover9_entailment as p9

    run = _Run(stdout=_HELP)
    probe.setattr(subprocess, "run", run)
    probe.setattr(p9, "check_logical_entailment", lambda *args, **kwargs: True)
    verdict = get_backend("prover9").decide(P(a), [P(a)], prover9_path="other-p9", use_wsl=True)
    assert verdict.status == "proved" and verdict.solver_version == _BANNER
    assert [command for command, _ in run.calls] == [["wsl.exe", "other-p9", "-h"]]


def test_the_version_probe_does_not_wait_for_an_idle_inherited_stdin():
    # Prover9 reads its problem from standard input for any flag it does not know, and would
    # block on an inherited pipe (an MCP server's own protocol stream). The probe runs in a child
    # whose stdin is a pipe that stays open and silent; the stand-in tool reads stdin to its end
    # before it prints the banner, so a probe that let it see that pipe would sit out its
    # 10-second limit and report no version. Only the command line is swapped for the stand-in.
    package_root = os.path.dirname(os.path.dirname(os.path.abspath(proto.__file__)))
    env = dict(os.environ, PYTHONPATH=os.pathsep.join(
        [os.path.dirname(package_root)] + ([os.environ["PYTHONPATH"]] if os.environ.get("PYTHONPATH") else [])))
    child_code = (
        "import subprocess, sys, time\n"
        "real_run = subprocess.run\n"
        "tool = ('import sys; sys.stdin.read(); '\n"
        "        'print(\"=== Prover9 ===\\\\nProver9 (64) version 9.9, stand-in.\")')\n"
        "subprocess.run = lambda cmd, *a, **k: real_run([sys.executable, '-c', tool], *a, **k)\n"
        "from unicode_fol_kit.atp.protocol import Prover9Backend\n"
        "started = time.perf_counter()\n"
        "banner = Prover9Backend._banner('fake-prover9', False)\n"
        "print(f'{banner}|{time.perf_counter() - started:.2f}')\n")
    child = subprocess.Popen([sys.executable, "-c", child_code], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
    try:
        output = child.stdout.read()
        child.wait(timeout=60)
    finally:
        child.stdin.close()
        if child.poll() is None:
            child.kill()
    banner, elapsed = output.strip().rsplit("|", 1)
    assert banner == "Prover9 (64) version 9.9, stand-in."
    assert float(elapsed) < 8


# -- the real binary --------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    not _BINARY,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the offline tests above carry the claim")


@live
def test_live_the_real_binary_answers_with_its_banner():
    version = Prover9Backend().solver_version()
    assert version is not None and re.fullmatch(r"Prover9 \(\d+\) version \S+, .+\.", version), version
    verdict = get_backend("prover9").decide(P(a), [P(a)], timeout=30000)
    assert verdict.status == "proved" and verdict.solver_version == version


# name, premises, goal, expected, reason. Hand-derived from the definition: a numeral is an
# uninterpreted constant named by its VALUE (two numerals of different value may denote one
# element, 1 and 1.0 are one numeral), a function symbol is uninterpreted, `-1` the NUMBER is a
# constant and `-(1)` the function applied to 1.
_N = Number
_NUMERAL_PROBLEMS = [
    ("1 = 2", [], Atom("=", [_N(1), _N(2)]), "invalid", "U={0,1}, the numeral 1 is 0 and 2 is 1"),
    ("1 != 2", [], Atom("≠", [_N(1), _N(2)]), "invalid", "U={0}: both numerals denote 0"),
    ("P(1) |- P(1.0)", [P(_N(1))], P(_N(1.0)), "valid", "one numeral: Number(1) == Number(1.0)"),
    ("P(2.5) |- P(2.5)", [P(_N(2.5))], P(_N(2.5)), "valid", "one numeral"),
    ("P(-1) |- P(-1)", [P(_N(-1))], P(_N(-1)), "valid", "one numeral"),
    ("P(-1) |- P(1)", [P(_N(-1))], P(_N(1)), "invalid", "U={0,1}, -1=0, 1=1, P={0}"),
    ("P(-1) |- P(-(1))", [P(_N(-1))], P(Function("-", [_N(1)])), "invalid",
     "the numeral -1 is a constant, -(1) the function applied to the constant 1: U={0,1}, -1=0, 1=1, -(1)=1, P={0}"),
    ("P(-(1)) |- P(-1)", [P(Function("-", [_N(1)]))], P(_N(-1)), "invalid", "the same two terms, the other way"),
    ("1 + 1 = 2", [], Atom("=", [Function("+", [_N(1), _N(1)]), _N(2)]), "invalid",
     "no arithmetic: + is an uninterpreted function"),
    ("1 < 2", [], Atom("<", [_N(1), _N(2)]), "invalid", "< is an uninterpreted relation"),
    ("P(a - b) |- P(a - b)", [P(Function("-", [a, b]))], P(Function("-", [a, b])), "valid", "one term"),
    ("P(a - b) |- P(b - a)", [P(Function("-", [a, b]))], P(Function("-", [b, a])), "invalid",
     "- is an uninterpreted function: U={0,1}, a=0, b=1, -(0,1)=0, -(1,0)=1, P={0}"),
    ("P(-(a)) |- P(-(a, a))", [P(Function("-", [a]))], P(Function("-", [a, a])), "invalid",
     "- of one argument and - of two arguments are two functions"),
]


@live
@pytest.mark.parametrize("name, premises, goal, expected, reason", _NUMERAL_PROBLEMS,
                         ids=[p[0] for p in _NUMERAL_PROBLEMS])
def test_live_prover9_never_contradicts_the_z3_route_on_numerals(name, premises, goal, expected, reason):
    # Z3 (numerals are uninterpreted constants named by their value) is the second oracle.
    z3 = api.prove(goal, premises, backends=["z3"], timeout=20000).status
    assert z3 == ("proved" if expected == "valid" else "refuted"), (name, reason, z3)
    result = get_backend("prover9").decide(goal, premises, timeout=30000)
    if expected == "valid":
        assert result.status == "proved", (name, reason, result)
    else:
        assert (result.status, result.reason) == ("unknown", "incomplete"), (name, reason, result)


@live
@pytest.mark.parametrize("word", ["all", "exists", "v", "set", "end_of_list", "label"])
def test_live_a_predicate_named_like_a_prover9_word_is_read_as_a_predicate(word):
    # ∃w:S W(w) ∧ ... : the guard atom is W(X) at the start of an operand. Valid: S is non-empty.
    premises = [SortedQuantifier("∀", x, "Q", Atom("=", [c, Constant("d")]))]
    goal = SortedQuantifier("∃", Variable("w"), word,
                            SortedQuantifier("∀", x, "Q", Atom("=", [c, Constant("d")])))
    assert get_backend("prover9").decide(goal, premises, timeout=30000).status == "proved"
