r"""A numeral is a constant on every TPTP problem writer, and ``+ - * /  < > ≤ ≥`` are ordinary symbols.

On a route that was not asked for arithmetic the kit reads a ``Number`` as a CONSTANT identified by
its value (``1``, ``1.0`` and ``01`` are one constant), knows nothing else about it, reads ``+ - * /``
as uninterpreted function symbols and ``< > ≤ ≥`` as uninterpreted binary predicates. TPTP says
otherwise of the text ``Number.to_tptp`` writes (``1`` is an ``$int``, ``$sum`` and ``$less`` are
arithmetic: Vampire 5.0.1 and E 3.5.1 prove ``$less(1,2)``, ``1 != 2`` and ``$sum(1,1) = 2``, and
refuse ``p(1)`` as a type error), so the problem writers write a numeral under a word of the target
grammar that the ordinary renamer chose, record it in the name map and read it back.

Every expected text and answer below is derived BY HAND from that definition. The ``fof`` word of a
numeral is the renamer's: the numeral ``1`` is the constant named ``1``, which is no TPTP word, so it
gets the digit-leading replacement ``n1`` (the prefix ``n``); ``-1`` gets ``u002d1`` (the code-point
escape of the ``-``); ``2.5`` gets ``n2u002e5``; ``+`` is ``u002b``, ``<`` is ``u003c``.

The answers of the live tests are the hand-derived column of the acceptance table (valid / not valid
by the one-universe reading of the kit), run on Vampire and E where they are reachable and skipped,
never weakened, where they are not:

* A1 ``∀x P(x) ⊢ P(1)`` valid (an instance)
* A2 ``P(1) ⊢ P(1.0)`` valid (one constant)
* A3 ``⊢ 1 ≠ 2`` not valid (a one-element universe)
* A4 ``⊢ 1 < 2`` not valid (``<`` empty)
* A5 ``⊢ 1 + 1 = 2`` not valid (universe {0, 1}: ``1`` is 0, ``2`` is 1, ``+`` constantly 0)
* A6 ``P(1), P(2) ⊢ ∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))`` not valid (a one-element universe)
* A7 ``P(1) ⊢ P(one)`` not valid (universe {0, 1}: ``1`` is 0, ``one`` is 1, P = {0})
* A8 ``∀x ∀y x + y = y + x ⊢ 1 + 2 = 2 + 1`` valid (an instance)
* A9 ``∀x (x < 2 → Q(x)), 1 < 2 ⊢ Q(1)`` valid (an instance and modus ponens)
* A10 ``⊢ 2.5 = 2.5`` valid (reflexivity: a decimal must be writable)
* A11 ``P(-1) ⊢ ∃x P(x)`` valid (a negative numeral must be writable)
"""

import random
import re
import shutil
import subprocess

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp._tff_problem import generate_tff_arith_problem
from unicode_logic_kit.atp._tptp_problem import (
    TptpNameMap, apply_reverse_tptp, generate_tptp_problem, generate_tptp_problem_for_prover,
    generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.atp._ascii_names import reverse_map_text
from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed, eprover_available
from unicode_logic_kit.atp.protocol import get_backend
from unicode_logic_kit.atp.resolution_check import (
    ResolutionDerivation, ResolutionStep, verify_resolution_proof,
)
from unicode_logic_kit.atp.tptp_tff import (
    Tf0Refusal, formula_to_tff, generate_tff_problem, generate_tff_problem_with_mapping,
    infer_tff_signature,
)
from unicode_logic_kit.atp.tstp import (
    _to_tstp_with_mapping, parse_tstp_derivation, reverse_map_derivation, to_tstp,
)
from unicode_logic_kit.atp.twee_entailment import twee_available
from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed
from unicode_logic_kit.fol._numeral_symbols import (
    numeral_name, numeral_value, numerals_as_constants, prefixed_numeral_name, term_numerals,
)
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Node, Not, Number, Or, Quantifier,
    SortedConstant, SortedQuantifier, Variable, substitute,
)
from unicode_logic_kit.fol.tptp_input import parse_tptp_formula

X, Y = Variable("x"), Variable("y")
LOWER_WORD = re.compile(r"[a-z][A-Za-z0-9_]*")


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def eq(a, b):
    return Atom("=", [a, b])


def plus(a, b):
    return Function("+", [a, b])


def forall(v, body):
    return Quantifier("∀", v, body)


def exists(v, body):
    return Quantifier("∃", v, body)


def lines(text):
    return [ln for ln in text.splitlines() if ln.strip()]


# ---------------------------------------------------------------------------------------------
# The numeral's name: one per VALUE
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("value, name", [
    (1, "1"), (1.0, "1"), (2, "2"), (2.5, "2.5"), (-1, "-1"), (-1.0, "-1"), (0, "0"), (-0.0, "0"),
    (100.0, "100"), (0.25, "0.25"), (True, "1"),
])
def test_numeral_name_is_the_text_of_the_value_with_an_integral_float_spelled_as_the_integer(value, name):
    assert numeral_name(value) == name


def test_equal_numerals_have_one_name_and_different_values_two():
    assert Number(1) == Number(1.0)                      # the kit's own notion of "one constant"
    assert numeral_name(1) == numeral_name(1.0)
    assert numeral_name(1) != numeral_name(2) and numeral_name(2) != numeral_name(2.5)


@pytest.mark.parametrize("name, value", [("1", 1), ("-1", -1), ("2.5", 2.5), ("0", 0)])
def test_the_value_of_a_name_is_the_number(name, value):
    got = numeral_value(name)
    assert got == value and type(got) is type(value)
    assert numeral_value(numeral_name(value)) == value


def test_the_higher_order_spelling_has_an_n_in_front():
    assert prefixed_numeral_name(1) == "n1" and prefixed_numeral_name(1.0) == "n1"
    assert prefixed_numeral_name(2.5) == "n2.5" and prefixed_numeral_name(-1) == "n-1"


@pytest.mark.parametrize("value", [float("inf"), float("-inf"), float("nan")])
def test_a_non_finite_value_has_no_name(value):
    with pytest.raises(ValueError, match="no literal"):
        numeral_name(value)


def test_a_value_that_is_no_int_or_float_is_refused_by_name():
    from fractions import Fraction
    with pytest.raises(NotImplementedError, match="Fraction"):
        numerals_as_constants([P(Number(Fraction(1, 2)))], where="w")


def test_only_numerals_in_term_position_are_rewritten():
    """The bound of a counting quantifier is not a term: ``∃≥2 x P(x, 1)`` keeps its ``2``."""
    count = Count("ge", Number(2), X, P(X, Number(1)))
    (rewritten,), names = numerals_as_constants([count], where="w")
    assert names == frozenset({"1"})
    assert rewritten == Count("ge", Number(2), X, P(X, Constant("1")))
    assert [n.value for n in term_numerals(count)] == [1]


def test_a_formula_without_a_numeral_comes_back_as_the_same_object():
    f = P(Constant("a"))
    (g,), names = numerals_as_constants([f], where="w")
    assert g is f and names == frozenset()


# ---------------------------------------------------------------------------------------------
# The fof writer: no bare number, no dollar word, one word per value
# ---------------------------------------------------------------------------------------------

def test_fof_text_of_one_constant_in_two_spellings_is_exact():
    """P(1) ⊢ P(1.0): the numeral is the constant ``1`` (a word of its own: ``n1``) in both places."""
    text = generate_tptp_problem([P(Number(1))], P(Number(1.0)))
    assert lines(text) == ["fof(premise_1, axiom, p(n1)).", "fof(goal, conjecture, p(n1))."]


def test_fof_text_of_two_numerals_has_two_words():
    text = generate_tptp_problem([], Atom("≠", [Number(1), Number(2)]))
    assert lines(text) == ["fof(goal, conjecture, (n1 != n2))."]


def test_fof_text_of_the_operators_is_ordinary_symbols():
    """``1 + 1 = 2`` is ``u002b(n1,n1) = n2``, with no ``$sum``: ``+`` is no TPTP word, so it gets the
    code-point escape of its character (U+002B)."""
    text = generate_tptp_problem([], eq(plus(Number(1), Number(1)), Number(2)))
    assert lines(text) == ["fof(goal, conjecture, (u002b(n1,n1) = n2))."]


@pytest.mark.parametrize("op, word", [("<", "u003c"), (">", "u003e"), ("≤", "u2264"), ("≥", "u2265")])
def test_fof_text_of_a_comparison_is_an_ordinary_predicate(op, word):
    text = generate_tptp_problem([], Atom(op, [Number(1), Number(2)]))
    assert lines(text) == [f"fof(goal, conjecture, {word}(n1,n2))."]


@pytest.mark.parametrize("op, word", [("+", "u002b"), ("-", "u002d"), ("*", "u002a"), ("/", "u002f")])
def test_fof_text_of_each_operator_is_an_ordinary_function(op, word):
    text = generate_tptp_problem([], eq(Function(op, [Constant("a"), Constant("b")]), Constant("c")))
    assert lines(text) == [f"fof(goal, conjecture, ({word}(a,b) = c))."]


@pytest.mark.parametrize("value, word", [(2.5, "n2u002e5"), (-1, "u002d1"), (0, "n0"), (100.0, "n100")])
def test_fof_text_writes_a_decimal_and_a_negative_numeral_as_a_legal_word(value, word):
    text = generate_tptp_problem([P(Number(value))], eq(Number(value), Number(value)))
    assert lines(text) == [f"fof(premise_1, axiom, p({word})).",
                           f"fof(goal, conjecture, ({word} = {word}))."]
    assert LOWER_WORD.fullmatch(word)


def test_fof_text_never_holds_a_dollar_word_a_number_or_a_quoted_object():
    """No numeral is written as a number (an ``$int``), no operator as an arithmetic ``$`` word, and
    no numeral as a double-quoted distinct object (TPTP makes those pairwise distinct)."""
    formula = Implies(And(Atom("<", [Number(1), Number(2.5)]), P(plus(Number(-1), Number(0)))),
                      Atom("≥", [Function("*", [Number(3), Number(4)]), Function("/", [Number(5), Number(6)])]))
    text = generate_tptp_problem([], formula)
    body = text.split(", conjecture, ", 1)[1]
    assert "$" not in text and '"' not in text
    assert not re.search(r"(?<![A-Za-z0-9_])-?\d", body), body        # no bare number anywhere
    for word in re.findall(r"[A-Za-z_][A-Za-z0-9_]*(?=\()", body):
        assert LOWER_WORD.fullmatch(word)


def test_the_word_of_a_numeral_does_not_depend_on_where_it_occurs():
    first = generate_tptp_problem([P(Number(1)), Q(Number(2))], P(Number(2)))
    second = generate_tptp_problem([Q(Number(2)), P(Number(1))], P(Number(2)))
    assert "p(n1)" in first and "q(n2)" in first and "p(n2)" in first
    assert "p(n1)" in second and "q(n2)" in second and "p(n2)" in second


def test_a_counting_bound_is_not_written_as_a_constant():
    """``∃≥2 x P(x, 1)``: the matrix has the constant ``n1``; the bound ``2`` is expanded into two
    witnesses and is no symbol of the problem."""
    count = Count("ge", Number(2), X, P(X, Number(1)))
    text, name_map = generate_tptp_problem_with_mapping([], count)
    assert "n1" in text and "n2" not in text
    assert name_map.numerals == frozenset({"1"})


# ---------------------------------------------------------------------------------------------
# The name map: what a numeral and an operator were written as
# ---------------------------------------------------------------------------------------------

def test_the_name_map_records_numerals_and_operators():
    text, name_map = generate_tptp_problem_with_mapping(
        [], Atom("<", [plus(Number(1), Number(2.5)), Number(-1)]))
    assert name_map.numerals == frozenset({"1", "2.5", "-1"})
    assert name_map.term == {"+": "u002b", "1": "n1", "2.5": "n2u002e5", "-1": "u002d1"}
    assert name_map.predicate == {"<": "U003c"}                  # the kit's upper-initial predicate token
    assert name_map.reverse_numerals() == {"n1": 1, "n2u002e5": 2.5, "u002d1": -1}


def test_a_map_of_a_problem_without_a_numeral_has_none():
    _, name_map = generate_tptp_problem_with_mapping([P(Constant("a"))], P(Constant("a")))
    assert name_map.numerals == frozenset() and name_map.reverse_numerals() == {}
    assert TptpNameMap().numerals == frozenset()


def test_a_numeral_never_takes_the_word_of_a_constant_the_user_wrote():
    """The user's constant ``n1`` keeps its word (an already-legal name is never renamed); the numeral
    ``1`` gets the next free one, ``n12``, and the two stay two symbols."""
    text, name_map = generate_tptp_problem_with_mapping([P(Number(1))], Q(Constant("n1")))
    assert lines(text) == ["fof(premise_1, axiom, p(n12)).", "fof(goal, conjecture, q(n1))."]
    assert name_map.term == {"n1": "n1", "1": "n12"} and name_map.numerals == frozenset({"1"})
    back = apply_reverse_tptp(parse_tptp_formula("p(n12) => q(n1)"), name_map)
    assert back == Implies(P(Number(1)), Q(Constant("n1")))


def test_an_operator_never_takes_the_word_of_a_function_the_user_wrote():
    user = Function("u002b", [Constant("a"), Constant("b")])
    text, name_map = generate_tptp_problem_with_mapping(
        [eq(user, Constant("c"))], eq(plus(Constant("a"), Constant("b")), Constant("c")))
    assert lines(text) == ["fof(premise_1, axiom, (u002b(a,b) = c)).",
                           "fof(goal, conjecture, (u002b2(a,b) = c))."]
    assert name_map.term["+"] == "u002b2" and name_map.term["u002b"] == "u002b"


def test_a_numeral_never_takes_the_word_of_a_predicate_either():
    """The predicate ``N1`` is written ``n1``; a function or constant may not share a predicate's word
    (a prover is not obliged to resolve it by position), so the numeral is separated to ``n1_term``,
    and the map has the word that was written."""
    text, name_map = generate_tptp_problem_with_mapping([Atom("N1", [Number(1)])], Atom("N1", [Number(1)]))
    assert lines(text) == ["fof(premise_1, axiom, n1(n1_term)).", "fof(goal, conjecture, n1(n1_term))."]
    assert name_map.term == {"1": "n1_term"} and name_map.numerals == frozenset({"1"})
    back = apply_reverse_tptp(parse_tptp_formula("n1(n1_term)"), name_map)
    assert back == Atom("N1", [Number(1)])


@pytest.mark.parametrize("write", [generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping],
                         ids=["fof", "tf0"])
def test_a_numeral_never_takes_the_word_of_a_sort_either(write):
    """The sort ``N1`` is the word ``n1`` (the guard predicate of the fof text, the type of the TF0 text),
    which no constant may share: the numeral ``1`` is written ``n1_term`` and the map says so."""
    premise = SortedQuantifier("∀", X, "N1", Q(X))
    text, name_map = write([premise], Atom("R", [Number(1)]))
    assert lines(text)[-1].endswith("r(n1_term)).") or lines(text)[-1].endswith("r(n1_term) ).")
    assert name_map.term == {"1": "n1_term"} and name_map.numerals == frozenset({"1"})
    assert name_map.reverse_numerals() == {"n1_term": 1}
    assert apply_reverse_tptp(parse_tptp_formula("r(n1_term)"), name_map) == Atom("R", [Number(1)])


@pytest.mark.parametrize("make", [
    lambda: ([P(Number(1))], Q(Constant("1"))),
    lambda: ([P(Number(1.0))], Q(Constant("1"))),
    lambda: ([P(Number(1))], Q(Function("1", [Constant("a")]))),
    lambda: ([P(Number(1))], Q(SortedConstant("1", "Srt"))),
    lambda: ([P(Number(2.5))], Q(Constant("2.5"))),
    lambda: ([P(Number(-1))], Q(Constant("-1"))),
], ids=["int", "float", "function", "sorted constant", "decimal", "negative"])
def test_a_constant_spelled_like_a_numeral_is_refused_by_name_on_every_writer(make):
    """``Number(1)`` and ``Constant('1')`` would be one name, so one symbol; the kit refuses to merge them.

    ``Number(1.0)`` IS ``Number(1)`` (a value has one spelling), so the constant spelled like it is
    ``'1'``; the constant ``'1.0'`` is spelled like no numeral, and is another symbol (the test below)."""
    premises, goal = make()
    for write in (generate_tptp_problem, generate_tptp_problem_with_mapping, generate_tff_problem,
                  generate_tff_problem_with_mapping):
        with pytest.raises(NotImplementedError, match="spelled alike") as caught:
            write(premises, goal)
        assert str(caught.value).startswith(write.__name__ + ":")
    with pytest.raises(NotImplementedError, match="spelled alike"):
        formula_to_tff(And(premises[0], goal))


@pytest.mark.parametrize("name", ["01", "one", "1.0", "n1", "1e3"])
def test_a_constant_that_is_not_spelled_like_the_numeral_is_another_symbol(name):
    """``Number(1)`` is written ``1``, never ``01``, ``one``, ``1.0`` or ``n1``: no clash, two symbols."""
    text, name_map = generate_tptp_problem_with_mapping([P(Number(1))], P(Constant(name)))
    premise, goal = lines(text)
    assert premise.split("p(")[1] != goal.split("p(")[1]
    assert apply_reverse_tptp(parse_tptp_formula("p(" + name_map.term[name] + ")"), name_map) == P(Constant(name))


def test_the_constant_spelled_like_the_float_form_of_a_numeral_is_another_symbol():
    """``Number(1.0)`` is the numeral ``1``, written ``1`` once, so the constant ``'1.0'`` is no
    spelling of it: two symbols, no refusal, and each reads back as the node it was."""
    text, name_map = generate_tptp_problem_with_mapping([P(Number(1.0))], P(Constant("1.0")))
    premise, goal = lines(text)
    assert premise.split("p(")[1] != goal.split("p(")[1]
    assert name_map.numerals == frozenset({"1"})
    assert apply_reverse_tptp(parse_tptp_formula("p(" + name_map.term["1.0"] + ")"), name_map) == P(Constant("1.0"))


# ---------------------------------------------------------------------------------------------
# Reading a prover's text back
# ---------------------------------------------------------------------------------------------

def test_a_proofs_formulas_read_back_with_the_numbers_and_the_operators():
    _, name_map = generate_tptp_problem_with_mapping(
        [], Implies(P(plus(Number(1), Number(2.5))), Atom("<", [Number(-1), Number(2)])))
    parsed = parse_tptp_formula("p(u002b(n1,n2u002e5)) => u003c(u002d1,n2)")
    assert apply_reverse_tptp(parsed, name_map) == Implies(
        P(plus(Number(1), Number(2.5))), Atom("<", [Number(-1), Number(2)]))


def test_the_number_that_comes_back_is_the_number_not_a_constant_spelled_alike():
    _, name_map = generate_tptp_problem_with_mapping([], P(Number(1)))
    back = apply_reverse_tptp(parse_tptp_formula("p(n1)"), name_map)
    assert isinstance(back.args[0], Number) and back.args[0] == Number(1)
    assert not isinstance(back.args[0], Constant)


def test_raw_prover_text_reads_back_with_the_numerals_and_operators_spelled_as_the_kit_does():
    _, name_map = generate_tptp_problem_with_mapping(
        [P(plus(Number(1), Number(2)))], P(Number(3)))
    pred_rev, term_rev = name_map.reverse_rendered()
    assert reverse_map_text("p(u002b(n1,n2)) | ~p(n3)", pred_rev, term_rev) == "P(+(1,2)) | ~P(3)"


def test_a_numeral_of_the_typed_map_reads_back_too():
    _, name_map = generate_tff_problem_with_mapping([P(Number(1))], P(Number(2.5)))
    assert name_map.numerals == frozenset({"1", "2.5"})
    assert apply_reverse_tptp(parse_tptp_formula("p(n2u002e5)"), name_map) == P(Number(2.5))


def test_round_trip_of_random_ground_terms_through_the_writer_and_the_reader():
    rng = random.Random(20240601)
    values = [1, 1.0, 2, 2.5, -1, 0, 7.25]

    def term(depth):
        if depth == 0 or rng.random() < 0.4:
            return Number(rng.choice(values)) if rng.random() < 0.7 else Constant("cc")
        return Function(rng.choice(["+", "-", "*", "/", "ff"]), [term(depth - 1), term(depth - 1)])

    for _ in range(60):
        goal = Atom(rng.choice(["P", "<", "≥"]), [term(2), term(2)])
        text, name_map = generate_tptp_problem_with_mapping([], goal)
        body = text.split(", conjecture, ", 1)[1].rsplit(").", 1)[0]
        assert apply_reverse_tptp(parse_tptp_formula(body), name_map) == goal, body


# ---------------------------------------------------------------------------------------------
# The typed (TF0) writer: a numeral is a declared constant of $i, an operator an uninterpreted symbol
# ---------------------------------------------------------------------------------------------

def test_tf0_text_declares_a_numeral_as_a_constant_of_the_individual_type():
    text = generate_tff_problem([P(Number(1))], P(Number(1.0)))
    assert lines(text) == [
        "tff(const_decl_1, type, n1: $i ).",
        "tff(pred_decl_2, type, p: $i > $o ).",
        "tff(premise_1, axiom, p(n1) ).",
        "tff(goal, conjecture, p(n1) ).",
    ]


def test_tf0_text_declares_an_operator_as_an_uninterpreted_function():
    text = generate_tff_problem([], eq(plus(Number(1), Number(1)), Number(2)))
    assert lines(text) == [
        "tff(func_decl_1, type, u002b: ($i * $i) > $i ).",
        "tff(const_decl_2, type, n1: $i ).",
        "tff(const_decl_3, type, n2: $i ).",
        "tff(goal, conjecture, u002b(n1,n1) = n2 ).",
    ]


def test_tf0_text_declares_a_comparison_as_an_uninterpreted_predicate():
    text = generate_tff_problem([Atom("<", [Number(1), Number(2)])], Atom("≤", [Number(2), Number(1)]))
    assert lines(text) == [
        "tff(const_decl_1, type, n1: $i ).",
        "tff(const_decl_2, type, n2: $i ).",
        "tff(pred_decl_3, type, u003c: ($i * $i) > $o ).",
        "tff(pred_decl_4, type, u2264: ($i * $i) > $o ).",
        "tff(premise_1, axiom, u003c(n1,n2) ).",
        "tff(goal, conjecture, u2264(n2,n1) ).",
    ]


def test_tf0_map_records_numerals_and_reads_back():
    _, name_map = generate_tff_problem_with_mapping([P(Number(1))], eq(plus(Number(1), Number(2)), Number(3)))
    assert name_map.numerals == frozenset({"1", "2", "3"})
    assert name_map.term["+"] == "u002b" and name_map.term["1"] == "n1"
    back = apply_reverse_tptp(parse_tptp_formula("u002b(n1,n2) = n3"), name_map)
    assert back == eq(plus(Number(1), Number(2)), Number(3))


def test_tf0_text_with_a_sort_keeps_the_numeral_at_the_individual_type():
    """The sorted premise is irrelevant to the numeral: ``∃x:Srt Rr(x)`` is a sort that no numeral is in."""
    text = generate_tff_problem([SortedQuantifier("∃", X, "Srt", Atom("Rr", [X]))], P(Number(1)))
    assert "tff(const_decl_2, type, n1: $i )." in lines(text)
    assert "tff(sort_decl_1, type, srt: $tType )." in lines(text)


def test_tf0_refuses_a_numeral_that_the_inference_would_put_into_a_sort():
    """``∀x:Srt Q(x), Q(1)``: ``Q``'s argument position holds the sort, and the numeral stands there. A
    numeral has no annotation (it is any element of the universe), so the typed text would assert that
    ``1`` is in ``Srt``: refused by name, with the reason."""
    premise = SortedQuantifier("∀", X, "Srt", Q(X))
    with pytest.raises(Tf0Refusal, match="numeral 1") as caught:
        generate_tff_problem([premise], Q(Number(1)))
    assert caught.value.reason == "unsorted_term_in_sort"
    assert "cannot be written with a sort" in str(caught.value)


def test_the_automatic_mode_writes_fof_for_a_numeral_the_typed_text_would_sort():
    premise = SortedQuantifier("∀", X, "Srt", Q(X))
    built = generate_tptp_problem_for_prover([premise], Q(Number(1)), tff=None)
    assert built.dialect == "fof" and built.tff_refusal is not None and "numeral 1" in built.tff_refusal
    assert "q(n1)" in built.text and "fof(nonempty_sort_1" in built.text
    with pytest.raises(Tf0Refusal):
        generate_tptp_problem_for_prover([premise], Q(Number(1)), tff=True)


def test_signature_inference_is_no_decision_route_and_still_refuses_arithmetic_by_name():
    with pytest.raises(NotImplementedError, match="arithmetic"):
        infer_tff_signature([P(Number(1))])
    with pytest.raises(NotImplementedError, match="arithmetic"):
        infer_tff_signature([Atom("<", [Constant("a"), Constant("b")])])


# ---------------------------------------------------------------------------------------------
# The arithmetic reading is asked for by name, and is not touched
# ---------------------------------------------------------------------------------------------

def test_the_typed_arithmetic_writer_still_writes_numbers_and_dollar_words():
    goal = eq(plus(Number(1), Number(1)), Number(2))
    text, name_map = generate_tff_arith_problem([], goal, sort="int")
    assert text == "tff(goal, conjecture, ($sum(1,1) = 2) ).\n"
    assert name_map.numerals == frozenset()
    text, _ = generate_tff_arith_problem([], Atom("<", [Number(1), Number(2)]), sort="real")
    assert text == "tff(goal, conjecture, $less(1.0,2.0) ).\n"


def test_the_single_formula_renderers_keep_the_arithmetic_spelling_and_say_so():
    """``to_tptp`` of ONE node is the arithmetic spelling; a problem is written by the checked writers."""
    # Number(1.0) IS Number(1): a value has one spelling, so there is no ``1.0`` to write for it
    # (a value that is no whole number, 2.5, keeps its point).
    assert Number(1).to_tptp() == "1" and Number(1.0).to_tptp() == "1" and Number(2.5).to_tptp() == "2.5"
    assert plus(Number(1), Number(1)).to_tptp() == "$sum(1,1)"
    assert Atom("<", [Number(1), Number(2)]).to_tptp() == "$less(1,2)"
    for method in (Number.to_tptp, Function.to_tptp, Atom.to_tptp):
        doc = method.__doc__
        assert "ARITHMETIC spelling" in doc and "checked writers" in doc and "generate_tptp_problem_with_mapping" in doc


def test_the_same_atom_is_arithmetic_in_the_single_renderer_and_ordinary_in_the_writer():
    """The same atom: the single renderer writes ``$less``, the writer does not."""
    atom = Atom("<", [Constant("a"), Constant("b")])
    assert atom.to_tptp() == "$less(a,b)"
    assert "$less" not in generate_tptp_problem([], atom)


# ---------------------------------------------------------------------------------------------
# The kit's own TSTP writer follows the same reading
# ---------------------------------------------------------------------------------------------

def _refutation_with_numerals():
    one, one_again = P(Number(1)), Not(P(Number(1.0)))
    inputs = (frozenset({one}), frozenset({one_again}))
    steps = (
        ResolutionStep(1, frozenset({one}), "input"),
        ResolutionStep(2, frozenset({one_again}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    derivation = ResolutionDerivation(inputs, steps)
    assert verify_resolution_proof(derivation).ok
    return derivation


def test_to_tstp_writes_a_numeral_as_the_constant_of_its_value():
    """{P(1)}, {¬P(1.0)} resolve to the empty clause (one constant, so the literals are complementary);
    the text has the word of the constant, once."""
    text = to_tstp(_refutation_with_numerals())
    assert text == (
        "cnf(c1, plain, p(n1)).\n"
        "cnf(c2, plain, ~(p(n1))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )


def test_to_tstp_text_reads_back_to_the_numbers_through_its_final_map():
    text, name_map = _to_tstp_with_mapping(_refutation_with_numerals())
    assert name_map.numerals == frozenset({"1"})
    derivation = reverse_map_derivation(parse_tstp_derivation(text), name_map)
    assert [step.formula for step in derivation.steps[:2]] == [P(Number(1)), Not(P(Number(1)))]


def test_to_tstp_reuses_the_word_of_a_problem_map():
    """A problem map that already has the numeral keeps its spelling in the proof."""
    _, problem_map = generate_tptp_problem_with_mapping([Q(Constant("n1"))], P(Number(1)))
    text = to_tstp(_refutation_with_numerals(), name_map=problem_map)
    assert "p(n12)" in text and "n1)" not in text.replace("n12)", "")


def test_to_tstp_writes_the_operators_as_ordinary_symbols():
    a_plus = P(plus(Constant("a"), Constant("b")))
    derivation = ResolutionDerivation(
        (frozenset({a_plus}), frozenset({Not(a_plus)})),
        (ResolutionStep(1, frozenset({a_plus}), "input"),
         ResolutionStep(2, frozenset({Not(a_plus)}), "input"),
         ResolutionStep(3, frozenset(), "resolve", (1, 2))))
    assert verify_resolution_proof(derivation).ok
    text = to_tstp(derivation)
    assert "u002b(a,b)" in text and "$sum" not in text


# ---------------------------------------------------------------------------------------------
# The other writers of the TPTP family
# ---------------------------------------------------------------------------------------------

def test_the_higher_order_writers_write_one_constant_per_value_and_refuse_a_merge():
    from unicode_logic_kit.fol.qml import to_thf_modal
    from unicode_logic_kit.fol.nodes import Box
    from unicode_logic_kit.hol.classical import to_isabelle_fol, to_thf_fol, to_thf_msfol
    from unicode_logic_kit.hol.free import to_thf_free
    from unicode_logic_kit.hol.thf_modal import to_thf_modal_full

    same = Implies(P(Number(1)), P(Number(1.0)))
    for write, formula in ((to_thf_fol, same), (to_thf_msfol, same), (to_thf_free, same),
                           (to_thf_modal, Box(same)), (to_thf_modal_full, Box(same))):
        text = write(formula)
        declared = re.findall(r"thf\((\w+)_decl, type, \( n\w* : \$i \)\)", text)
        assert declared == ["n1"], (write.__name__, declared)          # ONE constant for 1 and 1.0
    isabelle = to_isabelle_fol(same)
    assert isabelle.count('consts n1 :: "i"') == 1 and "n1_0" not in isabelle

    merged = Implies(P(Number(1)), P(Constant("n1")))      # the writers' spelling of the numeral 1 is n1
    for write, formula in ((to_thf_fol, merged), (to_thf_msfol, merged), (to_thf_free, merged),
                           (to_thf_modal, Box(merged)), (to_thf_modal_full, Box(merged)),
                           (to_isabelle_fol, merged)):
        with pytest.raises(NotImplementedError, match="spelled alike"):
            write(formula)


def test_the_higher_order_writers_keep_their_text_for_an_ordinary_numeral():
    from unicode_logic_kit.hol.classical import to_thf_fol
    text = to_thf_fol(Implies(P(Number(-1)), P(Number(2.5))))
    assert "thf(n_1_decl, type, ( n_1 : $i ))." in text and "thf(n2_5_decl, type, ( n2_5 : $i ))." in text
    assert "( ( p @ n_1 ) => ( p @ n2_5 ) )" in text


# ---------------------------------------------------------------------------------------------
# Live: Vampire and E answer the acceptance table
# ---------------------------------------------------------------------------------------------

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True, text=True,
                                timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_VAMPIRE_ON_PATH = shutil.which("vampire")
_HAVE_VAMPIRE = _VAMPIRE_ON_PATH is not None or _wsl_vampire_ok()
_HAVE_E = eprover_available()
_NEEDS_VAMPIRE = pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable")
_NEEDS_E = pytest.mark.skipif(not _HAVE_E, reason="no eprover binary found")


def _vampire_kwargs():
    if _VAMPIRE_ON_PATH is not None:
        return {"vampire_path": _VAMPIRE_ON_PATH, "use_wsl": False}
    return {"vampire_path": "vampire", "use_wsl": True}


def _parse(text) -> Node:
    result = api.parse_any(text)
    assert result.ok, (text, result)
    return result.formula


#: (label, premises, goal, valid) -- the hand-derived column of the table in the module docstring
TABLE = [
    ("A1", ["∀x P(x)"], "P(1)", True),
    ("A2", ["P(1)"], "P(1.0)", True),
    ("A3", [], "1 ≠ 2", False),
    ("A4", [], "1 < 2", False),
    ("A5", [], "1 + 1 = 2", False),
    ("A6", ["P(1)", "P(2)"], "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", False),
    ("A7", ["P(1)"], "P(one)", False),
    ("A8", ["∀x ∀y x + y = y + x"], "1 + 2 = 2 + 1", True),
    ("A9", ["∀x (x < 2 → Q(x))", "1 < 2"], "Q(1)", True),
    ("A10", [], "2.5 = 2.5", True),
    ("A11", ["P(-1)"], "∃x P(x)", True),
]
SORTED_PREMISE = "∃x:Srt Rr(x)"        # irrelevant to every row: Srt and Rr occur nowhere else


def _decide(prover, goal, premises, **options):
    if prover == "vampire":
        options = {**_vampire_kwargs(), **options}
    return get_backend(prover).decide(_parse(goal), [_parse(p) for p in premises], timeout=30000, **options)


def _check_row(prover, label, premises, goal, valid, **options):
    verdict = _decide(prover, goal, premises, **options)
    expected = "proved" if valid else "refuted"
    assert verdict.status == expected, (prover, label, options, verdict.status, verdict.reason, verdict.detail)


@pytest.mark.parametrize("label, premises, goal, valid", TABLE, ids=[row[0] for row in TABLE])
@_NEEDS_VAMPIRE
def test_vampire_answers_the_table_on_the_fof_text(label, premises, goal, valid):
    _check_row("vampire", label, premises, goal, valid, tff=False)
    _check_row("vampire", label, premises, goal, valid)               # the default options write fof here


@pytest.mark.parametrize("label, premises, goal, valid", TABLE, ids=[row[0] for row in TABLE])
@_NEEDS_E
def test_e_answers_the_table_on_the_fof_text(label, premises, goal, valid):
    _check_row("eprover", label, premises, goal, valid, tff=False)
    _check_row("eprover", label, premises, goal, valid)


@pytest.mark.parametrize("label, premises, goal, valid", [row for row in TABLE if row[0] != "A6"],
                         ids=[row[0] for row in TABLE if row[0] != "A6"])
@_NEEDS_VAMPIRE
def test_vampire_answers_the_table_on_the_tf0_text(label, premises, goal, valid):
    """The typed text, with an irrelevant sorted premise so that the TF0 writer is the one that writes."""
    _check_row("vampire", label, premises + [SORTED_PREMISE], goal, valid, tff=True)


@pytest.mark.parametrize("label, premises, goal, valid", [row for row in TABLE if row[0] != "A6"],
                         ids=[row[0] for row in TABLE if row[0] != "A6"])
@_NEEDS_E
def test_e_answers_the_table_on_the_tf0_text(label, premises, goal, valid):
    _check_row("eprover", label, premises + [SORTED_PREMISE], goal, valid, tff=True)


@pytest.mark.parametrize("prover", [
    pytest.param("vampire", marks=_NEEDS_VAMPIRE), pytest.param("eprover", marks=_NEEDS_E)])
def test_a6_with_a_sort_is_refused_by_the_typed_writer_and_answered_by_the_fof_text(prover):
    """A6 with an unsorted equation next to a sort is the TF0 writer's own refusal (an unsorted quantifier
    ranges over the whole universe, a typed ``$i`` does not): ``tff=True`` says ``unknown`` and never
    answers, and the automatic mode falls back to the fof text, which answers: not valid."""
    premises = ["P(1)", "P(2)", SORTED_PREMISE]
    forced = _decide(prover, "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", premises, tff=True)
    assert forced.status == "unknown" and forced.reason == "unsupported"
    automatic = _decide(prover, "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", premises)
    assert automatic.status == "refuted", (automatic.status, automatic.reason, automatic.detail)


@_NEEDS_VAMPIRE
def test_the_arithmetic_reading_asked_for_by_name_still_proves_what_the_prover_proves():
    """Control: with ``sort='int'`` the writer asks for ARITHMETIC, and Vampire proves ``1 + 1 = 2`` and
    ``1 ≠ 2`` (they are theorems of the integers). The same two goals, with no sort, are not valid."""
    for goal in ("1 + 1 = 2", "1 ≠ 2"):
        arithmetic = _decide("vampire", goal, [], sort="int")
        assert arithmetic.status == "proved", (goal, arithmetic.status, arithmetic.reason, arithmetic.detail)
        plain = _decide("vampire", goal, [])
        assert plain.status == "refuted", (goal, plain.status, plain.reason)


def _detailed(prover, premises, goal, names):
    if prover == "vampire":
        return check_entailment_vampire_detailed(premises, goal, timeout=30, premise_names=names,
                                                 **_vampire_kwargs())
    return check_entailment_eprover_detailed(premises, goal, timeout=30, premise_names=names)


@pytest.mark.parametrize("prover", [
    pytest.param("vampire", marks=_NEEDS_VAMPIRE), pytest.param("eprover", marks=_NEEDS_E)])
def test_a_proof_with_numerals_reports_the_premises_it_used_and_reads_back_as_numbers(prover):
    """P(1), Q(2), ∀x (P(x) → R(x)) ⊢ R(1): the proof is the first and the third premise (the second one
    says nothing about ``P`` or ``R``); its formulas come back with ``1`` as a ``Number``."""
    premises = [P(Number(1)), Q(Number(2)), forall(X, Implies(P(X), Atom("R", [X])))]
    result = _detailed(prover, premises, Atom("R", [Number(1)]), ["ax_a", "ax_b", "ax_c"])
    assert result["status"] == "proved" and result["relevant_premises"] == (0, 2)
    texts = [result.get("raw") or result["output_excerpt"]]
    assert not re.search(r"\bn[12]\b", texts[0]), "the writer's word of a numeral must be read back"
    formulas = [Node.from_dict(step["formula"]) for step in result["derivation"]["steps"]
                if step.get("formula") is not None]
    assert P(Number(1)) in formulas and Atom("R", [Number(1)]) in formulas
    for formula in formulas:
        assert not any(isinstance(n, Constant) and re.fullmatch(r"n\d+", n.name) for n in formula.walk())


@pytest.mark.parametrize("prover", [
    pytest.param("vampire", marks=_NEEDS_VAMPIRE), pytest.param("eprover", marks=_NEEDS_E)])
def test_a_countermodel_or_a_saturation_with_numerals_is_not_misread(prover):
    """P(1), Q(2.5) ⊢ 1 ≠ 2 is not valid: the answer is a saturation or a model, not a proof; the text
    that comes back names the numerals as numbers (``P(1)``, ``Q(2.5)``) and has no word of the writer."""
    premises = [P(Number(1)), Q(Number(2.5))]
    result = _detailed(prover, premises, Atom("≠", [Number(1), Number(2)]), None)
    assert result["status"] == "refuted" and result["relevant_premises"] is None
    text = result.get("raw") or result["output_excerpt"]
    assert not re.search(r"\bn[12]\b|n2u002e5", text)
    if prover == "eprover":
        assert "Q(2.5)" in text and "P(1)" in text


# ---------------------------------------------------------------------------------------------
# Live: Twee proves what is equational about numerals, and answers nothing for a non-theorem
# ---------------------------------------------------------------------------------------------

_NEEDS_TWEE = pytest.mark.skipif(not twee_available(), reason="no Twee binary reachable via WSL")


@pytest.mark.parametrize("premises, goal, valid", [
    (["∀x ∀y x + y = y + x"], "1 + 2 = 2 + 1", True),
    ([], "2.5 = 2.5", True),
    (["∀x ff(x) = 1"], "ff(ca) = ff(cb)", True),
    (["1 = 2"], "1.0 = 2", True),
    (["∀x ff(x) = x"], "ff(1) = 1", True),
    (["-1 = ca"], "ca = -1", True),
    ([], "1 + 1 = 2", False),
    ([], "1 = 2", False),
], ids=["comm", "reflexive decimal", "constant function", "one constant", "identity", "negative",
        "not valid sum", "not valid equation"])
@_NEEDS_TWEE
def test_twee_answers_equational_numeral_problems(premises, goal, valid):
    verdict = get_backend("twee").decide(_parse(goal), [_parse(p) for p in premises], timeout=30000)
    assert verdict.status == ("proved" if valid else "refuted"), (verdict.status, verdict.reason, verdict.detail)


# ---------------------------------------------------------------------------------------------
# Live: a fixed-seed differential against Z3 on the same nodes with the numerals and operators renamed
# ---------------------------------------------------------------------------------------------

_NUMERALS = [1, 1.0, 2, 2.5, -1, 0]
_FRESH_FUNC = {"+": "zplus", "-": "zminus", "*": "ztimes"}
_FRESH_PRED = {"<": "Zlt", "≤": "Zle", ">": "Zgt", "≥": "Zge"}


def _gen_term(rng, scope, depth):
    r = rng.random()
    if depth <= 0 or r < 0.45:
        pool = [Variable(v) for v in scope] + [Constant("ca"), Constant("cb")] + [Number(v) for v in _NUMERALS]
        weights = [1.0] * len(scope) + [1.0, 1.0] + [1.6] * len(_NUMERALS)
        return rng.choices(pool, weights)[0]
    if r < 0.6:
        return Function("ff", [_gen_term(rng, scope, depth - 1)])
    return Function(rng.choice(["+", "-", "*"]), [_gen_term(rng, scope, depth - 1), _gen_term(rng, scope, depth - 1)])


def _gen_atom(rng, scope):
    r, term = rng.random(), (lambda: _gen_term(rng, scope, 2))
    if r < 0.25:
        return Atom(rng.choice(["Pp", "Qq"]), [term()])
    if r < 0.35:
        return Atom("Rr", [term(), term()])
    if r < 0.6:
        return Atom("=", [term(), term()])
    if r < 0.7:
        return Atom("≠", [term(), term()])
    return Atom(rng.choice(["<", "≤", ">", "≥"]), [term(), term()])


def _gen_formula(rng, scope, depth):
    if depth <= 0 or rng.random() < 0.3:
        return _gen_atom(rng, scope)
    r = rng.random()
    if r < 0.15:
        return Not(_gen_formula(rng, scope, depth - 1))
    if r < 0.35:
        return And(_gen_formula(rng, scope, depth - 1), _gen_formula(rng, scope, depth - 1))
    if r < 0.5:
        return Or(_gen_formula(rng, scope, depth - 1), _gen_formula(rng, scope, depth - 1))
    if r < 0.7:
        return Implies(_gen_formula(rng, scope, depth - 1), _gen_formula(rng, scope, depth - 1))
    free = [v for v in ("x", "y") if v not in scope]
    if not free:
        return _gen_atom(rng, scope)
    v = rng.choice(free)
    return Quantifier(rng.choice(["∀", "∃"]), Variable(v), _gen_formula(rng, scope + [v], depth - 1))


def _gen_problem(rng):
    premises = [_gen_formula(rng, [], 2) for _ in range(rng.randint(0, 3))]
    if rng.random() < 0.35 and premises:                       # an instance: valid problems are not rare
        phi = _gen_formula(rng, ["x"], 1)
        premises.append(Quantifier("∀", Variable("x"), phi))
        return premises, substitute(phi, Variable("x"), _gen_term(rng, [], 1))
    return premises, _gen_formula(rng, [], 2)


def _renamed(node):
    """Every numeral and operator becomes a fresh ORDINARY symbol, here, so that the oracle does not
    depend on the kit's own reading of a numeral on the Z3 route."""
    if isinstance(node, Number):
        value = int(node.value) if float(node.value).is_integer() else node.value
        return Constant("zn_" + str(value).replace("-", "neg").replace(".", "_"))
    if isinstance(node, Function):
        return Function(_FRESH_FUNC.get(node.name, node.name), [_renamed(a) for a in node.args])
    if isinstance(node, Atom):
        return Atom(_FRESH_PRED.get(node.predicate, node.predicate), [_renamed(a) for a in node.args])
    return node.map_children(_renamed)


def _differential(prover, seeds, **options):
    contradictions, answered = [], 0
    for seed in seeds:
        premises, goal = _gen_problem(random.Random(seed))
        oracle = api.prove(_renamed(goal), [_renamed(p) for p in premises], backends=["z3"], timeout=8000)
        if oracle.status not in ("proved", "refuted"):
            continue
        got = get_backend(prover).decide(goal, premises, timeout=30000, **{**options, "tff": False})
        if got.status not in ("proved", "refuted"):
            continue
        answered += 1
        if got.status != oracle.status:
            contradictions.append((seed, oracle.status, got.status))
    return contradictions, answered


@_NEEDS_VAMPIRE
def test_vampire_agrees_with_z3_on_generated_problems_with_numerals_and_operators():
    contradictions, answered = _differential("vampire", range(7000, 7030), **_vampire_kwargs())
    assert contradictions == [] and answered >= 20


@_NEEDS_E
def test_e_agrees_with_z3_on_generated_problems_with_numerals_and_operators():
    contradictions, answered = _differential("eprover", range(7000, 7030))
    assert contradictions == [] and answered >= 20
