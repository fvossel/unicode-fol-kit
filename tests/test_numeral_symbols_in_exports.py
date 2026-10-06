r"""A numeral is ONE constant per VALUE in what the HOL, Lean, Prolog and nanoCoP writers write.

A numeral (a :class:`Number`) is a constant symbol identified by its value on every route that was
not asked for arithmetic: ``Number(1) == Number(1.0)``, so ``1`` and ``1.0`` are one constant, named
``n1`` by the higher-order writers (``n2.5`` is ``n2_5`` once the target's identifier rules have
made a word of it); nothing else is known about it. A constant spelled like it (``n1`` next to the
number ``1``, or ``1``) would be the same identifier, so the pair is refused by name and never merged.
``+ - * /`` are function symbols and ``< > ≤ ≥`` predicates of the problem. The one numeral that stays
a number is the operand of a comparison with a cardinality, which the Isabelle second-order writer
states over the naturals.

Every expectation is derived by hand: for ``P(1) → P(1.0)`` each writer declares its constant ONCE and
uses it twice, so the identifier occurs three times in the text; for two values it is two constants.
Prolog keeps the integer ``1`` and the float ``1.0`` apart (they do not unify), so the clause writer
writes a whole-number float as the integer; nanoCoP-M's language has no number and refuses one by name.
"""

import re

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.nanocop_backend import to_nanocop
from unicode_fol_kit.fol._numeral_symbols import (
    numerals_as_constants, prefixed_numeral_name, term_numerals,
)
from unicode_fol_kit.fol._symbol_names import SymbolNames
from unicode_fol_kit.fol.nodes import (
    And, Atom, Box, Cardinality, Constant, Function, Implies, Not, Number, Quantifier, Variable,
)
from unicode_fol_kit.fol.prolog_export import (
    PrologExportError, formula_to_prolog_clause, formula_to_prolog_program,
)
from unicode_fol_kit.fol.prolog_input import parse_prolog_clause
from unicode_fol_kit.fol.qml import to_thf_modal
from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory, modal_axiom_names, to_isabelle_modal
from unicode_fol_kit.hol.lean import to_lean_fol, to_lean_modal_k, to_lean_msfol
from unicode_fol_kit.hol.secondorder import to_isabelle_so, to_thf_so

a, b = Constant("a"), Constant("b")


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def _uses(text, ident):
    """How often ``ident`` occurs in ``text`` as a whole identifier (not as the start or the end of one)."""
    return len(re.findall(r"(?<![A-Za-z0-9_])" + re.escape(ident) + r"(?![A-Za-z0-9_])", text))


# The writers of a first-order problem with a numeral as a constant: name, writer.
_CONSTANT_WRITERS = [
    ("to_thf_so", to_thf_so),
    ("to_isabelle_so", to_isabelle_so),
    ("to_isabelle_modal", to_isabelle_modal),
    ("to_lean_fol", to_lean_fol),
    ("to_lean_msfol", to_lean_msfol),
    ("to_thf_modal", to_thf_modal),
]
_IDS = [name for name, _ in _CONSTANT_WRITERS]


# --------------------------------------------------------------------------- #
# One constant per value.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, writer", _CONSTANT_WRITERS, ids=_IDS)
@pytest.mark.parametrize("first, second", [(1, 1.0), (1.0, 1), (7, 7.0), (0, -0.0)])
def test_the_numerals_of_one_value_are_one_constant_declared_once_and_used_twice(name, writer, first, second):
    text = writer(Implies(P(Number(first)), P(Number(second))))
    ident = prefixed_numeral_name(first)
    sanitised = ident.replace(".", "_").replace("-", "_")
    if first == 0:
        assert ident == "n0"
    assert _uses(text, sanitised) == 3, (name, text)             # one declaration, two uses
    assert _uses(text, sanitised + "_0") == 0 and _uses(text, "n" + str(float(first)).replace(".", "_")) == 0


@pytest.mark.parametrize("name, writer", _CONSTANT_WRITERS, ids=_IDS)
def test_the_numerals_of_two_values_are_two_constants(name, writer):
    text = writer(And(P(Number(1)), P(Number(2))))
    assert _uses(text, "n1") == 2 and _uses(text, "n2") == 2, text         # a declaration and a use each
    text = writer(And(P(Number(2.5)), P(Number(2.0))))
    assert _uses(text, "n2_5") == 2 and _uses(text, "n2") == 2, text


@pytest.mark.parametrize("name, writer", _CONSTANT_WRITERS, ids=_IDS)
def test_a_negative_and_a_decimal_numeral_are_written_as_one_word_each(name, writer):
    # -1 has a sign and 2.5 a point, which no identifier of the targets has: each becomes ONE word
    # (n_1, n2_5), and -1.0 is the same word as -1.
    text = writer(And(P(Number(-1)), And(P(Number(-1.0)), P(Number(2.5)))))
    assert _uses(text, "n_1") == 3 and _uses(text, "n2_5") == 2, text


@pytest.mark.parametrize("name, writer", _CONSTANT_WRITERS, ids=_IDS)
@pytest.mark.parametrize("spelled_alike", ["n1", "1"])
def test_a_constant_spelled_like_a_numeral_is_refused_by_name_never_merged(name, writer, spelled_alike):
    for formula in (And(P(Number(1)), Q(Constant(spelled_alike))), And(Q(Constant(spelled_alike)), P(Number(1.0)))):
        with pytest.raises(NotImplementedError, match="spelled alike"):
            writer(formula)


@pytest.mark.parametrize("name, writer", _CONSTANT_WRITERS, ids=_IDS)
def test_a_constant_that_is_not_spelled_like_a_numeral_is_no_clash(name, writer):
    text = writer(And(P(Number(1)), Q(Constant("one"))))
    assert _uses(text, "n1") == 2 and _uses(text, "one") == 2


def test_the_modal_axiom_names_refuse_the_pair_like_the_theory_does():
    formula = And(Box(P(Number(1))), Q(Constant("n1")))
    with pytest.raises(NotImplementedError, match="spelled alike"):
        isabelle_modal_theory(formula)
    with pytest.raises(NotImplementedError, match="spelled alike"):
        modal_axiom_names(formula)
    assert modal_axiom_names(Box(P(Number(1)))) == modal_axiom_names(Box(P(Number(1.0))))


def test_the_modal_theory_of_one_value_is_the_same_text_whatever_the_spelling():
    assert isabelle_modal_theory(Box(P(Number(1)))) == isabelle_modal_theory(Box(P(Number(1.0))))
    assert to_thf_modal(Box(P(Number(1)))) == to_thf_modal(Box(P(Number(1.0))))


def test_the_other_writers_write_the_same_text_for_the_two_spellings_of_a_value():
    for writer in (to_thf_so, to_isabelle_so, to_lean_fol, to_lean_msfol, to_lean_modal_k):
        assert writer(P(Number(1))) == writer(P(Number(1.0))), writer.__name__


def test_the_resolver_of_symbol_names_names_a_numeral_by_its_value():
    names = SymbolNames(And(P(Number(1)), P(Number(1.0))), str)
    assert names.const == {"n1": "n1"}
    names = SymbolNames(And(P(Number(2.5)), P(Number(2))), str)
    assert sorted(names.const) == ["n2", "n2.5"]


# --------------------------------------------------------------------------- #
# The second-order writers: a number compared with a cardinality stays a number.
# --------------------------------------------------------------------------- #

_X = Variable("x")


def _count_at_least(number):
    return Atom("≥", [Cardinality(_X, P(_X)), number])


def test_a_number_compared_with_a_cardinality_is_the_natural_not_a_constant():
    text = to_isabelle_so(_count_at_least(Number(2)))
    assert re.search(r"\(\(card \{x\. \(p x\)\}\) \\<ge> 2\)", text), text
    assert "consts n2" not in text and _uses(text, "n2") == 0


def test_a_whole_number_float_next_to_a_cardinality_is_the_same_natural():
    assert to_isabelle_so(_count_at_least(Number(2.0))) == to_isabelle_so(_count_at_least(Number(2)))


def test_a_constant_named_like_the_natural_is_no_clash_next_to_a_cardinality():
    text = to_isabelle_so(And(_count_at_least(Number(2)), Q(Constant("n2"))))
    assert _uses(text, "n2") == 2 and "\\<ge> 2)" in text      # the constant n2: a declaration and a use


def test_a_numeral_that_is_an_individual_next_to_a_cardinality_is_still_a_constant():
    text = to_isabelle_so(And(_count_at_least(Number(2)), P(Number(2))))
    assert _uses(text, "n2") == 2 and "\\<ge> 2)" in text


def test_the_thf_writer_has_no_finite_sets_and_says_so_for_every_operand_order():
    for formula in (_count_at_least(Number(2)), Atom("≤", [Number(2), Cardinality(_X, P(_X))])):
        with pytest.raises(NotImplementedError, match="cardinality"):
            to_thf_so(formula)


def test_a_free_object_variable_spelled_like_a_numeral_constant_is_refused():
    # A free object variable is exported as an individual constant of its name, so the variable n1
    # and the numeral 1 (the constant n1) would be one symbol.
    for writer in (to_thf_so, to_isabelle_so):
        with pytest.raises(NotImplementedError, match="free object variable"):
            writer(And(P(Variable("n1")), P(Number(1))))
        # A BOUND variable of that name is no constant at all.
        text = writer(And(Quantifier("∀", Variable("n1"), P(Variable("n1"))), P(Number(1))))
        assert _uses(text, "n1") >= 2


def test_the_helper_leaves_a_number_compared_with_a_cardinality_alone_on_request():
    counting = _count_at_least(Number(2))
    (same,), names = numerals_as_constants([counting], where="w", counting_comparisons=True)
    assert same is counting and names == frozenset()
    assert list(term_numerals(counting, counting_comparisons=True)) == []
    assert [n.value for n in term_numerals(counting)] == [2]                     # the default reads it as a term
    (rewritten,), names = numerals_as_constants([counting], where="w")
    assert rewritten == Atom("≥", [Cardinality(_X, P(_X)), Constant("2")]) and names == frozenset({"2"})
    # An atom that is no comparison keeps its numerals: P(|{x : P(x)}|, 2) states an individual 2.
    odd = Atom("R", [Cardinality(_X, P(_X)), Number(2)])
    assert [n.value for n in term_numerals(odd, counting_comparisons=True)] == [2]
    # A comparison without a cardinality is a comparison of individuals.
    plain = Atom("<", [Number(1), Number(2)])
    assert [n.value for n in term_numerals(plain, counting_comparisons=True)] == [1, 2]
    # The numerals inside the cardinality's own matrix are in term position.
    inner = Atom("=", [Cardinality(_X, P(_X, Number(3))), Number(2)])
    assert [n.value for n in term_numerals(inner, counting_comparisons=True)] == [3]
    (rewritten,), _ = numerals_as_constants([inner], where="w", counting_comparisons=True,
                                            spell=prefixed_numeral_name)
    assert rewritten == Atom("=", [Cardinality(_X, P(_X, Constant("n3"))), Number(2)])


# --------------------------------------------------------------------------- #
# Lean, propositional modal K: an atom is a letter, P(1) and P(1.0) are one atom.
# --------------------------------------------------------------------------- #

def _letters(text):
    return [line for line in text.splitlines() if re.fullmatch(r"axiom \S+ : World → Prop", line)]


def test_a_ground_atom_with_a_numeral_is_one_propositional_letter_per_value():
    text = to_lean_modal_k(Implies(P(Number(1)), P(Number(1.0))))
    assert len(_letters(text)) == 1, text
    text = to_lean_modal_k(And(P(Number(1)), P(Number(2))))
    assert len(_letters(text)) == 2, text
    text = to_lean_modal_k(Implies(Box(P(Number(2.5))), Box(P(Number(2.5)))))
    assert len(_letters(text)) == 1 and "p_n2_5_" in text


def test_the_modal_k_letters_refuse_a_constant_spelled_like_the_numeral():
    with pytest.raises(NotImplementedError, match="spelled alike"):
        to_lean_modal_k(And(P(Number(1)), P(Constant("n1"))))


# --------------------------------------------------------------------------- #
# Prolog: the integer 1 and the float 1.0 do not unify, the numerals 1 and 1.0 are one.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("value, text", [
    (1, "1"), (1.0, "1"), (100.0, "100"), (0, "0"), (-0.0, "0"), (-3, "-3"), (-3.0, "-3"), (2.5, "2.5"),
    (0.1, "0.1"), (-2.5, "-2.5"),
])
def test_a_prolog_numeral_is_the_text_of_its_value(value, text):
    assert formula_to_prolog_clause(P(Number(value))) == f"p({text})."


def test_a_clause_over_two_spellings_of_a_value_is_a_clause_over_one_term():
    assert formula_to_prolog_clause(Implies(P(Number(1.0)), P(Number(1)))) == "p(1) :- p(1)."
    assert formula_to_prolog_clause(Implies(P(Number(1)), Q(Number(1.0)))) == "q(1) :- p(1)."


def test_a_numeral_and_a_constant_spelled_like_it_stay_two_prolog_terms():
    # The integer 1 and the quoted atom '1' do not unify in Prolog, so nothing is merged, and the
    # kit's reader gives each back as the node it was.
    clause = Implies(Q(Number(1)), P(Constant("1")))
    text = formula_to_prolog_clause(clause)
    assert text == "p('1') :- q(1)."
    assert parse_prolog_clause(text) == clause


def test_a_prolog_program_writes_one_numeral_per_value():
    assert formula_to_prolog_program([P(Number(1.0)), Q(Number(2.5))]) == "p(1).\nq(2.5)."


@pytest.mark.parametrize("value", [float("nan"), float("inf"), float("-inf"), 1e-10])
def test_a_number_without_a_prolog_numeral_is_still_refused(value):
    # 1e20 used to be in this list: Python prints the float as ``1e+20``, outside the numeral
    # grammar. A float with a whole value is stored as the integer it equals (a value has one
    # spelling), so 1e20 is the integer 100000000000000000000 and has a numeral (next test). What
    # is left to refuse is a float that has a fractional part and prints in exponent form, and a
    # value that is no finite number.
    with pytest.raises(PrologExportError, match="numeral grammar"):
        formula_to_prolog_clause(P(Number(value)))


def test_a_float_too_large_to_have_a_fraction_is_written_as_the_integer_it_equals():
    # 1e20 and 1e22 are exactly the integers 10**20 and 10**22; 1e23 is the double nearest 10**23,
    # which is exactly 99999999999999991611392. Each is the integer in the node and in the text,
    # and the clause reads back as the very node.
    for value, text in ((1e20, "100000000000000000000"), (1e22, "10000000000000000000000"),
                        (1e23, "99999999999999991611392")):
        node = P(Number(value))
        assert node.args[0].value == int(value) and isinstance(node.args[0].value, int)
        assert formula_to_prolog_clause(node) == f"p({text})."
        assert parse_prolog_clause(f"p({text}).") == node


def test_the_numeral_a_prolog_clause_writes_is_read_back_as_an_equal_node():
    for value in (1, 1.0, 100.0, -0.0, 2.5, -3):
        node = P(Number(value))
        assert parse_prolog_clause(formula_to_prolog_clause(node)) == node


# --------------------------------------------------------------------------- #
# nanoCoP-M: no number in the language; operators are ordinary functors.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("value", [1, 1.0, 2.5, -1])
def test_nanocop_refuses_a_number_by_name_in_every_position(value):
    for formula in (P(Number(value)), P(Function("f", [Number(value)])), Atom("<", [a, Number(value)]),
                    Not(P(Number(value))), Box(Q(Number(value)))):
        with pytest.raises(NotImplementedError, match="'Number'"):
            to_nanocop(formula)
    with pytest.raises(NotImplementedError, match="'Number'"):
        to_nanocop(P(a), [P(Number(value))])


def test_nanocop_writes_an_arithmetic_symbol_as_an_ordinary_functor_or_predicate():
    assert to_nanocop(P(Function("+", [a, b]))) == "f( p(+(a, b)) ).\n"
    assert to_nanocop(P(Function("/", [a, b]))) == "f( p(/(a, b)) ).\n"
    assert to_nanocop(Atom("<", [a, b])) == "f( <(a, b) ).\n"


def test_nanocop_keeps_a_constant_named_like_a_numeral_a_constant():
    assert to_nanocop(P(Constant("1"))) == "f( p(1) ).\n"
