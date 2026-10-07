r"""How the Prover9 reader reads a name: what a quantifier binds, which names are variables, and what
is a keyword.

Every expectation is derived by hand from what Prover9 2026-8A does (measured with the real binary,
and kept in the live tests at the end, which skip with a reason where there is none).

**A quantifier binds the SYMBOL it names, whatever its case.** In ``all x (man(x) -> mortal(x))`` the
three ``x`` are one variable, and the text with ``X`` says the same, with and without
``set(prolog_style_variables)``. The scope is the operand that follows the variable, so it ends
before a ``&``, ``|``, ``->``, ``<->`` or ``<-``; a quantifier over the same spelling inside the
scope rebinds the name, and when it ends the outer binding is back. A name that is applied to
arguments is a predicate or a function, no occurrence of the variable.

**A name that no quantifier binds** is a variable or a constant by the convention of the text:
under ``set(prolog_style_variables)`` a variable begins with ``A`` to ``Z`` (an underscore does not
make one), without it a variable begins with ``u`` to ``z``. The LAST ``set`` or ``clear`` of the
flag in a file decides for every formula of it. ``parse_prover9`` has no file and reads the first
convention unless it is told otherwise.

**Variables are compared as written**: ``Xa`` and ``XA`` are two variables, so are ``x`` and ``X``
and ``_x`` and ``_X``. The documented syllogism is valid. ``P(x) ⊢ ∀x P(x)`` is not (``x`` is a
constant in the premise: universe {0, 1}, x = 0, P = {0}), and the symmetry of an arbitrary ``P`` is not
valid (universe {0, 1}, P = {(0, 1)}).

**Keywords** ``all`` and ``exists`` are quantifiers only as words of their own, followed by a variable:
``allowed(a)``, ``exists_in(b)`` and ``allergic(a)`` are atoms of those predicates, so
``allowed(a) ⊢ allergic(a)`` is not valid (universe {0, 1}, a = 0, allowed = {0}, allergic = {1}).

**``<-``** is the reverse implication: ``p <- q`` is ``q -> p``, so ``p <- q, q ⊢ p`` is valid. It
binds looser than ``|`` and ``&``, is not associative (a chain, or a mix with ``->`` or ``<->``
without parentheses, is a syntax error in Prover9 and here), and ``a <-b`` is not ``a < -b``.

**``formulas(alpha, beta)``** with two or more arguments is an atom, not a list header.

**An unreadable numeral** is a ``Prover9ParsingError`` that says where it is.
"""

import os
import random

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.prover9_entailment import _run_prover9, generate_prover9_input_with_mapping
from unicode_logic_kit.atp.protocol import Prover9Backend
from unicode_logic_kit.fol import prover9_input
from unicode_logic_kit.fol._fol_nodes import NumeralTextError
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Iff, Implies, Not, Number, Or, Quantifier, Variable,
)
from unicode_logic_kit.fol.prover9_input import Prover9ParsingError, parse_prover9, parse_prover9_problem


def V(name):
    return Variable(name)


def C(name):
    return Constant(name)


def A(predicate, *args):
    return Atom(predicate, list(args))


def FA(variable, body):
    return Quantifier("∀", variable, body)


def EX(variable, body):
    return Quantifier("∃", variable, body)


def _default(text):
    return parse_prover9(text, prolog_style_variables=False)


# --------------------------------------------------------------------------- #
# A quantifier binds the symbol it names, whatever its case.
# --------------------------------------------------------------------------- #

_SYLLOGISM = FA(V("x"), Implies(A("man", V("x")), A("mortal", V("x"))))


@pytest.mark.parametrize("text", ["all x (man(x) -> mortal(x))", "all X (man(X) -> mortal(X))",
                                  "(all x (man(x) -> mortal(x)))."])
def test_a_quantifier_binds_the_name_it_names_whatever_its_case(text):
    assert parse_prover9(text) == _SYLLOGISM
    assert _default(text) == _SYLLOGISM


def test_a_binder_with_a_longer_name_binds_it_too():
    assert parse_prover9("all alpha P(alpha)") == FA(V("alpha"), A("P", V("alpha")))
    assert parse_prover9("all Alpha P(Alpha)") == FA(V("alpha"), A("P", V("alpha")))
    assert parse_prover9("exists _q P(_q)") == EX(V("_q"), A("P", V("_q")))


_DOCUMENTED_FILE = """
set(prolog_style_variables).
assign(max_seconds, 30).
formulas(assumptions).
  all x (man(x) -> mortal(x)).   % a universally quantified implication
  man(socrates).
end_of_list.
formulas(goals).
  mortal(socrates).
end_of_list.
"""


def _kit_verdict(text):
    """The status the kit's Z3 route gives the problem a file states: its assumptions and its goal."""
    records = parse_prover9_problem(text)
    premises = [r.formula for r in records if r.role in ("assumptions", "sos")]
    goals = [r.formula for r in records if r.role == "goals"]
    return api.prove(goals[0], premises, backends=["z3"], timeout=8000).status


def test_the_documented_syllogism_is_read_with_a_bound_variable_and_is_proved():
    records = parse_prover9_problem(_DOCUMENTED_FILE)
    assert [(r.role, r.formula) for r in records] == [
        ("assumptions", _SYLLOGISM), ("assumptions", A("man", C("socrates"))),
        ("goals", A("mortal", C("socrates")))]
    assert _kit_verdict(_DOCUMENTED_FILE) == "proved"


def test_a_free_lower_case_name_is_a_constant_so_p_x_does_not_give_all_x_p_x():
    text = "set(prolog_style_variables).\nformulas(assumptions).\n P(x).\nend_of_list.\nformulas(goals).\n all x P(x).\nend_of_list.\n"
    records = parse_prover9_problem(text)
    assert [r.formula for r in records] == [A("P", C("x")), FA(V("x"), A("P", V("x")))]
    assert _kit_verdict(text) == "refuted"            # x = 0, P = {0} in the universe {0, 1}


def test_the_scope_of_a_quantifier_ends_before_a_connective():
    # all x P(x) & Q(x): the operand of the quantifier is P(x); Q(x) is outside it.
    assert parse_prover9("all x P(x) & Q(x)") == And(FA(V("x"), A("P", V("x"))), A("Q", C("x")))
    assert _default("all x P(x) & Q(x)") == And(FA(V("x"), A("P", V("x"))), A("Q", V("x")))
    assert parse_prover9("all X P(X) | Q(X)") == Or(FA(V("x"), A("P", V("x"))), A("Q", V("x")))
    assert _default("all X P(X) -> Q(X)") == Implies(FA(V("x"), A("P", V("x"))), A("Q", C("X")))
    assert parse_prover9("(all x P(x)) <-> Q(x)") == Iff(FA(V("x"), A("P", V("x"))), A("Q", C("x")))


def test_a_name_that_is_bound_in_one_formula_is_free_in_the_next():
    records = parse_prover9_problem("set(prolog_style_variables).\nformulas(assumptions).\n all x P(x).\n Q(x).\n"
                                    " all X R(X).\n S(X).\nend_of_list.\n")
    assert [r.formula for r in records] == [
        FA(V("x"), A("P", V("x"))), A("Q", C("x")), FA(V("x"), A("R", V("x"))), A("S", V("x"))]


def test_an_inner_quantifier_over_the_same_name_rebinds_it_and_the_outer_binding_comes_back():
    # all x (all x P(x) & Q(x)): P(x) is bound by the inner quantifier, Q(x) by the outer one.
    inner_then_outer = parse_prover9("all x (all x P(x) & Q(x))")
    assert inner_then_outer == FA(V("x"), And(FA(V("x"), A("P", V("x"))), A("Q", V("x"))))
    # all x (P(x) -> exists x Q(x)): both occurrences are variables.
    assert parse_prover9("all x (P(x) -> exists x Q(x))") == FA(
        V("x"), Implies(A("P", V("x")), EX(V("x"), A("Q", V("x")))))
    # a name that is bound only in the inner scope is a constant outside of it (prolog style).
    assert parse_prover9("P(x) & all x Q(x)") == And(A("P", C("x")), FA(V("x"), A("Q", V("x"))))


def test_a_name_applied_to_arguments_is_no_occurrence_of_the_variable():
    assert parse_prover9("all x (P(x) | x(a))") == FA(V("x"), Or(A("P", V("x")), A("x", C("a"))))
    assert parse_prover9("all x P(x(a))") == FA(V("x"), A("P", Function("x", [C("a")])))
    assert _default("all x (x(a) = b)") == FA(V("x"), A("=", Function("x", [C("a")]), C("b")))


def test_a_bound_name_that_stands_as_a_formula_is_refused_as_prover9_refuses_it():
    with pytest.raises(Prover9ParsingError, match="variable"):
        parse_prover9("all x (P(x) & x)")
    with pytest.raises(Prover9ParsingError, match="variable"):
        _default("exists X (X | P(X))")


# --------------------------------------------------------------------------- #
# Which free names are variables.
# --------------------------------------------------------------------------- #

_LETTERS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"


@pytest.mark.parametrize("suffix", ["", "q9", "_y"])
def test_under_the_prolog_flag_a_free_name_is_a_variable_exactly_when_it_begins_with_a_to_z_capital(suffix):
    for letter in _LETTERS:
        name = letter + suffix
        expected = V(name.lower()) if letter.isupper() else C(name)
        assert parse_prover9(f"P({name})") == A("P", expected), name


@pytest.mark.parametrize("suffix", ["", "q9", "_y"])
def test_without_the_flag_a_free_name_is_a_variable_exactly_when_it_begins_with_u_to_z(suffix):
    for letter in _LETTERS:
        name = letter + suffix
        expected = V(name.lower()) if letter in "uvwxyz" else C(name)
        assert _default(f"P({name})") == A("P", expected), name


def test_only_the_first_character_decides():
    assert _default("P(zebra)") == A("P", V("zebra"))
    assert _default("P(tzz)") == A("P", C("tzz"))
    assert parse_prover9("P(Xx)") == A("P", V("xx"))
    assert parse_prover9("P(xX)") == A("P", C("xX"))


def test_an_underscore_is_no_variable_in_either_convention():
    assert parse_prover9("P(_x)") == A("P", C("_x"))
    assert _default("P(_x)") == A("P", C("_x"))
    assert parse_prover9("P(_)") == A("P", C("_"))


def _first(text):
    return parse_prover9_problem(text)[0].formula


def test_a_file_without_the_flag_reads_the_default_convention():
    assert _first("formulas(assumptions).\n P(x).\nend_of_list.\n") == A("P", V("x"))
    assert _first("formulas(assumptions).\n P(X).\nend_of_list.\n") == A("P", C("X"))
    assert _first("P(x).") == A("P", V("x"))


def test_the_last_flag_of_the_file_decides_for_every_formula_of_it():
    body = "formulas(assumptions).\n Q(X).\n Q(x).\nend_of_list.\n"
    prolog = [A("Q", V("x")), A("Q", C("x"))]
    default = [A("Q", C("X")), A("Q", V("x"))]

    def read(text):
        return [r.formula for r in parse_prover9_problem(text)]

    assert read("set(prolog_style_variables).\n" + body) == prolog
    assert read(body + "set(prolog_style_variables).\n") == prolog                       # set after the lists
    assert read(body + "set(prolog_style_variables).\nclear(prolog_style_variables).\n") == default
    assert read("set(prolog_style_variables).\n" + body + "clear(prolog_style_variables).\n") == default
    assert read("clear(prolog_style_variables).\n" + body + "set(prolog_style_variables).\n") == prolog
    assert read("set(prolog_style_variables).\n" + body) == read(body + "set(prolog_style_variables).\n")


def test_a_flag_inside_a_list_is_an_atom_and_decides_nothing():
    records = parse_prover9_problem("formulas(assumptions).\n set(prolog_style_variables).\n P(X).\nend_of_list.\n")
    assert [r.formula for r in records] == [A("set", C("prolog_style_variables")), A("P", C("X"))]


# --------------------------------------------------------------------------- #
# Variables are compared as written.
# --------------------------------------------------------------------------- #

def _two_variables(node):
    """The names of the two quantifiers of ``∀a ∀b (P(a, b) → P(b, a))`` and the symmetry shape of its body."""
    assert isinstance(node, Quantifier) and isinstance(node.formula, Quantifier)
    outer, inner = node.variable, node.formula.variable
    assert node.formula.formula == Implies(A("P", outer, inner), A("P", inner, outer))
    return outer.name, inner.name


@pytest.mark.parametrize("text", [
    "all Xa all XA (P(Xa, XA) -> P(XA, Xa))",
    "all XA all Xa (P(XA, Xa) -> P(Xa, XA))",
    "all xa all XA (P(xa, XA) -> P(XA, xa))",
    "all x all X (P(x, X) -> P(X, x))",
    "all _x all _X (P(_x, _X) -> P(_X, _x))",
    "all X all x (P(X, x) -> P(x, X))",
])
def test_two_variables_that_differ_only_in_case_stay_two_variables(text):
    for node in (parse_prover9(text), _default(text)):
        first, second = _two_variables(node)
        assert first != second, text


def test_the_symmetry_of_an_arbitrary_p_is_not_valid():
    # universe {0, 1}, P = {(0, 1)}: P(0, 1) holds and P(1, 0) does not.
    text = ("formulas(goals).\n  (all Xa (all XA (P(Xa, XA) -> P(XA, Xa)))).\nend_of_list.\n")
    goal = parse_prover9_problem(text)[0].formula
    assert api.prove(goal, [], backends=["z3"], timeout=8000).status == "refuted"
    # the same variable twice IS the symmetry of one element: valid.
    same = parse_prover9("all Xa all Xa (P(Xa, Xa) -> P(Xa, Xa))")
    assert api.prove(same, [], backends=["z3"], timeout=8000).status == "proved"


def test_free_variables_that_differ_only_in_case_are_two_parameters_in_a_formula_and_in_a_file():
    one_formula = parse_prover9("P(Xa) & Q(XA)")
    names = {v.name for v in one_formula.walk() if isinstance(v, Variable)}
    assert len(names) == 2
    records = parse_prover9_problem("set(prolog_style_variables).\nformulas(assumptions).\n P(Xa).\n Q(XA).\n"
                                    " R(Xa).\nend_of_list.\n")
    first, second, third = (next(n for n in r.formula.walk() if isinstance(n, Variable)) for r in records)
    assert first != second and first == third


def test_a_name_that_is_a_variable_in_the_text_keeps_its_lower_case_name_when_nothing_clashes():
    assert parse_prover9("all X1 P(X1)") == FA(V("x1"), A("P", V("x1")))
    assert parse_prover9("(all X (all Y R(X, Y)))") == FA(V("x"), FA(V("y"), A("R", V("x"), V("y"))))


def test_a_minted_name_is_fresh_against_every_word_of_the_text():
    # Xa and XA both want xa; the second gets a name that no word of the text has.
    text = "all Xa all XA (P(Xa, XA, x0, xa0))"
    node = parse_prover9(text)
    outer, inner = node.variable.name, node.formula.variable.name
    assert outer == "xa" and inner not in {"xa", "x0", "xa0"}


# --------------------------------------------------------------------------- #
# Keywords are words of their own.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", ["allowed", "allergic", "allen", "alloy", "all_men", "allx", "all1",
                                  "exists_in", "existsRoom", "exists2", "existsx", "existential"])
def test_a_predicate_that_begins_with_a_keyword_is_an_atom(name):
    assert parse_prover9(f"{name}(alpha)") == A(name, C("alpha"))
    assert parse_prover9(f"-{name}(alpha)") == Not(A(name, C("alpha")))
    assert parse_prover9(f"{name}(alpha) = beta") == A("=", Function(name, [C("alpha")]), C("beta"))
    assert parse_prover9(f"{name}(a) -> {name}(b)") == Implies(A(name, C("a")), A(name, C("b")))
    assert parse_prover9(f"(all X {name}(X))") == FA(V("x"), A(name, V("x")))
    assert parse_prover9(f"{name}(alpha, beta)") == A(name, C("alpha"), C("beta"))
    assert parse_prover9(f"P({name}(a))") == A("P", Function(name, [C("a")]))


def test_the_atoms_of_the_documented_text_read_as_two_unrelated_predicates():
    text = "formulas(assumptions).\n  allowed(a).\nend_of_list.\nformulas(goals).\n  allergic(a).\nend_of_list.\n"
    assert [r.formula for r in parse_prover9_problem(text)] == [A("allowed", C("a")), A("allergic", C("a"))]
    assert _kit_verdict(text) == "refuted"            # a = 0, allowed = {0}, allergic = {1}


def test_all_and_exists_themselves_are_atoms_when_applied_to_an_argument():
    assert parse_prover9("all(a)") == A("all", C("a"))
    assert parse_prover9("exists(a)") == A("exists", C("a"))
    assert parse_prover9("all x all(x)") == FA(V("x"), A("all", V("x")))
    assert parse_prover9("exists x (exists(x))") == EX(V("x"), A("exists", V("x")))


def test_a_quantifier_needs_no_space_before_its_operand_but_a_word_of_its_own():
    assert parse_prover9("all x(P(x))") == FA(V("x"), A("P", V("x")))
    assert parse_prover9("exists x ((P(x)))") == EX(V("x"), A("P", V("x")))
    with pytest.raises(Prover9ParsingError):
        parse_prover9("allx P(x)")              # one word, then another: Prover9 refuses it as well


def test_the_writers_own_text_for_these_names_reads_back_as_the_same_formula():
    for name in ("allowed", "exists_in", "allergic", "all_men", "existsRoom"):
        atom = A(name, C("alpha"))
        text, _ = generate_prover9_input_with_mapping([atom], A("Goal", C("alpha")))
        records = parse_prover9_problem(text)
        assert [r.formula for r in records] == [atom, A("Goal", C("alpha"))], name


# --------------------------------------------------------------------------- #
# The reverse implication.
# --------------------------------------------------------------------------- #

def test_the_reverse_implication_is_the_implication_turned_round():
    assert parse_prover9("p <- q") == Implies(A("q"), A("p"))
    assert parse_prover9("p<-q") == Implies(A("q"), A("p"))
    assert parse_prover9("p <-q") == Implies(A("q"), A("p"))
    assert parse_prover9("P(a) <- Q(a)") == Implies(A("Q", C("a")), A("P", C("a")))
    assert parse_prover9("(p <- q) <- r") == Implies(A("r"), Implies(A("q"), A("p")))
    assert parse_prover9("p <- (q <- r)") == Implies(Implies(A("r"), A("q")), A("p"))


def test_the_reverse_implication_binds_looser_than_and_or_and_negation():
    # a | b <- c & d is (a | b) <- (c & d), that is (c & d) -> (a | b)
    assert parse_prover9("a | b <- c & d") == Implies(And(A("c"), A("d")), Or(A("a"), A("b")))
    assert parse_prover9("-a <- -b") == Implies(Not(A("b")), Not(A("a")))
    assert parse_prover9("all x P(x) <- Q") == Implies(A("Q"), FA(V("x"), A("P", V("x"))))


@pytest.mark.parametrize("text", ["a <- b <- c", "a <- b -> c", "a -> b <- c", "a <-> b <- c", "a <- b <-> c",
                                  "a <- b <- c <- d"])
def test_a_chain_or_a_mix_of_the_reverse_implication_needs_parentheses(text):
    with pytest.raises(Prover9ParsingError):
        parse_prover9(text)


def test_less_than_followed_by_a_minus_is_the_reverse_implication_only_without_a_space():
    assert parse_prover9("a <-b") == Implies(A("b"), A("a"))
    assert parse_prover9("a < -b") == A("<", C("a"), Function("-", [C("b")]))
    assert parse_prover9("a <- b") == Implies(A("b"), A("a"))
    assert parse_prover9("a <= b") == A("≤", C("a"), C("b"))
    assert parse_prover9("a <-> b") == Iff(A("a"), A("b"))
    assert parse_prover9("a < b") == A("<", C("a"), C("b"))


def test_the_reverse_implication_gives_the_valid_syllogism_p_from_q_and_p_if_q():
    text = "formulas(assumptions).\n  p <- q.\n  q.\nend_of_list.\nformulas(goals).\n  p.\nend_of_list.\n"
    assert _kit_verdict(text) == "proved"
    not_converse = "formulas(assumptions).\n  p <- q.\nend_of_list.\nformulas(goals).\n  p -> q.\nend_of_list.\n"
    assert _kit_verdict(not_converse) == "refuted"     # p true, q false: q -> p holds, p -> q does not
    assert _kit_verdict("formulas(goals).\n  (p <- q) <-> (q -> p).\nend_of_list.\n") == "proved"


# --------------------------------------------------------------------------- #
# formulas( ... ) with two or more arguments is an atom.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("arity", [0, 2, 3, 4])
def test_the_writers_text_for_a_predicate_called_formulas_reads_back(arity):
    atom = A("formulas", *[C(f"c{i}") for i in range(arity)])
    text, _ = generate_prover9_input_with_mapping([atom], atom)
    assert [r.formula for r in parse_prover9_problem(text)] == [atom, atom]


def test_the_writers_text_for_formulas_of_one_argument_reads_back_under_the_name_it_was_given():
    atom = A("formulas", C("alpha"))
    text, names = generate_prover9_input_with_mapping([atom], atom)
    token = names.get_symbol("predicate", "formulas", 1)
    assert token != "formulas"
    assert [r.formula for r in parse_prover9_problem(text)] == [A(token, C("alpha"))] * 2


def test_formulas_with_two_arguments_is_an_atom_inside_a_list_and_a_function_in_an_equation():
    records = parse_prover9_problem("formulas(assumptions).\n formulas(alpha, beta).\n formulas(a, b) = c.\n"
                                    " -formulas(a, b, c).\nend_of_list.\n")
    assert [(r.role, r.formula) for r in records] == [
        ("assumptions", A("formulas", C("alpha"), C("beta"))),
        ("assumptions", A("=", Function("formulas", [C("a"), C("b")]), C("c"))),
        ("assumptions", Not(A("formulas", C("a"), C("b"), C("c"))))]


@pytest.mark.parametrize("text", [
    "formulas(assumptions\nend_of_list.\n",                        # the parenthesis is never closed
    "formulas(f(x)).\nend_of_list.\n",                             # one argument that is no name
    "formulas().\nend_of_list.\n",
    "formulas(1).\nend_of_list.\n",
    "formulas(a).\nformulas(b).\nend_of_list.\nend_of_list.\n",   # a list header inside a list
])
def test_a_list_header_that_is_not_well_formed_is_still_refused(text):
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem(text)


def test_a_header_still_opens_a_list_with_spaces_and_comments():
    records = parse_prover9_problem("formulas ( assumptions ) .\n P(a). % a comment\nend_of_list.\n")
    assert [(r.role, r.formula) for r in records] == [("assumptions", A("P", C("a")))]


# --------------------------------------------------------------------------- #
# A text the reader cannot read ends in a Prover9ParsingError.
# --------------------------------------------------------------------------- #

def test_a_numeral_that_cannot_be_read_is_a_parse_error_that_says_where_it_is():
    for text in ("P(" + "9" * 4301 + ")", 'P("' + "9" * 4301 + '")', "P(1" + "0" * 400 + ".5)",
                 "P(a, " + "9" * 4301 + ")"):
        for read in (parse_prover9, parse_prover9_problem):
            with pytest.raises(Prover9ParsingError) as caught:
                read(text if read is parse_prover9 else f"formulas(assumptions).\n {text}.\nend_of_list.\n")
            assert not isinstance(caught.value, (ValueError, OverflowError))
            assert "column" in str(caught.value) and "line 1" in str(caught.value), str(caught.value)[:200]


def test_the_position_is_the_one_of_the_numeral():
    with pytest.raises(Prover9ParsingError) as caught:
        parse_prover9("P(a, b, " + "9" * 4301 + ")")
    assert "column 9 " in str(caught.value)          # "P(a, b, " is 8 characters long


@pytest.mark.parametrize("error", [ValueError("no number"), OverflowError("too big"), NumeralTextError("refused")])
def test_whatever_the_numeral_reader_raises_leaves_the_reader_as_a_parse_error(monkeypatch, error):
    def refuse(text):
        raise error

    monkeypatch.setattr(prover9_input, "_numeral_from_text", refuse)
    for text in ("P(7)", 'P("7")', "P(2.5)"):
        with pytest.raises(Prover9ParsingError):
            parse_prover9(text)
        with pytest.raises(Prover9ParsingError):
            parse_prover9_problem(f"formulas(assumptions).\n {text}.\nend_of_list.\n")


_PIECES = ["all", "exists", "x", "X", "xa", "_q", "a", "alpha", "P", "Q", "f", "allowed", "(", ")", ",", "->", "<-",
           "<->", "&", "|", "-", "=", "!=", "<", "<=", "1", "01", "2.5", "99999999999999999999.5", '"q"', '"1"',
           "$T", ".", "%c\n", " ", "  ", "formulas", "end_of_list", "set", "op"]


def test_no_text_makes_the_reader_leave_in_any_other_way_than_a_parse_error():
    rng = random.Random(20260905)
    for _ in range(600):
        text = " ".join(rng.choice(_PIECES) for _ in range(rng.randint(1, 12)))
        for read in (parse_prover9, parse_prover9_problem,
                     lambda t: parse_prover9(t, prolog_style_variables=False)):
            try:
                read(text)
            except Prover9ParsingError:
                pass


_VALID_FILES = [
    "set(prolog_style_variables).\nformulas(assumptions).\n  all x (P(x) -> Q(x)).\nend_of_list.\n"
    "formulas(goals).\n  exists y P(y).\nend_of_list.\n",
    "op(450, infix_left, before).\nformulas(sos).\n  f(a before b) = c.\nend_of_list.\n",
    "formulas(assumptions).\n  P(1.5) & Q(\"2\") & R(01).\nend_of_list.\n",
    "op(700, infix, [rel, rel2]).\nop(150, prefix, neg).\nop(150, postfix, pr).\nP(a) | a rel b.\n",
    "formulas(sos). formulas(alpha, beta). a <- b. end_of_list.\n",
    "clear(prolog_style_variables).\nassign(max_seconds, 5).\nall X P(X) & Q(x).\n",
]
_VALID_FORMULAS = [
    "all x (P(x) -> Q(x))", "exists y (P(y) & -Q(y, a))", "p <- q", "(all X P(X)) <-> (exists Y P(Y))",
    "f(a, g(b)) = c | -(a != b)", "P(1.5) & Q(\"2\") & R(01)", "all_men(a) & existsRoom(b) | allowed(c)",
    "a - b < -c", "$T & $F", "-all x P(x) -> exists x all y R(x, y)",
]
_INSERTIONS = list("()&|-<>=,.\"%0123456789 \n_$[]!+*/'") + [
    "all ", "exists ", "x", "X", "formulas", "end_of_list", "op(", "set(", "9" * 40, "0.", "<-", "<->", "->", "A1"]


def _mutated(rng, pool):
    text = rng.choice(pool)
    for _ in range(rng.randint(1, 2)):
        position = rng.randint(0, len(text))
        roll = rng.random()
        if roll < 0.3:
            text = text[:position] + text[position + rng.randint(1, 6):]
        elif roll < 0.7:
            text = text[:position] + rng.choice(_INSERTIONS) + text[position:]
        else:
            other = rng.choice(pool)
            cut = rng.randint(0, len(other))
            text = text[:position] + other[cut:cut + rng.randint(1, 25)] + text[position:]
    return text


@pytest.mark.parametrize("reader, pool", [
    (parse_prover9, _VALID_FORMULAS),
    (lambda t: parse_prover9(t, prolog_style_variables=False), _VALID_FORMULAS),
    (parse_prover9_problem, _VALID_FILES),
], ids=["formula", "formula, default convention", "file"])
def test_a_text_cut_and_pasted_from_valid_ones_is_read_or_refused_never_left_with_another_error(reader, pool):
    rng = random.Random(20261204)
    read = refused = 0
    for _ in range(300):
        try:
            reader(_mutated(rng, pool))
            read += 1
        except Prover9ParsingError:
            refused += 1
    assert read > 30 and refused > 30              # the texts are neither all valid nor all rubbish


@pytest.mark.parametrize("digits", [4301, 6000])
def test_an_op_directive_whose_precedence_has_thousands_of_digits_is_a_parse_error(digits):
    for sign in ("", "-"):
        text = "op(" + sign + "9" * digits + ", infix, before).\nformulas(sos).\n  P(a).\nend_of_list.\n"
        with pytest.raises(Prover9ParsingError, match="1-998"):
            parse_prover9_problem(text)


@pytest.mark.parametrize("text", [
    "formulas(alpha, beta).\nformulas(assumptions).\n  P(a).\nend_of_list.\n",       # outside every list
    "formulas(alpha, beta).",
    "P(a).\nformulas(a, b, c).\n",
])
def test_a_call_of_formulas_with_two_arguments_outside_a_list_is_a_malformed_header(text):
    with pytest.raises(Prover9ParsingError, match="malformed 'formulas"):
        parse_prover9_problem(text)


# --------------------------------------------------------------------------- #
# Against the real Prover9: the kit's reading and Prover9's are one.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    _BINARY is None,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the offline tests above carry the claim")

_HEAD = "set(prolog_style_variables).\n"
_NO_FLAG = ""

# (name, flag line, assumptions, goal, valid)
_FILES = [
    ("syllogism", _HEAD, ["all x (man(x) -> mortal(x))", "man(socrates)"], "mortal(socrates)", True),
    ("syllogism, upper case", _HEAD, ["all X (man(X) -> mortal(X))", "man(socrates)"], "mortal(socrates)", True),
    ("syllogism, no flag", _NO_FLAG, ["all x (man(x) -> mortal(x))", "man(socrates)"], "mortal(socrates)", True),
    ("a constant is no universal claim", _HEAD, ["P(x)"], "all x P(x)", False),
    # (a free VARIABLE is left out on purpose: Prover9 closes it universally, the kit reads one unknown
    # element, see the module docstring of the reader.)
    ("a free X is a constant without the flag", _NO_FLAG, ["P(X)"], "all y P(y)", False),
    ("scope ends before &", _HEAD, ["all x P(x) & Q(x)"], "Q(a)", False),
    ("rebound name", _HEAD, ["all x (P(x) -> exists x Q(x))", "P(a)"], "exists y Q(y)", True),
    ("outer binding back", _HEAD, ["all x (all x P(x) & Q(x))"], "Q(a) & P(b)", True),
    ("symmetry is not valid", _NO_FLAG, [], "all Xa all XA (P(Xa, XA) -> P(XA, Xa))", False),
    ("x and X are two variables", _HEAD, [], "all x all X (P(x, X) -> P(X, x))", False),
    ("allowed is not allergic", _HEAD, ["allowed(a)"], "allergic(a)", False),
    ("exists_in", _HEAD, ["exists_in(b)"], "exists_in(b)", True),
    ("p <- q", _HEAD, ["p <- q", "q"], "p", True),
    ("p <- q is not p -> q", _HEAD, ["p <- q"], "p -> q", False),
    ("(p <- q) <-> (q -> p)", _HEAD, [], "(p <- q) <-> (q -> p)", True),
    ("a < -b is a comparison", _HEAD, ["a < -b"], "a < -b", True),
    ("formulas(alpha, beta)", _HEAD, ["formulas(alpha, beta)"], "formulas(alpha, beta)", True),
]


def _file(flag, assumptions, goal):
    return (flag + "clear(print_initial_clauses).\nclear(print_kept).\nclear(print_given).\n"
            "formulas(assumptions).\n" + "".join(f"  {a}.\n" for a in assumptions)
            + "end_of_list.\nformulas(goals).\n  " + goal + ".\nend_of_list.\n")


@live
@pytest.mark.parametrize("name, flag, assumptions, goal, valid", _FILES, ids=[f[0] for f in _FILES])
def test_live_prover9_and_the_kits_reading_of_the_same_text_agree(name, flag, assumptions, goal, valid):
    text = _file(flag, assumptions, goal)
    proved = _run_prover9(text, _BINARY, timeout=30, raise_on_rejection=True,
                          use_wsl=os.environ.get("UFK_PROVER9_WSL") == "1")
    assert proved == valid, (name, "Prover9 itself")
    assert (_kit_verdict(text) == "proved") == valid, (name, "the kit's reading")
