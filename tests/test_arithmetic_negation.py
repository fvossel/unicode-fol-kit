"""A one-argument minus is the negation on the arithmetic routes, whichever reader built it.

The Prover9 reader builds ``Function("-", [t])`` for ``-t`` and the SMT-LIB reader for ``(- t)``. Under the
arithmetic reading (``atp.z3_arith``, the typed TPTP writer) that node is ``0 - t``:

* ``∀x (-x + x = 0)`` is valid: ``(0 - x) + x = 0`` for every ``x``;
* ``∀x (-x = x)`` is not: at ``x = 1`` it says ``-1 = 1``;
* ``∀x (-(-x) = x)`` is valid: ``0 - (0 - x) = x``;
* ``∀x ∀y (x - y = x + -y)`` is valid: subtraction is the sum with the negation.

Read as a function symbol of its own, every one of them comes out not valid, which for the three valid ones
is a wrong answer about the text the reader was given.
"""

import pytest

from unicode_fol_kit.atp._tff_problem import formula_to_tff_arith
from unicode_fol_kit.atp.z3_arith import is_valid_arith
from unicode_fol_kit.atp.z3_input import parse_smtlib
from unicode_fol_kit.fol.nodes import Atom, Function, Number, Quantifier, Variable
from unicode_fol_kit.fol.prover9_input import parse_prover9

X, Y = Variable("x"), Variable("y")


def forall(body, variable=X):
    return Quantifier("∀", variable, body)


def neg(term):
    return Function("-", [term])


CANCELS = forall(Atom("=", [Function("+", [neg(X), X]), Number(0)]))
FIXED_POINT = forall(Atom("=", [neg(X), X]))
TWICE = forall(Atom("=", [neg(neg(X)), X]))
DIFFERENCE = forall(forall(Atom("=", [Function("-", [X, Y]), Function("+", [X, neg(Y)])]), Y))


@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("formula, valid", [(CANCELS, True), (FIXED_POINT, False), (TWICE, True), (DIFFERENCE, True)])
def test_the_arithmetic_reading_of_a_one_argument_minus(formula, valid, sort):
    assert is_valid_arith(formula, sort=sort) is valid


def test_the_smtlib_reader_builds_the_node_and_the_text_is_decided_as_it_reads():
    [read] = parse_smtlib("(assert (forall ((x Int)) (= (+ (- x) x) 0)))")
    assert read == CANCELS
    assert is_valid_arith(read, sort="int") is True


def test_the_prover9_reader_builds_the_node_and_the_text_is_decided_as_it_reads():
    read = parse_prover9("all x (-x + x = 0)")
    assert read == CANCELS
    assert is_valid_arith(read, sort="int") is True


@pytest.mark.parametrize("sort, zero", [("int", "0"), ("real", "0.0")])
def test_the_typed_writer_writes_the_negation_word(sort, zero):
    assert formula_to_tff_arith(CANCELS, sort=sort) == f"(![X: ${sort}]: ($sum($uminus(X),X) = {zero}))"


def test_a_minus_at_three_arguments_is_no_operator():
    # there is no ternary subtraction: z3_arith reads a function symbol, the typed writer refuses the node
    ternary = forall(Atom("=", [Function("-", [X, X, X]), X]))
    assert is_valid_arith(ternary, sort="int") is False
    with pytest.raises(NotImplementedError, match="'-' is applied to 3 argument"):
        formula_to_tff_arith(ternary, sort="int")
