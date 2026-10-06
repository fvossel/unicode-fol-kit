"""``Signature.validate`` reads the variable a counting binder introduces.

``∃≥2 x:B P(x)`` and ``|{x:B : P(x)}|`` bind ``x`` at the sort ``B`` exactly as ``∃x:B P(x)`` does, so
the atom ``P(x)`` inside is an occurrence of a ``B`` variable. Against a signature that declares the
argument of ``P`` at the sort ``A`` (and no edge ``B < A``) all three formulas break the signature in
the same way. The unsorted binders ``∃≥2 x`` and ``|{x : φ}|`` bind a variable of no known sort, which
shadows an outer ``x:B``. Every expected message below is the one the existing check writes for the
quantifier form, read off the declaration next to it.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    And, Atom, Cardinality, Count, Number, SortedCardinality, SortedCount, SortedQuantifier, Variable,
)
from unicode_fol_kit.fol.signature import Signature

X = Variable("x")
BODY = Atom("P", [X])
MISMATCH = ["predicate 'P' argument 1 expects sort 'A', got sort 'B'"]


def declared(subsorts=None):
    d = {"predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}}, "sorts": ["A", "B"]}
    if subsorts:
        d["subsorts"] = subsorts
    return Signature.from_dict(d)


def cardinality_comparison(node):
    return Atom(">", [node, Number(1)])


BINDERS = {
    "quantifier": SortedQuantifier("∃", X, "B", BODY),
    "counting quantifier": SortedCount("ge", Number(2), X, "B", BODY),
    "cardinality term": cardinality_comparison(SortedCardinality(X, "B", BODY)),
}


@pytest.mark.parametrize("label", sorted(BINDERS))
def test_a_sorted_binder_breaks_a_signature_that_wants_another_sort(label):
    assert declared().validate(BINDERS[label]) == MISMATCH


@pytest.mark.parametrize("label", sorted(BINDERS))
def test_a_sorted_binder_over_a_subsort_of_the_declared_sort_conforms(label):
    # the declaration says B lies in A, so a B variable is allowed where A is wanted
    assert declared({"B": ["A"]}).validate(BINDERS[label]) == []


@pytest.mark.parametrize("label", sorted(BINDERS))
def test_a_sorted_binder_over_the_declared_sort_conforms(label):
    sig = Signature.from_dict({"predicates": {"P": {"arity": 1, "arg_sorts": ["B"]}}, "sorts": ["B"]})
    assert sig.validate(BINDERS[label]) == []


def test_the_message_is_written_once_per_occurrence():
    twice = And(BINDERS["counting quantifier"], BINDERS["cardinality term"])
    assert declared().validate(twice) == MISMATCH + MISMATCH


def test_an_unsorted_counting_binder_gives_its_variable_no_sort():
    # nothing is known of x, so nothing conflicts
    assert declared().validate(Count("ge", Number(2), X, BODY)) == []
    assert declared().validate(cardinality_comparison(Cardinality(X, BODY))) == []


def test_an_unsorted_counting_binder_shadows_an_outer_sorted_variable():
    # inside the count the x is the counted one, not the x:B that encloses it
    inner = Count("ge", Number(2), X, BODY)
    assert declared().validate(SortedQuantifier("∀", X, "B", inner)) == []
    outer_only = And(SortedQuantifier("∀", X, "B", Atom("P", [X])), inner)
    assert declared().validate(outer_only) == MISMATCH


def test_a_sorted_counting_binder_shadows_an_outer_sorted_variable():
    # x:A outside, x:B inside the count: the atom in the matrix is read at B
    outer = SortedQuantifier("∀", X, "A", SortedCount("ge", Number(2), X, "B", BODY))
    assert declared().validate(outer) == MISMATCH
    # and the atom beside the count, at A, is fine
    beside = SortedQuantifier("∀", X, "A", And(BODY, Atom("Q", [X])))
    sig = Signature.from_dict({
        "predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}, "Q": {"arity": 1, "arg_sorts": ["A"]}},
        "sorts": ["A", "B"]})
    assert sig.validate(beside) == []


def test_the_binding_does_not_leak_out_of_the_binder():
    # the x after the count is free again: unknown sort, no conflict
    free_after = And(SortedCount("ge", Number(2), X, "B", Atom("R", [X])), BODY)
    sig = Signature.from_dict({
        "predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}, "R": {"arity": 1, "arg_sorts": ["B"]}},
        "sorts": ["A", "B"]})
    assert sig.validate(free_after) == []


def test_arity_and_declaredness_are_still_checked_inside_the_binders():
    assert declared().validate(SortedCount("ge", Number(2), X, "B", Atom("Z", [X]))) == [
        "undeclared predicate 'Z' (arity 1)"]
    # P is declared with one argument, so the second x has no declared sort to meet; the first x is a B
    # variable where an A is wanted, which the quantifier form reports in the same order after the arity
    wrong_arity = cardinality_comparison(SortedCardinality(X, "B", Atom("P", [X, X])))
    assert declared().validate(wrong_arity) == [
        "predicate 'P' expects arity 1, used with arity 2"] + MISMATCH
