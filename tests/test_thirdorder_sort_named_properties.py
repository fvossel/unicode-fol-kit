"""The third-order evaluator and a property that has the name of a sort.

A sort and the unary predicate of the same name are ONE symbol: ``Human`` is both the universe of the
sort and the property "is a Human". In argument position (``Positive(Human)``) the name denotes that
property -- a relation, here the set of 1-tuples of the sort's members -- also when the structure
knows ``Human`` only as a sort and has no predicate table for it. ``semantics.tarski`` reads an atom
``Human(t)`` that way; the third-order evaluator has to read the argument the same way, or a property
named like a sort reads as the empty relation.
"""

import pytest

from unicode_logic_kit.fol.nodes import Atom, Constant, Not, PredicateTerm, Quantifier, Variable
from unicode_logic_kit.semantics.tarski import IllegalStructureError, Structure, satisfies
from unicode_logic_kit.semantics.thirdorder import _extension_in, holds_to, satisfies_to

HUMAN = frozenset({(0,)})                  # the property "is a Human" when Human = {0}
POSITIVE_HUMAN = Atom("Positive", [PredicateTerm("Human")])


def structure(**kwargs):
    kwargs.setdefault("sorts", {"Human": (0,)})
    return Structure([0, 1], **kwargs)


def test_a_property_known_only_as_a_sort_is_the_sorts_universe():
    # Positive holds of exactly the property HUMAN = {(0,)}: Human = {0} as a sort, no table for it.
    only_a_sort = structure(predicates={("Positive", 1): {(HUMAN,)}})
    assert holds_to(POSITIVE_HUMAN, only_a_sort) is True


def test_it_is_the_same_property_when_the_structure_also_lists_a_table_for_the_name():
    both = structure(predicates={("Human", 1): {(0,)}, ("Positive", 1): {(HUMAN,)}})
    assert holds_to(POSITIVE_HUMAN, both) is True


def test_another_universe_is_another_property():
    # Human = {0, 1}: the property is {(0,), (1,)}, which Positive (holding of {(0,)} only) does not hold of.
    wider = structure(sorts={"Human": (0, 1)}, predicates={("Positive", 1): {(HUMAN,)}})
    assert holds_to(POSITIVE_HUMAN, wider) is False
    assert holds_to(Atom("Positive", [PredicateTerm("Human")]),
                    structure(sorts={"Human": (0, 1)},
                              predicates={("Positive", 1): {(frozenset({(0,), (1,)}),)}})) is True


def test_a_name_that_is_not_a_sort_is_still_the_empty_relation_when_it_has_no_table():
    # the first-order convention for a missing predicate table is unchanged
    no_sort = Structure([0, 1], predicates={("Positive", 1): {(frozenset(),)}})
    assert holds_to(POSITIVE_HUMAN, no_sort) is True               # Human: no sort, no table: empty
    assert holds_to(POSITIVE_HUMAN, Structure([0, 1], predicates={("Positive", 1): {(HUMAN,)}})) is False


def test_the_property_is_read_inside_a_quantifier_too():
    # ∃x Positive(Human) ∧ Human(x): the property argument is the same relation at every x
    formula = Quantifier("∃", Variable("x"), Atom("Positive", [PredicateTerm("Human")]))
    assert satisfies_to(formula, structure(predicates={("Positive", 1): {(HUMAN,)}})) is True


def test_an_atom_over_the_sort_name_and_the_property_argument_agree():
    # Human(x) read first order, and Human as a property read third order, describe the same set
    s = structure(predicates={("Positive", 1): {(HUMAN,)}})
    members = [d for d in s.domain if satisfies(Atom("Human", [Constant("zero")]), Structure(
        s.domain, constants={"zero": d}, sorts=s.sorts))]
    assert members == [0]
    assert frozenset((d,) for d in members) == HUMAN


@pytest.mark.parametrize("sorts,table,expected", [
    ({"Human": (0, 1)}, None, {(0,), (1,)}),             # a sort and no table: the universe
    ({"Human": (0,)}, {(0,)}, {(0,)}),                    # a table that agrees with the sort: the table
    ({}, {(1,)}, {(1,)}),                                 # not a sort: the table
    ({}, None, set()),                                    # neither: the empty relation
])
def test_the_extension_of_a_unary_name(sorts, table, expected):
    predicates = {} if table is None else {("Human", 1): table}
    assert set(_extension_in(Structure([0, 1], sorts=sorts, predicates=predicates), "Human", 1)) == expected


def test_a_name_of_another_arity_is_never_read_as_the_sort():
    s = structure()
    assert set(_extension_in(s, "Human", 2)) == set()


def test_a_sort_that_breaks_the_definition_is_a_loud_error_here_as_it_is_at_first_order():
    # an empty sort is no structure of the definition
    illegal = Structure([0, 1], sorts={"Human": ()}, predicates={("Positive", 1): {(frozenset(),)}})
    with pytest.raises(IllegalStructureError):
        holds_to(POSITIVE_HUMAN, illegal)
    with pytest.raises(IllegalStructureError):
        satisfies(Atom("Human", [Constant("zero")]), Structure([0, 1], constants={"zero": 0},
                                                                 sorts={"Human": ()}))
    # a sort that disagrees with the predicate table of its name
    disagree = Structure([0, 1], sorts={"Human": (0,)}, predicates={("Human", 1): {(1,)}})
    with pytest.raises(IllegalStructureError):
        holds_to(POSITIVE_HUMAN, disagree)
