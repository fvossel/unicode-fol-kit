"""Which sorts a formula uses: ``ValidationReport.sorts_used`` and ``Signature.from_formulas``.

Four node types carry a sort name: the sorted quantifier ``∀x:S φ``, the sorted constant ``c:S``,
the sorted counting quantifier ``∃≥n x:S φ`` and the sorted cardinality term ``|{x:S : φ}|``. A sort
that occurs in ANY of them is a sort the formula uses, whether or not one of the other three also
names it. Each expected set below is read off the formula written next to it.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.eval.validate import validate, validate_text
from unicode_fol_kit.fol._msfl_nodes import _SORTED_NODE_TYPES
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Not, Number, SortedCardinality, SortedConstant, SortedCount,
    SortedQuantifier, Variable,
)
from unicode_fol_kit.fol.signature import Signature

X = Variable("x")
BODY = Atom("P", [X])


def parse(text):
    return MSFLParser(many_sorted=True).parse(text)


#: one formula per sorted node type, each naming a sort that no other node of the formula names
FORMULAS = {
    "quantifier": (SortedQuantifier("∀", X, "OnlyInQuantifier", BODY), {"OnlyInQuantifier"}),
    "constant": (Atom("Q", [SortedConstant("carl", "OnlyInConstant")]), {"OnlyInConstant"}),
    "counting quantifier": (SortedCount("ge", Number(2), X, "OnlyInCount", BODY), {"OnlyInCount"}),
    "cardinality term": (Atom(">", [SortedCardinality(X, "OnlyInCardinality", BODY), Number(1)]),
                         {"OnlyInCardinality"}),
}


@pytest.mark.parametrize("label", sorted(FORMULAS))
def test_a_sort_named_by_one_kind_of_node_alone_is_a_sort_used(label):
    formula, sorts = FORMULAS[label]
    assert set(validate(formula).sorts_used) == sorts


def test_every_node_type_that_carries_a_sort_is_read():
    # the four types, and no other: the report must follow the reduction to plain FOL, which names them
    assert set(_SORTED_NODE_TYPES) == {SortedQuantifier, SortedConstant, SortedCount, SortedCardinality}


def test_the_sorts_of_all_four_kinds_are_listed_once_each_in_sorted_order():
    formulas = [formula for formula, _ in FORMULAS.values()]
    conjunction = formulas[0]
    for formula in formulas[1:]:
        conjunction = And(conjunction, formula)
    # the same sort in a second node is not listed twice
    conjunction = And(conjunction, SortedCount("le", Number(1), X, "OnlyInCount", BODY))
    # alphabetical: Cardinality < Constant ("n" < "u" in Con/Cou) < Count < Quantifier
    assert validate(conjunction).sorts_used == (
        "OnlyInCardinality", "OnlyInConstant", "OnlyInCount", "OnlyInQuantifier")


def test_a_sorted_node_under_other_operators_is_found():
    formula, sorts = FORMULAS["counting quantifier"]
    assert set(validate(Not(And(BODY, formula))).sorts_used) == sorts


@pytest.mark.parametrize("text,sorts", [
    ("∃≥2 x:Human Mortal(x)", ("Human",)),
    ("∃=1 x:Human Mortal(x)", ("Human",)),
    ("∃≤3 x:Cat Fluffy(x)", ("Cat",)),
    ("|{x:Human : Mortal(x)}| > 1", ("Human",)),
    ("∃≥2 x:Human Mortal(x) ∧ ∀y:Animal Alive(y)", ("Animal", "Human")),
])
def test_the_text_forms_report_the_sorts_they_write(text, sorts):
    assert validate_text(text, parser=MSFLParser(many_sorted=True)).sorts_used == sorts


def test_an_unsorted_formula_uses_no_sort():
    assert validate(And(BODY, Atom("Q", [Constant("carl")]))).sorts_used == ()


# ---- the same hole in the signature a batch of formulas implies --------------------------------

@pytest.mark.parametrize("label", sorted(FORMULAS))
def test_a_signature_inferred_from_formulas_lists_a_sort_named_by_one_kind_of_node_alone(label):
    formula, sorts = FORMULAS[label]
    assert Signature.from_formulas([formula]).sorts == frozenset(sorts)


def test_a_signature_inferred_from_a_counting_formula_in_text_lists_its_sort():
    assert Signature.from_formulas([parse("∃≥2 x:Human Mortal(x)")]).sorts == frozenset({"Human"})
    assert Signature.from_formulas([parse("|{x:Human : Mortal(x)}| > 1")]).sorts == frozenset({"Human"})
