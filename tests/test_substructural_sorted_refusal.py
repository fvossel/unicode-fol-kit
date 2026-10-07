"""Intuitionistic linear logic and the Lambek calculus refuse a many-sorted node, by name.

Both calculi have categories (resources) and connectives, no individuals, no sorts and no quantifiers. A
sorted quantifier, constant, count or cardinality taken for one more opaque category would make a
derivability verdict about ANOTHER formula: ``∀x:Human Mortal(x)`` does not derive ``Mortal(socrates:Human)``
as two unrelated categories, and it does in every first-order reading, so a REFUTED verdict was a claim
the calculus could not stand behind. The backends answer UNKNOWN, reason "unsupported", and the detail
names the node and what to use instead. A plain category is decided exactly as before.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_logic_kit.fol.nodes import (
    Atom, Number, SortedCardinality, SortedConstant, SortedCount, SortedQuantifier, Variable,
)

X = Variable("x")
SORTED_NODES = {
    "SortedConstant": Atom("NP", [SortedConstant("carl", "Human")]),
    "SortedQuantifier": SortedQuantifier("∀", X, "Human", Atom("Mortal", [X])),
    "SortedCount": SortedCount("ge", Number(2), X, "Human", Atom("Mortal", [X])),
    "SortedCardinality": Atom("=", [SortedCardinality(X, "Human", Atom("P", [X])), Number(2)]),
}
PLAIN = Atom("NP", [])


@pytest.mark.parametrize("backend, logic", [("ill", "ill"), ("lambek", "lambek")])
@pytest.mark.parametrize("node_name", sorted(SORTED_NODES))
def test_a_sorted_node_is_refused_by_name(backend, logic, node_name):
    node = SORTED_NODES[node_name]
    for premises, goal in (([node], PLAIN), ([PLAIN], node)):
        verdict = get_backend(backend).decide(goal, premises)
        assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
        assert node_name in verdict.detail
        assert "first-order route" in verdict.detail


@pytest.mark.parametrize("backend, logic", [("ill", "ill"), ("lambek", "lambek")])
def test_through_api_prove_the_refusal_carries_its_reason(backend, logic):
    node = SORTED_NODES["SortedQuantifier"]
    verdict = api.prove(PLAIN, [node], backends=[backend], logic=logic)
    assert verdict.status == UNKNOWN
    assert "SortedQuantifier" in verdict.detail and "unsupported" in verdict.detail


@pytest.mark.parametrize("backend, logic", [("ill", "ill"), ("lambek", "lambek")])
def test_a_plain_category_is_decided_as_before(backend, logic):
    other = Atom("S", [])
    assert get_backend(backend).decide(PLAIN, [PLAIN]).status == PROVED       # A ⊢ A
    assert get_backend(backend).decide(other, [PLAIN]).status == REFUTED      # A ⊢ B has no derivation

