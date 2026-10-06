# -*- coding: utf-8 -*-
"""``Node.walk`` yields a node before its children, the children left to right, and has no depth limit.

The order is the one a recursive reading of the tree gives, derived by hand below: a node, then
everything under its first child, then everything under its second child, and so on. The children of
a node are the node-valued fields of its dataclass, in field order (``Node._child_nodes``): a
quantifier has its bound variable and then its body, an atom its arguments, a binary connective its
left and then its right operand, a counting quantifier its bound, its variable and its body.

A formula nested thousands of levels deep is walked as readily as a small one: the traversal keeps its
own stack and does not use the interpreter's recursion limit.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Node, Not, Number, Or, Quantifier, Variable,
)


def labels(node):
    """One short label per node of ``node.walk()``, in the order it is yielded."""
    out = []
    for n in node.walk():
        if isinstance(n, Atom):
            out.append(f"atom:{n.predicate}")
        elif isinstance(n, (Variable, Constant)):
            out.append(f"{type(n).__name__[:3].lower()}:{n.name}")
        elif isinstance(n, Function):
            out.append(f"fun:{n.name}")
        elif isinstance(n, Number):
            out.append(f"num:{n.value}")
        else:
            out.append(type(n).__name__)
    return out


def test_a_node_is_followed_by_its_children_from_left_to_right():
    # ∀x (P(x) → (Q(alpha) ∧ ¬R(f(x, 2))))
    formula = Quantifier("∀", Variable("x"), Implies(
        Atom("P", [Variable("x")]),
        And(Atom("Q", [Constant("alpha")]),
            Not(Atom("R", [Function("f", [Variable("x"), Number(2)])])))))
    assert labels(formula) == [
        "Quantifier", "var:x",                      # the quantifier, its bound variable
        "Implies",                                  # then its body
        "atom:P", "var:x",                          # the antecedent and its argument
        "And",                                      # then the consequent
        "atom:Q", "con:alpha",                      # its left operand
        "Not", "atom:R", "fun:f", "var:x", "num:2",  # its right operand, down to the last leaf
    ]


def test_every_node_is_yielded_once_and_the_first_is_the_root():
    formula = Or(Atom("P", []), Implies(Atom("Q", []), Atom("R", [])))
    walked = list(formula.walk())
    assert walked[0] is formula
    assert [type(n).__name__ for n in walked] == ["Or", "Atom", "Implies", "Atom", "Atom"]


def test_a_left_nested_chain_lists_its_connectives_before_its_leaves():
    # ((((A0 ∧ A1) ∧ A2) ∧ A3) ∧ A4): the root, then the root of its left operand, and so on down
    # to A0 ∧ A1; after that A0 and A1, and then the right operands A2, A3, A4 from the inside out.
    formula = Atom("A0", [])
    for i in range(1, 5):
        formula = And(formula, Atom(f"A{i}", []))
    assert labels(formula) == ["And"] * 4 + [f"atom:A{i}" for i in range(5)]


def test_a_right_nested_chain_alternates_a_leaf_and_a_connective():
    # (A0 ∧ (A1 ∧ (A2 ∧ (A3 ∧ A4)))): the root, its left operand, its right operand, and so on
    formula = Atom("A4", [])
    for i in (3, 2, 1, 0):
        formula = And(Atom(f"A{i}", []), formula)
    assert labels(formula) == ["And", "atom:A0", "And", "atom:A1", "And", "atom:A2", "And",
                               "atom:A3", "atom:A4"]


@pytest.mark.parametrize("depth", [3000, 200000])
def test_a_deep_chain_is_walked_without_the_recursion_limit(depth):
    formula = Atom("P", [])
    for _ in range(depth):
        formula = Not(formula)
    count = 0
    for node in formula.walk():
        count += 1
    assert count == depth + 1


def test_a_deep_left_nested_formula_keeps_its_order():
    depth = 3000
    formula = Atom("A0", [])
    for i in range(1, depth + 1):
        formula = And(formula, Atom(f"A{i}", []))
    walked = list(formula.walk())
    assert [type(n).__name__ for n in walked[:depth]] == ["And"] * depth
    assert [n.predicate for n in walked[depth:]] == [f"A{i}" for i in range(depth + 1)]


def test_walk_is_lazy():
    deep = Atom("P", [])
    for _ in range(100000):
        deep = Not(deep)
    walker = deep.walk()
    assert next(walker) is deep
    assert isinstance(next(walker), Not)


# The same order on parsed formulas of every parser mode: the definition of the order is the
# recursion over ``_child_nodes``, written out here independently of ``walk``.
FORMULAS = [
    ({}, "∀x (P(x) → ∃y (R(x, y) ∧ ¬Q(f(y))))"),
    ({}, "x + 1 = 2 ∧ 3 < y"),
    ({}, "∃≥2 x P(x)"),
    ({}, "P(alpha) ↔ (Q(beta) ∨ R(gamma))"),
    ({"modal": True}, "□(P → Q) → (□P → □Q)"),
    ({"modal": True}, "◇P ∧ □¬P"),
    ({"second_order": True}, "∀P ∃x P(x)"),
    ({"third_order": True}, "∀P (P(a) → P(a))"),
    ({"many_sorted": True}, "∀x:Human Mortal(x) → Mortal(socrates:Human)"),
    ({"many_sorted": True}, "∃≥2 x:Human Mortal(x)"),
    ({"linear": True}, "A ⊗ B ⊸ B ⊗ A"),
    ({"lambek": True}, "A / B"),
    ({"fuzzy": True}, "P(a) ∧ Q(b)"),
    ({"dependence": True}, "=(x, y)"),
]


def recursive_order(node):
    yield node
    for child in node._child_nodes():
        yield from recursive_order(child)


@pytest.mark.parametrize("mode, text", FORMULAS)
def test_the_order_is_that_of_the_recursion_over_the_children(mode, text):
    node = MSFLParser(**mode).parse(text)
    walked = list(node.walk())
    expected = list(recursive_order(node))
    assert len(walked) == len(expected) > 1
    assert all(a is b for a, b in zip(walked, expected))
    assert all(isinstance(n, Node) for n in walked)
