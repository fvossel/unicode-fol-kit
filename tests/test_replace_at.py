"""Tests for ``fol.nodes.replace_at`` — public, path-addressed subtree
replacement (spec item B1).

``replace_at(root, path, new_node)`` rebuilds ``root`` with the subtree at
``path`` replaced by ``new_node``. A path is a tuple of ints indexing a
node's PATH CHILDREN at each level — ``Node._child_nodes()`` order (the SAME
child order ``Node.map_children`` already uses, see ``test_map_children.py``)
for every node EXCEPT a ``Quantifier``, whose bound variable is excluded: a
``Quantifier``'s only path child is its ``formula``, at index 0 (see
``fol/_fol_nodes.py``'s "Public tree editing" section and
``fol/spans.py``'s module docstring for why — this is the SAME convention
:func:`unicode_fol_kit.fol.spans.traverse`/:class:`~unicode_fol_kit.fol.spans.SpanMap`
use, so a path from one is valid input to the other, per spec item A2).

This suite checks: root replacement, a nested replacement several levels
deep, invalid-path errors, and — the B1 STABILITY GUARANTEE — that any path
which does not run through the replaced subtree addresses the exact same
object (``is``, not just ``==``) in the result as it did in the original
tree, while the spine from the root down to the replaced node is rebuilt.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser,
    Variable, Constant, Atom, And, Implies, Or, Quantifier,
    replace_at,
)

FOL = MSFLParser()


class TestReplaceAtBasics:
    def test_empty_path_replaces_root(self):
        root = Atom("P", [Variable("x")])
        new = Atom("Q", [])
        assert replace_at(root, (), new) is new

    def test_replace_direct_child(self):
        p, q, r = Atom("P", []), Atom("Q", []), Atom("R", [])
        root = And(p, q)
        out = replace_at(root, (0,), r)
        assert out == And(r, q)
        assert out.right is q  # untouched sibling: same object

    def test_replace_nested_subtree(self):
        # root is a Quantifier: its only path child is its formula, at
        # index 0 (not index 1 — the bound variable is not a path child).
        root = FOL.parse("∀x (P(x) ∧ Q(x))")
        out = replace_at(root, (0, 0), Atom("R", [Variable("x")]))
        assert out == FOL.parse("∀x (R(x) ∧ Q(x))")

    def test_replace_argument_term(self):
        root = Atom("P", [Variable("x"), Constant("a")])
        out = replace_at(root, (1,), Constant("b"))
        assert out == Atom("P", [Variable("x"), Constant("b")])

    def test_quantifier_formula_is_index_0(self):
        # A Quantifier's ONLY path child is its formula (its bound variable
        # is deliberately excluded — see the module docstring).
        root = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
        out = replace_at(root, (0,), Atom("Q", [Variable("x")]))
        assert out == Quantifier("∀", Variable("x"), Atom("Q", [Variable("x")]))

    def test_quantifier_bound_variable_is_not_path_addressable(self):
        # With formula as the sole path child at index 0, index 1 (where the
        # bound variable would have sat under plain _child_nodes() order) is
        # simply out of range -- the variable cannot be reached via any
        # replace_at path at all, matching fol.spans.traverse.
        root = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
        with pytest.raises(IndexError):
            replace_at(root, (1,), Variable("y"))

    def test_new_node_need_not_match_the_old_shape(self):
        # replace_at does not type-check the replacement against the slot;
        # it is a structural edit, not a typed rewrite rule.
        root = And(Atom("P", []), Atom("Q", []))
        out = replace_at(root, (0,), Variable("z"))
        assert out == And(Variable("z"), Atom("Q", []))


class TestReplaceAtErrors:
    def test_index_out_of_range_raises(self):
        root = And(Atom("P", []), Atom("Q", []))
        with pytest.raises(IndexError):
            replace_at(root, (2,), Atom("R", []))

    def test_path_into_leaf_raises(self):
        # Variable/Constant have no children at all.
        with pytest.raises(IndexError):
            replace_at(Variable("x"), (0,), Variable("y"))

    def test_negative_index_raises(self):
        root = And(Atom("P", []), Atom("Q", []))
        with pytest.raises(IndexError):
            replace_at(root, (-1,), Atom("R", []))

    def test_overlong_path_past_a_leaf_raises(self):
        root = And(Atom("P", []), Atom("Q", []))
        with pytest.raises(IndexError):
            replace_at(root, (0, 0, 0), Atom("R", []))


class TestReplaceAtStabilityGuarantee:
    """B1: a path that does not run through the replaced subtree still
    addresses the identical object in the result; only the spine from the
    root down to the replaced node is rebuilt."""

    @staticmethod
    def _formula():
        # ∀x ((P(x) ∧ Q(x)) → (R(x) ∨ S(x)))
        return FOL.parse("∀x ((P(x) ∧ Q(x)) → (R(x) ∨ S(x)))")

    def test_untouched_branch_of_the_spine_is_the_same_object(self):
        root = self._formula()
        implies = root._child_nodes()[1]
        or_node = implies._child_nodes()[1]           # R(x) ∨ S(x)

        out = replace_at(root, (0, 0, 0), Atom("T", [Variable("x")]))

        out_implies = out._child_nodes()[1]
        assert out_implies._child_nodes()[1] is or_node

    def test_untouched_sibling_within_a_rebuilt_ancestor_is_the_same_object(self):
        root = self._formula()
        implies = root._child_nodes()[1]
        and_node = implies._child_nodes()[0]
        q_atom = and_node._child_nodes()[1]            # Q(x), sibling of P(x)

        out = replace_at(root, (0, 0, 0), Atom("T", [Variable("x")]))

        out_and = out._child_nodes()[1]._child_nodes()[0]
        assert out_and._child_nodes()[1] is q_atom

    def test_replaced_path_addresses_the_new_node_object(self):
        root = self._formula()
        replacement = Atom("T", [Variable("x")])
        out = replace_at(root, (0, 0, 0), replacement)
        out_and = out._child_nodes()[1]._child_nodes()[0]
        assert out_and._child_nodes()[0] is replacement

    def test_spine_ancestors_are_rebuilt_not_reused(self):
        root = self._formula()
        out = replace_at(root, (0, 0, 0), Atom("T", [Variable("x")]))
        assert out is not root
        assert out._child_nodes()[1] is not root._child_nodes()[1]

    def test_original_tree_is_unmodified(self):
        # Nodes are frozen dataclasses so in-place mutation is impossible,
        # but pin the observable behaviour down as a regression test.
        root = self._formula()
        before = repr(root)
        replace_at(root, (0, 0, 0), Atom("T", [Variable("x")]))
        assert repr(root) == before

    def test_replacing_back_restores_structural_equality(self):
        root = self._formula()
        original_p = root._child_nodes()[1]._child_nodes()[0]._child_nodes()[0]
        mutated = replace_at(root, (0, 0, 0), Atom("T", [Variable("x")]))
        restored = replace_at(mutated, (0, 0, 0), original_p)
        assert restored == root
