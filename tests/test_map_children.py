"""Tests for Node.map_children — the single structural-recursion engine.

map_children rebuilds a node applying a function to each immediate Node child,
preserving node type, field order, and container kind (tuple/list). It backs the
purely structural recursions (to_msfol, _relativize, beta/eta reduction, scope
resolution, term substitution), so a new structural node type is handled without
touching each traversal.
"""

from unicode_fol_kit import MSFLParser
from unicode_fol_kit import (
    Variable, Constant, Function, Atom, And, Not, Quantifier, LambdaVar, Lambda, Application,
)


class TestMapChildren:
    def test_identity_returns_equal_node(self):
        node = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
        assert node.map_children(lambda c: c) == node

    def test_applies_to_each_immediate_child(self):
        # Replace each immediate child with a sentinel atom.
        sentinel = Atom("S", [])
        node = And(Atom("P", []), Atom("Q", []))
        assert node.map_children(lambda c: sentinel) == And(sentinel, sentinel)

    def test_preserves_tuple_args_and_maps_elements(self):
        atom = Atom("P", [Variable("x"), Constant("a")])
        # Rename every Variable child to y; non-Node handling is automatic.
        renamed = atom.map_children(
            lambda c: Variable("y") if isinstance(c, Variable) else c
        )
        assert renamed == Atom("P", [Variable("y"), Constant("a")])
        assert isinstance(renamed.args, tuple)

    def test_function_args_container_preserved(self):
        f = Function("f", [Variable("x")])
        out = f.map_children(lambda c: c)
        assert out == f and isinstance(out.args, tuple)

    def test_binder_bound_var_is_a_child(self):
        # Quantifier exposes its bound Variable as a child field; map_children
        # touches it too (here it is a leaf, so it round-trips).
        q = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
        assert q.map_children(lambda c: c) == q

    def test_leaf_has_no_node_children(self):
        # A leaf rebuilds to an equal leaf (no Node-valued fields to map).
        assert Constant("a").map_children(lambda c: c) == Constant("a")
        assert Variable("x").map_children(lambda c: c) == Variable("x")

    def test_count_children_via_map(self):
        seen = []
        Application(LambdaVar("p"), Variable("x")).map_children(lambda c: seen.append(c) or c)
        assert seen == [LambdaVar("p"), Variable("x")]
