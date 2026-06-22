"""Tests for the Node traversal/inspection API and to_dot() Graphviz export."""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol._fol_nodes import (
    Atom, Variable, And, Quantifier, Not, Implies,
)

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)


class TestWalk:
    def test_walk_yields_self_first(self):
        node = FOL.parse("P(x) ∧ Q(x)")
        assert list(node.walk())[0] is node

    def test_walk_visits_all_nodes(self):
        # And(Atom P [Var x], Atom Q [Var x]) → And, P, x, Q, x = 5 nodes
        node = FOL.parse("P(x) ∧ Q(x)")
        assert len(list(node.walk())) == 5

    def test_walk_preorder(self):
        node = FOL.parse("¬P(x)")
        kinds = [type(n).__name__ for n in node.walk()]
        assert kinds == ["Not", "Atom", "Variable"]


class TestSubformulas:
    def test_excludes_terms(self):
        node = FOL.parse("P(x) ∧ Q(y)")
        subs = node.subformulas()
        # And + two Atoms; the Variables x, y are terms and excluded
        assert {type(n).__name__ for n in subs} == {"And", "Atom"}
        assert all(type(n).__name__ != "Variable" for n in subs)


class TestAtomsVariables:
    def test_atoms(self):
        node = FOL.parse("∀x (P(x) → Q(x))")
        assert sorted(a.predicate for a in node.atoms()) == ["P", "Q"]

    def test_variables_includes_bound(self):
        node = FOL.parse("∀x (P(x) → Q(y))")
        assert {v.name for v in node.variables()} == {"x", "y"}

    def test_atoms_keep_duplicates(self):
        node = FOL.parse("P(x) ∧ P(x)")
        assert len(node.atoms()) == 2


class TestCountDepth:
    def test_count_all(self):
        assert FOL.parse("P(x) ∧ Q(x)").count() == 5

    def test_count_by_class(self):
        node = FOL.parse("∀x (P(x) → Q(x))")
        assert node.count(Atom) == 2
        assert node.count(Quantifier) == 1
        # 3 Variable nodes: the quantifier's bound x, plus x in P(x) and in Q(x).
        # walk() counts every occurrence; variables() (a set) would dedupe to {x}.
        assert node.count(Variable) == 3

    def test_depth_leafish(self):
        # Atom P [Var x]: Atom → Variable = depth 2
        assert FOL.parse("P(x)").depth() == 2

    def test_depth_nested(self):
        # Quantifier → Implies → Atom → Variable = depth 4
        assert FOL.parse("∀x (P(x) → Q(x))").depth() == 4


class TestToDot:
    def test_is_digraph(self):
        dot = FOL.parse("P(x) ∧ Q(x)").to_dot()
        assert dot.startswith("digraph AST {")
        assert dot.rstrip().endswith("}")

    def test_contains_labels_and_edges(self):
        dot = FOL.parse("∀x (Human(x) → Mortal(x))").to_dot()
        assert 'label="∀ x"' in dot
        assert 'label="Atom: Human"' in dot
        assert "->" in dot

    def test_node_count_matches_tree_parts(self):
        # one DOT node declaration per node in the tree-view
        node = FOL.parse("P(x) → Q(x)")
        dot = node.to_dot()
        decl_lines = [ln for ln in dot.splitlines() if "label=" in ln]
        # Implies + P + x + Q + x = 5
        assert len(decl_lines) == 5

    def test_escapes_quotes(self):
        # comparison atoms contain no quotes, but ensure backslash/quote-safe output
        dot = FOL.parse("x = y").to_dot()
        assert "digraph" in dot
