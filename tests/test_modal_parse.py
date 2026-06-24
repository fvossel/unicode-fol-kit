"""Tests for modal-logic mode of MSFLParser (alethic, epistemic, doxastic, temporal).

Covers, for many formulas across all eight modal operators: AST shape, Unicode
parser round-trip, to_dict/from_dict round-trip, LaTeX glyphs, tree_str, and the
export-rejection contract (to_z3/to_prover9/to_tptp raise NotImplementedError).
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Node,
    Atom, Variable, Constant,
    And, Or, Xor, Not, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
)


P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])
PX = Atom("P", [Variable("x")])


@pytest.fixture
def parser():
    return MSFLParser(modal=True)


# ---------------------------------------------------------------------------
# Mode construction and combination rules
# ---------------------------------------------------------------------------

class TestModalMode:
    def test_mode_string(self):
        assert MSFLParser(modal=True)._mode == "modal"

    def test_modal_with_many_sorted_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(modal=True, many_sorted=True)

    def test_modal_with_fuzzy_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(modal=True, fuzzy=True)

    def test_modal_with_both_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(modal=True, many_sorted=True, fuzzy=True)

    def test_default_modal_false(self):
        assert MSFLParser()._mode == "fol"


# ---------------------------------------------------------------------------
# AST shape for each operator
# ---------------------------------------------------------------------------

# (source string, expected AST)
PARSE_CASES = [
    ("□P", Box(P)),
    ("◇P", Diamond(P)),
    ("ⒼP", Always(P)),
    ("ⒻP", Eventually(P)),
    ("ⓃP", Next(P)),
    ("K_alice P", Knows("alice", P)),
    ("B_bob Q", Believes("bob", Q)),
    ("P Ⓤ Q", Until(P, Q)),
    # nesting
    ("□◇P", Box(Diamond(P))),
    ("ⒼⒻP", Always(Eventually(P))),
    ("ⓃⓃP", Next(Next(P))),
    ("K_alice B_bob P", Knows("alice", Believes("bob", P))),
    ("□□□P", Box(Box(Box(P)))),
    # mixing with classical connectives
    ("□P ∧ Q", And(Box(P), Q)),
    ("□(P ∧ Q)", Box(And(P, Q))),
    ("◇P ∨ ◇Q", Or(Diamond(P), Diamond(Q))),
    ("□P → ◇Q", Implies(Box(P), Diamond(Q))),
    ("□P ↔ ◇P", Iff(Box(P), Diamond(P))),
    ("□P ⊕ Q", Xor(Box(P), Q)),
    ("¬□P", Not(Box(P))),
    ("□¬P", Box(Not(P))),
    ("¬□P → Q", Implies(Not(Box(P)), Q)),
    # with quantifiers
    ("∀x □P(x)", Quantifier("∀", Variable("x"), Box(PX))),
    ("□∀x P(x)", Box(Quantifier("∀", Variable("x"), PX))),
    ("∃x ◇P(x)", Quantifier("∃", Variable("x"), Diamond(PX))),
    # epistemic with different agents and bodies
    ("K_a (P ∧ Q)", Knows("a", And(P, Q))),
    ("B_carol (P → Q)", Believes("carol", Implies(P, Q))),
    ("K_alice ◇P", Knows("alice", Diamond(P))),
    # Until precedence and associativity
    ("P Ⓤ Q Ⓤ R", Until(P, Until(Q, R))),          # right-associative
    ("P ∧ Q Ⓤ R", Until(And(P, Q), R)),            # looser than ∧
    ("P Ⓤ Q → R", Implies(Until(P, Q), R)),        # tighter than →
    ("P → Q Ⓤ R", Implies(P, Until(Q, R))),
    ("□P Ⓤ ◇Q", Until(Box(P), Diamond(Q))),
    ("ⒼP Ⓤ ⒻQ", Until(Always(P), Eventually(Q))),
]


class TestParseShape:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_parse(self, parser, src, expected):
        assert parser.parse(src) == expected


# ---------------------------------------------------------------------------
# Unicode parser round-trip: parse(ast.to_unicode_str()) == ast
# ---------------------------------------------------------------------------

class TestUnicodeRoundTrip:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_round_trip(self, parser, src, expected):
        ast = parser.parse(src)
        assert parser.parse(ast.to_unicode_str()) == ast

    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_round_trip_equals_expected(self, parser, src, expected):
        assert parser.parse(expected.to_unicode_str()) == expected


# ---------------------------------------------------------------------------
# to_dict / from_dict round-trip
# ---------------------------------------------------------------------------

class TestDictRoundTrip:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_dict_round_trip(self, expected, src):
        assert Node.from_dict(expected.to_dict()) == expected

    def test_knows_dict_has_agent(self):
        d = Knows("alice", P).to_dict()
        assert d == {"_type": "Knows", "agent": "alice", "formula": P.to_dict()}

    def test_believes_dict_has_agent(self):
        d = Believes("bob", Q).to_dict()
        assert d == {"_type": "Believes", "agent": "bob", "formula": Q.to_dict()}

    def test_until_dict(self):
        d = Until(P, Q).to_dict()
        assert d == {"_type": "Until", "left": P.to_dict(), "right": Q.to_dict()}

    @pytest.mark.parametrize("node", [
        Box(P), Diamond(P), Always(P), Eventually(P), Next(P),
        Knows("a", P), Believes("b", Q), Until(P, Q),
    ])
    def test_each_node_dict_round_trip(self, node):
        assert Node.from_dict(node.to_dict()) == node


# ---------------------------------------------------------------------------
# LaTeX glyphs
# ---------------------------------------------------------------------------

class TestLatex:
    @pytest.mark.parametrize("node,expected", [
        (Box(P), "\\Box P"),
        (Diamond(P), "\\Diamond P"),
        (Always(P), "\\mathsf{G} P"),
        (Eventually(P), "\\mathsf{F} P"),
        (Next(P), "\\mathsf{X} P"),
        (Knows("alice", P), "K_{alice} P"),
        (Believes("bob", Q), "B_{bob} Q"),
        (Until(P, Q), "P \\mathbin{\\mathsf{U}} Q"),
    ])
    def test_latex_glyphs(self, node, expected):
        assert node.to_latex() == expected

    def test_latex_nested(self):
        assert Box(Diamond(P)).to_latex() == "\\Box \\Diamond P"

    def test_latex_until_parenthesised_under_implies(self, parser):
        ast = parser.parse("P Ⓤ Q → R")
        assert ast.to_latex() == "(P \\mathbin{\\mathsf{U}} Q) \\rightarrow R"

    def test_latex_box_and(self, parser):
        ast = parser.parse("□P ∧ Q")
        assert ast.to_latex() == "\\Box P \\land Q"


# ---------------------------------------------------------------------------
# tree_str
# ---------------------------------------------------------------------------

class TestTreeStr:
    def test_box_tree(self):
        s = Box(P).tree_str()
        assert s.startswith("□")
        assert "Atom: P" in s

    def test_knows_tree_shows_agent(self):
        s = Knows("alice", P).tree_str()
        assert "K_alice" in s

    def test_believes_tree_shows_agent(self):
        s = Believes("bob", Q).tree_str()
        assert "B_bob" in s

    def test_until_tree_two_children(self):
        s = Until(P, Q).tree_str()
        assert s.startswith("Ⓤ")
        assert "Atom: P" in s and "Atom: Q" in s

    def test_temporal_tree_labels(self):
        assert Always(P).tree_str().startswith("Ⓖ")
        assert Eventually(P).tree_str().startswith("Ⓕ")
        assert Next(P).tree_str().startswith("Ⓝ")
        assert Diamond(P).tree_str().startswith("◇")


# ---------------------------------------------------------------------------
# Export rejection: to_z3 / to_prover9 / to_tptp raise NotImplementedError
# ---------------------------------------------------------------------------

MODAL_NODES = [
    Box(P), Diamond(P), Always(P), Eventually(P), Next(P),
    Knows("a", P), Believes("b", Q), Until(P, Q),
]


class TestExportRejection:
    @pytest.mark.parametrize("node", MODAL_NODES)
    def test_to_z3_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_z3()

    @pytest.mark.parametrize("node", MODAL_NODES)
    def test_to_prover9_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_prover9()

    @pytest.mark.parametrize("node", MODAL_NODES)
    def test_to_tptp_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_tptp()


# ---------------------------------------------------------------------------
# Structural inheritance: free_variables / traversal recurse into modal nodes
# ---------------------------------------------------------------------------

class TestStructural:
    def test_free_variables_through_box(self):
        from unicode_fol_kit.fol.nodes import free_variables
        node = Box(Atom("P", [Variable("x")]))
        assert free_variables(node) == {Variable("x")}

    def test_free_variables_bound_under_modal(self):
        from unicode_fol_kit.fol.nodes import free_variables
        node = Box(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))
        assert free_variables(node) == set()

    def test_until_free_variables_union(self):
        from unicode_fol_kit.fol.nodes import free_variables
        node = Until(Atom("P", [Variable("x")]), Atom("Q", [Variable("y")]))
        assert free_variables(node) == {Variable("x"), Variable("y")}

    def test_walk_visits_modal_children(self):
        node = Knows("a", And(P, Q))
        kinds = [type(n).__name__ for n in node.walk()]
        assert kinds[0] == "Knows"
        assert "And" in kinds and kinds.count("Atom") == 2

    def test_depth_counts_modal_layer(self):
        assert Box(P).depth() == 2
        assert Box(Diamond(P)).depth() == 3
