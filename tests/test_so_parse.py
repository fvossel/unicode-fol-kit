"""Tests for second-order mode of MSFLParser (∀P / ∃P over predicate variables).

Covers, across a range of formulas: the SecondOrderQuantifier AST shape including
the inferred arity, Unicode parser round-trip, to_dict/from_dict round-trip, LaTeX
rendering, tree_str, the mode-combination rules, the arity-inference rule
(including consistency, propositional arity 0, and shadowing), the
conflicting-arity ParsingError, and the export-rejection contract
(to_z3/to_prover9/to_tptp raise NotImplementedError).
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser, ConflictingArityError
from unicode_fol_kit.fol.nodes import (
    Node,
    Atom, Variable,
    And, Or, Not, Implies, Quantifier,
    SecondOrderQuantifier,
)
from unicode_fol_kit.fol.naming import ParsingError


def PX(*vs):
    return Atom("P", [Variable(v) for v in vs])


@pytest.fixture
def parser():
    return MSFLParser(second_order=True)


# ---------------------------------------------------------------------------
# Mode construction and combination rules
# ---------------------------------------------------------------------------

class TestSecondOrderMode:
    def test_mode_string(self):
        assert MSFLParser(second_order=True)._mode == "so"

    def test_default_second_order_false(self):
        assert MSFLParser()._mode == "fol"

    def test_so_with_many_sorted_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(second_order=True, many_sorted=True)

    def test_so_with_fuzzy_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(second_order=True, fuzzy=True)

    def test_so_with_modal_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(second_order=True, modal=True)

    def test_so_with_all_raises(self):
        with pytest.raises(ValueError):
            MSFLParser(second_order=True, many_sorted=True, fuzzy=True, modal=True)


# ---------------------------------------------------------------------------
# AST shape (incl. inferred arity)
# ---------------------------------------------------------------------------

# (source string, expected AST)
PARSE_CASES = [
    # monadic predicate variable
    ("∀P P(x)",
     SecondOrderQuantifier("∀", "P", 1, Atom("P", [Variable("x")]))),
    ("∃P P(x)",
     SecondOrderQuantifier("∃", "P", 1, Atom("P", [Variable("x")]))),
    # existential with a compound body
    ("∃P (P(a) ∧ ¬P(b))",
     SecondOrderQuantifier("∃", "P", 1,
        And(Atom("P", [Variable("a")]), Not(Atom("P", [Variable("b")]))))),
    # nested second-order quantifiers over different names
    ("∀P ∃Q (P(x) → Q(x))",
     SecondOrderQuantifier("∀", "P", 1,
        SecondOrderQuantifier("∃", "Q", 1,
            Implies(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")]))))),
    # binary predicate variable (arity 2)
    ("∀R R(x,y)",
     SecondOrderQuantifier("∀", "R", 2,
        Atom("R", [Variable("x"), Variable("y")]))),
    # propositional / Boolean quantification — arity 0
    ("∀P (P → P)",
     SecondOrderQuantifier("∀", "P", 0,
        Implies(Atom("P", []), Atom("P", [])))),
    ("∃P (P ∧ ¬P)",
     SecondOrderQuantifier("∃", "P", 0,
        And(Atom("P", []), Not(Atom("P", []))))),
    # mixing object (lowercase) and predicate (uppercase) quantifiers
    ("∀x ∀P (P(x) ∨ ¬P(x))",
     Quantifier("∀", Variable("x"),
        SecondOrderQuantifier("∀", "P", 1,
            Or(Atom("P", [Variable("x")]), Not(Atom("P", [Variable("x")])))))),
    ("∀P ∀x (P(x) ∨ ¬P(x))",
     SecondOrderQuantifier("∀", "P", 1,
        Quantifier("∀", Variable("x"),
            Or(Atom("P", [Variable("x")]), Not(Atom("P", [Variable("x")])))))),
    # second-order body with consistent monadic uses
    ("∀P (P(a) ∧ P(b))",
     SecondOrderQuantifier("∀", "P", 1,
        And(Atom("P", [Variable("a")]), Atom("P", [Variable("b")])))),
    # ternary predicate variable
    ("∃S S(x,y,z)",
     SecondOrderQuantifier("∃", "S", 3,
        Atom("S", [Variable("x"), Variable("y"), Variable("z")]))),
]


class TestParseShape:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_parse(self, parser, src, expected):
        assert parser.parse(src) == expected

    def test_top_level_is_so_node(self, parser):
        ast = parser.parse("∀P P(x)")
        assert isinstance(ast, SecondOrderQuantifier)
        assert ast.type == "∀"
        assert ast.predicate == "P"
        assert ast.arity == 1


# ---------------------------------------------------------------------------
# Arity inference
# ---------------------------------------------------------------------------

class TestArityInference:
    @pytest.mark.parametrize("src,arity", [
        ("∀P P(x)", 1),
        ("∀R R(x,y)", 2),
        ("∃S S(x,y,z)", 3),
        ("∀P (P → P)", 0),               # never applied -> propositional
        ("∀P (P(a) ∧ P(b))", 1),         # consistent monadic uses
    ])
    def test_inferred_arity(self, parser, src, arity):
        assert parser.parse(src).arity == arity

    def test_shadowing_inner_binder_does_not_affect_outer(self, parser):
        # The inner ∀P rebinds P at arity 2; the outer ∀P must stay arity 1
        # because its arity is inferred only from uses NOT shadowed by a
        # rebinding of the same name.
        ast = parser.parse("∀P (P(x) ∧ ∀P P(a,b))")
        assert isinstance(ast, SecondOrderQuantifier)
        assert ast.predicate == "P"
        assert ast.arity == 1
        inner = ast.formula.right
        assert isinstance(inner, SecondOrderQuantifier)
        assert inner.predicate == "P"
        assert inner.arity == 2

    def test_conflicting_arity_raises_parsing_error(self, parser):
        with pytest.raises(ParsingError):
            parser.parse("∀P (P(x) ∧ P(x,y))")

    def test_conflicting_arity_raises_specific_subclass(self, parser):
        with pytest.raises(ConflictingArityError):
            parser.parse("∀P (P(x) ∧ P(x,y))")

    def test_conflicting_arity_prop_vs_unary(self, parser):
        # P used both propositionally (arity 0) and as P(x) (arity 1).
        with pytest.raises(ParsingError):
            parser.parse("∀P (P ∧ P(x))")


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

    def test_arity_not_printed(self, parser):
        # The arity is re-inferred on re-parse; to_unicode_str must not encode it.
        ast = parser.parse("∀R R(x,y)")
        assert ast.to_unicode_str() == "∀R R(x, y)"


# ---------------------------------------------------------------------------
# to_dict / from_dict round-trip
# ---------------------------------------------------------------------------

class TestDictRoundTrip:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_dict_round_trip(self, expected, src):
        assert Node.from_dict(expected.to_dict()) == expected

    def test_dict_records_type_predicate_arity(self):
        node = SecondOrderQuantifier("∀", "P", 2, Atom("P", [Variable("x"), Variable("y")]))
        d = node.to_dict()
        assert d["_type"] == "SecondOrderQuantifier"
        assert d["type"] == "∀"
        assert d["predicate"] == "P"
        assert d["arity"] == 2
        assert d["formula"] == Atom("P", [Variable("x"), Variable("y")]).to_dict()

    def test_dict_round_trip_preserves_arity(self):
        node = SecondOrderQuantifier("∃", "P", 0, Atom("P", []))
        assert Node.from_dict(node.to_dict()) == node


# ---------------------------------------------------------------------------
# LaTeX rendering
# ---------------------------------------------------------------------------

class TestLatex:
    @pytest.mark.parametrize("node,expected", [
        (SecondOrderQuantifier("∀", "P", 1, Atom("P", [Variable("x")])),
         "\\forall P\\, P(x)"),
        (SecondOrderQuantifier("∃", "P", 1, Atom("P", [Variable("x")])),
         "\\exists P\\, P(x)"),
        (SecondOrderQuantifier("∀", "R", 2, Atom("R", [Variable("x"), Variable("y")])),
         "\\forall R\\, R(x, y)"),
        (SecondOrderQuantifier("∀", "P", 0, Atom("P", [])),
         "\\forall P\\, P"),
    ])
    def test_latex(self, node, expected):
        assert node.to_latex() == expected

    def test_latex_nested(self, parser):
        ast = parser.parse("∀P ∃Q (P(x) → Q(x))")
        assert ast.to_latex() == "\\forall P\\, \\exists Q\\, (P(x) \\rightarrow Q(x))"

    def test_latex_mixed_object_and_predicate(self, parser):
        ast = parser.parse("∀x ∀P (P(x) ∨ ¬P(x))")
        assert ast.to_latex() == "\\forall x\\, \\forall P\\, (P(x) \\lor \\lnot P(x))"


# ---------------------------------------------------------------------------
# tree_str
# ---------------------------------------------------------------------------

class TestTreeStr:
    def test_tree_shows_type_predicate_arity(self):
        s = SecondOrderQuantifier("∀", "P", 2, Atom("P", [Variable("x"), Variable("y")])).tree_str()
        assert s.startswith("∀ P/2")
        assert "Atom: P" in s

    def test_tree_arity_zero(self):
        s = SecondOrderQuantifier("∃", "P", 0, Atom("P", [])).tree_str()
        assert s.startswith("∃ P/0")


# ---------------------------------------------------------------------------
# Export rejection: second-order quantification is not first-order / SMT
# ---------------------------------------------------------------------------

class TestExportRejection:
    @pytest.fixture
    def node(self):
        return SecondOrderQuantifier("∀", "P", 1, Atom("P", [Variable("x")]))

    def test_to_z3_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_z3()

    def test_to_prover9_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_prover9()

    def test_to_tptp_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_tptp()

    def test_parsed_node_rejects_z3(self, parser):
        with pytest.raises(NotImplementedError):
            parser.parse("∀P P(x)").to_z3()


# ---------------------------------------------------------------------------
# Inherited structural behaviour (traversal / free variables)
# ---------------------------------------------------------------------------

class TestStructural:
    def test_walk_includes_body(self, parser):
        ast = parser.parse("∀P P(x)")
        nodes = list(ast.walk())
        assert ast in nodes
        assert Atom("P", [Variable("x")]) in nodes

    def test_free_variables_unaffected_by_predicate_binder(self, parser):
        # Binding the predicate name P does not bind the object variable x.
        from unicode_fol_kit.fol.nodes import free_variables
        ast = parser.parse("∀P P(x)")
        assert free_variables(ast) == {Variable("x")}

    def test_count_atoms(self, parser):
        ast = parser.parse("∃P (P(a) ∧ ¬P(b))")
        assert ast.count(Atom) == 2
