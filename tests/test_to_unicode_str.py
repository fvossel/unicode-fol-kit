"""Tests for Node.to_unicode_str(): render → re-parse parser round-trip.

The core contract: for any parser-produced AST in a given mode,
    parse(node.to_unicode_str()) == node
holds structurally. Each mode is exercised with its own parser instance.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol._fol_nodes import (
    Variable, Constant, Number, Function, Atom,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
)
from unicode_fol_kit.fol._msfl_nodes import (
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)


# ---------------------------------------------------------------------------
# Helpers: one parser per mode; round-trip assertion
# ---------------------------------------------------------------------------

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)
MSFL = MSFLParser(many_sorted=True, fuzzy=True)
FL = MSFLParser(many_sorted=False, fuzzy=True)


def _roundtrip(parser, formula: str):
    """Parse formula, render it back, re-parse, and assert AST equality.

    Returns the rendered string so individual tests can additionally assert on
    its exact shape where the canonical form matters.
    """
    ast = parser.parse(formula)
    rendered = ast.to_unicode_str()
    reparsed = parser.parse(rendered)
    assert reparsed == ast, (
        f"round-trip mismatch\n  input:    {formula!r}\n"
        f"  rendered: {rendered!r}\n  ast:      {ast!r}\n  reparsed: {reparsed!r}"
    )
    return rendered


# ---------------------------------------------------------------------------
# FOL mode
# ---------------------------------------------------------------------------

class TestFOLRoundtrip:
    @pytest.mark.parametrize("formula", [
        "P(x)",
        "P",
        "¬P(x)",
        "¬¬P(x)",
        "P(x) ∧ Q(x)",
        "P(x) ∨ Q(x)",
        "P(x) ⊕ Q(x)",
        "P(x) → Q(x)",
        "P(x) ↔ Q(x)",
        "P(x) ∧ Q(x) ∧ R(x)",
        "(P(x) ∧ Q(x)) ∨ R(x)",
        "P(x) ∧ (Q(x) ∨ R(x))",
        "P(x) → Q(x) → R(x)",
        "(P(x) → Q(x)) → R(x)",
        "P(x) → Q(x) ↔ R(x)",
        "P(x) ↔ Q(x) → R(x)",
        "¬(P(x) ∧ Q(x))",
        "∀x P(x)",
        "∃x P(x)",
        "∀x (P(x) → Q(x))",
        "∀x P(x) ∧ Q(x)",
        "∀x ∃y R(x, y)",
        "∀x (P(x) ∧ Q(x) → R(x))",
        "¬∀x P(x)",
        "P(socrates)",
        "P(c_a)",
        "Human(socrates) → Mortal(socrates)",
        "x = y",
        "x ≠ y",
        "x < y",
        "x ≤ y",
        "x ≥ y",
        "x > y",
        "x + y = z",
        "x + y * z = w",
        "(x + y) * z = w",
        "x - (y - z) = w",
        "distance(y, centerOf(x)) = distance(z, centerOf(x))",
        "P(x) ∧ Q(x) → R(x)",
    ])
    def test_roundtrip(self, formula):
        _roundtrip(FOL, formula)

    def test_complete_sphere_example(self):
        formula = (
            "∀x ((Object(x) ∧ HasThreeDimensionalShape(x) ∧ "
            "∀y ∀z ((Point(y) ∧ OnSurfaceOf(y, x) ∧ Point(z) ∧ OnSurfaceOf(z, x)) "
            "→ distance(y, centerOf(x)) = distance(z, centerOf(x)))) "
            "→ Sphere(x))"
        )
        _roundtrip(FOL, formula)


# ---------------------------------------------------------------------------
# MSFOL mode
# ---------------------------------------------------------------------------

class TestMSFOLRoundtrip:
    @pytest.mark.parametrize("formula", [
        "∀x:Human P(x)",
        "∃x:Human P(x)",
        "∀x:Human (Mortal(x) ∧ ¬Immortal(x))",
        "P(alice:Human)",
        "∀x:Person ∀y:Person ((Knows(x, y) ∧ Trusted(y)) → Shares(x, y))",
        "∀x:Human (P(x) → Q(x))",
        "∀x:H ∀y:H ∃z:A R(x, y)",
        "P(alice:Human) ∧ Q(bob:Human)",
    ])
    def test_roundtrip(self, formula):
        _roundtrip(MSFOL, formula)


# ---------------------------------------------------------------------------
# MSFL mode
# ---------------------------------------------------------------------------

class TestMSFLRoundtrip:
    @pytest.mark.parametrize("formula", [
        "P(x) ∧ Q(x)",
        "P(x) ∨ Q(x)",
        "P(x) ⊗ Q(x)",
        "P(x) ⊕ Q(x)",
        "¬P(x)",
        "P(x) → Q(x)",
        "P(x) ↔ Q(x)",
        "∀x:Human P(x)",
        "(P(x) ∧ Q(x)) ⊗ R(x)",
        "(P(x) ⊗ Q(x)) ∧ R(x)",
        "P(x) ⊗ Q(x) ⊗ R(x)",
        "¬(P(x) ⊗ Q(x))",
        "∀x:Patient ∀y:Treatment ((Effective(y) ⊗ Tolerable(x, y)) → Recommended(x, y))",
    ])
    def test_roundtrip(self, formula):
        _roundtrip(MSFL, formula)

    def test_strong_disjunction_is_not_xor(self):
        ast = MSFL.parse("P(x) ⊕ Q(x)")
        assert isinstance(ast, StrongDisjunction)
        assert isinstance(MSFL.parse(ast.to_unicode_str()), StrongDisjunction)


# ---------------------------------------------------------------------------
# FL mode
# ---------------------------------------------------------------------------

class TestFLRoundtrip:
    @pytest.mark.parametrize("formula", [
        "P(x) ∧ Q(x)",
        "P(x) ⊗ Q(x)",
        "P(x) ⊕ Q(x)",
        "¬P(x)",
        "P(x) → Q(x)",
        "P(x) ↔ Q(x)",
        "∀x P(x)",
        "∃x P(x)",
        "P(alice)",
        "∀x (P(x) ⊗ Q(x))",
        "(P(x) ∧ Q(x)) ⊗ R(x)",
        "∀x ∀y ((Effective(y) ⊗ Tolerable(x, y)) → Recommended(x, y))",
    ])
    def test_roundtrip(self, formula):
        _roundtrip(FL, formula)

    def test_unsorted_quantifier_stays_unsorted(self):
        ast = FL.parse("∀x P(x)")
        assert isinstance(ast, Quantifier)
        assert ":" not in ast.to_unicode_str()


# ---------------------------------------------------------------------------
# Lambda / higher-order (all modes share the syntax; FOL parser used here)
# ---------------------------------------------------------------------------

class TestLambdaRoundtrip:
    @pytest.mark.parametrize("formula", [
        "λx. P(x)",
        "λx. P(x) ∧ Q(x)",
        "λx. P(x) → Q(x)",
        "λP. P(x)",
        "λP. λx. P(x)",
        "λfoo. P(foo(x))",
        "λfoo. P(foo(x, y))",
        "(λx. P(x))(a)",
        "(λx. P(x))(alice)",
        "(λP. P(x))(Q)",
        "(λP. P(x))(Q(y))",
        "λx. ∀x P(x)",
        "∀x (P(x) ∧ Q(x))",
    ])
    def test_roundtrip(self, formula):
        _roundtrip(FOL, formula)

    def test_lambda_in_fl_mode(self):
        _roundtrip(FL, "λx. P(x) ⊗ Q(x)")

    def test_higher_order_predicate_application_form(self):
        # λP. P(x) resolves to Application(LambdaVar("P"), Variable("x"));
        # rendered as (P)(x) and re-parses/resolves to the same node.
        ast = FOL.parse("λP. P(x)")
        assert ast == Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
        assert FOL.parse(ast.to_unicode_str()) == ast


# ---------------------------------------------------------------------------
# Hand-built ASTs (not via parser) still render and round-trip
# ---------------------------------------------------------------------------

class TestHandBuiltRoundtrip:
    def test_left_nested_conjunction_flattens(self):
        node = And(And(Atom("P", []), Atom("Q", [])), Atom("R", []))
        assert node.to_unicode_str() == "P ∧ Q ∧ R"
        assert FOL.parse(node.to_unicode_str()) == node

    def test_right_nested_conjunction_parenthesised(self):
        node = And(Atom("P", []), And(Atom("Q", []), Atom("R", [])))
        assert node.to_unicode_str() == "P ∧ (Q ∧ R)"
        assert FOL.parse(node.to_unicode_str()) == node

    def test_mixed_level2_parenthesised(self):
        node = Or(And(Atom("P", []), Atom("Q", [])), Atom("R", []))
        assert node.to_unicode_str() == "(P ∧ Q) ∨ R"
        assert FOL.parse(node.to_unicode_str()) == node

    def test_implication_right_assoc(self):
        node = Implies(Atom("P", []), Implies(Atom("Q", []), Atom("R", [])))
        assert node.to_unicode_str() == "P → Q → R"
        assert FOL.parse(node.to_unicode_str()) == node

    def test_implication_left_nested_parenthesised(self):
        node = Implies(Implies(Atom("P", []), Atom("Q", [])), Atom("R", []))
        assert node.to_unicode_str() == "(P → Q) → R"
        assert FOL.parse(node.to_unicode_str()) == node


# ---------------------------------------------------------------------------
# Unknown node type raises
# ---------------------------------------------------------------------------

class TestUnicodeTypeError:
    def test_unknown_node_type_raises(self):
        from unicode_fol_kit.fol._msfl_nodes import _uni
        with pytest.raises(TypeError, match="to_unicode_str"):
            _uni(object())
