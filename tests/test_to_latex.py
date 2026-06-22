"""Tests for Node.to_latex(): exact LaTeX math-mode output."""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol._fol_nodes import Atom, And, Or, Implies, Not

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)
MSFL = MSFLParser(many_sorted=True, fuzzy=True)


class TestLatexFOL:
    @pytest.mark.parametrize("formula, expected", [
        ("P(x)", "P(x)"),
        ("P", "P"),
        ("¬P(x)", "\\lnot P(x)"),
        ("P(x) ∧ Q(x)", "P(x) \\land Q(x)"),
        ("P(x) ∨ Q(x)", "P(x) \\lor Q(x)"),
        ("P(x) ⊕ Q(x)", "P(x) \\oplus Q(x)"),
        ("P(x) → Q(x)", "P(x) \\rightarrow Q(x)"),
        ("P(x) ↔ Q(x)", "P(x) \\leftrightarrow Q(x)"),
        ("∀x P(x)", "\\forall x\\, P(x)"),
        ("∃x P(x)", "\\exists x\\, P(x)"),
        ("∀x (P(x) → Q(x))", "\\forall x\\, (P(x) \\rightarrow Q(x))"),
        ("¬(P(x) ∧ Q(x))", "\\lnot (P(x) \\land Q(x))"),
        ("x ≠ y", "x \\neq y"),
        ("x ≤ y", "x \\leq y"),
        ("x ≥ y", "x \\geq y"),
        ("x = y", "x = y"),
        ("x + y = z", "x + y = z"),
        ("x * y = z", "x \\cdot y = z"),
        ("(P(x) ∧ Q(x)) ∨ R(x)", "(P(x) \\land Q(x)) \\lor R(x)"),
    ])
    def test_latex(self, formula, expected):
        assert FOL.parse(formula).to_latex() == expected


class TestLatexSorted:
    def test_sorted_quantifier(self):
        assert MSFOL.parse("∀x:Human P(x)").to_latex() == "\\forall x{:}\\mathrm{Human}\\, P(x)"

    def test_sorted_constant(self):
        assert MSFOL.parse("P(alice:Human)").to_latex() == "P(alice{:}\\mathrm{Human})"


class TestLatexMSFL:
    def test_strong_conjunction(self):
        assert MSFL.parse("P(x) ⊗ Q(x)").to_latex() == "P(x) \\otimes Q(x)"

    def test_strong_disjunction(self):
        assert MSFL.parse("P(x) ⊕ Q(x)").to_latex() == "P(x) \\oplus Q(x)"


class TestLatexLambda:
    def test_lambda(self):
        assert FOL.parse("λx. P(x)").to_latex() == "\\lambda x.\\, P(x)"

    def test_higher_order_application(self):
        assert FOL.parse("λP. P(x)").to_latex() == "\\lambda P.\\, (P)(x)"


class TestLatexTypeError:
    def test_unknown_node_type_raises(self):
        from unicode_fol_kit.fol._msfl_nodes import _latex
        with pytest.raises(TypeError, match="to_latex"):
            _latex(object())
