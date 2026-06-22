"""Tests for Z3-backed satisfiability, validity, and model extraction."""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.atp import is_satisfiable, is_valid, get_model, formulas_are_equivalent
from unicode_fol_kit.fol._fol_nodes import Not

FOL = MSFLParser()


class TestSatisfiable:
    def test_atom_satisfiable(self):
        assert is_satisfiable(FOL.parse("P")) is True

    def test_contradiction_unsatisfiable(self):
        assert is_satisfiable(FOL.parse("P ∧ ¬P")) is False

    def test_tautology_satisfiable(self):
        assert is_satisfiable(FOL.parse("P ∨ ¬P")) is True


class TestValid:
    def test_excluded_middle_valid(self):
        assert is_valid(FOL.parse("P ∨ ¬P")) is True

    def test_contingent_not_valid(self):
        assert is_valid(FOL.parse("P → Q")) is False

    def test_demorgan_valid(self):
        assert is_valid(FOL.parse("¬(P ∧ Q) ↔ (¬P ∨ ¬Q)")) is True


class TestGetModel:
    def test_model_for_satisfiable(self):
        model = get_model(FOL.parse("P ∧ Q"))
        assert model == {"P": "True", "Q": "True"}

    def test_model_none_for_unsatisfiable(self):
        assert get_model(FOL.parse("P ∧ ¬P")) is None

    def test_model_is_a_witness(self):
        # P ∨ Q is satisfiable; the returned model assigns at least one true.
        model = get_model(FOL.parse("P ∨ Q"))
        assert model is not None
        assert "True" in model.values()


class TestCounterexample:
    def test_counterexample_for_non_equivalence(self):
        # P and Q are not equivalent; ¬(P ↔ Q) is satisfiable and its model
        # is the concrete counterexample distinguishing them.
        f1, f2 = FOL.parse("P"), FOL.parse("Q")
        assert formulas_are_equivalent(f1, f2) is False
        counter = get_model(Not(FOL.parse("P ↔ Q")))
        assert counter is not None
        assert counter.get("P") != counter.get("Q")
