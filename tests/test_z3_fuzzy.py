"""Tests for Łukasiewicz fuzzy SAT/validity via Z3 reals (z3_fuzzy.py).

Hand-checkable oracles use the Łukasiewicz semantics over [0, 1]:
  ¬a = 1−a; weak ∧ = min; weak ∨ = max; ⊗ = max(0, a+b−1);
  ⊕ = min(1, a+b); → = min(1, 1−a+b); ↔ = 1−|a−b|.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.atp.z3_fuzzy import (
    fuzzy_is_satisfiable,
    fuzzy_is_valid,
    fuzzy_get_model,
    degree_expr,
)

P = MSFLParser(fuzzy=True)


# ---------------------------------------------------------------------------
# Validity
# ---------------------------------------------------------------------------

def test_strong_excluded_middle_is_valid():
    # P ⊕ ¬P = min(1, p + (1-p)) = min(1, 1) = 1 for all p, so valid.
    assert fuzzy_is_valid(P.parse("P ⊕ ¬P")) is True


def test_self_implication_is_valid():
    # P → P = min(1, 1 - p + p) = 1 for all p, so valid.
    assert fuzzy_is_valid(P.parse("P → P")) is True


def test_weak_excluded_middle_is_not_valid():
    # P ∨ ¬P = max(p, 1-p); at p = 0.5 this is 0.5 < 1, so NOT valid.
    assert fuzzy_is_valid(P.parse("P ∨ ¬P")) is False


def test_weak_contradiction_is_not_valid():
    # P ∧ ¬P = min(p, 1-p) <= 0.5 < 1, so NOT valid.
    assert fuzzy_is_valid(P.parse("P ∧ ¬P")) is False


def test_equivalence_reflexive_is_valid():
    # P ↔ P = 1 - |p - p| = 1, so valid.
    assert fuzzy_is_valid(P.parse("P ↔ P")) is True


# ---------------------------------------------------------------------------
# Strong conjunction thresholds
# ---------------------------------------------------------------------------

def test_strong_contradiction_unsat_at_half():
    # P ⊗ ¬P = max(0, p + (1-p) - 1) = max(0, 0) = 0 for all p.
    # Degree is always 0, so it never reaches threshold 0.5.
    assert fuzzy_is_satisfiable(P.parse("P ⊗ ¬P"), threshold=0.5) is False


def test_strong_contradiction_sat_at_zero():
    # Degree 0 >= threshold 0.0, so satisfiable at threshold 0.0.
    assert fuzzy_is_satisfiable(P.parse("P ⊗ ¬P"), threshold=0.0) is True


def test_strong_contradiction_no_model_at_half():
    assert fuzzy_get_model(P.parse("P ⊗ ¬P"), threshold=0.5) is None


# ---------------------------------------------------------------------------
# Weak conjunction max degree is 0.5
# ---------------------------------------------------------------------------

def test_weak_contradiction_sat_at_half():
    # max degree of min(p, 1-p) is 0.5, reached at p = 0.5; sat at threshold 0.5.
    assert fuzzy_is_satisfiable(P.parse("P ∧ ¬P"), threshold=0.5) is True


def test_weak_contradiction_unsat_strictly_above_half():
    # No valuation exceeds 0.5, so strict > 0.5 is unsatisfiable.
    assert fuzzy_is_satisfiable(P.parse("P ∧ ¬P"), threshold=0.5, strict=True) is False


def test_weak_contradiction_default_threshold_unsat():
    # Default threshold is 1.0; max degree 0.5 < 1.0, so not satisfiable.
    assert fuzzy_is_satisfiable(P.parse("P ∧ ¬P")) is False


def test_weak_contradiction_model_degrees_in_unit_interval():
    model = fuzzy_get_model(P.parse("P ∧ ¬P"), threshold=0.5)
    assert model is not None
    # Every entry (including the 'degree') must lie in [0, 1].
    for key, value in model.items():
        assert 0.0 <= value <= 1.0, f"{key}={value} out of [0,1]"
    # The reached degree must meet the threshold.
    assert model["degree"] >= 0.5
    # The only ground atom is P; at degree 0.5 it must sit at 0.5.
    assert model["P"] == pytest.approx(0.5)
    assert model["degree"] == pytest.approx(0.5)


# ---------------------------------------------------------------------------
# Satisfiability of a plainly true formula and a degree check
# ---------------------------------------------------------------------------

def test_strong_disjunction_model_reaches_one():
    model = fuzzy_get_model(P.parse("P ⊕ ¬P"), threshold=1.0)
    assert model is not None
    assert model["degree"] == pytest.approx(1.0)
    assert 0.0 <= model["P"] <= 1.0


def test_implication_degree_oracle():
    # ¬P → Q with P=1, Q=0: ¬P=0, so 0 → 0 = min(1, 1-0+0) = 1.  Always >= 1?
    # Degree = min(1, 1 - (1-p) + q) = min(1, p + q). Max is 1 (e.g. p=q=1),
    # so satisfiable at threshold 1.0.
    f = P.parse("¬P → Q")
    assert fuzzy_is_satisfiable(f, threshold=1.0) is True
    model = fuzzy_get_model(f, threshold=1.0)
    assert model is not None
    assert model["degree"] == pytest.approx(1.0)


def test_implication_below_threshold_unsat():
    # P → Q = min(1, 1 - p + q). To force this below, e.g. threshold 1.5 is
    # impossible (degree capped at 1). strict > 1.0 is unsatisfiable.
    f = P.parse("P → Q")
    assert fuzzy_is_satisfiable(f, threshold=1.0, strict=True) is False


# ---------------------------------------------------------------------------
# Equivalence oracle
# ---------------------------------------------------------------------------

def test_equivalence_max_degree_one():
    # P ↔ Q = 1 - |p - q|; equals 1 when p == q, so sat at threshold 1.0.
    assert fuzzy_is_satisfiable(P.parse("P ↔ Q"), threshold=1.0) is True


def test_equivalence_not_valid():
    # With p != q the degree drops below 1, so not valid.
    assert fuzzy_is_valid(P.parse("P ↔ Q")) is False


# ---------------------------------------------------------------------------
# Shared atoms key by to_unicode_str
# ---------------------------------------------------------------------------

def test_repeated_atom_shares_one_variable():
    # P(a) appears twice; only one Z3 variable should be created for it.
    expr, constraints, atom_vars = degree_expr(P.parse("P(a) ⊗ P(a)"))
    assert set(atom_vars.keys()) == {"P(a)"}
    # One atom -> exactly two unit-interval bounds (0 <= v and v <= 1).
    assert len(constraints) == 2


def test_distinct_atoms_get_distinct_variables():
    expr, constraints, atom_vars = degree_expr(P.parse("P(a) ⊗ P(b)"))
    assert set(atom_vars.keys()) == {"P(a)", "P(b)"}
    assert len(constraints) == 4


# ---------------------------------------------------------------------------
# Quantifiers are rejected in v1
# ---------------------------------------------------------------------------

def test_quantifier_raises_not_implemented_validity():
    f = P.parse("∀x P(x)")
    with pytest.raises(NotImplementedError):
        fuzzy_is_valid(f)


def test_quantifier_raises_not_implemented_sat():
    f = P.parse("∃x P(x)")
    with pytest.raises(NotImplementedError):
        fuzzy_is_satisfiable(f)


def test_quantifier_raises_not_implemented_model():
    f = P.parse("∀x P(x)")
    with pytest.raises(NotImplementedError):
        fuzzy_get_model(f)


# ---------------------------------------------------------------------------
# Reviewer-added edge cases (independent oracles)
# ---------------------------------------------------------------------------

def test_double_negation_equivalence_is_valid():
    # ¬¬P = 1 - (1 - p) = p, so (¬¬P) ↔ P = 1 - |p - p| = 1 for all p: valid.
    assert fuzzy_is_valid(P.parse("(¬¬P) ↔ P")) is True


def test_strong_contradiction_negation_is_valid():
    # P ⊗ ¬P = max(0, p + (1-p) - 1) = 0, and ¬0 = 1 for all p: valid.
    assert fuzzy_is_valid(P.parse("¬(P ⊗ ¬P)")) is True


def test_strong_contradiction_strict_above_zero_unsat():
    # Degree of P ⊗ ¬P is exactly 0 for every valuation, so it can never be
    # strictly greater than 0: strict threshold > 0.0 is unsatisfiable.
    assert fuzzy_is_satisfiable(
        P.parse("P ⊗ ¬P"), threshold=0.0, strict=True
    ) is False


def test_strong_self_conjunction_threshold_oracle():
    # P ⊗ P = max(0, 2p - 1). Reaching 0.5 needs p >= 0.75 (feasible), and 1.0
    # needs p = 1 (feasible), but it is 0 at p = 0 so it is NOT valid.
    f = P.parse("P ⊗ P")
    assert fuzzy_is_satisfiable(f, threshold=0.5) is True
    assert fuzzy_is_satisfiable(f, threshold=1.0) is True
    assert fuzzy_is_valid(f) is False


def test_weak_vs_strong_disjunction_at_half():
    # At the natural witness p = 0.5: weak P ∨ ¬P = max(0.5, 0.5) = 0.5, while
    # strong P ⊕ ¬P = min(1, 1) = 1. Weak version cannot exceed 0.5 here, so a
    # strict threshold just above 0.5 separates them only for the weak case.
    assert fuzzy_is_satisfiable(P.parse("P ∨ ¬P"), threshold=1.0) is True  # p=1
    assert fuzzy_is_satisfiable(P.parse("P ∨ ¬P"), threshold=0.5, strict=True) is True
    # min(p, 1-p)-style is irrelevant here; the strong ⊕ is always 1:
    assert fuzzy_is_valid(P.parse("P ⊕ ¬P")) is True


def test_threshold_above_one_is_never_satisfiable():
    # Every Łukasiewicz degree is clamped into [0, 1], so no formula can reach a
    # threshold above 1.0.
    assert fuzzy_is_satisfiable(P.parse("P ⊕ ¬P"), threshold=1.5) is False
    assert fuzzy_get_model(P.parse("P ⊕ ¬P"), threshold=1.5) is None


def test_degree_expr_returns_documented_triple():
    # degree_expr returns (expr, constraints, atom_vars); atom_vars is keyed by
    # to_unicode_str and constraints are two bounds per distinct atom.
    expr, constraints, atom_vars = degree_expr(P.parse("P → (Q ⊗ P)"))
    assert set(atom_vars.keys()) == {"P", "Q"}
    assert len(constraints) == 4
    # expr must be a usable Z3 expression (has a sort), not a bare Python value.
    assert hasattr(expr, "sort")


def test_implication_intermediate_degree_model():
    # P → Q with the threshold 0.5 is reachable (e.g. p=0.5,q=0), and the
    # returned model's degree must actually meet the threshold and lie in [0,1].
    f = P.parse("P → Q")
    model = fuzzy_get_model(f, threshold=0.5)
    assert model is not None
    assert model["degree"] >= 0.5
    for value in model.values():
        assert 0.0 <= value <= 1.0
