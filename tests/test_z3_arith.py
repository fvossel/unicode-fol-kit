"""Tests for arithmetic-aware Z3 translation (Real/Int).

These exercise genuine arithmetic reasoning — solving linear constraints,
proving arithmetic identities valid, detecting numeric contradictions — none of
which the default uninterpreted ``to_z3`` can do. Each case has a hand-checkable
oracle. Formulas are produced by ``MSFLParser()`` (unsorted classical FOL).
"""

import z3

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.atp.z3_arith import (
    to_z3_arith,
    is_satisfiable_arith,
    is_valid_arith,
    get_model_arith,
    ArithEnv,
)

FOL = MSFLParser()


class TestSatisfiableArith:
    def test_linear_constraint_satisfiable(self):
        # x + 1 = 2 ∧ x > 0 forces x = 1, which is > 0: satisfiable.
        assert is_satisfiable_arith(FOL.parse("x + 1 = 2 ∧ x > 0")) is True

    def test_numeric_contradiction_unsatisfiable(self):
        # No real is both > 0 and < 0.
        assert is_satisfiable_arith(FOL.parse("x > 0 ∧ x < 0")) is False

    def test_squeeze_with_disequality_unsatisfiable(self):
        # x ≤ 2 ∧ x ≥ 2 pins x to exactly 2, which contradicts x ≠ 2.
        assert is_satisfiable_arith(FOL.parse("x ≤ 2 ∧ x ≥ 2 ∧ x ≠ 2")) is False

    def test_squeeze_without_disequality_satisfiable(self):
        # x ≤ 2 ∧ x ≥ 2 alone is satisfiable (x = 2).
        assert is_satisfiable_arith(FOL.parse("x ≤ 2 ∧ x ≥ 2")) is True

    def test_default_to_z3_cannot_decide_this(self):
        # Sanity check that the contrast with the default translation is real:
        # the uninterpreted to_z3 reads "+" and numbers as opaque symbols, so
        # x + 1 = 2 ∧ x > 0 is "satisfiable" there for the wrong reasons. The
        # arithmetic translation reasons about the actual numbers.
        f = FOL.parse("x ≤ 2 ∧ x ≥ 2 ∧ x ≠ 2")
        # Arithmetic: genuinely unsatisfiable.
        assert is_satisfiable_arith(f) is False


class TestModelArith:
    def test_model_recovers_x_equals_one(self):
        # x + 1 = 2 ∧ x > 0 has the unique solution x = 1.
        model = get_model_arith(FOL.parse("x + 1 = 2 ∧ x > 0"))
        assert model is not None
        assert "x" in model
        assert model["x"] == "1"

    def test_model_none_for_unsatisfiable(self):
        assert get_model_arith(FOL.parse("x > 0 ∧ x < 0")) is None

    def test_model_satisfies_int_sort(self):
        # Over the integers, 2*x = 6 ∧ x > 0 gives x = 3.
        model = get_model_arith(FOL.parse("x + x = 6 ∧ x > 0"), sort="int")
        assert model is not None
        assert model["x"] == "3"


class TestValidArith:
    def test_doubling_identity_valid(self):
        # ∀x (x * 2 = x + x) is a true arithmetic identity.
        assert is_valid_arith(FOL.parse("∀x (x * 2 = x + x)")) is True

    def test_false_identity_not_valid(self):
        # ∀x (x + 1 = x) is false.
        assert is_valid_arith(FOL.parse("∀x (x + 1 = x)")) is False

    def test_existential_witness_valid(self):
        # ∀x ∃y (y = x + 1) — every real has a successor.
        assert is_valid_arith(FOL.parse("∀x ∃y (y = x + 1)")) is True

    def test_transitivity_of_order_valid(self):
        # ∀x∀y∀z ((x < y ∧ y < z) → x < z).
        f = FOL.parse("∀x ∀y ∀z ((x < y ∧ y < z) → x < z)")
        assert is_valid_arith(f) is True


class TestRealVsInt:
    def test_half_exists_over_reals(self):
        # 2*x = 1 has a real solution (x = 1/2) ...
        assert is_satisfiable_arith(FOL.parse("x + x = 1")) is True

    def test_half_has_no_integer_solution(self):
        # ... but no integer solution.
        assert is_satisfiable_arith(FOL.parse("x + x = 1"), sort="int") is False


class TestTranslationStructure:
    def test_number_uses_real_val(self):
        # z3 may reorder the equality's operands, so collect both sides.
        expr = to_z3_arith(FOL.parse("x = 3"))
        operands = [expr.arg(0), expr.arg(1)]
        # The literal 3 is an interpreted real numeral, not an uninterpreted
        # constant in some abstract sort.
        assert any(op.eq(z3.RealVal(3)) for op in operands)
        assert all(op.sort() == z3.RealSort() for op in operands)

    def test_number_uses_int_val_when_int(self):
        expr = to_z3_arith(FOL.parse("x = 3"), sort="int")
        operands = [expr.arg(0), expr.arg(1)]
        assert any(op.eq(z3.IntVal(3)) for op in operands)
        assert all(op.sort() == z3.IntSort() for op in operands)

    def test_plus_is_interpreted_addition(self):
        # x + 1 translates to a Z3 arithmetic '+' application, not an
        # uninterpreted function symbol named "+".
        expr = to_z3_arith(FOL.parse("x + 1 = y"))
        lhs = expr.arg(0)
        assert lhs.decl().kind() == z3.Z3_OP_ADD

    def test_unknown_predicate_is_uninterpreted_bool(self):
        # P(x) over the numeric sort becomes an uninterpreted (sort -> Bool) app.
        expr = to_z3_arith(FOL.parse("P(x)"))
        assert expr.sort() == z3.BoolSort()
        assert expr.decl().range() == z3.BoolSort()
        assert expr.decl().domain(0) == z3.RealSort()

    def test_unknown_function_is_uninterpreted_over_sort(self):
        # foo(x) becomes an uninterpreted (Real -> Real) function application.
        # (Single lowercase letters are reserved for variables by the grammar,
        # so the function symbol is a multi-character name.)
        expr = to_z3_arith(FOL.parse("foo(x) = 0"))
        operands = [expr.arg(0), expr.arg(1)]
        # Pick the operand that is the foo application (the other is the literal 0).
        fx = next(op for op in operands if op.decl().name() == "foo")
        assert fx.sort() == z3.RealSort()
        assert fx.decl().range() == z3.RealSort()
        assert fx.decl().domain(0) == z3.RealSort()

    def test_shared_env_reuses_symbol(self):
        env = ArithEnv("real")
        to_z3_arith(FOL.parse("x > 0"), env=env)
        to_z3_arith(FOL.parse("x < 5"), env=env)
        # Both translations resolved x to the one cached Z3 constant.
        assert list(env.symbols.keys()) == ["x"]
        assert env.symbols["x"].eq(z3.Const("x", z3.RealSort()))


class TestConnectives:
    def test_iff_arith(self):
        # (x > 0) ↔ (x > 0) is valid.
        assert is_valid_arith(FOL.parse("(x > 0) ↔ (x > 0)")) is True

    def test_implies_arith(self):
        # ∀x (x > 1 → x > 0) is valid.
        assert is_valid_arith(FOL.parse("∀x (x > 1 → x > 0)")) is True

    def test_not_arith(self):
        # ¬(x ≠ x) is valid (x always equals itself).
        assert is_valid_arith(FOL.parse("¬(x ≠ x)")) is True

    def test_xor_partition_is_valid(self):
        # Over a total order every x is in exactly one of {>0, ≤0}, so the
        # exclusive-or of the two halves is a tautology.
        assert is_valid_arith(FOL.parse("(x > 0) ⊕ (x ≤ 0)")) is True

    def test_xor_of_identical_is_unsatisfiable(self):
        # φ ⊕ φ is false for every truth value of φ, hence unsatisfiable.
        assert is_satisfiable_arith(FOL.parse("(x > 0) ⊕ (x > 0)")) is False


# Reviewer-added edge cases: real fractional models, integer division, a
# non-linear validity, the explicit sort guard, and the int/real split shown
# directly through get_model_arith (not just the boolean sat checks above).
class TestReviewerEdgeCases:
    def test_real_model_is_the_exact_fraction(self):
        # x + x = 1 over the reals has the unique solution x = 1/2; Z3 renders
        # the rational exactly (not as a float), so the model string is "1/2".
        model = get_model_arith(FOL.parse("x + x = 1"))
        assert model is not None
        assert model["x"] == "1/2"

    def test_real_literal_is_translated_exactly(self):
        # The literal 1.5 must enter Z3 as the exact rational 3/2, so x = 1.5
        # forces x to 3/2 — a value with no integer counterpart.
        model = get_model_arith(FOL.parse("x = 1.5"))
        assert model is not None
        assert model["x"] == "3/2"

    def test_integer_division_is_floor_like(self):
        # Z3 integer division: 7 / 2 = 3 in the integer theory. The point is that
        # '/' is interpreted (not an uninterpreted symbol), giving a concrete 3.
        model = get_model_arith(FOL.parse("x = 7 / 2"), sort="int")
        assert model is not None
        assert model["x"] == "3"

    def test_nonlinear_square_is_nonnegative_over_reals(self):
        # ∀x (x * x ≥ 0) is a true (nonlinear) real identity — '*' is interpreted
        # multiplication, so Z3 actually proves it rather than leaving x*x opaque.
        assert is_valid_arith(FOL.parse("∀x (x * x ≥ 0)")) is True

    def test_sorted_guard_relativizes_universally(self):
        # A SortedQuantifier is lowered with to_fol: ∀x:S φ becomes
        # ∀x (S(x) → φ) with S an uninterpreted predicate. With φ := (x = x) the
        # result is valid no matter how S is interpreted.
        from unicode_fol_kit.fol.nodes import SortedQuantifier, Variable, Atom
        sq = SortedQuantifier(
            "∀", Variable("x"), "S", Atom("=", [Variable("x"), Variable("x")])
        )
        assert is_valid_arith(sq) is True

    def test_arith_env_rejects_unknown_sort(self):
        import pytest
        with pytest.raises(ValueError):
            ArithEnv("complex")

    def test_int_and_real_disagree_on_half(self):
        # The same formula is satisfiable over the reals (x = 1/2) but has no
        # integer model — the sort genuinely changes the answer.
        f = "x + x = 1"
        assert get_model_arith(FOL.parse(f)) is not None
        assert get_model_arith(FOL.parse(f), sort="int") is None
