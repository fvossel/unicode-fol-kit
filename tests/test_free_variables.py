"""Tests for free_variables over all node types."""
import pytest
from unicode_fol_kit.fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    free_variables,
)

_x = Variable("x")
_y = Variable("y")
_Px = LambdaVar("P")
_Py = LambdaVar("Q")


# ---------------------------------------------------------------------------
# Leaves
# ---------------------------------------------------------------------------

class TestFreeVariablesLeaves:
    def test_variable(self):
        assert free_variables(Variable("x")) == {Variable("x")}

    def test_lambdavar(self):
        assert free_variables(LambdaVar("P")) == {LambdaVar("P")}

    def test_constant(self):
        assert free_variables(Constant("a")) == set()

    def test_number(self):
        assert free_variables(Number(3)) == set()

    def test_sorted_constant(self):
        assert free_variables(SortedConstant("a", "S")) == set()


# ---------------------------------------------------------------------------
# Atom / Function
# ---------------------------------------------------------------------------

class TestFreeVariablesAtomFunction:
    def test_atom_two_distinct_args(self):
        assert free_variables(Atom("P", [_x, _y])) == {Variable("x"), Variable("y")}

    def test_atom_repeated_arg_deduplicates(self):
        assert free_variables(Atom("P", [_x, _x])) == {Variable("x")}

    def test_atom_constant_arg(self):
        assert free_variables(Atom("P", [Constant("a")])) == set()

    def test_function_mixed_args(self):
        assert free_variables(Function("f", [_x, Constant("a")])) == {Variable("x")}

    def test_atom_zero_arity(self):
        assert free_variables(Atom("P", [])) == set()


# ---------------------------------------------------------------------------
# Connectives
# ---------------------------------------------------------------------------

class TestFreeVariablesConnectives:
    def test_not(self):
        assert free_variables(Not(Atom("P", [_x]))) == {Variable("x")}

    def test_and(self):
        assert free_variables(And(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_or(self):
        assert free_variables(Or(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_xor(self):
        assert free_variables(Xor(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_implies(self):
        assert free_variables(Implies(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_iff(self):
        assert free_variables(Iff(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_luk_negation(self):
        assert free_variables(LukNegation(Atom("P", [_x]))) == {Variable("x")}

    def test_weak_conjunction(self):
        assert free_variables(WeakConjunction(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_weak_disjunction(self):
        assert free_variables(WeakDisjunction(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_strong_conjunction(self):
        assert free_variables(StrongConjunction(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_strong_disjunction(self):
        assert free_variables(StrongDisjunction(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_luk_implication(self):
        assert free_variables(LukImplication(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}

    def test_luk_equivalence(self):
        assert free_variables(LukEquivalence(Atom("P", [_x]), Atom("Q", [_y]))) == {Variable("x"), Variable("y")}


# ---------------------------------------------------------------------------
# Binders
# ---------------------------------------------------------------------------

class TestFreeVariablesBinders:
    def test_lambda_binds_its_param(self):
        lv = LambdaVar("x")
        assert free_variables(Lambda(lv, lv)) == set()

    def test_lambda_leaves_other_lambdavar_free(self):
        assert free_variables(Lambda(LambdaVar("x"), LambdaVar("y"))) == {LambdaVar("y")}

    def test_quantifier_binds_its_variable(self):
        assert free_variables(Quantifier("∀", _x, Atom("P", [_x]))) == set()

    def test_quantifier_leaves_other_var_free(self):
        assert free_variables(Quantifier("∀", _x, Atom("P", [_x, _y]))) == {Variable("y")}

    def test_sorted_quantifier_binds_its_variable(self):
        assert free_variables(SortedQuantifier("∀", _x, "S", Atom("P", [_x]))) == set()

    def test_sorted_quantifier_leaves_other_var_free(self):
        assert free_variables(SortedQuantifier("∀", _x, "S", Atom("P", [_x, _y]))) == {Variable("y")}


# ---------------------------------------------------------------------------
# Mixed kinds: the core correctness tests
# ---------------------------------------------------------------------------

class TestFreeVariablesMixedKinds:
    def test_lambda_does_not_remove_logical_variable(self):
        # Lambda binds LambdaVar("x"); logical Variable("x") stays free
        lv = LambdaVar("x")
        lx = Variable("x")
        node = Lambda(lv, Atom("P", [lx]))
        assert free_variables(node) == {Variable("x")}

    def test_quantifier_does_not_remove_lambdavar(self):
        # Quantifier binds Variable("x"); LambdaVar("P") stays free
        node = Quantifier("∀", _x, Application(LambdaVar("P"), _x))
        assert free_variables(node) == {LambdaVar("P")}

    def test_both_kinds_coexist_in_application(self):
        assert free_variables(Application(LambdaVar("P"), _x)) == {LambdaVar("P"), Variable("x")}

    def test_same_name_different_kinds_both_free(self):
        # Variable("x") and LambdaVar("x") are distinct objects; both should appear
        lx = LambdaVar("x")
        vx = Variable("x")
        node = Application(lx, vx)
        result = free_variables(node)
        assert LambdaVar("x") in result
        assert Variable("x") in result
        assert len(result) == 2

    def test_lambda_over_x_does_not_remove_variable_x(self):
        # λ(LambdaVar x). Application(LambdaVar x, Variable x)
        # Lambda removes LambdaVar("x") but NOT Variable("x")
        lv = LambdaVar("x")
        vx = Variable("x")
        node = Lambda(lv, Application(lv, vx))
        assert free_variables(node) == {Variable("x")}


# ---------------------------------------------------------------------------
# Nested and shadowing
# ---------------------------------------------------------------------------

class TestFreeVariablesNested:
    def test_classic_forall_no_free(self):
        # ∀x. P(x) — x is bound
        assert free_variables(Quantifier("∀", _x, Atom("P", [_x]))) == set()

    def test_classic_forall_with_free_y(self):
        # ∀x. P(x, y) — y is free
        assert free_variables(Quantifier("∀", _x, Atom("P", [_x, _y]))) == {Variable("y")}

    def test_nested_quantifiers_no_free(self):
        inner = Quantifier("∀", _y, Atom("P", [_x, _y]))
        outer = Quantifier("∀", _x, inner)
        assert free_variables(outer) == set()

    def test_lambda_shadowing(self):
        # λx. (λx. x)(x)
        # Inner λx. x  → free set = {} (x bound)
        # Inner arg x  → free set = {LambdaVar("x")}
        # Application  → free set = {LambdaVar("x")}
        # Outer λx     → free set = {LambdaVar("x")} - {LambdaVar("x")} = {}
        lv = LambdaVar("x")
        inner = Lambda(lv, lv)
        app = Application(inner, lv)
        outer = Lambda(lv, app)
        assert free_variables(outer) == set()

    def test_redex_free_variables(self):
        # (λx. P(x))(a)  — Variable x is free in the body; Constant a contributes nothing
        lv = LambdaVar("x")
        vx = Variable("x")
        redex = Application(Lambda(lv, Atom("P", [vx])), Constant("a"))
        assert free_variables(redex) == {Variable("x")}

    def test_closed_redex(self):
        # (λx. x)(a)  — body is LambdaVar x, which Lambda binds; Constant a contributes nothing
        lv = LambdaVar("x")
        redex = Application(Lambda(lv, lv), Constant("a"))
        assert free_variables(redex) == set()


# ---------------------------------------------------------------------------
# TypeError for unknown node type
# ---------------------------------------------------------------------------

class TestFreeVariablesTypeError:
    def test_unknown_type_raises(self):
        class Alien(Node):
            pass
        with pytest.raises(TypeError, match="unknown node type"):
            free_variables(Alien())
