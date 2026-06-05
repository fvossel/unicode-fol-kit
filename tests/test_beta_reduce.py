"""Tests for beta_reduce, substitute, and ReductionLimitError."""
import pytest
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Function,
    Atom, Not, And, Or, Quantifier, SortedQuantifier,
    LambdaVar, Lambda, Application,
    free_variables, substitute, beta_reduce, ReductionLimitError,
)


# ---------------------------------------------------------------------------
# Basic reduction
# ---------------------------------------------------------------------------

class TestBetaReduceBasic:
    def test_identity_applied_to_constant(self):
        # (λx. x)(a) → a
        lx = LambdaVar("x")
        assert beta_reduce(Application(Lambda(lx, lx), Constant("a"))) == Constant("a")

    def test_constant_body_ignores_arg(self):
        # (λx. c)(a) → c
        lx = LambdaVar("x")
        assert beta_reduce(Application(Lambda(lx, Constant("c")), Constant("a"))) == Constant("c")

    def test_double_application(self):
        # (λf. (λx. f(x)))(λy. y) applied to Constant("a")
        # Step 1: (λf. λx. f(x))(λy.y) → λx. (λy.y)(x)
        # Step 2: λx. x   (well, reduced under lambda → λx. x)
        # Then apply to a → a
        lf = LambdaVar("f")
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        identity = Lambda(ly, ly)
        app_f_x = Application(lf, lx)
        inner = Lambda(lx, app_f_x)
        outer = Lambda(lf, inner)
        full = Application(Application(outer, identity), Constant("a"))
        assert beta_reduce(full) == Constant("a")

    def test_already_normal_variable(self):
        vx = Variable("x")
        assert beta_reduce(vx) is vx

    def test_already_normal_constant(self):
        c = Constant("a")
        assert beta_reduce(c) is c

    def test_already_normal_atom(self):
        atom = Atom("P", [Variable("x")])
        assert beta_reduce(atom) == atom

    def test_already_normal_lambda(self):
        lv = LambdaVar("x")
        lam = Lambda(lv, lv)
        assert beta_reduce(lam) == lam

    def test_already_normal_quantifier(self):
        q = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
        assert beta_reduce(q) == q

    def test_predicate_variable_substitution(self):
        # (λP. And(P, Atom("R", [])))(Atom("Q", [])) → And(Atom("Q",[]), Atom("R",[]))
        lP = LambdaVar("P")
        Q = Atom("Q", [])
        R = Atom("R", [])
        term = Application(Lambda(lP, And(lP, R)), Q)
        assert beta_reduce(term) == And(Q, R)


# ---------------------------------------------------------------------------
# LambdaVar capture avoidance
# ---------------------------------------------------------------------------

class TestBetaReduceLambdaVarCapture:
    def test_simple_capture_avoidance(self):
        # (λx. λy. x)(y_free)  →  λy_0. y_free
        # The binder LambdaVar("y") would capture the free LambdaVar("y") in the arg.
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        term = Application(Lambda(lx, Lambda(ly, lx)), ly)
        result = beta_reduce(term)
        assert isinstance(result, Lambda)
        assert result.param.name != "y"           # alpha-converted away from "y"
        assert LambdaVar("y") in free_variables(result)

    def test_multi_collision_skips_y_0(self):
        # (λx. λy. λy_0. x)(y_free)
        # Alpha-converting the λy binder: avoid = {"y", "y_0", "x"} so fresh skips y_0 → y_1.
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        ly0 = LambdaVar("y_0")
        y_free = LambdaVar("y")
        term = Application(Lambda(lx, Lambda(ly, Lambda(ly0, lx))), y_free)
        result = beta_reduce(term)
        assert isinstance(result, Lambda)
        assert result.param.name not in {"y", "y_0"}  # skipped past both collisions
        assert result.param.name == "y_1"              # landed on y_1
        assert LambdaVar("y") in free_variables(result)


# ---------------------------------------------------------------------------
# Variable (cross-kind) capture avoidance
# ---------------------------------------------------------------------------

class TestBetaReduceVariableCapture:
    def test_quantifier_variable_capture_avoidance(self):
        # (λP. ∀x. App(P, x))(λQ. x_free)
        # Substituting P → (λQ. x_free) into ∀x. App(P, x):
        # Variable("x") is free in the replacement; Quantifier binds Variable("x") → alpha-convert.
        lP = LambdaVar("P")
        lQ = LambdaVar("Q")
        vx = Variable("x")
        replacement = Lambda(lQ, vx)
        term = Application(
            Lambda(lP, Quantifier("∀", vx, Application(lP, vx))),
            replacement,
        )
        result = beta_reduce(term)
        assert isinstance(result, Quantifier)
        assert result.variable.name != "x"              # alpha-converted
        assert Variable("x") in free_variables(result)  # x_free from replacement stays free

    def test_sorted_quantifier_variable_capture_avoidance(self):
        # Same as above but with SortedQuantifier.
        lP = LambdaVar("P")
        lQ = LambdaVar("Q")
        vx = Variable("x")
        replacement = Lambda(lQ, vx)
        term = Application(
            Lambda(lP, SortedQuantifier("∀", vx, "S", Application(lP, vx))),
            replacement,
        )
        result = beta_reduce(term)
        assert isinstance(result, SortedQuantifier)
        assert result.variable.name != "x"
        assert Variable("x") in free_variables(result)

    def test_logical_variable_unchanged_during_lambda_subst(self):
        # Substituting a LambdaVar never touches a logical Variable with the same name.
        # (λP. Atom("Q", [Variable("x")]))(Constant("a")) → Atom("Q", [Variable("x")])
        lP = LambdaVar("P")
        vx = Variable("x")
        term = Application(Lambda(lP, Atom("Q", [vx])), Constant("a"))
        result = beta_reduce(term)
        assert result == Atom("Q", [vx])


# ---------------------------------------------------------------------------
# Reduction in subterms (under binders and connectives)
# ---------------------------------------------------------------------------

class TestBetaReduceInSubterms:
    def test_reduction_under_lambda(self):
        # λz. (λx. x)(a)  →  λz. a
        lz = LambdaVar("z")
        lx = LambdaVar("x")
        term = Lambda(lz, Application(Lambda(lx, lx), Constant("a")))
        assert beta_reduce(term) == Lambda(lz, Constant("a"))

    def test_reduction_in_quantifier_formula(self):
        # ∀y. App(λx. x, a)  →  ∀y. a
        vy = Variable("y")
        lx = LambdaVar("x")
        term = Quantifier("∀", vy, Application(Lambda(lx, lx), Constant("a")))
        assert beta_reduce(term) == Quantifier("∀", vy, Constant("a"))

    def test_reduction_in_sorted_quantifier(self):
        vy = Variable("y")
        lx = LambdaVar("x")
        term = SortedQuantifier("∃", vy, "S", Application(Lambda(lx, lx), Constant("a")))
        assert beta_reduce(term) == SortedQuantifier("∃", vy, "S", Constant("a"))

    def test_reduction_in_and_connective(self):
        # And(App(λx. x, a), App(λx. x, b))  →  And(a, b)
        lx = LambdaVar("x")
        term = And(
            Application(Lambda(lx, lx), Constant("a")),
            Application(Lambda(lx, lx), Constant("b")),
        )
        assert beta_reduce(term) == And(Constant("a"), Constant("b"))

    def test_reduction_in_not(self):
        lx = LambdaVar("x")
        term = Not(Application(Lambda(lx, lx), Atom("P", [])))
        assert beta_reduce(term) == Not(Atom("P", []))

    def test_reduction_in_atom_args(self):
        # Atom args can technically be Applications if someone builds the AST directly.
        # Atom("P", [App(λx. x, Variable("y"))])  →  Atom("P", [Variable("y")])
        lx = LambdaVar("x")
        vy = Variable("y")
        term = Atom("P", [Application(Lambda(lx, lx), vy)])
        assert beta_reduce(term) == Atom("P", [vy])

    def test_reduction_in_function_args(self):
        lx = LambdaVar("x")
        vy = Variable("y")
        term = Function("f", [Application(Lambda(lx, lx), vy)])
        assert beta_reduce(term) == Function("f", [vy])


# ---------------------------------------------------------------------------
# Shadowing
# ---------------------------------------------------------------------------

class TestBetaReduceShadowing:
    def test_inner_lambda_shadows_substitution(self):
        # (λx. λx. x)(a)
        # Substitute LambdaVar("x") → Constant("a") in Lambda(LambdaVar("x"), LambdaVar("x")).
        # The inner binder re-binds x, so substitution stops.  Result: λx. x (the identity).
        lx = LambdaVar("x")
        term = Application(Lambda(lx, Lambda(lx, lx)), Constant("a"))
        result = beta_reduce(term)
        assert result == Lambda(lx, lx)

    def test_inner_quantifier_does_not_shadow_lambda_subst(self):
        # (λP. ∀x. P)(Atom("Q", []))  →  ∀x. Atom("Q",[])
        # Quantifier binds Variable("x"), not LambdaVar("P"), so P is still substituted.
        lP = LambdaVar("P")
        vx = Variable("x")
        Q = Atom("Q", [])
        term = Application(Lambda(lP, Quantifier("∀", vx, lP)), Q)
        assert beta_reduce(term) == Quantifier("∀", vx, Q)


# ---------------------------------------------------------------------------
# Purity (input never mutated)
# ---------------------------------------------------------------------------

class TestBetaReducePurity:
    def test_original_application_unchanged(self):
        lx = LambdaVar("x")
        term = Application(Lambda(lx, lx), Constant("a"))
        _ = beta_reduce(term)
        assert isinstance(term, Application)
        assert isinstance(term.func, Lambda)
        assert term.func.param == lx
        assert term.arg == Constant("a")

    def test_original_lambda_unchanged(self):
        lx = LambdaVar("x")
        lam = Lambda(lx, lx)
        _ = beta_reduce(Application(lam, Constant("a")))
        assert lam.param == lx
        assert lam.body == lx


# ---------------------------------------------------------------------------
# ReductionLimitError
# ---------------------------------------------------------------------------

class TestReductionLimitError:
    def _omega(self):
        lx = LambdaVar("x")
        return Lambda(lx, Application(lx, lx))

    def test_omega_combinator_raises(self):
        # Ω = (λx. x x)(λx. x x) — diverges
        omega = self._omega()
        with pytest.raises(ReductionLimitError, match="beta-reduction exceeded"):
            beta_reduce(Application(omega, omega))

    def test_error_message_contains_limit(self):
        omega = self._omega()
        with pytest.raises(ReductionLimitError) as exc_info:
            beta_reduce(Application(omega, omega))
        assert "10000" in str(exc_info.value)

    def test_error_message_contains_explanation(self):
        omega = self._omega()
        with pytest.raises(ReductionLimitError) as exc_info:
            beta_reduce(Application(omega, omega))
        assert "normalizing" in str(exc_info.value)


# ---------------------------------------------------------------------------
# substitute (public API)
# ---------------------------------------------------------------------------

class TestSubstitute:
    def test_leaf_match(self):
        lx = LambdaVar("x")
        assert substitute(lx, lx, Constant("a")) == Constant("a")

    def test_leaf_no_match(self):
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        assert substitute(ly, lx, Constant("a")) == ly

    def test_logical_variable_not_affected(self):
        # Substituting LambdaVar("x") never touches Variable("x").
        vx = Variable("x")
        lx = LambdaVar("x")
        assert substitute(vx, lx, Constant("a")) == vx

    def test_lambda_shadowing_stops_substitution(self):
        # substitute in (λx. x) for target LambdaVar("x") → unchanged (shadowed)
        lx = LambdaVar("x")
        lam = Lambda(lx, lx)
        assert substitute(lam, lx, Constant("a")) == lam

    def test_substitution_into_atom_args(self):
        lx = LambdaVar("x")
        atom = Atom("P", [lx, Variable("y")])
        result = substitute(atom, lx, Constant("a"))
        assert result == Atom("P", [Constant("a"), Variable("y")])

    def test_substitution_into_or(self):
        lP = LambdaVar("P")
        term = Or(lP, Atom("Q", []))
        result = substitute(term, lP, Atom("R", []))
        assert result == Or(Atom("R", []), Atom("Q", []))

    def test_purity(self):
        lx = LambdaVar("x")
        body = Application(lx, Variable("y"))
        lam = Lambda(lx, body)
        _ = substitute(lam, LambdaVar("z"), Constant("a"))
        assert lam.param == lx
        assert lam.body == body
