"""Tests for eta_reduce and beta_eta_normalize."""
import pytest
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Function,
    Atom, Not, And, Or, Quantifier, SortedQuantifier,
    LambdaVar, Lambda, Application,
    free_variables, eta_reduce, beta_eta_normalize, ReductionLimitError,
)


# ---------------------------------------------------------------------------
# Basic eta-reduction
# ---------------------------------------------------------------------------

class TestEtaReduceBasic:
    def test_simple_eta_redex(self):
        # λx. f(x) → f
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        assert eta_reduce(Lambda(lx, Application(lf, lx))) == lf

    def test_eta_with_atom_func(self):
        # λx. P()(x) where P is an Atom not containing x → P
        lx = LambdaVar("x")
        P = Atom("P", [])
        assert eta_reduce(Lambda(lx, Application(P, lx))) == P

    def test_cond3_fails_param_free_in_func(self):
        # λx. (x x): arg == param (cond 2 ✓) but x ∈ fv(x) (cond 3 ✗) — must NOT reduce
        lx = LambdaVar("x")
        term = Lambda(lx, Application(lx, lx))
        assert eta_reduce(term) == term

    def test_cond2_fails_arg_is_not_param(self):
        # λx. f(y): arg = y ≠ x (cond 2 ✗) — must NOT reduce
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        lf = LambdaVar("f")
        term = Lambda(lx, Application(lf, ly))
        assert eta_reduce(term) == term

    def test_cond1_fails_body_not_application(self):
        # λx. f: body is a LambdaVar, not an Application (cond 1 ✗) — must NOT reduce
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        term = Lambda(lx, lf)
        assert eta_reduce(term) == term

    def test_cascading_eta(self):
        # λx. (λy. g(y))(x)
        # Inner λy. g(y) → g first; then λx. g(x) → g.
        # Both contractions happen in a single bottom-up pass.
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        lg = LambdaVar("g")
        term = Lambda(lx, Application(Lambda(ly, Application(lg, ly)), lx))
        assert eta_reduce(term) == lg

    def test_quantifier_is_not_eta_redex(self):
        # ∀x. P(x) must NOT reduce — quantifiers have no eta-analogue
        vx = Variable("x")
        term = Quantifier("∀", vx, Atom("P", [vx]))
        assert eta_reduce(term) == term

    def test_eta_inside_quantifier_body(self):
        # ∀z. (λx. f(x))  →  ∀z. f  (eta fires inside the quantifier body)
        vz = Variable("z")
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        inner = Lambda(lx, Application(lf, lx))
        term = Quantifier("∀", vz, inner)
        assert eta_reduce(term) == Quantifier("∀", vz, lf)

    def test_eta_under_and_connective(self):
        # And(λx. f(x), Q)  →  And(f, Q)
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        Q = Atom("Q", [])
        term = And(Lambda(lx, Application(lf, lx)), Q)
        assert eta_reduce(term) == And(lf, Q)

    def test_eta_under_not(self):
        # Not(λx. f(x))  →  Not(f)
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        term = Not(Lambda(lx, Application(lf, lx)))
        assert eta_reduce(term) == Not(lf)

    def test_eta_in_atom_args(self):
        # Atom("P", [λx. f(x)])  →  Atom("P", [f])
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        term = Atom("P", [Lambda(lx, Application(lf, lx))])
        assert eta_reduce(term) == Atom("P", [lf])

    def test_already_normal_variable(self):
        vx = Variable("x")
        assert eta_reduce(vx) is vx

    def test_already_normal_constant(self):
        c = Constant("a")
        assert eta_reduce(c) is c

    def test_already_normal_lambda_variable_body(self):
        # λx. x — body is a LambdaVar, cond 1 fails, no reduction
        lx = LambdaVar("x")
        lam = Lambda(lx, lx)
        assert eta_reduce(lam) == lam

    def test_already_normal_quantifier(self):
        vx = Variable("x")
        q = Quantifier("∀", vx, Atom("P", [vx]))
        assert eta_reduce(q) == q

    def test_sorted_quantifier_not_eta_redex(self):
        vx = Variable("x")
        term = SortedQuantifier("∀", vx, "S", Atom("P", [vx]))
        assert eta_reduce(term) == term

    def test_sorted_quantifier_eta_inside_body(self):
        vz = Variable("z")
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        inner = Lambda(lx, Application(lf, lx))
        term = SortedQuantifier("∀", vz, "S", inner)
        assert eta_reduce(term) == SortedQuantifier("∀", vz, "S", lf)


# ---------------------------------------------------------------------------
# Purity (input never mutated)
# ---------------------------------------------------------------------------

class TestEtaReducePurity:
    def test_original_lambda_unchanged(self):
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        term = Lambda(lx, Application(lf, lx))
        _ = eta_reduce(term)
        assert isinstance(term, Lambda)
        assert term.param == lx
        assert isinstance(term.body, Application)
        assert term.body.func == lf
        assert term.body.arg == lx

    def test_original_application_unchanged(self):
        lx = LambdaVar("x")
        lf = LambdaVar("f")
        outer = Lambda(lx, Application(lf, lx))
        term = Application(outer, Constant("a"))
        _ = eta_reduce(term)
        assert isinstance(term, Application)
        assert term.func == outer


# ---------------------------------------------------------------------------
# beta_eta_normalize
# ---------------------------------------------------------------------------

class TestBetaEtaNormalize:
    def test_beta_then_eta(self):
        # (λg. λx. g(x))(h)  →β→  λx. h(x)  →η→  h
        lg = LambdaVar("g")
        lx = LambdaVar("x")
        lh = LambdaVar("h")
        term = Application(Lambda(lg, Lambda(lx, Application(lg, lx))), lh)
        assert beta_eta_normalize(term) == lh

    def test_eta_exposes_fresh_beta_redex(self):
        # Application(Lambda(x, Application(Lambda(y, M), x)), arg)
        #
        # eta_reduce contracts the func Lambda(x, Application(Lambda(y,M), x))
        # to Lambda(y, M) — because Application(Lambda(y,M), x) has arg==x==param
        # and x ∉ fv(Lambda(y,M)).  This turns the whole term into
        # Application(Lambda(y, M), arg) — a FRESH beta-redex that was not a
        # top-level redex in the original.  This confirms that eta can expose
        # beta-redexes and the alternation loop in beta_eta_normalize is a
        # genuine code path, not merely a safety net for pathological terms.
        lx = LambdaVar("x")
        ly = LambdaVar("y")
        M = Constant("m")
        arg = Constant("a")
        term = Application(
            Lambda(lx, Application(Lambda(ly, M), lx)),
            arg,
        )
        # eta_reduce alone exposes a fresh beta-redex:
        after_eta = eta_reduce(term)
        assert isinstance(after_eta, Application)
        assert isinstance(after_eta.func, Lambda)   # eta produced a beta-redex
        assert after_eta != M                        # the beta-redex is not yet contracted

        # beta_eta_normalize reaches the fully reduced form:
        assert beta_eta_normalize(term) == M

    def test_already_normal_term_unchanged(self):
        # A term with no beta- or eta-redexes should be returned as-is.
        vx = Variable("x")
        term = Quantifier("∀", vx, Atom("P", [vx]))
        assert beta_eta_normalize(term) == term

    def test_only_beta_needed(self):
        # (λx. x)(a) → a; no eta-redex in result
        lx = LambdaVar("x")
        term = Application(Lambda(lx, lx), Constant("a"))
        assert beta_eta_normalize(term) == Constant("a")

    def test_omega_combinator_raises(self):
        lx = LambdaVar("x")
        omega = Lambda(lx, Application(lx, lx))
        with pytest.raises(ReductionLimitError):
            beta_eta_normalize(Application(omega, omega))

    def test_purity(self):
        lg = LambdaVar("g")
        lx = LambdaVar("x")
        lh = LambdaVar("h")
        term = Application(Lambda(lg, Lambda(lx, Application(lg, lx))), lh)
        _ = beta_eta_normalize(term)
        assert isinstance(term, Application)
        assert isinstance(term.func, Lambda)
        assert term.func.param == lg
        assert isinstance(term.arg, LambdaVar)
        assert term.arg == lh
