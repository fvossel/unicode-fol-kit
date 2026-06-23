# -*- coding: utf-8 -*-
"""Tests for lambda_tools: has_lambdas, eliminate_lambdas, beta_reduce_step, reduce_trace."""
import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Function,
    Atom, Not, And, Quantifier,
    SortedQuantifier,
    WeakConjunction, LukImplication,
    LambdaVar, Lambda, Application,
    beta_reduce, ReductionLimitError,
)
from unicode_fol_kit.fol.normalforms import to_nnf
from unicode_fol_kit.fol.lambda_tools import (
    has_lambdas, eliminate_lambdas, beta_reduce_step, reduce_trace,
)


def parse(s):
    return MSFLParser().parse(s)


# ---------------------------------------------------------------------------
# has_lambdas
# ---------------------------------------------------------------------------

class TestHasLambdas:
    def test_plain_atom_is_false(self):
        assert has_lambdas(Atom("P", [Variable("x")])) is False

    def test_constant_and_variable_false(self):
        assert has_lambdas(Constant("a")) is False
        assert has_lambdas(Variable("x")) is False

    def test_lambdavar_true(self):
        assert has_lambdas(LambdaVar("p")) is True

    def test_bare_lambda_true(self):
        assert has_lambdas(Lambda(LambdaVar("x"), LambdaVar("x"))) is True

    def test_application_true(self):
        # (λx.P(x))(a)
        node = Application(Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")])), Constant("a"))
        assert has_lambdas(node) is True

    def test_parsed_application_true(self):
        assert has_lambdas(parse(u"(λP. P(x))(a)")) is True

    def test_lambda_nested_inside_quantifier_and_connective(self):
        # ∀x (P(x) ∧ (λy.y)(x))   — lambda buried deep is still found
        inner = Application(Lambda(LambdaVar("y"), LambdaVar("y")), Variable("x"))
        node = Quantifier("∀", Variable("x"), And(Atom("P", [Variable("x")]), inner))
        assert has_lambdas(node) is True

    def test_no_lambda_in_quantified_formula(self):
        node = Quantifier("∀", Variable("x"), Not(Atom("P", [Variable("x")])))
        assert has_lambdas(node) is False


# ---------------------------------------------------------------------------
# eliminate_lambdas
# ---------------------------------------------------------------------------

class TestEliminateLambdas:
    def test_applied_predicate_collapses_to_atom(self):
        # (λP. P(x))(Q)  -- Q parses as nullary Atom('Q', []); beta gives the
        # stuck spine Application(Atom('Q',[]), x), which must collapse to Q(x).
        result = eliminate_lambdas(parse(u"(λP. P(x))(Q)"))
        assert result == Atom("Q", [Variable("x")])

    def test_eliminated_node_exports_to_tptp_and_prover9(self):
        result = eliminate_lambdas(parse(u"(λP. P(x))(Q)"))
        # No lambda constructs remain, so the first-order exporters succeed.
        assert result.to_tptp() == "q(X)"
        assert result.to_prover9() == "Q(X)"

    def test_identity_application_to_constant(self):
        # (λx. x)(a) → a
        node = Application(Lambda(LambdaVar("x"), LambdaVar("x")), Constant("a"))
        assert eliminate_lambdas(node) == Constant("a")

    def test_already_lambda_free_passes_through(self):
        node = Atom("P", [Variable("x"), Constant("a")])
        assert eliminate_lambdas(node) == node

    def test_lambda_free_after_normalization_under_quantifier(self):
        # ∀x ((λy. P(y))(x))  →  ∀x P(x)
        body = Application(Lambda(LambdaVar("y"), Atom("P", [LambdaVar("y")])), Variable("x"))
        node = Quantifier("∀", Variable("x"), body)
        assert eliminate_lambdas(node) == Quantifier("∀", Variable("x"),
                                                      Atom("P", [Variable("x")]))

    def test_stuck_application_headed_by_lambdavar_raises(self):
        # Application whose func is a free LambdaVar — no redex, genuinely stuck.
        node = Application(LambdaVar("f"), Constant("a"))
        with pytest.raises(ValueError):
            eliminate_lambdas(node)

    def test_partially_applied_term_raises(self):
        # (λf. f(a))(g) where g is itself a free higher-order var (LambdaVar):
        # beta gives g(a) headed by a LambdaVar — stuck.
        node = Application(
            Lambda(LambdaVar("f"), Application(LambdaVar("f"), Constant("a"))),
            LambdaVar("g"),
        )
        with pytest.raises(ValueError):
            eliminate_lambdas(node)

    def test_bare_residual_lambda_raises(self):
        # λx. x normalizes to itself (an honest abstraction) — not exportable.
        with pytest.raises(ValueError):
            eliminate_lambdas(Lambda(LambdaVar("x"), LambdaVar("x")))


# ---------------------------------------------------------------------------
# beta_reduce_step
# ---------------------------------------------------------------------------

class TestBetaReduceStep:
    def test_single_redex_contracts(self):
        # (λx. x)(a) → a in one step
        node = Application(Lambda(LambdaVar("x"), LambdaVar("x")), Constant("a"))
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        assert out == Constant("a")

    def test_normal_form_reports_false_and_same_object(self):
        node = Atom("P", [Variable("x")])
        out, reduced = beta_reduce_step(node)
        assert reduced is False
        assert out is node

    def test_leftmost_outermost_contracts_outer_first(self):
        # (λx. x)((λy. y)(a)): outermost redex is the outer one.
        inner = Application(Lambda(LambdaVar("y"), LambdaVar("y")), Constant("a"))
        node = Application(Lambda(LambdaVar("x"), LambdaVar("x")), inner)
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        # One outer contraction yields the still-reducible inner redex (λy.y)(a),
        # NOT the constant a (which would require contracting the inner redex first).
        assert out == inner

    def test_step_under_lambda(self):
        # λz. (λx. x)(z)  → λz. z   (reduce inside the abstraction body)
        body = Application(Lambda(LambdaVar("x"), LambdaVar("x")), LambdaVar("z"))
        node = Lambda(LambdaVar("z"), body)
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        assert out == Lambda(LambdaVar("z"), LambdaVar("z"))

    def test_step_inside_atom_argument(self):
        # P((λx. x)(a)) → P(a)
        arg = Application(Lambda(LambdaVar("x"), LambdaVar("x")), Constant("a"))
        node = Atom("P", [arg])
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        assert out == Atom("P", [Constant("a")])

    def test_capture_avoiding_contraction(self):
        # (λx. λy. x)(y) must alpha-rename to avoid capturing the free y.
        node = Application(
            Lambda(LambdaVar("x"), Lambda(LambdaVar("y"), LambdaVar("x"))),
            LambdaVar("y"),
        )
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        # Result is λy'. y  for some fresh y' (NOT λy. y, which would be capture).
        assert isinstance(out, Lambda)
        assert out.param.name != "y"
        assert out.body == LambdaVar("y")


# ---------------------------------------------------------------------------
# reduce_trace
# ---------------------------------------------------------------------------

class TestReduceTrace:
    def test_trace_of_double_lambda(self):
        original = parse(u"(λP. λx. P(x))(Q)")
        trace = reduce_trace(original)
        assert len(trace) >= 2
        # First snapshot is the original term unchanged.
        assert trace[0] == original
        # Last snapshot equals beta_reduce of the original (beta-normal form).
        assert trace[-1] == beta_reduce(original)
        # The body head is lambda-free: the result is λx. Q(x), whose body is an
        # Application headed by the (lambda-free) Atom Q, not a Lambda/LambdaVar.
        assert isinstance(trace[-1], Lambda)
        head = trace[-1].body
        while isinstance(head, Application):
            head = head.func
        assert isinstance(head, Atom)

    def test_consecutive_snapshots_are_one_step_apart(self):
        original = parse(u"(λP. λx. P(x))(Q)")
        trace = reduce_trace(original)
        for before, after in zip(trace, trace[1:]):
            stepped, reduced = beta_reduce_step(before)
            assert reduced is True
            assert stepped == after
        # And the final snapshot is genuinely normal.
        _, reduced = beta_reduce_step(trace[-1])
        assert reduced is False

    def test_normal_form_yields_singleton(self):
        node = Atom("P", [Variable("x")])
        trace = reduce_trace(node)
        assert trace == [node]

    def test_multi_step_count_is_exact(self):
        # (λx. x)((λy. y)(a)): outer step then inner step → 3 snapshots total.
        inner = Application(Lambda(LambdaVar("y"), LambdaVar("y")), Constant("a"))
        node = Application(Lambda(LambdaVar("x"), LambdaVar("x")), inner)
        trace = reduce_trace(node)
        assert len(trace) == 3
        assert trace[0] == node
        assert trace[1] == inner
        assert trace[2] == Constant("a")

    def test_limit_overflow_raises(self):
        # Omega = (λx. x x)(λx. x x) never reaches normal form.
        sx = LambdaVar("x")
        omega_half = Lambda(sx, Application(sx, sx))
        omega = Application(omega_half, omega_half)
        with pytest.raises(ReductionLimitError):
            reduce_trace(omega, limit=25)


# ---------------------------------------------------------------------------
# Adversarial reviewer's fresh edge cases
# ---------------------------------------------------------------------------

class TestReviewerEdgeCases:
    def test_has_lambdas_recurses_into_lukasiewicz_and_sorted_nodes(self):
        # has_lambdas must descend through Łukasiewicz and sort-restricted nodes,
        # not just the classical connectives covered above.
        lam = Application(Lambda(LambdaVar("y"), LambdaVar("y")), Variable("x"))
        luk = LukImplication(Atom("P", [Variable("x")]), Atom("Q", [lam]))
        assert has_lambdas(luk) is True
        sq = SortedQuantifier("∀", Variable("x"), "Human", Atom("Q", [lam]))
        assert has_lambdas(sq) is True
        # And False when no lambda is buried in such a node.
        clean = WeakConjunction(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")]))
        assert has_lambdas(clean) is False

    def test_has_lambdas_false_on_arithmetic_and_comparison(self):
        # x + 1 < y  parses to an infix-comparison Atom over an arithmetic
        # Function; neither is a lambda construct.
        node = MSFLParser().parse(u"x + 1 < y")
        assert has_lambdas(node) is False

    def test_eliminate_under_sorted_quantifier_normalizes_body(self):
        # ∀x:Human ((λy. Q(y))(x))  →  ∀x:Human Q(x), shell preserved.
        body = Application(Lambda(LambdaVar("y"), Atom("Q", [LambdaVar("y")])), Variable("x"))
        node = SortedQuantifier("∀", Variable("x"), "Human", body)
        assert eliminate_lambdas(node) == SortedQuantifier(
            "∀", Variable("x"), "Human", Atom("Q", [Variable("x")])
        )

    def test_eliminated_higher_arity_predicate_collapses_and_exports(self):
        # (λP. P(x,y))(R) must un-curry to the binary call R(x,y) and survive the
        # Z3 / NNF passes (not just the string exporters the original tests check).
        result = eliminate_lambdas(parse(u"(λP. P(x,y))(R)"))
        assert result == Atom("R", [Variable("x"), Variable("y")])
        assert to_nnf(result) == result
        assert result.to_z3() is not None  # builds a Z3 expr without error
        assert result.to_tptp() == "r(X,Y)"

    def test_residual_lambda_inside_atom_argument_raises(self):
        # P(λz. z): the abstraction is normal but not first-order; it sits in an
        # argument position, so the leftover-scan must reach it and reject.
        node = Atom("P", [Lambda(LambdaVar("z"), LambdaVar("z"))])
        with pytest.raises(ValueError):
            eliminate_lambdas(node)

    def test_capture_avoidance_matches_full_beta_reduce(self):
        # (λx. λy. P(x, y))(y): contracting must alpha-rename the inner binder so
        # the free outer y is not captured. The single-step result must equal the
        # package's full beta_reduce (which also avoids capture), and the body
        # must mention the ORIGINAL free y plus a fresh bound variable != y.
        node = Application(
            Lambda(LambdaVar("x"),
                   Lambda(LambdaVar("y"), Atom("P", [LambdaVar("x"), LambdaVar("y")]))),
            LambdaVar("y"),
        )
        out, reduced = beta_reduce_step(node)
        assert reduced is True
        assert out == beta_reduce(node)
        assert isinstance(out, Lambda)
        assert out.param.name != "y"          # inner binder was renamed
        # Body is P(y, <fresh>): first arg is the captured-free y, second the fresh binder.
        assert out.body == Atom("P", [LambdaVar("y"), out.param])

    def test_trace_final_equals_eliminate_lambdas_when_first_order(self):
        # When a term beta-normalizes to a first-order shape, the last trace
        # snapshot collapses (via eliminate_lambdas) to the same Atom that the
        # export pipeline would consume.
        original = parse(u"(λP. P(x))(Q)")
        trace = reduce_trace(original)
        assert eliminate_lambdas(trace[-1]) == Atom("Q", [Variable("x")])
        assert eliminate_lambdas(trace[-1]) == eliminate_lambdas(original)
