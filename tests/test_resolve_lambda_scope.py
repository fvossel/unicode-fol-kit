"""Tests for resolve_lambda_scope: lexical scope resolution of lambda-bound names."""

import pytest

from unicode_fol_kit.fol._msfl_nodes import (
    _resolve,
    resolve_lambda_scope,
    free_variables,
    beta_reduce,
    LambdaVar, Lambda, Application,
    SortedQuantifier,
    WeakConjunction,
)
from unicode_fol_kit.fol._fol_nodes import (
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Quantifier, Implies,
)
from unicode_fol_kit.fol.msflparser import MSFLParser


# ---------------------------------------------------------------------------
# Variable rewrite: name in lambda-bound set → LambdaVar
# ---------------------------------------------------------------------------

class TestResolveVariables:
    def test_bound_variable_becomes_lambdavar(self):
        # λx. P(x) — x is lambda-bound; body arg x becomes LambdaVar.
        # P is NOT lambda-bound, so Atom stays Atom.
        node = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
        result = resolve_lambda_scope(node)
        assert result == Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))

    def test_unbound_variable_stays_variable(self):
        # λx. Q(x, y) — x becomes LambdaVar; y is not in scope → stays Variable.
        node = Lambda(LambdaVar("x"), Atom("Q", [Variable("x"), Variable("y")]))
        result = resolve_lambda_scope(node)
        body = result.body
        assert body.args[0] == LambdaVar("x")
        assert body.args[1] == Variable("y")

    def test_unrelated_variable_in_body_untouched(self):
        # λx. P(y) — y never in scope, stays Variable.
        node = Lambda(LambdaVar("x"), Atom("P", [Variable("y")]))
        result = resolve_lambda_scope(node)
        assert result.body == Atom("P", [Variable("y")])


# ---------------------------------------------------------------------------
# Atom → Application (higher-order predicate parameter)
# ---------------------------------------------------------------------------

class TestResolveHigherOrder:
    def test_single_arg_atom_becomes_application(self):
        # λP. P(x) — P lambda-bound; Atom("P",[Variable("x")]) → Application(LambdaVar("P"), Variable("x"))
        node = Lambda(LambdaVar("P"), Atom("P", [Variable("x")]))
        result = resolve_lambda_scope(node)
        assert result == Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
        assert result.body.arg == Variable("x")   # x NOT bound here → stays Variable

    def test_nested_lambda_both_in_scope(self):
        # λP. λx. P(x) — at inner body, scope={P,x}; P(x) → Application(LambdaVar("P"), LambdaVar("x"))
        node = Lambda(LambdaVar("P"), Lambda(LambdaVar("x"), Atom("P", [Variable("x")])))
        result = resolve_lambda_scope(node)
        inner = result.body
        assert inner == Lambda(LambdaVar("x"), Application(LambdaVar("P"), LambdaVar("x")))

    def test_multi_arg_currying(self):
        # λP. P(x, y) — two args: Application(Application(LambdaVar("P"), Variable("x")), Variable("y"))
        node = Lambda(LambdaVar("P"), Atom("P", [Variable("x"), Variable("y")]))
        result = resolve_lambda_scope(node)
        body = result.body
        assert isinstance(body, Application)
        assert isinstance(body.func, Application)
        assert body.func.func == LambdaVar("P")
        assert body.func.arg == Variable("x")
        assert body.arg == Variable("y")

    def test_zero_arg_atom_becomes_lambdavar(self):
        # λP. P — Atom("P", []) under λP → bare LambdaVar("P")
        node = Lambda(LambdaVar("P"), Atom("P", []))
        result = resolve_lambda_scope(node)
        assert result == Lambda(LambdaVar("P"), LambdaVar("P"))


# ---------------------------------------------------------------------------
# Function node in term position with lambda-bound name
# ---------------------------------------------------------------------------

class TestResolveFunction:
    def test_function_name_in_scope_becomes_application(self):
        # λfoo. P(foo(x)) — body is Atom("P", [Function("foo", [Variable("x")])]).
        # "foo" is lambda-bound → Function becomes Application; P is not → stays Atom.
        node = Lambda(
            LambdaVar("foo"),
            Atom("P", [Function("foo", [Variable("x")])])
        )
        result = resolve_lambda_scope(node)
        assert isinstance(result.body, Atom)
        assert result.body.predicate == "P"
        inner = result.body.args[0]
        assert inner == Application(LambdaVar("foo"), Variable("x"))

    def test_function_name_not_in_scope_stays_function(self):
        # λx. P(bar(x)) — "bar" not lambda-bound; Function("bar",...) stays Function.
        node = Lambda(
            LambdaVar("x"),
            Atom("P", [Function("bar", [Variable("x")])])
        )
        result = resolve_lambda_scope(node)
        inner = result.body.args[0]
        assert isinstance(inner, Function)
        assert inner.name == "bar"
        assert inner.args == [LambdaVar("x")]   # x IS bound → renamed inside


# ---------------------------------------------------------------------------
# Shadowing: quantifier removes name from lambda-bound set
# ---------------------------------------------------------------------------

class TestResolveShadowing:
    def test_quantifier_shadows_lambda(self):
        # λx. ∀x. P(x) — ∀x removes x from scope; inner P(x)'s arg stays Variable("x").
        node = Lambda(
            LambdaVar("x"),
            Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
        )
        result = resolve_lambda_scope(node)
        quant = result.body
        assert isinstance(quant, Quantifier)
        assert quant.variable == Variable("x")
        # x inside quantifier body must be logical Variable, NOT LambdaVar
        assert quant.formula.args[0] == Variable("x")

    def test_mixed_scope_lambda_then_shadow(self):
        # λx. P(x) ∧ ∀x. Q(x) — left P(x) has x lambda-bound (LambdaVar);
        # right Q(x) under ∀x has x shadowed (Variable).
        node = Lambda(
            LambdaVar("x"),
            And(
                Atom("P", [Variable("x")]),
                Quantifier("∀", Variable("x"), Atom("Q", [Variable("x")]))
            )
        )
        result = resolve_lambda_scope(node)
        and_node = result.body
        assert and_node.left.args[0] == LambdaVar("x")    # lambda scope
        assert and_node.right.formula.args[0] == Variable("x")  # shadowed

    def test_sorted_quantifier_shadows_lambda(self):
        # λx. ∀x:Sort. P(x) — SortedQuantifier removes x from scope.
        node = Lambda(
            LambdaVar("x"),
            SortedQuantifier("∀", Variable("x"), "Sort", Atom("P", [Variable("x")]))
        )
        result = resolve_lambda_scope(node)
        sq = result.body
        assert isinstance(sq, SortedQuantifier)
        assert sq.formula.args[0] == Variable("x")   # NOT LambdaVar

    def test_higher_order_param_with_logical_var_in_body(self):
        # λP. ∀y. P(y) — P lambda-bound (Application); y quantifier-bound (stays Variable).
        node = Lambda(
            LambdaVar("P"),
            Quantifier("∀", Variable("y"), Atom("P", [Variable("y")]))
        )
        result = resolve_lambda_scope(node)
        quant = result.body
        assert isinstance(quant, Quantifier)
        assert isinstance(quant.formula, Application)
        assert quant.formula.func == LambdaVar("P")
        assert quant.formula.arg == Variable("y")   # y NOT lambda-bound → stays Variable


# ---------------------------------------------------------------------------
# Non-interference: resolver is identity on lambda-free terms
# ---------------------------------------------------------------------------

class TestResolveNonInterference:
    def test_pure_fol_formula_unchanged(self):
        # ∀x. P(x) → Q(x) — no lambdas; resolver returns structurally identical node.
        node = Quantifier(
            "∀", Variable("x"),
            Implies(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")]))
        )
        result = resolve_lambda_scope(node)
        assert result == node

    def test_unbound_predicate_stays_atom(self):
        # Atom whose predicate shares no name with any lambda param → unchanged.
        node = Lambda(LambdaVar("x"), Atom("Q", [Variable("x")]))
        result = resolve_lambda_scope(node)
        # Q is not lambda-bound; body is still Atom("Q", [...])
        assert isinstance(result.body, Atom)
        assert result.body.predicate == "Q"


# ---------------------------------------------------------------------------
# Integration: parse() auto-resolves; end-to-end with beta_reduce
# ---------------------------------------------------------------------------

class TestResolveIntegration:
    def test_parse_auto_resolves(self):
        # MSFLParser.parse() calls resolve_lambda_scope automatically.
        # λP. λx. P(x) should arrive fully resolved without an explicit call.
        result = MSFLParser().parse("λP. λx. P(x)")
        assert isinstance(result, Lambda)
        inner = result.body
        assert isinstance(inner, Lambda)
        assert inner.body == Application(LambdaVar("P"), LambdaVar("x"))

    def test_end_to_end_beta_reduce_clean(self):
        # (λP. P(x))(λy. Q(y)) — parse → resolve → beta_reduce → Atom("Q", [Variable("x")])
        #
        # After parse+resolve:
        #   func = Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
        #   arg  = Lambda(LambdaVar("y"), Atom("Q", [LambdaVar("y")]))
        # Beta: substitute P → arg in Application(LambdaVar("P"), Variable("x"))
        #   → Application(Lambda(LambdaVar("y"), Atom("Q",[LambdaVar("y")])), Variable("x"))
        # Beta again: substitute y → Variable("x") in Atom("Q",[LambdaVar("y")])
        #   → Atom("Q", [Variable("x")])
        result = MSFLParser().parse("(λP. (P)(x))(λy. Q(y))")
        reduced = beta_reduce(result)
        assert reduced == Atom("Q", [Variable("x")])

    def test_end_to_end_beta_reduce_with_capture_avoidance(self):
        # (λP. ∀x. P(x))(Q(x)) exercises Quantifier alpha-conversion in beta_reduce.
        #
        # After parse+resolve:
        #   func = Lambda(LambdaVar("P"), Quantifier("∀", Variable("x"),
        #                 Application(LambdaVar("P"), Variable("x"))))
        #   arg  = Atom("Q", [Variable("x")])          ← x is FREE in the argument
        #
        # Naive substitution of P→Atom("Q",[Variable("x")]) inside Quantifier(∀x,...)
        # would capture x.  Capture-avoiding substitution alpha-renames ∀x to ∀x_0,
        # so the original x from Q(x) remains free in the result.
        #
        # Without alpha-conversion the result would be Quantifier(∀x, App(Atom("Q",[x]),x))
        # whose free_variables is {} — x captured.  With alpha-conversion it is {Variable("x")}.
        parsed = MSFLParser().parse("(λP. ∀x P(x))(Q(x))")
        result = beta_reduce(parsed)
        fv = free_variables(result)
        assert Variable("x") in fv   # x from Q(x) in the argument must remain free


# ---------------------------------------------------------------------------
# Purity
# ---------------------------------------------------------------------------

class TestResolvePurity:
    def test_original_node_unchanged(self):
        node = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
        original_body = node.body
        resolve_lambda_scope(node)
        assert node.body is original_body
        assert node.body.args[0] == Variable("x")   # unchanged


# ---------------------------------------------------------------------------
# TypeError on unknown node type
# ---------------------------------------------------------------------------

class TestResolveTypeError:
    def test_unknown_type_raises(self):
        with pytest.raises(TypeError, match="resolve_lambda_scope"):
            _resolve(object(), frozenset())
