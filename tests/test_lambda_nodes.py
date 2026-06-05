"""Tests for lambda-calculus AST nodes (LambdaVar, Lambda, Application)."""
import pytest
from unicode_fol_kit.fol.nodes import (
    Node, Variable, Constant, Atom,
    LambdaVar, Lambda, Application,
)

_X = Variable("x")
_P = Atom("P", [Variable("x")])


# ---------------------------------------------------------------------------
# LambdaVar
# ---------------------------------------------------------------------------

class TestLambdaVar:
    def test_construction(self):
        v = LambdaVar("P")
        assert v.name == "P"
        assert isinstance(v, LambdaVar)

    def test_round_trip(self):
        v = LambdaVar("P")
        assert Node.from_dict(v.to_dict()) == v

    def test_to_dict_type_tag(self):
        assert LambdaVar("P").to_dict() == {"_type": "LambdaVar", "name": "P"}

    def test_tree_str_label(self):
        assert "LambdaVar: P" in LambdaVar("P").tree_str()

    def test_tree_str_is_leaf(self):
        assert "\n" not in LambdaVar("P").tree_str()

    def test_to_z3_raises(self):
        with pytest.raises(NotImplementedError):
            LambdaVar("P").to_z3()

    def test_to_prover9_raises(self):
        with pytest.raises(NotImplementedError):
            LambdaVar("P").to_prover9()

    def test_to_tptp_raises(self):
        with pytest.raises(NotImplementedError):
            LambdaVar("P").to_tptp()

    def test_to_msfol_raises(self):
        with pytest.raises(NotImplementedError):
            LambdaVar("P").to_msfol()

    def test_relativize_raises(self):
        with pytest.raises(NotImplementedError):
            LambdaVar("P")._relativize([])


# ---------------------------------------------------------------------------
# Lambda
# ---------------------------------------------------------------------------

class TestLambda:
    def test_construction(self):
        lv = LambdaVar("P")
        lam = Lambda(lv, _P)
        assert lam.param is lv
        assert lam.body is _P

    def test_param_is_lambda_var(self):
        lam = Lambda(LambdaVar("x"), _P)
        assert isinstance(lam.param, LambdaVar)

    def test_round_trip(self):
        lam = Lambda(LambdaVar("P"), _P)
        assert Node.from_dict(lam.to_dict()) == lam

    def test_from_dict_param_type(self):
        lam = Lambda(LambdaVar("P"), _P)
        restored = Node.from_dict(lam.to_dict())
        assert isinstance(restored.param, LambdaVar)

    def test_to_dict_shape(self):
        d = Lambda(LambdaVar("P"), _P).to_dict()
        assert d["_type"] == "Lambda"
        assert d["param"] == {"_type": "LambdaVar", "name": "P"}

    def test_tree_str_label(self):
        assert "λ P" in Lambda(LambdaVar("P"), _P).tree_str()

    def test_tree_str_shows_body(self):
        tree = Lambda(LambdaVar("P"), _P).tree_str()
        assert "Atom: P" in tree

    def test_to_z3_raises(self):
        with pytest.raises(NotImplementedError):
            Lambda(LambdaVar("P"), _P).to_z3()

    def test_to_prover9_raises(self):
        with pytest.raises(NotImplementedError):
            Lambda(LambdaVar("P"), _P).to_prover9()

    def test_to_tptp_raises(self):
        with pytest.raises(NotImplementedError):
            Lambda(LambdaVar("P"), _P).to_tptp()

    def test_to_msfol_raises(self):
        with pytest.raises(NotImplementedError):
            Lambda(LambdaVar("P"), _P).to_msfol()

    def test_relativize_raises(self):
        with pytest.raises(NotImplementedError):
            Lambda(LambdaVar("P"), _P)._relativize([])


# ---------------------------------------------------------------------------
# Application
# ---------------------------------------------------------------------------

class TestApplication:
    def test_construction(self):
        app = Application(LambdaVar("P"), _X)
        assert app.func == LambdaVar("P")
        assert app.arg == _X

    def test_round_trip(self):
        app = Application(LambdaVar("P"), _X)
        assert Node.from_dict(app.to_dict()) == app

    def test_to_dict_shape(self):
        d = Application(LambdaVar("P"), _X).to_dict()
        assert d["_type"] == "Application"
        assert "func" in d and "arg" in d

    def test_tree_str_label(self):
        assert "App" in Application(LambdaVar("P"), _X).tree_str()

    def test_tree_str_shows_children(self):
        tree = Application(LambdaVar("P"), _X).tree_str()
        assert "LambdaVar: P" in tree
        assert "Variable: x" in tree

    def test_to_z3_raises(self):
        with pytest.raises(NotImplementedError):
            Application(LambdaVar("P"), _X).to_z3()

    def test_to_prover9_raises(self):
        with pytest.raises(NotImplementedError):
            Application(LambdaVar("P"), _X).to_prover9()

    def test_to_tptp_raises(self):
        with pytest.raises(NotImplementedError):
            Application(LambdaVar("P"), _X).to_tptp()

    def test_to_msfol_raises(self):
        with pytest.raises(NotImplementedError):
            Application(LambdaVar("P"), _X).to_msfol()

    def test_relativize_raises(self):
        with pytest.raises(NotImplementedError):
            Application(LambdaVar("P"), _X)._relativize([])


# ---------------------------------------------------------------------------
# Nested term: Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
# ---------------------------------------------------------------------------

class TestNested:
    def _term(self):
        return Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))

    def test_round_trip(self):
        t = self._term()
        assert Node.from_dict(t.to_dict()) == t

    def test_inner_param_is_lambda_var(self):
        restored = Node.from_dict(self._term().to_dict())
        assert isinstance(restored.param, LambdaVar)

    def test_tree_str_contains_all_labels(self):
        tree = self._term().tree_str()
        assert "λ P" in tree
        assert "App" in tree
        assert "LambdaVar: P" in tree
        assert "Variable: x" in tree


# ---------------------------------------------------------------------------
# Redex round-trip: Application(Lambda(...), Constant("a"))
# ---------------------------------------------------------------------------

class TestRedex:
    def _redex(self):
        # Shape that step 3 (beta-reduction) will reduce:
        # (λx. P(x))(a)
        return Application(
            Lambda(LambdaVar("x"), Atom("P", [Variable("x")])),
            Constant("a"),
        )

    def test_round_trip(self):
        r = self._redex()
        assert Node.from_dict(r.to_dict()) == r

    def test_func_is_lambda_after_round_trip(self):
        restored = Node.from_dict(self._redex().to_dict())
        assert isinstance(restored.func, Lambda)

    def test_func_param_is_lambda_var_after_round_trip(self):
        restored = Node.from_dict(self._redex().to_dict())
        assert isinstance(restored.func.param, LambdaVar)

    def test_tree_str_shows_redex_shape(self):
        tree = self._redex().tree_str()
        assert "App" in tree
        assert "λ x" in tree
        assert "Constant: a" in tree
