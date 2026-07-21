"""Tests for MSFL AST nodes (unicode_fol_kit/fol/nodes.py)."""
import pytest
from unicode_fol_kit.fol.nodes import (
    Node, Variable, Atom,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
)

_X = Variable("x")
_P = Atom("P", [Variable("x")])
_Q = Atom("Q", [Variable("y")])


# ---------------------------------------------------------------------------
# SortedQuantifier
# ---------------------------------------------------------------------------

class TestSortedQuantifier:
    def test_construction(self):
        n = SortedQuantifier("∀", _X, "Human", _P)
        assert n.type == "∀"
        assert n.variable == _X
        assert n.sort == "Human"
        assert n.formula == _P

    def test_round_trip_forall(self):
        n = SortedQuantifier("∀", _X, "Human", _P)
        assert Node.from_dict(n.to_dict()) == n

    def test_round_trip_exists(self):
        n = SortedQuantifier("∃", _X, "Animal", _P)
        assert Node.from_dict(n.to_dict()) == n

    def test_tree_str_shows_sort(self):
        n = SortedQuantifier("∀", _X, "Human", _P)
        assert "∀ x:Human" in n.tree_str()

    def test_to_z3_auto_reduces(self):
        assert SortedQuantifier("∀", _X, "Human", _P).to_z3() is not None

    def test_to_prover9_auto_reduces(self):
        result = SortedQuantifier("∀", _X, "Human", _P).to_prover9()
        assert isinstance(result, str) and result

    def test_to_tptp_auto_reduces(self):
        result = SortedQuantifier("∀", _X, "Human", _P).to_tptp()
        assert isinstance(result, str) and result


# ---------------------------------------------------------------------------
# SortedConstant
# ---------------------------------------------------------------------------

class TestSortedConstant:
    def test_construction(self):
        n = SortedConstant("alice", "Human")
        assert n.name == "alice"
        assert n.sort == "Human"

    def test_round_trip(self):
        n = SortedConstant("alice", "Human")
        assert Node.from_dict(n.to_dict()) == n

    def test_tree_str_leaf(self):
        n = SortedConstant("alice", "Human")
        tree = n.tree_str()
        assert "alice:Human" in tree
        assert "\n" not in tree  # leaf — single line

    def test_to_z3_auto_reduces(self):
        assert SortedConstant("alice", "Human").to_z3() is not None

    def test_to_prover9_auto_reduces(self):
        result = SortedConstant("alice", "Human").to_prover9()
        assert isinstance(result, str) and result

    def test_to_tptp_auto_reduces(self):
        result = SortedConstant("alice", "Human").to_tptp()
        assert isinstance(result, str) and result


# ---------------------------------------------------------------------------
# WeakConjunction
# ---------------------------------------------------------------------------

class TestWeakConjunction:
    def test_construction(self):
        n = WeakConjunction(_P, _Q)
        assert n.left == _P
        assert n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(WeakConjunction(_P, _Q).to_dict()) == WeakConjunction(_P, _Q)

    def test_tree_str_glyph(self):
        assert "∧" in WeakConjunction(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            WeakConjunction(_P, _Q).to_z3()


# ---------------------------------------------------------------------------
# WeakDisjunction
# ---------------------------------------------------------------------------

class TestWeakDisjunction:
    def test_construction(self):
        n = WeakDisjunction(_P, _Q)
        assert n.left == _P and n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(WeakDisjunction(_P, _Q).to_dict()) == WeakDisjunction(_P, _Q)

    def test_tree_str_glyph(self):
        assert "∨" in WeakDisjunction(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            WeakDisjunction(_P, _Q).to_z3()


# ---------------------------------------------------------------------------
# StrongConjunction
# ---------------------------------------------------------------------------

class TestStrongConjunction:
    def test_construction(self):
        n = StrongConjunction(_P, _Q)
        assert n.left == _P and n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(StrongConjunction(_P, _Q).to_dict()) == StrongConjunction(_P, _Q)

    def test_tree_str_glyph(self):
        assert "⊗" in StrongConjunction(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            StrongConjunction(_P, _Q).to_z3()


# ---------------------------------------------------------------------------
# StrongDisjunction
# ---------------------------------------------------------------------------

class TestStrongDisjunction:
    def test_construction(self):
        n = StrongDisjunction(_P, _Q)
        assert n.left == _P and n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(StrongDisjunction(_P, _Q).to_dict()) == StrongDisjunction(_P, _Q)

    def test_tree_str_glyph(self):
        assert "⊕" in StrongDisjunction(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            StrongDisjunction(_P, _Q).to_z3()


# ---------------------------------------------------------------------------
# LukNegation
# ---------------------------------------------------------------------------

class TestLukNegation:
    def test_construction(self):
        n = LukNegation(_P)
        assert n.formula == _P

    def test_round_trip(self):
        assert Node.from_dict(LukNegation(_P).to_dict()) == LukNegation(_P)

    def test_tree_str_glyph(self):
        assert "¬" in LukNegation(_P).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            LukNegation(_P).to_z3()


# ---------------------------------------------------------------------------
# LukImplication
# ---------------------------------------------------------------------------

class TestLukImplication:
    def test_construction(self):
        n = LukImplication(_P, _Q)
        assert n.left == _P and n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(LukImplication(_P, _Q).to_dict()) == LukImplication(_P, _Q)

    def test_tree_str_glyph(self):
        assert "→" in LukImplication(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            LukImplication(_P, _Q).to_z3()


# ---------------------------------------------------------------------------
# LukEquivalence
# ---------------------------------------------------------------------------

class TestLukEquivalence:
    def test_construction(self):
        n = LukEquivalence(_P, _Q)
        assert n.left == _P and n.right == _Q

    def test_round_trip(self):
        assert Node.from_dict(LukEquivalence(_P, _Q).to_dict()) == LukEquivalence(_P, _Q)

    def test_tree_str_glyph(self):
        assert "↔" in LukEquivalence(_P, _Q).tree_str()

    def test_to_z3_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic; the classical
        # exports now refuse and point at the fuzzy tools (to_fol = the opt-in).
        with pytest.raises(NotImplementedError, match='fuzzy_is_valid'):
            LukEquivalence(_P, _Q).to_z3()
