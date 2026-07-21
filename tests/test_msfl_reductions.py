"""Tests for MSFL → FOL reductions: to_msfol, to_fol, and auto-reduce exporters."""
import pytest
from dataclasses import fields
from unicode_fol_kit.fol.nodes import (
    Node, Variable, Constant, Atom, And, Or, Not, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    to_fol,
)
from unicode_fol_kit import formulas_are_equivalent

_X = Variable("x")
_P = Atom("P", [Variable("x")])
_Q = Atom("Q", [Variable("y")])


def _count_predicate(node: Node, pred: str) -> int:
    """Count Atom nodes with the given predicate name anywhere in the tree."""
    if isinstance(node, Atom) and node.predicate == pred:
        return 1
    total = 0
    try:
        for f in fields(node):
            val = getattr(node, f.name)
            if isinstance(val, Node):
                total += _count_predicate(val, pred)
            elif isinstance(val, list):
                total += sum(_count_predicate(c, pred) for c in val if isinstance(c, Node))
    except TypeError:
        pass
    return total


# ---------------------------------------------------------------------------
# to_msfol — operator lowering
# ---------------------------------------------------------------------------

class TestToMsfol:
    def test_weak_conjunction_to_and(self):
        result = WeakConjunction(_P, _Q).to_msfol()
        assert type(result) is And
        assert result.left == _P
        assert result.right == _Q

    def test_strong_conjunction_to_and(self):
        assert type(StrongConjunction(_P, _Q).to_msfol()) is And

    def test_weak_disjunction_to_or(self):
        assert type(WeakDisjunction(_P, _Q).to_msfol()) is Or

    def test_strong_disjunction_to_or(self):
        assert type(StrongDisjunction(_P, _Q).to_msfol()) is Or

    def test_luk_negation_to_not(self):
        result = LukNegation(_P).to_msfol()
        assert type(result) is Not
        assert result.formula == _P

    def test_luk_implication_to_implies(self):
        result = LukImplication(_P, _Q).to_msfol()
        assert type(result) is Implies
        assert result.left == _P
        assert result.right == _Q

    def test_luk_equivalence_to_iff(self):
        result = LukEquivalence(_P, _Q).to_msfol()
        assert type(result) is Iff

    def test_sorted_quantifier_survives(self):
        n = SortedQuantifier("∀", _X, "Human", _P)
        result = n.to_msfol()
        assert type(result) is SortedQuantifier
        assert result.type == "∀"
        assert result.sort == "Human"
        assert type(result.formula) is Atom

    def test_sorted_constant_survives(self):
        n = SortedConstant("alice", "Human")
        result = n.to_msfol()
        assert type(result) is SortedConstant
        assert result.name == "alice"
        assert result.sort == "Human"

    def test_deep_nesting_fully_lowered(self):
        n = WeakConjunction(LukNegation(_P), StrongDisjunction(_Q, _P))
        result = n.to_msfol()
        assert type(result) is And
        assert type(result.left) is Not
        assert type(result.right) is Or

    def test_purity(self):
        n = WeakConjunction(_P, _Q)
        _ = n.to_msfol()
        assert type(n) is WeakConjunction
        assert n.left is _P
        assert n.right is _Q


# ---------------------------------------------------------------------------
# to_fol — relativization shapes
# ---------------------------------------------------------------------------

class TestToFolRelativization:
    def test_forall_uses_implies(self):
        result = to_fol(SortedQuantifier("∀", _X, "Human", _P))
        assert type(result) is Quantifier
        assert result.type == "∀"
        assert type(result.formula) is Implies
        guard = result.formula.left
        assert type(guard) is Atom
        assert guard.predicate == "Human"
        assert guard.args[0] == _X

    def test_exists_uses_and(self):
        result = to_fol(SortedQuantifier("∃", _X, "Human", _P))
        assert type(result) is Quantifier
        assert result.type == "∃"
        assert type(result.formula) is And
        guard = result.formula.left
        assert guard.predicate == "Human"

    def test_sorted_constant_becomes_constant(self):
        result = to_fol(Atom("P", [SortedConstant("alice", "Human")]))
        assert type(result) is Atom
        assert type(result.args[0]) is Constant
        assert result.args[0].name == "alice"

    def test_purity(self):
        n = SortedQuantifier("∀", _X, "Human", _P)
        _ = to_fol(n)
        assert type(n) is SortedQuantifier
        assert n.sort == "Human"

    def test_plain_fol_passthrough(self):
        n = And(_P, _Q)
        result = to_fol(n)
        assert type(result) is And
        assert result.left == _P


# ---------------------------------------------------------------------------
# to_fol — sort facts
# ---------------------------------------------------------------------------

class TestToFolSortFacts:
    def test_no_facts_by_default(self):
        result = to_fol(Atom("P", [SortedConstant("alice", "Human")]))
        assert type(result) is Atom

    def test_fact_conjoined_at_top(self):
        result = to_fol(Atom("P", [SortedConstant("alice", "Human")]),
                        include_sort_facts=True)
        assert type(result) is And
        assert result.left == Atom("Human", [Constant("alice")])
        assert type(result.right) is Atom
        assert result.right.predicate == "P"

    def test_duplicate_constant_deduped(self):
        n = And(Atom("P", [SortedConstant("alice", "Human")]),
                Atom("Q", [SortedConstant("alice", "Human")]))
        result = to_fol(n, include_sort_facts=True)
        assert _count_predicate(result, "Human") == 1

    def test_two_distinct_constants_two_facts(self):
        n = And(Atom("P", [SortedConstant("alice", "Human")]),
                Atom("Q", [SortedConstant("bob", "Human")]))
        result = to_fol(n, include_sort_facts=True)
        assert _count_predicate(result, "Human") == 2

    def test_no_sorted_constants_no_facts(self):
        result = to_fol(And(_P, _Q), include_sort_facts=True)
        assert type(result) is And
        assert _count_predicate(result, "Human") == 0


# ---------------------------------------------------------------------------
# End-to-end — Z3 semantic equivalence
# ---------------------------------------------------------------------------

class TestEndToEnd:
    def test_forall_z3_equivalent(self):
        msfl = SortedQuantifier("∀", _X, "Human", _P)
        expected = Quantifier("∀", _X, Implies(Atom("Human", [_X]), _P))
        assert formulas_are_equivalent(to_fol(msfl), expected)

    def test_exists_z3_equivalent(self):
        msfl = SortedQuantifier("∃", _X, "Human", _P)
        expected = Quantifier("∃", _X, And(Atom("Human", [_X]), _P))
        assert formulas_are_equivalent(to_fol(msfl), expected)

    def test_luk_z3_export_raises_with_pointer(self):
        # The silent classical collapse decided the WRONG logic (fuzzy P ∨ ¬P is
        # not Łukasiewicz-valid; its classical image is), so the Łukasiewicz
        # nodes now refuse the classical exports and point at the fuzzy tools.
        n = WeakConjunction(_P, _Q)
        with pytest.raises(NotImplementedError, match="fuzzy_is_valid"):
            n.to_z3()

    def test_explicit_collapse_z3_equivalent_to_and(self):
        # The collapse itself stays available — explicitly, via to_fol.
        n = WeakConjunction(_P, _Q)
        assert formulas_are_equivalent(to_fol(n), And(_P, _Q))
        assert to_fol(n).to_z3() is not None

    def test_luk_prover9_export_raises_with_pointer(self):
        n = LukNegation(_P)
        with pytest.raises(NotImplementedError, match="to_fol"):
            n.to_prover9()
        assert isinstance(to_fol(n).to_prover9(), str)

    def test_luk_tptp_export_raises_with_pointer(self):
        n = LukImplication(_P, _Q)
        with pytest.raises(NotImplementedError, match="Łukasiewicz"):
            n.to_tptp()
        assert isinstance(to_fol(n).to_tptp(), str)

    def test_sort_facts_with_z3(self):
        n = Atom("P", [SortedConstant("alice", "Human")])
        fol_with = to_fol(n, include_sort_facts=True)
        fol_without = to_fol(n)
        assert fol_with.to_z3() is not None
        assert fol_without.to_z3() is not None


# ---------------------------------------------------------------------------
# Classical passthrough — base-class generic methods
# ---------------------------------------------------------------------------

class TestClassicalPassthrough:
    def test_to_msfol_on_classical_does_not_raise(self):
        x = Variable("x")
        formula = Quantifier("∀", x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))
        result = formula.to_msfol()
        assert type(result) is Quantifier
        assert type(result.formula) is Implies

    def test_to_fol_classical_semantically_equivalent(self):
        x = Variable("x")
        formula = Quantifier("∀", x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))
        assert formulas_are_equivalent(to_fol(formula), formula)

    def test_to_fol_classical_with_constant(self):
        c = Constant("socrates")
        formula = Atom("Human", [c])
        result = to_fol(formula)
        assert type(result) is Atom
        assert result.args[0] == c

    def test_to_fol_classical_purity(self):
        x = Variable("x")
        n = Quantifier("∀", x, Implies(Atom("Human", [x]), _P))
        _ = to_fol(n)
        assert type(n) is Quantifier
        assert type(n.formula) is Implies


# ---------------------------------------------------------------------------
# Explicit to_msfol overrides on SortedQuantifier / SortedConstant
# ---------------------------------------------------------------------------

class TestSortedNodeToMsfol:
    def test_sorted_quantifier_to_msfol_preserves_sort(self):
        x = Variable("x")
        n = SortedQuantifier("∀", x, "Human", _P)
        result = n.to_msfol()
        assert type(result) is SortedQuantifier
        assert result.sort == "Human"
        assert result.type == "∀"

    def test_sorted_quantifier_to_msfol_recurses_body(self):
        x = Variable("x")
        n = SortedQuantifier("∀", x, "Human", WeakConjunction(_P, _Q))
        result = n.to_msfol()
        assert type(result) is SortedQuantifier
        assert type(result.formula) is And

    def test_sorted_constant_to_msfol_is_identity(self):
        n = SortedConstant("alice", "Human")
        result = n.to_msfol()
        assert type(result) is SortedConstant
        assert result.name == "alice"
        assert result.sort == "Human"


# ---------------------------------------------------------------------------
# Mixed formula — sorted quantifier with Łukasiewicz body
# ---------------------------------------------------------------------------

class TestMixedFormula:
    def test_sorted_forall_with_luk_body_shape(self):
        x = Variable("x")
        n = SortedQuantifier("∀", x, "Human", WeakConjunction(Atom("P", [x]), Atom("Q", [x])))
        result = to_fol(n)
        assert type(result) is Quantifier
        assert result.type == "∀"
        assert type(result.formula) is Implies
        guard = result.formula.left
        assert type(guard) is Atom and guard.predicate == "Human"
        body = result.formula.right
        assert type(body) is And
        assert body.left == Atom("P", [x])
        assert body.right == Atom("Q", [x])

    def test_sorted_forall_with_luk_body_z3(self):
        x = Variable("x")
        n = SortedQuantifier("∀", x, "Human", WeakConjunction(Atom("P", [x]), Atom("Q", [x])))
        assert to_fol(n).to_z3() is not None

    def test_mixed_purity(self):
        x = Variable("x")
        n = SortedQuantifier("∀", x, "Human", LukNegation(_P))
        _ = to_fol(n)
        assert type(n) is SortedQuantifier
        assert type(n.formula) is LukNegation
