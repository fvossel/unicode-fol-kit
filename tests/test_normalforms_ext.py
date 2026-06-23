"""Tests for the extended normal forms: to_dnf and to_tseitin_cnf.

``to_dnf`` is equivalence-preserving (verified against Z3) and yields a
disjunction of conjunctions of literals. ``to_tseitin_cnf`` is only
equisatisfiable (definitional encoding with fresh auxiliary predicates) and
yields a conjunction of disjunctions of literals.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.normalforms import (
    to_dnf, to_tseitin_cnf, _prenex_split, _conjuncts, _disjuncts,
)
from unicode_fol_kit.fol._fol_nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier,
)
from unicode_fol_kit import formulas_are_equivalent, is_satisfiable

FOL = MSFLParser()


# ---------------------------------------------------------------------------
# Structural helpers
# ---------------------------------------------------------------------------

def _is_literal(n):
    """A literal is an Atom or the negation of an Atom."""
    return isinstance(n, Atom) or (isinstance(n, Not) and isinstance(n.formula, Atom))


def _assert_dnf_shape(matrix):
    """matrix must be a disjunction of conjunctions of literals."""
    for clause in _disjuncts(matrix):           # split on Or
        for lit in _conjuncts(clause):          # split each clause on And
            assert _is_literal(lit), f"non-literal {lit!r} in DNF conjunctive clause"


def _assert_cnf_shape(matrix):
    """matrix must be a conjunction of disjunctions of literals."""
    for clause in _conjuncts(matrix):           # split on And
        for lit in _disjuncts(clause):          # split each clause on Or
            assert _is_literal(lit), f"non-literal {lit!r} in CNF clause"


# ---------------------------------------------------------------------------
# to_dnf — equivalence (Z3 oracle)
# ---------------------------------------------------------------------------

class TestDNFEquivalence:
    CASES = [
        "P ∧ (Q ∨ R)",
        "(P → Q) ↔ R",
        "¬(P ∧ Q)",
        "(P ∨ Q) ∧ (R ∨ S)",
        "P ↔ Q",
        "P ⊕ Q",
        "(P ∧ Q) ∨ (R ∧ S)",
        "¬(P ∨ (Q ∧ R))",
    ]

    @pytest.mark.parametrize("formula", CASES)
    def test_dnf_equivalent(self, formula):
        f = FOL.parse(formula)
        assert formulas_are_equivalent(f, to_dnf(f))

    def test_dnf_equivalent_quantified(self):
        f = FOL.parse("∀x (P(x) ∧ (Q(x) ∨ R(x)))")
        assert formulas_are_equivalent(f, to_dnf(f))


# ---------------------------------------------------------------------------
# to_dnf — structural shape
# ---------------------------------------------------------------------------

class TestDNFShape:
    @pytest.mark.parametrize("formula", [
        "P ∧ (Q ∨ R)",
        "(P → Q) ↔ R",
        "¬(P ∧ Q)",
        "(P ∨ Q) ∧ (R ∨ S)",
        "(P ∧ Q) ∨ (R ∧ S)",
    ])
    def test_matrix_is_disjunction_of_conjunctions(self, formula):
        dnf = to_dnf(FOL.parse(formula))
        _, matrix = _prenex_split(dnf)
        # No connective other than And/Or/Not(atom) survives in the matrix.
        for node in matrix.walk():
            assert not isinstance(node, (Implies, Iff)), f"{node!r} survived in DNF"
            if isinstance(node, Not):
                assert isinstance(node.formula, Atom)
        _assert_dnf_shape(matrix)

    def test_no_conjunction_above_a_disjunction(self):
        # P ∧ (Q ∨ R) must distribute to (P ∧ Q) ∨ (P ∧ R): the top must be Or.
        dnf = to_dnf(FOL.parse("P ∧ (Q ∨ R)"))
        _, matrix = _prenex_split(dnf)
        assert isinstance(matrix, Or), f"expected top-level Or, got {type(matrix).__name__}"
        # and each disjunct is a pure conjunction of literals (no Or inside)
        for clause in _disjuncts(matrix):
            for node in clause.walk():
                assert not isinstance(node, Or), "Or nested inside a DNF conjunctive clause"

    def test_quantifier_prefix_retained(self):
        dnf = to_dnf(FOL.parse("∀x ∃y (P(x) ∧ (Q(y) ∨ R(y)))"))
        prefix, matrix = _prenex_split(dnf)
        assert [t for t, _ in prefix] == ["∀", "∃"]
        for node in matrix.walk():
            assert not isinstance(node, Quantifier), "quantifier left in DNF matrix"


# ---------------------------------------------------------------------------
# to_tseitin_cnf — equisatisfiability (Z3 oracle)
# ---------------------------------------------------------------------------

class TestTseitinEquisatisfiable:
    @pytest.mark.parametrize("formula", [
        "P ∧ ¬P",            # UNSAT
        "P ∨ Q",             # SAT
        "(P → Q) ↔ R",       # SAT
        "¬(P ∧ Q)",          # SAT
        "(P ∨ Q) ∧ (¬P ∨ ¬Q)",   # SAT
        "P ⊕ Q",             # SAT
        "(P ∧ ¬P) ∨ (Q ∧ ¬Q)",   # UNSAT
        "(P ↔ Q) ∧ (Q ↔ R) ∧ (P ↔ ¬R)",  # UNSAT
    ])
    def test_satisfiability_preserved(self, formula):
        f = FOL.parse(formula)
        assert is_satisfiable(f) == is_satisfiable(to_tseitin_cnf(f))

    def test_unsat_case_stays_unsat(self):
        f = FOL.parse("P ∧ ¬P")
        assert is_satisfiable(f) is False
        assert is_satisfiable(to_tseitin_cnf(f)) is False

    def test_sat_case_stays_sat(self):
        f = FOL.parse("P ∨ Q")
        assert is_satisfiable(f) is True
        assert is_satisfiable(to_tseitin_cnf(f)) is True

    @pytest.mark.parametrize("formula", [
        "P(a) ∧ (Q(b) ∨ R(c))",        # ground, SAT
        "P(a) ∧ ¬P(a)",                # ground, UNSAT
        "(P(a) ∨ P(b)) ∧ (¬P(a) ∨ ¬P(b))",   # ground, SAT
    ])
    def test_ground_predicates_preserved(self, formula):
        # Quantifier-free formulas over ground atoms (constant arguments) are the
        # intended use: the 0-ary auxiliaries are sound there, so satisfiability
        # must be preserved exactly.
        f = FOL.parse(formula)
        assert is_satisfiable(f) == is_satisfiable(to_tseitin_cnf(f))


# ---------------------------------------------------------------------------
# to_tseitin_cnf — structural shape and non-equivalence
# ---------------------------------------------------------------------------

class TestTseitinShape:
    @pytest.mark.parametrize("formula", [
        "P ∧ (Q ∨ R)",
        "(P → Q) ↔ R",
        "¬(P ∧ Q)",
        "(P ∨ Q) ∧ (R ∨ S)",
        "P ⊕ Q",
    ])
    def test_matrix_is_conjunction_of_disjunctions(self, formula):
        cnf = to_tseitin_cnf(FOL.parse(formula))
        _, matrix = _prenex_split(cnf)
        for node in matrix.walk():
            assert not isinstance(node, (Implies, Iff)), f"{node!r} survived in Tseitin CNF"
            if isinstance(node, Not):
                assert isinstance(node.formula, Atom)
        _assert_cnf_shape(matrix)

    def test_introduces_fresh_auxiliaries(self):
        # A compound formula must gain at least one fresh 'ts'-prefixed predicate.
        cnf = to_tseitin_cnf(FOL.parse("P ∧ (Q ∨ R)"))
        aux_names = {a.predicate for a in cnf.atoms() if a.predicate.startswith("ts")}
        assert aux_names, "no fresh Tseitin auxiliary predicate introduced"

    def test_not_equivalence_preserving_but_equisatisfiable(self):
        # The encoding adds auxiliary variables, so it is NOT equivalent to the
        # input — yet it must remain equisatisfiable.
        f = FOL.parse("P ∧ (Q ∨ R)")
        ts = to_tseitin_cnf(f)
        assert not formulas_are_equivalent(f, ts)
        assert is_satisfiable(f) == is_satisfiable(ts)

    def test_quantified_input_rejected(self):
        # The 0-ary auxiliaries are propositional definitions and are NOT sound
        # under a quantifier prefix (a single global ts cannot track a literal
        # whose truth value varies over the domain). to_tseitin_cnf must refuse
        # such inputs rather than silently return a non-equisatisfiable result.
        with pytest.raises(ValueError):
            to_tseitin_cnf(FOL.parse("∀x ∃y (P(x) ∧ (Q(y) ∨ R(y)))"))
        with pytest.raises(ValueError):
            to_tseitin_cnf(FOL.parse("∃x P(x)"))

    def test_no_exponential_blowup(self):
        # A chain of biconditionals blows up the distributive CNF; the Tseitin
        # encoding stays linear-ish. Just assert it produces a modest CNF.
        f = FOL.parse("(P ↔ Q) ↔ ((R ↔ S) ↔ (T ↔ U))")
        cnf = to_tseitin_cnf(f)
        _, matrix = _prenex_split(cnf)
        _assert_cnf_shape(matrix)
        # Should be far below the distributive explosion; generous bound.
        assert len(_conjuncts(matrix)) < 200
