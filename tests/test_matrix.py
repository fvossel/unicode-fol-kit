"""Tests for the finite-valued matrix layer (unicode_fol_kit.semantics.matrix).

Two things are checked: (1) the K3 and LP matrices reproduce the existing
hard-wired three-valued decisions *exactly* (a differential over random formulas),
and (2) Belnap–Dunn FDE exhibits its textbook behaviour — paraconsistent (no
explosion), paracomplete (no excluded middle), and with no logical truths at all
(even ``p → p`` fails). Custom-matrix construction and validation are covered too.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable,
)
from unicode_fol_kit.semantics.matrix import (
    TruthMatrix, matrix_value, matrix_is_valid, matrix_is_satisfiable, matrix_entails,
    K3_MATRIX, LP_MATRIX, FDE_MATRIX, MATRICES,
)
from unicode_fol_kit.semantics.manyvalued import is_valid, is_satisfiable, entails

p, q, r = Atom("p", ()), Atom("q", ()), Atom("r", ())


# --------------------------------------------------------------------------- #
# K3 / LP matrices reproduce the existing three-valued decisions.
# --------------------------------------------------------------------------- #

_ATOMS = [p, q, r]


def _rand(depth, rng):
    if depth <= 0 or (depth < 3 and rng.random() < 0.4):
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.18:
        return Not(_rand(depth - 1, rng))
    if k < 0.36:
        return And(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.54:
        return Or(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.72:
        return Implies(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.86:
        return Iff(_rand(depth - 1, rng), _rand(depth - 1, rng))
    return Xor(_rand(depth - 1, rng), _rand(depth - 1, rng))


@pytest.mark.parametrize("logic, matrix", [("K3", K3_MATRIX), ("LP", LP_MATRIX)])
def test_matrix_reproduces_existing_three_valued_decisions(logic, matrix):
    rng = random.Random(hash(logic) & 0xFFFF)
    for _ in range(250):
        f = _rand(3, rng)
        assert matrix_is_valid(f, matrix) == is_valid(f, logic), f.to_unicode_str()
        assert matrix_is_satisfiable(f, matrix) == is_satisfiable(f, logic), f.to_unicode_str()


def test_matrix_entailment_matches_existing():
    rng = random.Random(99)
    for _ in range(150):
        a, b, c = _rand(2, rng), _rand(2, rng), _rand(2, rng)
        for logic, matrix in [("K3", K3_MATRIX), ("LP", LP_MATRIX)]:
            assert matrix_entails([a, b], c, matrix) == entails([a, b], c, logic)


# --------------------------------------------------------------------------- #
# Belnap–Dunn FDE: paraconsistent, paracomplete, and no theorems.
# --------------------------------------------------------------------------- #

def test_fde_paraconsistent_no_explosion():
    # p ∧ ¬p does NOT entail an arbitrary q (FDE tolerates contradictions).
    assert matrix_entails([And(p, Not(p))], q, FDE_MATRIX) is False
    # ...and it is satisfiable (designated at the value B = "both").
    assert matrix_is_satisfiable(And(p, Not(p)), FDE_MATRIX) is True


def test_fde_paracomplete_no_excluded_middle():
    assert matrix_is_valid(Or(p, Not(p)), FDE_MATRIX) is False
    assert matrix_entails([q], Or(p, Not(p)), FDE_MATRIX) is False


def test_fde_has_no_logical_truths():
    # The law of identity p → p is NOT FDE-valid (it takes value N at N).
    assert matrix_is_valid(Implies(p, p), FDE_MATRIX) is False
    assert matrix_is_valid(Implies(And(p, q), p), FDE_MATRIX) is False


def test_fde_material_modus_ponens_fails():
    assert matrix_entails([p, Implies(p, q)], q, FDE_MATRIX) is False


@pytest.mark.parametrize("premises, conclusion", [
    ([And(p, q)], p),                       # ∧-elim
    ([p], Or(p, q)),                        # ∨-intro
    ([Not(Not(p))], p),                     # ¬¬-elim
    ([p], Not(Not(p))),                     # ¬¬-intro
    ([Not(And(p, q))], Or(Not(p), Not(q))),  # De Morgan
    ([Not(Or(p, q))], And(Not(p), Not(q))),  # De Morgan
    ([And(p, Or(q, r))], Or(And(p, q), And(p, r))),  # distribution
])
def test_fde_valid_entailments(premises, conclusion):
    assert matrix_entails(premises, conclusion, FDE_MATRIX) is True


def test_fde_values_and_designation():
    assert set(FDE_MATRIX.values) == {"T", "F", "N", "B"}
    assert FDE_MATRIX.designated == frozenset({"T", "B"})
    # ¬ swaps T/F and fixes N, B.
    assert FDE_MATRIX.neg["T"] == "F" and FDE_MATRIX.neg["F"] == "T"
    assert FDE_MATRIX.neg["N"] == "N" and FDE_MATRIX.neg["B"] == "B"


def test_fde_evaluation_under_a_valuation():
    # p=B (both true&false), q=N (neither). ∧ = (B.t ∧ N.t, B.f ∨ N.f) = (0,1) = F;
    # ∨ = (B.t ∨ N.t, B.f ∧ N.f) = (1,0) = T.
    v = {"p": "B", "q": "N"}
    assert matrix_value(And(p, q), v, FDE_MATRIX) == "F"
    assert matrix_value(Or(p, q), v, FDE_MATRIX) == "T"


# --------------------------------------------------------------------------- #
# Quantifiers and custom matrices.
# --------------------------------------------------------------------------- #

def test_fde_quantifier_folds_over_domain():
    Px = Atom("P", [Variable("x")])
    forall = Quantifier("∀", Variable("x"), Px)
    # ∀x P(x) with P(a)=T, P(b)=F  ->  conj(T, F) = F  (undesignated).
    v = {"P(a)": "T", "P(b)": "F"}
    assert matrix_value(forall, v, FDE_MATRIX, domain={"a", "b"}) == "F"
    exists = Quantifier("∃", Variable("x"), Px)
    assert matrix_value(exists, v, FDE_MATRIX, domain={"a", "b"}) == "T"


def test_custom_matrix_from_functions_validates_closure():
    # A bogus 'conj' that escapes the value set must be rejected at build time.
    with pytest.raises(ValueError, match="not one of the matrix values"):
        TruthMatrix.from_functions(
            "bad", (0, 1), designated=(1,),
            neg=lambda x: 1 - x, conj=lambda a, b: 2, disj=max)
    with pytest.raises(ValueError, match="not a value"):
        TruthMatrix.from_functions(
            "bad2", (0, 1), designated=(5,),
            neg=lambda x: 1 - x, conj=min, disj=max)


def test_classical_two_valued_matrix_matches_tautologies():
    boolean = TruthMatrix.from_functions(
        "B2", (False, True), designated=(True,),
        neg=lambda x: not x, conj=lambda a, b: a and b, disj=lambda a, b: a or b)
    assert matrix_is_valid(Or(p, Not(p)), boolean) is True            # LEM holds classically
    assert matrix_is_valid(Implies(p, p), boolean) is True
    assert matrix_entails([p, Implies(p, q)], q, boolean) is True     # MP holds


def test_matrices_registry():
    assert MATRICES["K3"] is K3_MATRIX
    assert MATRICES["LP"] is LP_MATRIX
    assert MATRICES["FDE"] is FDE_MATRIX
