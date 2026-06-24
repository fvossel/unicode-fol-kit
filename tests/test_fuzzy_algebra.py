"""Łukasiewicz-algebra cross-checks for the fuzzy evaluator (seeded + grid).

Each identity below is a theorem of standard Łukasiewicz logic
(⊗ = max(0, x+y−1), ⊕ = min(1, x+y), ¬x = 1−x, x→y = min(1, 1−x+y),
weak ∧/∨ = min/max, x↔y = 1−|x−y|). They are verified by evaluating both sides
with ``fuzzy_evaluate`` over many random valuations AND a boundary grid, so the
checks pin the implementation to the algebra independently of how each connective
is coded.
"""

import itertools
import random

from unicode_fol_kit.fol.nodes import (
    Atom,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
)
from unicode_fol_kit import fuzzy_evaluate

A = Atom("P", [])
B = Atom("Q", [])
C = Atom("S", [])
_EPS = 1e-9

# Random valuations plus a boundary grid (0, ¼, ½, ¾, 1) on every atom — the grid
# exercises the exact t-norm/t-conorm clamping corners.
_GRID = [0.0, 0.25, 0.5, 0.75, 1.0]


def _valuations(rng, n_random):
    """Yield boundary-grid then random valuations of P, Q, S into [0, 1]."""
    for va, vb, vc in itertools.product(_GRID, repeat=3):
        yield {"P": va, "Q": vb, "S": vc}
    for _ in range(n_random):
        yield {"P": rng.random(), "Q": rng.random(), "S": rng.random()}


def _equal_everywhere(lhs, rhs, rng, n_random=400):
    """True iff fuzzy_evaluate(lhs) ≈ fuzzy_evaluate(rhs) for every valuation."""
    for val in _valuations(rng, n_random):
        if abs(fuzzy_evaluate(lhs, val) - fuzzy_evaluate(rhs, val)) > _EPS:
            return False, val
    return True, None


def test_luk_double_negation():
    """¬¬a ≡ a."""
    rng = random.Random(1)
    ok, val = _equal_everywhere(LukNegation(LukNegation(A)), A, rng)
    assert ok, val


def test_luk_strong_de_morgan():
    """¬(a ⊗ b) ≡ ¬a ⊕ ¬b   and   ¬(a ⊕ b) ≡ ¬a ⊗ ¬b."""
    rng = random.Random(2)
    ok1, v1 = _equal_everywhere(
        LukNegation(StrongConjunction(A, B)),
        StrongDisjunction(LukNegation(A), LukNegation(B)), rng)
    assert ok1, v1
    ok2, v2 = _equal_everywhere(
        LukNegation(StrongDisjunction(A, B)),
        StrongConjunction(LukNegation(A), LukNegation(B)), rng)
    assert ok2, v2


def test_luk_weak_de_morgan():
    """¬(a ∧ b) ≡ ¬a ∨ ¬b   and   ¬(a ∨ b) ≡ ¬a ∧ ¬b  (min/max duality)."""
    rng = random.Random(3)
    ok1, v1 = _equal_everywhere(
        LukNegation(WeakConjunction(A, B)),
        WeakDisjunction(LukNegation(A), LukNegation(B)), rng)
    assert ok1, v1
    ok2, v2 = _equal_everywhere(
        LukNegation(WeakDisjunction(A, B)),
        WeakConjunction(LukNegation(A), LukNegation(B)), rng)
    assert ok2, v2


def test_luk_implication_as_disjunction():
    """The Łukasiewicz residuum a → b ≡ ¬a ⊕ b."""
    rng = random.Random(4)
    ok, val = _equal_everywhere(
        LukImplication(A, B), StrongDisjunction(LukNegation(A), B), rng)
    assert ok, val


def test_luk_equivalence_as_conjoined_implications():
    """a ↔ b ≡ (a → b) ∧ (b → a)  (weak conjunction of the two residua)."""
    rng = random.Random(5)
    ok, val = _equal_everywhere(
        LukEquivalence(A, B),
        WeakConjunction(LukImplication(A, B), LukImplication(B, A)), rng)
    assert ok, val


def test_luk_residuation_adjunction():
    """The defining adjunction: a ⊗ b ≤ c  ⟺  a ≤ (b → c).

    Evaluated as a relation between the fuzzy truth degrees over the grid and
    random valuations; with a shared ε the two ≤-tests must always agree.
    """
    rng = random.Random(6)
    a_and_b = StrongConjunction(A, B)
    b_to_c = LukImplication(B, C)
    for val in _valuations(rng, 600):
        lhs = fuzzy_evaluate(a_and_b, val) <= val["S"] + _EPS      # a⊗b ≤ c
        rhs = val["P"] <= fuzzy_evaluate(b_to_c, val) + _EPS       # a ≤ (b→c)
        assert lhs == rhs, val
