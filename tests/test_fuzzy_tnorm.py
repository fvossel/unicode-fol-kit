"""Tests for the fuzzy t-norm selector (Łukasiewicz / Gödel / product) and the
finite-domain quantifier grounding that makes quantified fuzzy formulas decidable.

The *strong* connectives ⊗ ⊕ → ¬ ↔ take their meaning from the chosen continuous
t-norm; the weak ∧ / ∨ stay min / max and the quantifiers stay inf / sup. The Z3
decider supports the two piecewise-linear t-norms (Łukasiewicz, Gödel) and rejects
the nonlinear product with a pointer to the evaluator. Quantified formulas are
ground over a finite domain before decision.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Variable, Constant, Quantifier, SortedQuantifier,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence, LukNegation,
)
from unicode_fol_kit.semantics.fuzzy import evaluate, ground_quantifiers
from unicode_fol_kit.semantics.tnorm import get_tnorm, TNORMS, LUKASIEWICZ, GODEL, PRODUCT
from unicode_fol_kit.atp.z3_fuzzy import (
    fuzzy_is_valid, fuzzy_is_satisfiable, fuzzy_get_model,
)

p, q, r = Atom("p", ()), Atom("q", ()), Atom("r", ())


# --------------------------------------------------------------------------- #
# Evaluator: each t-norm computes the right degree.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("tnorm, conj, disj, impl, neg", [
    # at p=0.6, q=0.7: ⊗, ⊕, →, ¬p
    ("lukasiewicz", 0.3, 1.0, 1.0, 0.4),     # max(0,.3); min(1,1.3); min(1,1-.6+.7); 1-.6
    ("godel", 0.6, 0.7, 1.0, 0.0),           # min; max; (a<=b?1)=1; (p>0?0)
    ("product", 0.42, 0.88, 1.0, 0.0),       # .42; .6+.7-.42; (a<=b?1); (p>0?0)
])
def test_evaluator_tnorm_degrees(tnorm, conj, disj, impl, neg):
    V = {"p": 0.6, "q": 0.7}
    assert evaluate(StrongConjunction(p, q), V, tnorm=tnorm) == pytest.approx(conj)
    assert evaluate(StrongDisjunction(p, q), V, tnorm=tnorm) == pytest.approx(disj)
    assert evaluate(LukImplication(p, q), V, tnorm=tnorm) == pytest.approx(impl)
    assert evaluate(LukNegation(p), V, tnorm=tnorm) == pytest.approx(neg)


def test_default_is_lukasiewicz_unchanged():
    V = {"p": 0.6, "q": 0.7}
    assert evaluate(StrongConjunction(p, q), V) == pytest.approx(0.3)
    assert evaluate(LukEquivalence(p, q), V) == pytest.approx(1 - abs(0.6 - 0.7))


def test_weak_connectives_are_min_max_for_all_tnorms():
    V = {"p": 0.6, "q": 0.7}
    for tnorm in TNORMS:
        assert evaluate(WeakConjunction(p, q), V, tnorm=tnorm) == pytest.approx(0.6)
        assert evaluate(WeakDisjunction(p, q), V, tnorm=tnorm) == pytest.approx(0.7)


def test_unknown_tnorm_rejected():
    with pytest.raises(ValueError, match="unknown t-norm"):
        evaluate(p, {"p": 0.5}, tnorm="hamacher")
    with pytest.raises(ValueError, match="unknown t-norm"):
        get_tnorm("nope")


# --------------------------------------------------------------------------- #
# Distinguishing validities decided by Z3 (Gödel vs Łukasiewicz).
# --------------------------------------------------------------------------- #

_CONTRACTION = LukImplication(p, StrongConjunction(p, p))      # p → (p ⊗ p)
_IDEMPOTENCE = LukEquivalence(p, StrongConjunction(p, p))      # p ↔ (p ⊗ p)
_PRELINEARITY = StrongDisjunction(LukImplication(p, q), LukImplication(q, p))


@pytest.mark.parametrize("formula, tnorm, expected", [
    (_CONTRACTION, "godel", True),         # ⊗ = min is idempotent ⇒ contraction valid
    (_CONTRACTION, "lukasiewicz", False),
    (_IDEMPOTENCE, "godel", True),
    (_IDEMPOTENCE, "lukasiewicz", False),
    (_PRELINEARITY, "lukasiewicz", True),  # a BL axiom: holds in every BL t-norm
    (_PRELINEARITY, "godel", True),
])
def test_tnorm_distinguishing_validities(formula, tnorm, expected):
    assert fuzzy_is_valid(formula, tnorm=tnorm) is expected


def test_product_is_evaluator_only():
    # The evaluator supports product; the Z3 decider rejects it (nonlinear).
    assert evaluate(StrongConjunction(p, q), {"p": 0.5, "q": 0.5}, tnorm="product") == pytest.approx(0.25)
    with pytest.raises(NotImplementedError, match="product"):
        fuzzy_is_valid(p, tnorm="product")
    with pytest.raises(ValueError, match="unknown t-norm"):
        fuzzy_is_valid(p, tnorm="bogus")


# --------------------------------------------------------------------------- #
# Quantifier grounding makes quantified fuzzy formulas decidable.
# --------------------------------------------------------------------------- #

_x = Variable("x")
_Px = Atom("P", [_x])
_FORALL = Quantifier("∀", _x, _Px)
_EXISTS = Quantifier("∃", _x, _Px)


def test_ground_quantifiers_folds_to_weak_connectives():
    grounded = ground_quantifiers(_FORALL, domain={"a", "b"})
    # ∀ becomes a weak conjunction of the instances.
    assert isinstance(grounded, WeakConjunction)
    assert ground_quantifiers(_EXISTS, domain={"a"}) == Atom("P", [Constant("a")])


def test_quantified_fuzzy_decidable_via_grounding():
    Pa = Atom("P", [Constant("a")])
    # ∀x P(x) → P(a) is valid (degree 1) on any domain containing a.
    assert fuzzy_is_valid(LukImplication(_FORALL, Pa), domain={"a", "b"}) is True
    # ∀x P(x) is satisfiable to degree 1 but not valid.
    assert fuzzy_is_satisfiable(_FORALL, domain={"a", "b"}) is True
    assert fuzzy_is_valid(_FORALL, domain={"a", "b"}) is False
    m = fuzzy_get_model(_FORALL, threshold=0.5, domain={"a", "b"})
    assert m is not None and m["degree"] >= 0.5


def test_quantifier_without_domain_raises():
    with pytest.raises(ValueError, match="domain"):
        fuzzy_is_valid(_FORALL)


def test_sorted_quantifier_grounding():
    sx = SortedQuantifier("∀", _x, "Human", _Px)
    Pa = Atom("P", [Constant("alice")])
    assert fuzzy_is_valid(LukImplication(sx, Pa),
                          sort_universes={"Human": {"alice", "bob"}}) is True


# --------------------------------------------------------------------------- #
# Differential: the Z3 Gödel decision agrees with the evaluator at the model.
# --------------------------------------------------------------------------- #

_ATOMS = [p, q, r]


def _rand(depth, rng):
    if depth <= 0 or rng.random() < 0.4:
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.18:
        return LukNegation(_rand(depth - 1, rng))
    if k < 0.36:
        return StrongConjunction(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.54:
        return StrongDisjunction(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.72:
        return LukImplication(_rand(depth - 1, rng), _rand(depth - 1, rng))
    if k < 0.86:
        return LukEquivalence(_rand(depth - 1, rng), _rand(depth - 1, rng))
    return WeakConjunction(_rand(depth - 1, rng), _rand(depth - 1, rng))


@pytest.mark.parametrize("tnorm", ["lukasiewicz", "godel"])
def test_z3_model_matches_evaluator(tnorm):
    rng = random.Random(hash(tnorm) & 0xFFFF)
    checked = 0
    for _ in range(60):
        f = _rand(3, rng)
        m = fuzzy_get_model(f, threshold=0.5, tnorm=tnorm)
        if m is None:
            continue
        val = {k: v for k, v in m.items() if k != "degree"}
        assert evaluate(f, val, tnorm=tnorm) == pytest.approx(m["degree"], abs=1e-6), \
            f.to_unicode_str()
        checked += 1
    assert checked > 0
