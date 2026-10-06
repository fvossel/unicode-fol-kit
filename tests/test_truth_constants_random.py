"""Random formulas over ``P``, ``Q``, ``$true`` and ``$false``, decided by every route.

The oracle is a plain evaluator written in this file: the classical one reads the two
constants as ``True`` and ``False``, the three-valued one as the values ``1`` and
``0`` of strong Kleene (K3 designates ``1``, LP designates ``1`` and ``½``).
Every route that decides must agree with it; a prover that can fail to find a
proof must never prove what the oracle calls invalid.
"""

import random
from itertools import product

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, And, Or, Implies, Iff, Box, Diamond

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())
Q = Atom("Q", ())
LEAVES = (P, Q, T, F)
SEEDS = range(120)


def random_formula(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(LEAVES)
    kind = rng.choice(["not", "and", "or", "imp", "iff"])
    if kind == "not":
        return Not(random_formula(rng, depth - 1))
    node = {"and": And, "or": Or, "imp": Implies, "iff": Iff}[kind]
    return node(random_formula(rng, depth - 1), random_formula(rng, depth - 1))


# ---------------------------------------------------------------------------
# Oracles
# ---------------------------------------------------------------------------

def classical_value(node, valuation):
    if isinstance(node, Atom):
        if node.predicate == "$true":
            return True
        if node.predicate == "$false":
            return False
        return valuation[node.predicate]
    if isinstance(node, Not):
        return not classical_value(node.formula, valuation)
    left, right = classical_value(node.left, valuation), classical_value(node.right, valuation)
    if isinstance(node, And):
        return left and right
    if isinstance(node, Or):
        return left or right
    if isinstance(node, Implies):
        return (not left) or right
    return left == right                     # Iff


def classically_valid(node):
    return all(classical_value(node, {"P": p, "Q": q})
               for p, q in product((False, True), repeat=2))


def kleene_value(node, valuation):
    """Strong Kleene on {0, ½, 1}: ¬a = 1-a, ∧ = min, ∨ = max, a→b = max(1-a, b)."""
    if isinstance(node, Atom):
        if node.predicate == "$true":
            return 1.0
        if node.predicate == "$false":
            return 0.0
        return valuation[node.predicate]
    if isinstance(node, Not):
        return 1.0 - kleene_value(node.formula, valuation)
    a, b = kleene_value(node.left, valuation), kleene_value(node.right, valuation)
    if isinstance(node, And):
        return min(a, b)
    if isinstance(node, Or):
        return max(a, b)
    if isinstance(node, Implies):
        return max(1.0 - a, b)
    return min(max(1.0 - a, b), max(1.0 - b, a))      # Iff = (a→b) ∧ (b→a)


def kleene_valid(node, designated):
    return all(kleene_value(node, {"P": p, "Q": q}) in designated
               for p, q in product((0.0, 0.5, 1.0), repeat=2))


# ---------------------------------------------------------------------------
# Classical routes
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seed", SEEDS)
def test_classical_routes_agree_with_the_evaluator(seed):
    from unicode_fol_kit.semantics.truthtable import is_tautology
    from unicode_fol_kit.atp.z3_models import is_valid
    from unicode_fol_kit.atp.tableau import prove_tableau
    from unicode_fol_kit.atp.resolution import prove as resolution_prove
    formula = random_formula(random.Random(seed), 3)
    expected = classically_valid(formula)
    assert is_tautology(formula, "classical") is expected, formula.to_unicode_str()
    assert is_valid(formula) is expected, formula.to_unicode_str()
    assert prove_tableau([], formula) is expected, formula.to_unicode_str()
    assert resolution_prove([], formula) is expected, formula.to_unicode_str()


@pytest.mark.parametrize("seed", SEEDS)
def test_entailment_routes_agree_with_the_evaluator(seed):
    from unicode_fol_kit.atp.tableau import prove_tableau
    from unicode_fol_kit.atp.resolution import prove as resolution_prove
    from unicode_fol_kit.atp.z3_models import is_valid
    rng = random.Random(10_000 + seed)
    premise, goal = random_formula(rng, 2), random_formula(rng, 2)
    expected = classically_valid(Implies(premise, goal))
    text = f"{premise.to_unicode_str()} ⊢ {goal.to_unicode_str()}"
    assert prove_tableau([premise], goal) is expected, text
    assert resolution_prove([premise], goal) is expected, text
    assert is_valid(Implies(premise, goal)) is expected, text


@pytest.mark.parametrize("seed", SEEDS)
def test_a_found_fitch_proof_is_sound_and_checks(seed):
    from unicode_fol_kit.atp.fitch_search import find_fitch_proof
    from unicode_fol_kit.atp.fitch import verify_proof
    formula = random_formula(random.Random(20_000 + seed), 3)
    proof = find_fitch_proof([], formula)
    if proof is None:
        return                       # the search is bounded: no proof found says nothing
    assert classically_valid(formula), formula.to_unicode_str()
    result = verify_proof(proof)
    assert result.ok, (formula.to_unicode_str(), result.error)


# ---------------------------------------------------------------------------
# Intuitionistic routes
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seed", SEEDS)
def test_the_two_intuitionistic_routes_agree_and_imply_classical_validity(seed):
    from unicode_fol_kit.atp.lj import int_decide
    from unicode_fol_kit.semantics.intuitionistic import int_valid
    formula = random_formula(random.Random(30_000 + seed), 3)
    sequent_route, kripke_route = int_decide(formula), int_valid(formula)
    assert sequent_route == kripke_route, formula.to_unicode_str()
    if sequent_route:
        assert classically_valid(formula), formula.to_unicode_str()


# ---------------------------------------------------------------------------
# Three-valued routes: two implementations of the same tables
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seed", SEEDS)
def test_k3_and_lp_agree_with_the_evaluator(seed):
    from unicode_fol_kit.semantics.manyvalued import is_valid
    from unicode_fol_kit.semantics.matrix import matrix_entails, K3_MATRIX, LP_MATRIX
    from unicode_fol_kit.semantics.truthtable import is_tautology
    formula = random_formula(random.Random(40_000 + seed), 3)
    k3, lp = kleene_valid(formula, {1.0}), kleene_valid(formula, {1.0, 0.5})
    text = formula.to_unicode_str()
    assert is_valid(formula, "K3") is k3, text
    assert is_valid(formula, "LP") is lp, text
    assert matrix_entails([], formula, K3_MATRIX) is k3, text
    assert matrix_entails([], formula, LP_MATRIX) is lp, text
    assert is_tautology(formula, "K3") is k3, text
    assert is_tautology(formula, "LP") is lp, text


# ---------------------------------------------------------------------------
# Modal routes against enumerated Kripke models
# ---------------------------------------------------------------------------

def random_modal(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(LEAVES)
    kind = rng.choice(["not", "and", "or", "imp", "box", "dia"])
    if kind == "not":
        return Not(random_modal(rng, depth - 1))
    if kind == "box":
        return Box(random_modal(rng, depth - 1))
    if kind == "dia":
        return Diamond(random_modal(rng, depth - 1))
    node = {"and": And, "or": Or, "imp": Implies}[kind]
    return node(random_modal(rng, depth - 1), random_modal(rng, depth - 1))


def enumerated_countermodel_exists(formula, max_worlds=2):
    """Some Kripke model with at most ``max_worlds`` worlds falsifies ``formula`` at a world."""
    from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
    for size in range(1, max_worlds + 1):
        worlds = list(range(size))
        edges = [(a, b) for a in worlds for b in worlds]
        for mask in product((False, True), repeat=len(edges)):
            relation = {e for e, on in zip(edges, mask) if on}
            for bits in product((False, True), repeat=2 * size):
                valuation = {w: {name for name, on in zip(("P", "Q"), bits[2 * w:2 * w + 2]) if on}
                             for w in worlds}
                model = KripkeModel(worlds, {"alethic": relation}, valuation)
                if any(not satisfies_modal(formula, model, w) for w in worlds):
                    return True
    return False


@pytest.mark.parametrize("seed", range(60))
def test_modal_tableau_never_proves_what_an_enumerated_model_refutes(seed):
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid
    formula = random_modal(random.Random(50_000 + seed), 2)
    refuted = enumerated_countermodel_exists(formula)
    valid = is_modal_valid(formula)
    # a model that falsifies the formula at some world means the formula is not
    # valid; a valid formula has no countermodel anywhere
    assert not (refuted and valid), formula.to_unicode_str()


def test_the_constants_are_valid_or_invalid_in_every_modal_model():
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid
    # □⊤ and ◇⊤ differ at a dead end: □⊤ is valid, ◇⊤ is not (needs a successor)
    assert is_modal_valid(Box(T))
    assert not is_modal_valid(Diamond(T))
    # □⊥ is not valid (a successor exists in some model), ◇⊥ is false everywhere
    assert not is_modal_valid(Box(F))
    assert is_modal_valid(Not(Diamond(F)))
    # the constants are rigid: □⊤ ↔ ⊤ and ◇⊥ ↔ ⊥ hold at every world
    assert is_modal_valid(Iff(Box(T), T))
    assert is_modal_valid(Iff(Diamond(F), F))
    assert enumerated_countermodel_exists(Diamond(T))
    assert not enumerated_countermodel_exists(Box(T))
