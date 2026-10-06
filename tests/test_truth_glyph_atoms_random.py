"""Random formulas over ``P``, ``Q``, ``⊤``, ``⊥``, ``$true`` and ``$false``, decided by every route.

The atoms named like the glyphs are the truth constants, and so are the TPTP words, so a formula
may spell the same constant either way and mix the spellings. The oracle is the evaluator of
``test_truth_constants_random`` (a plain evaluator written there, sharing no code with any route)
run on the same formula with every glyph spelled as its TPTP word. Every route that decides must
agree with it, and a prover that can fail to find a proof must never prove what the oracle calls
invalid.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import And, Atom, Box, Diamond, Iff, Implies, Not, Or
from test_truth_constants_random import (
    classically_valid, enumerated_countermodel_exists, kleene_valid,
)

LEAVES = (Atom("P", ()), Atom("Q", ()), Atom("⊤", ()), Atom("⊥", ()),
          Atom("$true", ()), Atom("$false", ()))
SEEDS = range(120)
_WORDS = {"⊤": "$true", "⊥": "$false"}


def random_formula(rng, depth, modal=False):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(LEAVES)
    kinds = ["not", "and", "or", "imp", "iff"] + (["box", "dia"] if modal else [])
    kind = rng.choice(kinds)
    if kind == "not":
        return Not(random_formula(rng, depth - 1, modal))
    if kind == "box":
        return Box(random_formula(rng, depth - 1, modal))
    if kind == "dia":
        return Diamond(random_formula(rng, depth - 1, modal))
    node = {"and": And, "or": Or, "imp": Implies, "iff": Iff}[kind]
    return node(random_formula(rng, depth - 1, modal), random_formula(rng, depth - 1, modal))


def in_words(node):
    """``node`` with every glyph-named atom spelled as its TPTP word, for the oracle."""
    if isinstance(node, Atom):
        return Atom(_WORDS[node.predicate], ()) if node.predicate in _WORDS else node
    return node.map_children(in_words)


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
    expected = classically_valid(in_words(formula))
    text = formula.to_unicode_str()
    assert is_tautology(formula, "classical") is expected, text
    assert is_valid(formula) is expected, text
    assert prove_tableau([], formula) is expected, text
    assert resolution_prove([], formula) is expected, text


@pytest.mark.parametrize("seed", SEEDS)
def test_entailment_routes_agree_with_the_evaluator(seed):
    from unicode_fol_kit.atp.tableau import prove_tableau
    from unicode_fol_kit.atp.resolution import prove as resolution_prove
    from unicode_fol_kit.atp.z3_models import is_valid
    rng = random.Random(10_000 + seed)
    premise, goal = random_formula(rng, 2), random_formula(rng, 2)
    expected = classically_valid(in_words(Implies(premise, goal)))
    text = f"{premise.to_unicode_str()} ⊢ {goal.to_unicode_str()}"
    assert prove_tableau([premise], goal) is expected, text
    assert resolution_prove([premise], goal) is expected, text
    assert is_valid(Implies(premise, goal)) is expected, text


@pytest.mark.parametrize("seed", SEEDS)
def test_the_model_finder_finds_a_countermodel_exactly_when_the_formula_is_invalid(seed):
    from unicode_fol_kit.semantics.modelfinder import find_countermodel
    formula = random_formula(random.Random(60_000 + seed), 3)
    expected = classically_valid(in_words(formula))
    assert (find_countermodel([], formula) is None) is expected, formula.to_unicode_str()


@pytest.mark.parametrize("seed", SEEDS)
def test_a_found_fitch_proof_is_sound_and_checks(seed):
    from unicode_fol_kit.atp.fitch_search import find_fitch_proof
    from unicode_fol_kit.atp.fitch import verify_proof
    formula = random_formula(random.Random(20_000 + seed), 3)
    proof = find_fitch_proof([], formula)
    if proof is None:
        return                       # the search is bounded: no proof found says nothing
    assert classically_valid(in_words(formula)), formula.to_unicode_str()
    result = verify_proof(proof)
    assert result.ok, (formula.to_unicode_str(), result.error)


# ---------------------------------------------------------------------------
# Intuitionistic and three-valued routes
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seed", SEEDS)
def test_the_two_intuitionistic_routes_agree_and_imply_classical_validity(seed):
    from unicode_fol_kit.atp.lj import int_decide
    from unicode_fol_kit.semantics.intuitionistic import int_valid
    formula = random_formula(random.Random(30_000 + seed), 3)
    sequent_route, kripke_route = int_decide(formula), int_valid(formula)
    assert sequent_route == kripke_route, formula.to_unicode_str()
    if sequent_route:
        assert classically_valid(in_words(formula)), formula.to_unicode_str()


@pytest.mark.parametrize("seed", SEEDS)
def test_k3_and_lp_agree_with_the_evaluator(seed):
    from unicode_fol_kit.semantics.manyvalued import is_valid
    from unicode_fol_kit.semantics.matrix import matrix_entails, K3_MATRIX, LP_MATRIX
    formula = random_formula(random.Random(40_000 + seed), 3)
    words = in_words(formula)
    k3, lp = kleene_valid(words, {1.0}), kleene_valid(words, {1.0, 0.5})
    text = formula.to_unicode_str()
    assert is_valid(formula, "K3") is k3, text
    assert is_valid(formula, "LP") is lp, text
    assert matrix_entails([], formula, K3_MATRIX) is k3, text
    assert matrix_entails([], formula, LP_MATRIX) is lp, text


# ---------------------------------------------------------------------------
# Modal routes against enumerated Kripke models
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("seed", range(60))
def test_modal_tableau_never_proves_what_an_enumerated_model_refutes(seed):
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid
    formula = random_formula(random.Random(50_000 + seed), 2, modal=True)
    refuted = enumerated_countermodel_exists(formula)
    valid = is_modal_valid(formula)
    assert not (refuted and valid), formula.to_unicode_str()


def test_the_glyph_constants_are_valid_or_invalid_in_every_modal_model():
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid
    top, bottom = Atom("⊤", ()), Atom("⊥", ())
    # □⊤ and ◇⊤ differ at a dead end: □⊤ is valid, ◇⊤ is not (needs a successor)
    assert is_modal_valid(Box(top)) and not is_modal_valid(Diamond(top))
    # □⊥ is not valid (a successor exists in some model), ◇⊥ is false everywhere
    assert not is_modal_valid(Box(bottom)) and is_modal_valid(Not(Diamond(bottom)))
    # the constants are rigid: □⊤ ↔ ⊤ and ◇⊥ ↔ ⊥ hold at every world
    assert is_modal_valid(Iff(Box(top), top)) and is_modal_valid(Iff(Diamond(bottom), bottom))
    assert enumerated_countermodel_exists(Diamond(top)) and not enumerated_countermodel_exists(Box(top))
