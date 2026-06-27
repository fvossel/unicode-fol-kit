"""Tests for the Fitch backtracking proof searcher (atp.fitch_search).

The decisive property is SOUNDNESS: every proof the searcher returns is re-validated
by ``check_proof`` (so it is a genuine Fitch proof), and — the randomised cross-check
— ``fitch_prove`` never claims a non-theorem: ``fitch_prove(Γ, φ)`` implies Z3 agrees
that ``⋀Γ → φ`` is valid. Completeness is best-effort (bounded), so the curated
theorems double as a regression set for what the search *does* find.
"""

from functools import reduce
import random

import pytest

from unicode_fol_kit import is_valid
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant,
)
from unicode_fol_kit.atp.fitch_search import find_fitch_proof, fitch_prove, is_valid_fitch
from unicode_fol_kit.atp.fitch import verify_proof

P, Q, R = Atom("P", ()), Atom("Q", ()), Atom("R", ())
x = Variable("x")
a = Constant("a")


def ALL(v, f):
    return Quantifier("∀", v, f)


def EX(v, f):
    return Quantifier("∃", v, f)


def Px(t):
    return Atom("P", [t])


def Qx(t):
    return Atom("Q", [t])


THEOREMS = [
    ([], Implies(P, P), "→I"),
    ([], Or(P, Not(P)), "LEM via RAA"),
    ([], Implies(Implies(Implies(P, Q), P), P), "Peirce"),
    ([], Iff(P, P), "↔I"),
    ([And(P, Q)], And(Q, P), "∧ commutes"),
    ([P, Implies(P, Q)], Q, "modus ponens"),
    ([Implies(P, Q), Implies(Q, R)], Implies(P, R), "hypothetical syllogism"),
    ([Not(Or(P, Q))], And(Not(P), Not(Q)), "De Morgan ¬∨"),
    ([Not(And(P, Q))], Or(Not(P), Not(Q)), "De Morgan ¬∧"),
    ([Not(Not(P))], P, "DNE"),
    ([Or(P, Q), Implies(P, R), Implies(Q, R)], R, "∨ elimination"),
    ([ALL(x, Px(x))], Px(a), "∀ instantiation"),
    ([ALL(x, Implies(Px(x), Qx(x))), ALL(x, Px(x))], ALL(x, Qx(x)), "∀ distribution"),
    ([Px(a)], EX(x, Px(x)), "∃ introduction"),
    ([EX(x, Px(x)), ALL(x, Implies(Px(x), Qx(x)))], EX(x, Qx(x)), "∃ elimination"),
]

NON_THEOREMS = [
    ([P], Q),
    ([], P),
    ([Implies(P, Q)], P),
    ([Or(P, Q)], P),
    ([ALL(x, Px(x))], EX(x, Qx(x))),
]


@pytest.mark.parametrize("premises,goal,name", THEOREMS, ids=[t[2] for t in THEOREMS])
def test_finds_theorem_and_proof_is_valid(premises, goal, name):
    proof = find_fitch_proof(premises, goal, max_depth=10)
    assert proof is not None, f"no proof found for {name}"
    result = verify_proof(proof)
    assert result.ok, f"assembled proof for {name} failed checking: {result.error}"
    # The certified sequent must be exactly premises ⊢ goal.
    assert result.conclusion == goal
    assert set(result.premises) == set(premises)


@pytest.mark.parametrize("premises,goal", NON_THEOREMS)
def test_non_theorems_not_found(premises, goal):
    assert find_fitch_proof(premises, goal, max_depth=7) is None


# ---------------------------------------------------------------------------
# Randomised soundness cross-check: fitch_prove ⇒ Z3-valid (no false positives)
# ---------------------------------------------------------------------------

_ATOMS = [P, Q, R, Atom("S", ())]


def _rand(rng, depth):
    if depth <= 0 or rng.random() < 0.4:
        atom = rng.choice(_ATOMS)
        return Not(atom) if rng.random() < 0.25 else atom
    op = rng.choice([And, Or, Implies, Iff, "not"])
    if op == "not":
        return Not(_rand(rng, depth - 1))
    return op(_rand(rng, depth - 1), _rand(rng, depth - 1))


def test_random_propositional_soundness():
    rng = random.Random(20260627)
    proved = 0
    for _ in range(400):
        f = _rand(rng, rng.randint(1, 3))
        if fitch_prove([], f, max_depth=8):
            proved += 1
            # Soundness: a found proof's goal MUST be a genuine validity.
            assert is_valid(f), f"unsound: claimed {f.to_unicode_str()} provable"
            # And the returned proof must actually check.
            assert verify_proof(find_fitch_proof([], f, max_depth=8)).ok
    assert proved > 0  # non-vacuous


def test_random_entailment_soundness():
    rng = random.Random(99)
    for _ in range(300):
        prems = [_rand(rng, rng.randint(0, 2)) for _ in range(rng.randint(1, 3))]
        goal = _rand(rng, rng.randint(1, 2))
        if fitch_prove(prems, goal, max_depth=7):
            big = Implies(reduce(And, prems), goal)
            assert is_valid(big), (
                f"unsound: {[p.to_unicode_str() for p in prems]} ⊢ {goal.to_unicode_str()}")


def test_is_valid_fitch_has_high_recall_on_shallow_tautologies():
    # The search is sound but bounded-incomplete, so it need not find EVERY tautology
    # (deeply nested biconditionals are the hard case). It should, however, find the
    # large majority of shallow ones — this pins best-effort completeness.
    rng = random.Random(7)
    tautologies = found = 0
    for _ in range(120):
        f = _rand(rng, 2)
        if is_valid(f):
            tautologies += 1
            if is_valid_fitch(f, max_depth=8):
                found += 1
    assert tautologies > 0
    assert found / tautologies >= 0.75, f"low recall: {found}/{tautologies}"


def test_top_level_exports():
    import unicode_fol_kit as u
    for name in ("find_fitch_proof", "fitch_prove", "is_valid_fitch"):
        assert hasattr(u, name) and name in u.__all__, name
