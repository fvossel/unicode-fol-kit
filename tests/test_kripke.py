"""Tests for the Kripke (possible-worlds) evaluator, semantics/kripke.py.

The truths asserted here are hand-computed against small, explicit frames, plus
two schematic checks (the K axiom and the box/diamond and G/F dualities) over
several random frames.
"""

import random

import pytest

from unicode_fol_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, models_at, reflexive_transitive_closure,
)
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Not, And, Or, Implies, Iff,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Quantifier, Variable, SortedQuantifier,
    LukNegation, Lambda, LambdaVar,
)

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])


# ---------------------------------------------------------------------------
# Helpers for random-frame schematic checks
# ---------------------------------------------------------------------------

def _random_alethic_model(rng, n_worlds=3):
    """Build a random alethic Kripke model over worlds 0..n-1 with atoms P, Q."""
    worlds = list(range(n_worlds))
    edges = {(a, b) for a in worlds for b in worlds if rng.random() < 0.5}
    valuation = {}
    for w in worlds:
        true_here = set()
        if rng.random() < 0.5:
            true_here.add("P")
        if rng.random() < 0.5:
            true_here.add("Q")
        valuation[w] = true_here
    return KripkeModel(worlds=worlds, relations={"alethic": edges}, valuation=valuation)


def _random_temporal_model(rng, n_worlds=4):
    """Build a random temporal Kripke model over worlds 0..n-1 with atom P."""
    worlds = list(range(n_worlds))
    edges = {(a, b) for a in worlds for b in worlds if rng.random() < 0.4}
    valuation = {w: ({"P"} if rng.random() < 0.5 else set()) for w in worlds}
    return KripkeModel(worlds=worlds, relations={"temporal": edges}, valuation=valuation)


# ---------------------------------------------------------------------------
# Schematic validity: the K axiom
# ---------------------------------------------------------------------------

def test_k_axiom_is_frame_valid():
    """□(p→q) → (□p→□q) is true at every world of many random alethic frames."""
    rng = random.Random(20240623)
    k_axiom = Implies(
        Box(Implies(P, Q)),
        Implies(Box(P), Box(Q)),
    )
    for _ in range(200):
        model = _random_alethic_model(rng, n_worlds=rng.randint(1, 4))
        for w in model.worlds:
            assert satisfies_modal(k_axiom, model, w) is True


def test_diamond_box_duality_random():
    """◇p has the same truth as ¬□¬p at every world of many random frames."""
    rng = random.Random(99)
    lhs = Diamond(P)
    rhs = Not(Box(Not(P)))
    for _ in range(200):
        model = _random_alethic_model(rng, n_worlds=rng.randint(1, 4))
        for w in model.worlds:
            assert satisfies_modal(lhs, model, w) == satisfies_modal(rhs, model, w)


def test_eventually_always_duality_random():
    """Fp has the same truth as ¬G¬p at every world of many random temporal frames."""
    rng = random.Random(7)
    lhs = Eventually(P)
    rhs = Not(Always(Not(P)))
    for _ in range(200):
        model = _random_temporal_model(rng, n_worlds=rng.randint(1, 5))
        for w in model.worlds:
            assert satisfies_modal(lhs, model, w) == satisfies_modal(rhs, model, w)


# ---------------------------------------------------------------------------
# A concrete alethic frame, all truths computed by hand
# ---------------------------------------------------------------------------

def test_concrete_alethic_frame():
    """Three-world frame 0->1, 0->2 with P at 1 only, Q at 1 and 2.

    Successors of 0 are {1, 2}; of 1 and 2 none.
        - □P @0 false (P fails at 2); ◇P @0 true (P at 1).
        - □Q @0 true (Q at both 1 and 2); ◇Q @0 true.
        - □P @1 and □P @2 true vacuously (no successors).
        - ◇P @1 false (no successors).
    """
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"alethic": {(0, 1), (0, 2)}},
        valuation={1: {"P", "Q"}, 2: {"Q"}},
    )
    assert satisfies_modal(Box(P), model, 0) is False
    assert satisfies_modal(Diamond(P), model, 0) is True
    assert satisfies_modal(Box(Q), model, 0) is True
    assert satisfies_modal(Diamond(Q), model, 0) is True
    assert satisfies_modal(Box(P), model, 1) is True
    assert satisfies_modal(Box(P), model, 2) is True
    assert satisfies_modal(Diamond(P), model, 1) is False
    # A frame where ◇p but not □p, at world 0.
    assert (satisfies_modal(Diamond(P), model, 0)
            and not satisfies_modal(Box(P), model, 0))


def test_reflexive_frame_gives_factivity_for_knows():
    """On a reflexive K-frame, K_a p -> p holds at every world (factivity / T)."""
    # Reflexive epistemic relation for agent alice over {0,1,2}.
    refl = {(w, w) for w in (0, 1, 2)} | {(0, 1), (1, 0)}
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"K:alice": refl},
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )
    factivity = Implies(Knows("alice", P), P)
    for w in model.worlds:
        assert satisfies_modal(factivity, model, w) is True
    # K_alice P is true at 0 (both 0 and 1 accessible have P), false at 2.
    assert satisfies_modal(Knows("alice", P), model, 0) is True
    assert satisfies_modal(Knows("alice", P), model, 2) is False


def test_knows_and_believes_use_distinct_relations():
    """Knows reads K:agent, Believes reads B:agent; agents are independent."""
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={
            "K:alice": {(0, 1)},
            "B:alice": {(0, 2)},
            "K:bob": {(0, 0)},
        },
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )
    # alice knows P at 0 (succ {1}, P there) but does not believe P (succ {2}, no P).
    assert satisfies_modal(Knows("alice", P), model, 0) is True
    assert satisfies_modal(Believes("alice", P), model, 0) is False
    # bob (reflexive at 0) knows P.
    assert satisfies_modal(Knows("bob", P), model, 0) is True
    # A different agent with no relation: universal over empty => vacuously true.
    assert satisfies_modal(Knows("carol", Atom("Z", [])), model, 0) is True


# ---------------------------------------------------------------------------
# Temporal operators on explicit frames
# ---------------------------------------------------------------------------

def test_next_universal_over_temporal_successors():
    """Next φ is true iff φ holds at every immediate temporal successor."""
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"temporal": {(0, 1), (0, 2)}},
        valuation={1: {"P"}, 2: {"P", "Q"}},
    )
    assert satisfies_modal(Next(P), model, 0) is True   # P at both 1 and 2
    assert satisfies_modal(Next(Q), model, 0) is False  # Q fails at 1
    # No successors => vacuously true.
    assert satisfies_modal(Next(P), model, 1) is True


def test_always_eventually_over_chain():
    """Linear chain 0->1->2->3; Always/Eventually over reflexive-transitive reach."""
    model = KripkeModel(
        worlds={0, 1, 2, 3},
        relations={"temporal": {(0, 1), (1, 2), (2, 3)}},
        valuation={0: {"P"}, 1: {"P"}, 2: {"P"}, 3: {"P", "Q"}},
    )
    # Always P @0: P at 0,1,2,3 => True.
    assert satisfies_modal(Always(P), model, 0) is True
    # Always Q @0: Q only at 3 => False.
    assert satisfies_modal(Always(Q), model, 0) is False
    # Eventually Q @0: Q at 3 reachable => True.
    assert satisfies_modal(Eventually(Q), model, 0) is True
    # Eventually Q @3 (itself reflexive) => True; @2 => True (3 reachable).
    assert satisfies_modal(Eventually(Q), model, 2) is True
    # Always Q @3: only world reachable is 3, Q there => True.
    assert satisfies_modal(Always(Q), model, 3) is True


def test_always_includes_current_world_reflexively():
    """Always is reflexive: φ must hold at the current world too."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"temporal": {(0, 1)}},
        valuation={0: set(), 1: {"P"}},
    )
    # P holds at 1 but not at 0; Always P @0 must be False (current world counts).
    assert satisfies_modal(Always(P), model, 0) is False
    assert satisfies_modal(Eventually(P), model, 0) is True  # P reachable at 1


def test_always_handles_cycles():
    """Closure terminates on a cyclic temporal frame and is correct."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"temporal": {(0, 1), (1, 0)}},
        valuation={0: {"P"}, 1: {"P"}},
    )
    assert satisfies_modal(Always(P), model, 0) is True
    model_bad = KripkeModel(
        worlds={0, 1},
        relations={"temporal": {(0, 1), (1, 0)}},
        valuation={0: {"P"}, 1: set()},
    )
    assert satisfies_modal(Always(P), model_bad, 0) is False
    assert satisfies_modal(Eventually(P), model_bad, 0) is True


# ---------------------------------------------------------------------------
# Until
# ---------------------------------------------------------------------------

def test_until_on_linear_chain_true():
    """Chain 0->1->2 with ψ only at 2 and φ at 0,1 => Until(φ,ψ) true at 0."""
    phi = P
    psi = Q
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"temporal": {(0, 1), (1, 2)}},
        valuation={0: {"P"}, 1: {"P"}, 2: {"Q"}},
    )
    assert satisfies_modal(Until(phi, psi), model, 0) is True
    # At 1: φ at 1, ψ at 2 => still true.
    assert satisfies_modal(Until(phi, psi), model, 1) is True
    # At 2: ψ already true => true (n=0).
    assert satisfies_modal(Until(phi, psi), model, 2) is True


def test_until_false_when_phi_fails_before_psi():
    """If φ fails at an intermediate world before ψ, Until is false."""
    phi = P
    psi = Q
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"temporal": {(0, 1), (1, 2)}},
        valuation={0: {"P"}, 1: set(), 2: {"Q"}},  # φ fails at 1
    )
    assert satisfies_modal(Until(phi, psi), model, 0) is False


def test_until_psi_now_is_true_regardless_of_phi():
    """Strong Until succeeds at n=0 when ψ already holds, even if φ is false."""
    model = KripkeModel(
        worlds={0},
        relations={"temporal": set()},
        valuation={0: {"Q"}},  # ψ true, φ false, no successors
    )
    assert satisfies_modal(Until(P, Q), model, 0) is True


def test_until_false_when_psi_unreachable():
    """If ψ never holds on any path, Until is false even with φ everywhere."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"temporal": {(0, 1), (1, 1)}},
        valuation={0: {"P"}, 1: {"P"}},  # ψ=Q never true
    )
    assert satisfies_modal(Until(P, Q), model, 0) is False


# ---------------------------------------------------------------------------
# Defaults / ergonomics
# ---------------------------------------------------------------------------

def test_missing_relation_and_valuation_defaults():
    """Missing relation => empty (Box vacuously true, Diamond false); missing val => false."""
    model = KripkeModel(worlds={0})
    assert satisfies_modal(Box(P), model, 0) is True
    assert satisfies_modal(Diamond(P), model, 0) is False
    assert satisfies_modal(P, model, 0) is False  # missing valuation => atom false


def test_atom_with_arguments_key():
    """A ground atom with arguments is keyed by its Unicode rendering."""
    likes = Atom("Likes", [Constant("a"), Constant("b")])
    key = likes.to_unicode_str()
    model = KripkeModel(worlds={0}, valuation={0: {key}})
    assert satisfies_modal(likes, model, 0) is True
    assert satisfies_modal(Not(likes), model, 0) is False


def test_classical_connectives_recurse_same_world():
    """And/Or/Implies/Iff/Not evaluate at the same world."""
    model = KripkeModel(worlds={0}, valuation={0: {"P"}})
    assert satisfies_modal(And(P, Not(Q)), model, 0) is True
    assert satisfies_modal(Or(Q, P), model, 0) is True
    assert satisfies_modal(Implies(Q, P), model, 0) is True
    assert satisfies_modal(Iff(P, Q), model, 0) is False


def test_models_at_alias():
    """models_at is an alias of satisfies_modal."""
    model = KripkeModel(worlds={0}, valuation={0: {"P"}})
    assert models_at(P, model, 0) == satisfies_modal(P, model, 0)


# ---------------------------------------------------------------------------
# Reflexive-transitive-closure helper
# ---------------------------------------------------------------------------

def test_reflexive_transitive_closure_basic():
    """Closure includes the sources and everything reachable, terminating on cycles."""
    edges = {(0, 1), (1, 2), (2, 0)}
    assert reflexive_transitive_closure(edges, [0]) == {0, 1, 2}
    assert reflexive_transitive_closure(edges, [2]) == {0, 1, 2}
    assert reflexive_transitive_closure({(0, 1)}, [1]) == {1}
    assert reflexive_transitive_closure(set(), [5]) == {5}


def test_closure_does_not_mutate_input():
    """The closure helper must not mutate the caller's edge set."""
    edges = {(0, 1)}
    snapshot = set(edges)
    reflexive_transitive_closure(edges, [0])
    assert edges == snapshot


# ---------------------------------------------------------------------------
# Out-of-scope node kinds are rejected
# ---------------------------------------------------------------------------

def test_quantifier_needs_domain():
    """An object quantifier needs the model to carry object domains.

    A purely propositional model (no ``domains`` / ``domain``) raises a clear error;
    a model with per-world domains interprets the quantifier actualistically.
    """
    f = Box(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))
    propositional = KripkeModel(worlds={0}, relations={"alethic": {(0, 0)}})
    with pytest.raises(ValueError):
        satisfies_modal(f, propositional, 0)
    model = KripkeModel(worlds={0}, relations={"alethic": {(0, 0)}},
                        valuation={0: {"P(a)"}}, domain={"a"})
    assert satisfies_modal(f, model, 0) is True


def test_quantifier_shadowing_not_captured():
    """An inner quantifier that re-binds the outer variable must shadow it.

    Regression: grounding the outer ∀x must NOT leak into the inner ∃x's scope.
    ∀x ∃x A(x) ≡ ∃x A(x), so with D={a,b} and only A(a) true it is True (witness a).
    The buggy substitute() corrupted ∃x A(x) into ∃x A(a)/∃x A(b) and returned False.
    """
    x = Variable("x")
    A = lambda t: Atom("A", [t])
    m = KripkeModel(worlds={0}, valuation={0: {"A(a)"}}, domain={"a", "b"})
    assert satisfies_modal(Quantifier("∀", x, Quantifier("∃", x, A(x))), m, 0) is True
    # a legitimate free occurrence alongside the shadowing sub-quantifier:
    # ∀x (P(x) ∧ ∃x Q(x)) with P(a),P(b),Q(b) all true is True.
    m2 = KripkeModel(worlds={0}, valuation={0: {"P(a)", "P(b)", "Q(b)"}}, domain={"a", "b"})
    f = Quantifier("∀", x, And(Atom("P", [x]), Quantifier("∃", x, Atom("Q", [x]))))
    assert satisfies_modal(f, m2, 0) is True
    # and the bug propagated through a modality: ∀x □∃x A(x).
    m3 = KripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1)}},
                     valuation={1: {"A(a)"}}, domain={"a", "b"})
    assert satisfies_modal(Quantifier("∀", x, Box(Quantifier("∃", x, A(x)))), m3, 0) is True


def test_sorted_quantifier_rejected():
    """A sorted quantifier is rejected."""
    f = SortedQuantifier("∀", Variable("x"), "nat", Atom("P", [Variable("x")]))
    model = KripkeModel(worlds={0})
    with pytest.raises(NotImplementedError):
        satisfies_modal(f, model, 0)


def test_fuzzy_node_rejected():
    """A Łukasiewicz node is rejected (modal v1 is two-valued)."""
    f = LukNegation(P)
    model = KripkeModel(worlds={0})
    with pytest.raises(NotImplementedError):
        satisfies_modal(f, model, 0)


def test_lambda_node_rejected():
    """A lambda node is rejected."""
    f = Lambda(LambdaVar("x"), P)
    model = KripkeModel(worlds={0})
    with pytest.raises(NotImplementedError):
        satisfies_modal(f, model, 0)


# ---------------------------------------------------------------------------
# Immutability of inputs
# ---------------------------------------------------------------------------

def test_model_copies_inputs():
    """KripkeModel copies its mappings; later edits to caller data do not leak."""
    rel = {(0, 1)}
    val = {0: {"P"}}
    model = KripkeModel(worlds={0, 1}, relations={"alethic": rel}, valuation=val)
    rel.add((1, 0))
    val[0].add("Q")
    val[1] = {"Z"}
    # The model still sees the original snapshot.
    assert model.relation("alethic") == frozenset({(0, 1)})
    assert model.atoms_true_at(0) == frozenset({"P"})
    assert model.atoms_true_at(1) == frozenset()
