"""Tests for the Kripke (possible-worlds) evaluator, semantics/kripke.py.

The truths asserted here are hand-computed against small, explicit frames, plus
two schematic checks (the K axiom and the box/diamond and G/F dualities) over
several random frames.
"""

import random

import pytest

from unicode_logic_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, models_at, reflexive_transitive_closure,
    ctl_ex, ctl_af, ctl_eg, ctl_au,
)
from unicode_logic_kit.semantics.action_models import (
    everybody_knows, distributed_knowledge_holds, common_knowledge_holds,
)
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, Not, And, Or, Xor, Implies, Iff,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted, Nominal, At, Down,
    Quantifier, Variable, SortedQuantifier,
    LukNegation, Lambda, LambdaVar,
)
from unicode_logic_kit.fol._modal_nodes import (
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    Announce, AnnounceDiamond,
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
# Group epistemic dispatch (EverybodyKnows/DistributedKnowledge/CommonKnowledge
# -> semantics.action_models): a THIN wiring test, hand-computed on one small
# frame -- the semantics themselves (union/intersection/closure) are the
# action_models functions' own responsibility and are tested exhaustively in
# tests/test_action_models.py and tests/test_group_epistemic.py.
# ---------------------------------------------------------------------------

def test_group_operators_dispatch_to_action_models():
    """Hand-computed on one small frame: K:a -> {0,1} (P true both), K:b ->
    {0,2} (P true at 0, false at 2), from world 0.

    - E_{a,b} P: union successors {0,1,2} -- P false at 2 -- FALSE.
    - D_{a,b} P: intersection successors {0} only -- P true there -- TRUE.
    - C_{a,b} P: reflexive-transitive closure from 0 over the union is
      {0,1,2} (2 reachable via the union edge (0,2)) -- P false at 2 --
      FALSE, same reachable set as E_G here since the union graph from 0 is
      already fully explored in one step.
    """
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"K:a": {(0, 0), (0, 1)}, "K:b": {(0, 0), (0, 2)}},
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )
    assert satisfies_modal(EverybodyKnows(("a", "b"), P), model, 0) is False
    assert satisfies_modal(DistributedKnowledge(("a", "b"), P), model, 0) is True
    assert satisfies_modal(CommonKnowledge(("a", "b"), P), model, 0) is False


def test_group_operators_agree_with_direct_action_models_calls():
    """The dispatch is a THIN wrapper: satisfies_modal(node, ...) must equal
    calling the matching semantics.action_models function directly with the
    same agent-name list, on every world of a random small frame."""
    rng = random.Random(20260917)
    for _ in range(30):
        n_worlds = rng.randint(1, 4)
        worlds = list(range(n_worlds))
        relations = {
            f"K:{a}": {(x, y) for x in worlds for y in worlds if rng.random() < 0.5}
            for a in ("a", "b")
        }
        valuation = {w: ({"P"} if rng.random() < 0.5 else set()) for w in worlds}
        model = KripkeModel(worlds=worlds, relations=relations, valuation=valuation)
        for w in worlds:
            assert (satisfies_modal(EverybodyKnows(("a", "b"), P), model, w)
                    == everybody_knows(model, w, ["a", "b"], P))
            assert (satisfies_modal(DistributedKnowledge(("a", "b"), P), model, w)
                    == distributed_knowledge_holds(model, w, ["a", "b"], P))
            assert (satisfies_modal(CommonKnowledge(("a", "b"), P), model, w)
                    == common_knowledge_holds(model, w, ["a", "b"], P))


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


def test_sorted_quantifier_ranges_over_its_sort_only():
    """A sorted quantifier is evaluated by relativizing it to the sort predicate.

    The evaluator used to refuse SortedQuantifier outright; it now reads
    ∀x:nat P(x) as ∀x (nat(x) → P(x)) and ∃x:nat P(x) as ∃x (nat(x) ∧ P(x)).
    The domain is {a, b} with only a in the sort and only P(a) true, so both
    verdicts below are wrong unless b really is excluded by the guard.
    """
    x = Variable("x")
    m = KripkeModel(worlds={0}, valuation={0: {"P(a)", "nat(a)"}}, domain={"a", "b"})
    assert satisfies_modal(SortedQuantifier("∀", x, "nat", Atom("P", [x])), m, 0) is True
    assert satisfies_modal(SortedQuantifier("∃", x, "nat", Atom("P", [x])), m, 0) is True
    # Q holds nowhere, so the universal over the same sort is False, not vacuous.
    assert satisfies_modal(SortedQuantifier("∀", x, "nat", Atom("Q", [x])), m, 0) is False


def test_sorted_quantifier_needs_a_domain():
    """Relativized, a sorted quantifier is an object quantifier: it needs a domain."""
    f = SortedQuantifier("∀", Variable("x"), "nat", Atom("P", [Variable("x")]))
    model = KripkeModel(worlds={0})
    with pytest.raises(ValueError, match="no object domains"):
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
# Equality is NOT interpreted: an '=' / '≠' atom is refused BY NAME, wherever it
# sits. This evaluator has no term semantics (an atom is looked up by its rendered
# key in the valuation), so reading ``a = b`` as the proposition keyed "a = b"
# would answer wrongly (``a = a`` false). The first-order route fol.qml reads '='
# as rigid identity instead; tests/test_qml.py holds that table.
# ---------------------------------------------------------------------------

_A, _B = Constant("a"), Constant("b")
EQ = Atom("=", (_A, _B))
NEQ = Atom("≠", (_A, _B))
Z = Atom("Z", ())          # the control: the same wrapper around an ordinary atom
_REFUSAL = r"equality is not interpreted.*qml_is_valid"


def _everything_model():
    """Worlds 0 -> 1 on every relation family the evaluator reads, plus a nominal
    and a domain, so EVERY wrapper below is evaluable when it holds a normal atom
    (the control) and the refusal can only be due to the equality atom."""
    rels = {name: {(0, 1)} for name in
            ("alethic", "temporal", "deontic", "K:a", "B:a", "Say:a", "Want:a")}
    return KripkeModel(worlds={0, 1}, relations=rels,
                       valuation={0: {"Z"}, 1: {"Z"}},
                       domain={"a", "b"}, nominals={"i": 0})


# every place an equality atom can sit: each node type that has a sub-formula
_WRAPPERS = {
    "bare": lambda e: e,
    "not": Not,
    "and_left": lambda e: And(e, Z),
    "and_right": lambda e: And(Z, e),
    "or_left": lambda e: Or(e, Z),
    "or_right": lambda e: Or(Z, e),
    "xor": lambda e: Xor(Z, e),
    "implies_antecedent": lambda e: Implies(e, Z),
    "implies_consequent": lambda e: Implies(Z, e),
    "iff": lambda e: Iff(Z, e),
    "box": Box,
    "diamond": Diamond,
    "knows": lambda e: Knows(Constant("a"), e),
    "believes": lambda e: Believes(Constant("a"), e),
    "says": lambda e: Says(Constant("a"), e),
    "wants": lambda e: Wants(Constant("a"), e),
    "obligatory": Obligatory,
    "permitted": Permitted,
    "next": Next,
    "always": Always,
    "eventually": Eventually,
    "until_left": lambda e: Until(e, Z),
    "until_right": lambda e: Until(Z, e),
    "historically": Historically,
    "once": Once,
    "previous": Previous,
    "since_left": lambda e: Since(e, Z),
    "since_right": lambda e: Since(Z, e),
    "at": lambda e: At(Nominal("i"), e),
    "down": lambda e: Down(Nominal("j"), e),
    "announce_announcement": lambda e: Announce(e, Z),
    "announce_body": lambda e: Announce(Z, e),
    "announce_diamond_announcement": lambda e: AnnounceDiamond(e, Z),
    "announce_diamond_body": lambda e: AnnounceDiamond(Z, e),
    "everybody_knows": lambda e: EverybodyKnows((Constant("a"),), e),
    "distributed_knowledge": lambda e: DistributedKnowledge((Constant("a"),), e),
    "common_knowledge": lambda e: CommonKnowledge((Constant("a"),), e),
    "forall": lambda e: Quantifier("∀", Variable("x"), e),
    "exists": lambda e: Quantifier("∃", Variable("x"), e),
    "sorted_forall": lambda e: SortedQuantifier("∀", Variable("x"), "S", e),
    "sorted_exists": lambda e: SortedQuantifier("∃", Variable("x"), "S", e),
    "deep": lambda e: Box(Diamond(And(Z, Or(Not(Z), Knows(Constant("a"), e))))),
}


@pytest.mark.parametrize("name", sorted(_WRAPPERS))
def test_equality_atom_is_refused_wherever_it_sits(name):
    """Control: the wrapper around an ordinary atom evaluates (no refusal, a bool).
    Then the very same wrapper around ``a = b`` / ``a ≠ b`` is refused, by name."""
    model = _everything_model()
    wrap = _WRAPPERS[name]
    assert satisfies_modal(wrap(Z), model, 0) in (True, False)      # control
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        satisfies_modal(wrap(EQ), model, 0)
    with pytest.raises(NotImplementedError, match=r"disequality atom.*" + _REFUSAL):
        satisfies_modal(wrap(NEQ), model, 0)


def test_equality_refusal_names_the_atom_and_the_route():
    with pytest.raises(NotImplementedError) as info:
        satisfies_modal(Box(EQ), _everything_model(), 0)
    msg = str(info.value)
    assert msg.startswith("satisfies_modal:")         # the module's own refusal style
    assert "'a = b'" in msg and "'='" in msg           # the atom, by name
    assert "fol.qml.qml_is_valid" in msg and "first-order" in msg
    with pytest.raises(NotImplementedError) as info:
        satisfies_modal(NEQ, _everything_model(), 0)
    assert "disequality" in str(info.value) and "'≠'" in str(info.value)


# Places where evaluation would NEVER reach the atom: a lazy check on the Atom
# case would let each of these return a verdict that did not look at it. Each row
# gives (wrapper, model builder, evaluation world, hand-derived control verdict);
# the control is the same wrapper around the ordinary atom Z.
def _dead_end():
    """0 -> 1 on alethic and temporal; nothing leaves 1; Z is true at 0 only."""
    return KripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1)}, "temporal": {(0, 1)}},
                       valuation={0: {"Z"}}, domain={"a"})


def _empty_domain():
    """One world whose domain is empty: ∀x ranges over nothing, ∃x over nothing."""
    return KripkeModel(worlds={0}, valuation={0: {"Z"}}, domains={0: set()})


_VACUOUS = {
    # Z is true at 0, so Z ∨ _ is true without looking at _
    "or_short_circuit": (lambda e: Or(Z, e), _dead_end, 0, True),
    # ¬Z is false at 0, so ¬Z ∧ _ is false without looking at _
    "and_short_circuit": (lambda e: And(Not(Z), e), _dead_end, 0, False),
    # ¬Z is false at 0, so ¬Z → _ is true without looking at _
    "implies_false_antecedent": (lambda e: Implies(Not(Z), e), _dead_end, 0, True),
    # world 1 has no alethic successor: □_ is vacuously true there ...
    "box_at_dead_end": (Box, _dead_end, 1, True),
    # ... and ◇_ is false there
    "diamond_at_dead_end": (Diamond, _dead_end, 1, False),
    # empty domain: ∀x _ is vacuously true, ∃x _ is false
    "forall_over_empty_domain": (lambda e: Quantifier("∀", Variable("x"), e), _empty_domain, 0, True),
    "exists_over_empty_domain": (lambda e: Quantifier("∃", Variable("x"), e), _empty_domain, 0, False),
    # Until: the right argument holds at once, so the left is never evaluated
    "until_left_never_reached": (lambda e: Until(e, Z), _dead_end, 0, True),
    # an untruthful announcement (¬Z is false at 0) is vacuously fine; body never evaluated
    "announce_untruthful": (lambda e: Announce(Not(Z), e), _dead_end, 0, True),
}


@pytest.mark.parametrize("name", sorted(_VACUOUS))
def test_equality_refusal_survives_short_circuit_and_vacuous_evaluation(name):
    wrap, make_model, world, expected = _VACUOUS[name]
    model = make_model()
    # control: the ordinary atom evaluates fine, to the vacuous / short-circuited verdict
    assert satisfies_modal(wrap(Z), model, world) is expected
    # ... and with an equality atom in the position evaluation skips, it still refuses
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        satisfies_modal(wrap(EQ), model, world)


def test_equality_refused_in_a_substituted_quantifier_instance():
    """∀x (x = x): each instance ``a = a`` would be looked up by key; it is refused up
    front, so a caller never sees the false the lookup would give (even when the key
    "a = a" happens to be listed in the valuation)."""
    x = Variable("x")
    m = KripkeModel(worlds={0}, valuation={0: {"a = a"}}, domain={"a"})
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        satisfies_modal(Quantifier("∀", x, Atom("=", (x, x))), m, 0)


def test_equality_refused_by_the_ctl_entry_points_too():
    """ctl_ex at a world with NO successor never calls satisfies_modal (``any`` over an
    empty set), so the refusal has to sit in the CTL functions themselves."""
    dead = KripkeModel(worlds={0}, relations={}, valuation={})
    assert ctl_ex(dead, 0, Z) is False                       # control: no successor
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        ctl_ex(dead, 0, EQ)
    # 0 -> 1 -> 1 (total); Z holds at 1 only. Hand-derived controls: AF Z at 0 is true
    # (every path reaches 1), EG Z at 0 is false (0 itself lacks Z), A[¬Z U Z] at 0 true.
    loop = KripkeModel(worlds={0, 1}, relations={"temporal": {(0, 1), (1, 1)}},
                       valuation={1: {"Z"}})
    assert ctl_af(loop, 0, Z) is True and ctl_eg(loop, 0, Z) is False
    assert ctl_au(loop, 0, Not(Z), Z) is True
    for call in (lambda: ctl_ex(loop, 0, EQ), lambda: ctl_af(loop, 0, EQ),
                 lambda: ctl_eg(loop, 0, NEQ), lambda: ctl_au(loop, 0, EQ, Z),
                 lambda: ctl_au(loop, 0, Z, NEQ)):
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            call()


def test_equality_refused_by_the_group_operators_through_satisfies_modal():
    """The group operators dispatch into action_models; the refusal fires before."""
    for node in (EverybodyKnows, DistributedKnowledge, CommonKnowledge):
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            satisfies_modal(node((Constant("a"),), EQ), _everything_model(), 0)


def test_other_infix_atoms_are_still_ordinary_keyed_atoms():
    """Only '=' / '≠' are refused: '<', '≤' ... are looked up by key exactly as before."""
    lt = Atom("<", (_A, _B))
    m = KripkeModel(worlds={0, 1}, valuation={0: {lt.to_unicode_str()}})
    assert lt.to_unicode_str() == "a < b"
    assert satisfies_modal(lt, m, 0) is True and satisfies_modal(lt, m, 1) is False
    assert satisfies_modal(Atom("≤", (_A, _B)), m, 0) is False


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
