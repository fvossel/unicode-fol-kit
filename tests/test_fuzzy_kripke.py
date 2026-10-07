"""Tests for the graded (fuzzy) Kripke evaluator, semantics/fuzzy_kripke.py.

Four independent routes, following test_kripke.py's own template:

1. Differential collapse against the crisp evaluator (semantics.kripke) on
   {0, 1}-restricted frames, over many random frames and all three t-norms.
2. Textbook hand-computations (worked by hand in the docstrings below) for
   each of the three t-norms.
3. Schematic algebraic laws: the residuated duality Diamond phi = Not(Box(Not
   phi)) holds under Lukasiewicz's involutive negation, and a concrete
   witness where it FAILS under Goedel's non-involutive negation.
4. Monotonicity/boundary property tests plus rejection tests for every
   out-of-scope node family.
"""

import random

import pytest

from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_logic_kit.semantics.tnorm import LUKASIEWICZ, GODEL, PRODUCT
from unicode_logic_kit.fol.nodes import (
    Atom, Not, And, Or, Implies,
    Box, Diamond, Knows, Believes, Says, Wants,
    Next, Nominal, At, Obligatory, Permitted,
    Quantifier, Variable, SortedQuantifier,
    LambdaVar, Lambda, Application,
    WeakConjunction, WeakDisjunction,
    LukNegation, LukImplication,
)
from unicode_logic_kit.fol._modal_nodes import (
    Announce, AnnounceDiamond, EverybodyKnows, DistributedKnowledge, CommonKnowledge,
)

P = Atom("P", [])
Q = Atom("Q", [])

_TNORMS = (LUKASIEWICZ, GODEL, PRODUCT)


# ---------------------------------------------------------------------------
# 1. Differential collapse against the crisp evaluator
# ---------------------------------------------------------------------------

def _random_crisp_frame(rng, n_worlds=3):
    """Build a random alethic (worlds, edges, valuation) triple, atoms P, Q."""
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
    return worlds, edges, valuation


def test_collapse_to_crisp_evaluator_all_tnorms():
    """On {0,1}-restricted edges/valuations, satisfies_fuzzy_modal(...) is exactly
    1.0/0.0 wherever satisfies_modal on the structurally matching crisp formula
    (weak-fuzzy connective <-> classical connective) is True/False, for all
    three t-norms (each collapses to Boolean logic on {0,1} inputs)."""
    rng = random.Random(20260913)
    # (crisp formula, structurally matching fuzzy formula) pairs.
    pairs = [
        (Box(P), Box(P)),
        (Diamond(P), Diamond(P)),
        (Box(And(P, Q)), Box(WeakConjunction(P, Q))),
        (Diamond(And(P, Q)), Diamond(WeakConjunction(P, Q))),
        (Box(Or(P, Q)), Box(WeakDisjunction(P, Q))),
        (Diamond(Or(P, Q)), Diamond(WeakDisjunction(P, Q))),
        (Box(Implies(P, Q)), Box(LukImplication(P, Q))),
        (Box(Not(P)), Box(LukNegation(P))),
        (Knows(Atom("a", []), P), Knows(Atom("a", []), P)),
        (Believes(Atom("a", []), P), Believes(Atom("a", []), P)),
    ]
    trials = 0
    for tnorm in _TNORMS:
        for _ in range(150):
            n = rng.randint(1, 4)
            worlds, edges, valuation = _random_crisp_frame(rng, n)
            crisp = KripkeModel(
                worlds=worlds,
                relations={"alethic": edges, "K:a": edges, "B:a": edges},
                valuation=valuation,
            )
            fuzzy_edges = {(a, b): 1.0 for (a, b) in edges}
            fuzzy_valuation = {w: {k: 1.0 for k in valuation[w]} for w in worlds}
            fuzzy = FuzzyKripkeModel(
                worlds=worlds,
                relations={"alethic": fuzzy_edges, "K:a": fuzzy_edges, "B:a": fuzzy_edges},
                valuation=fuzzy_valuation,
                tnorm=tnorm,
            )
            for w in worlds:
                for crisp_f, fuzzy_f in pairs:
                    trials += 1
                    expected = 1.0 if satisfies_modal(crisp_f, crisp, w) else 0.0
                    got = satisfies_fuzzy_modal(fuzzy_f, fuzzy, w)
                    assert got == pytest.approx(expected, abs=1e-9), (
                        f"{tnorm.name} {crisp_f.to_unicode_str()!r} at {w!r}: "
                        f"crisp={expected} fuzzy={got}"
                    )
    assert trials > 5000  # sanity: the loop actually ran a substantial battery


def test_collapse_agrees_on_edge_target_outside_worlds():
    """Regression for a relation edge whose target lies OUTSIDE the declared
    worlds= set. Both KripkeModel.successors and the fuzzy aggregation domain
    must still include that edge (neither is filtered by model.worlds), so
    the {0,1}-collapse guarantee must hold here too -- it previously did not
    (Diamond silently read 0.0 instead of 1.0, Box silently read 1.0 instead
    of 0.0), because the aggregate only ever ranged over model.worlds."""
    crisp = KripkeModel(worlds=[0], relations={"alethic": {(0, 1)}}, valuation={1: {"P"}})
    fuzzy = FuzzyKripkeModel(worlds={0}, relations={"alethic": {(0, 1): 1.0}},
                             valuation={1: {"P": 1.0}})
    assert satisfies_modal(Diamond(P), crisp, 0) is True
    assert satisfies_fuzzy_modal(Diamond(P), fuzzy, 0) == pytest.approx(1.0)

    crisp2 = KripkeModel(worlds=[0], relations={"alethic": {(0, 1)}}, valuation={1: set()})
    fuzzy2 = FuzzyKripkeModel(worlds={0}, relations={"alethic": {(0, 1): 1.0}},
                              valuation={1: {}})
    assert satisfies_modal(Box(P), crisp2, 0) is False
    assert satisfies_fuzzy_modal(Box(P), fuzzy2, 0) == pytest.approx(0.0)


def _random_crisp_frame_with_dangling_edges(rng, n_worlds=3, n_extra=2):
    """Like _random_crisp_frame, but each world may also carry an edge to a
    world OUTSIDE the declared worlds= set (an id >= n_worlds), exercising the
    same structural situation as test_collapse_agrees_on_edge_target_outside_worlds
    but across many random frames and all three t-norms."""
    worlds = list(range(n_worlds))
    outside = list(range(n_worlds, n_worlds + n_extra))
    edges = {(a, b) for a in worlds for b in worlds if rng.random() < 0.5}
    edges |= {(a, b) for a in worlds for b in outside if rng.random() < 0.3}
    valuation = {}
    for w in worlds + outside:
        true_here = set()
        if rng.random() < 0.5:
            true_here.add("P")
        if rng.random() < 0.5:
            true_here.add("Q")
        valuation[w] = true_here
    return worlds, edges, valuation


def test_collapse_to_crisp_evaluator_with_dangling_edges():
    """Same differential-collapse oracle as
    test_collapse_to_crisp_evaluator_all_tnorms, but the frame generator may
    also place edges to worlds outside the declared worlds= set -- the
    situation the blocker fix (aggregating over model.worlds UNION the actual
    successors, not model.worlds alone) is specifically for. Only Box/Diamond
    are checked here (Knows/Believes share the same aggregator, already
    covered by the main collapse test; this one is about the aggregation
    domain, not the relation-name dispatch)."""
    rng = random.Random(7331)
    trials = 0
    for tnorm in _TNORMS:
        for _ in range(100):
            n = rng.randint(1, 3)
            worlds, edges, valuation = _random_crisp_frame_with_dangling_edges(rng, n)
            crisp = KripkeModel(worlds=worlds, relations={"alethic": edges}, valuation=valuation)
            fuzzy_edges = {(a, b): 1.0 for (a, b) in edges}
            fuzzy_valuation = {w: {k: 1.0 for k in v} for w, v in valuation.items()}
            fuzzy = FuzzyKripkeModel(worlds=worlds, relations={"alethic": fuzzy_edges},
                                     valuation=fuzzy_valuation, tnorm=tnorm)
            for w in worlds:
                for crisp_f, fuzzy_f in [(Box(P), Box(P)), (Diamond(P), Diamond(P))]:
                    trials += 1
                    expected = 1.0 if satisfies_modal(crisp_f, crisp, w) else 0.0
                    got = satisfies_fuzzy_modal(fuzzy_f, fuzzy, w)
                    assert got == pytest.approx(expected, abs=1e-9), (
                        f"{tnorm.name} {crisp_f.to_unicode_str()!r} at {w!r}: "
                        f"crisp={expected} fuzzy={got}"
                    )
    assert trials > 500


# ---------------------------------------------------------------------------
# 2. Textbook hand-computations, one per t-norm
# ---------------------------------------------------------------------------
#
# Shared frame: two worlds w0, w1; the only alethic edge is R(w0, w1) = 0.6
# (w0 has no self-loop, so R(w0, w0) = 0.0 by the missing-edge convention);
# val_w1(P) = 0.5. Worked by hand for each t-norm's conj/impl:
#
#   Diamond P (w0) = sup_{w' in {w0,w1}} conj(R(w0,w'), val(P,w'))
#                   = max(conj(0, val_w0(P)), conj(0.6, 0.5))     [conj(0,*) = 0]
#                   = conj(0.6, 0.5)
#   Box     P (w0) = inf_{w' in {w0,w1}} impl(R(w0,w'), val(P,w'))
#                   = min(impl(0, val_w0(P)), impl(0.6, 0.5))     [impl(0,*) = 1]
#                   = impl(0.6, 0.5)

def _two_world_frame(tnorm, r=0.6, p_at_w1=0.5):
    return FuzzyKripkeModel(
        worlds={"w0", "w1"},
        relations={"alethic": {("w0", "w1"): r}},
        valuation={"w1": {"P": p_at_w1}},
        tnorm=tnorm,
    )


def test_hand_computed_lukasiewicz():
    """Lukasiewicz: conj(0.6,0.5) = max(0, 0.6+0.5-1) = 0.1; impl(0.6,0.5) =
    min(1, 1-0.6+0.5) = 0.9. (Matches the spec's own worked example shape,
    Hajek 1998 sec 8.1's Lukasiewicz-t-norm residuum.)"""
    m = _two_world_frame(LUKASIEWICZ)
    assert satisfies_fuzzy_modal(Diamond(P), m, "w0") == pytest.approx(0.1)
    assert satisfies_fuzzy_modal(Box(P), m, "w0") == pytest.approx(0.9)


def test_hand_computed_lukasiewicz_spec_example():
    """The batch spec's own worked example: R(w0,w1)=0.6, val_w1(P)=0.8 under
    Lukasiewicz gives Diamond P(w0) = max(0, 0.6+0.8-1) = 0.4."""
    m = _two_world_frame(LUKASIEWICZ, r=0.6, p_at_w1=0.8)
    assert satisfies_fuzzy_modal(Diamond(P), m, "w0") == pytest.approx(0.4)


def test_hand_computed_godel():
    """Goedel: conj = min(0.6,0.5) = 0.5. impl(x,y) = 1 if x<=y else y; since
    0.6 > 0.5, impl(0.6,0.5) = 0.5."""
    m = _two_world_frame(GODEL)
    assert satisfies_fuzzy_modal(Diamond(P), m, "w0") == pytest.approx(0.5)
    assert satisfies_fuzzy_modal(Box(P), m, "w0") == pytest.approx(0.5)


def test_hand_computed_product():
    """Product (Goguen): conj(0.6,0.5) = 0.6*0.5 = 0.3; the Goguen residuum
    impl(x,y) = y/x when x>y, so impl(0.6,0.5) = 0.5/0.6 = 5/6."""
    m = _two_world_frame(PRODUCT)
    assert satisfies_fuzzy_modal(Diamond(P), m, "w0") == pytest.approx(0.3)
    assert satisfies_fuzzy_modal(Box(P), m, "w0") == pytest.approx(5.0 / 6.0)


# ---------------------------------------------------------------------------
# 3. Schematic algebraic laws: residuated duality
# ---------------------------------------------------------------------------

def _random_fuzzy_frame(rng, tnorm, n_worlds=3):
    worlds = list(range(n_worlds))
    edges = {(a, b): rng.random() for a in worlds for b in worlds if rng.random() < 0.6}
    valuation = {w: {"P": rng.random()} for w in worlds if rng.random() < 0.8}
    return FuzzyKripkeModel(worlds=worlds, relations={"alethic": edges},
                            valuation=valuation, tnorm=tnorm)


def test_diamond_box_duality_holds_under_lukasiewicz():
    """Diamond P = Not(Box(Not P)) (via LukNegation) holds numerically, exactly,
    under Lukasiewicz's INVOLUTIVE residual negation (neg(x) = 1-x is an
    order-reversing bijection of [0,1], and conj(a,b) = neg(impl(a, neg(b)))
    is the defining MV-algebra identity for an involutive t-norm negation —
    Hajek 1998, ch. 2)."""
    rng = random.Random(4242)
    dual = LukNegation(Box(LukNegation(P)))
    for _ in range(200):
        n = rng.randint(1, 4)
        m = _random_fuzzy_frame(rng, LUKASIEWICZ, n)
        for w in m.worlds:
            lhs = satisfies_fuzzy_modal(Diamond(P), m, w)
            rhs = satisfies_fuzzy_modal(dual, m, w)
            assert lhs == pytest.approx(rhs, abs=1e-9)


def test_diamond_box_duality_fails_under_godel():
    """Goedel's residual negation is NOT involutive (neg(x) = 0 for every
    x > 0, so it collapses (0,1] to a single point and cannot be an
    order-reversing bijection) -- the duality is expected to break, and does,
    on this hand-picked witness: R(w0,w1) = 0.5, val_w1(P) = 0.5 gives
    Diamond P(w0) = min(0.5,0.5) = 0.5, but Not(Box(Not P))(w0) = 1.0 (see
    the module docstring's aggregation-domain discussion for why 0-weight
    self-loops never matter here)."""
    m = FuzzyKripkeModel(
        worlds={"w0", "w1"},
        relations={"alethic": {("w0", "w1"): 0.5}},
        valuation={"w1": {"P": 0.5}},
        tnorm=GODEL,
    )
    diamond_val = satisfies_fuzzy_modal(Diamond(P), m, "w0")
    dual_val = satisfies_fuzzy_modal(LukNegation(Box(LukNegation(P))), m, "w0")
    assert diamond_val == pytest.approx(0.5)
    assert dual_val == pytest.approx(1.0)
    assert diamond_val != pytest.approx(dual_val)


# ---------------------------------------------------------------------------
# 4. Monotonicity and boundary properties
# ---------------------------------------------------------------------------
#
# NOTE on a spec inaccuracy: the batch's test_oracle claims "raising any atom
# valuation or edge weight can only increase Diamond phi / decrease-or-hold
# Box phi". That is only half right. Raising an EDGE WEIGHT does increase
# Diamond and decrease-or-hold Box (conj is monotone non-decreasing in its
# first argument, the residuum impl is monotone NON-INCREASING in its first
# argument, for all three t-norms in tnorm.py). But raising an ATOM
# VALUATION increases-or-holds BOTH Diamond and Box (impl is monotone
# NON-DECREASING in its SECOND argument too, for all three t-norms) -- it
# does not decrease Box. Verified by hand for all three t-norms
# (impl(0,y)=1 constant; Lukasiewicz impl(x,y)=min(1,1-x+y) is +1 in y;
# Goedel/Product impl(x,y) is y itself, or 1, in the y-branch -- non-decreasing
# either way) and confirmed by the property tests below, which test the
# mathematically correct direction rather than the spec's.

def test_monotone_in_edge_weight():
    """Raising an alethic edge weight (atom valuation fixed) can only increase
    Diamond P and decrease-or-hold Box P, for every t-norm."""
    rng = random.Random(99)
    for tnorm in _TNORMS:
        for _ in range(200):
            r1 = rng.random()
            r2 = r1 + rng.random() * (1.0 - r1)  # r2 >= r1, both in [0,1]
            p_val = rng.random()
            m1 = FuzzyKripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1): r1}},
                                  valuation={1: {"P": p_val}}, tnorm=tnorm)
            m2 = FuzzyKripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1): r2}},
                                  valuation={1: {"P": p_val}}, tnorm=tnorm)
            d1 = satisfies_fuzzy_modal(Diamond(P), m1, 0)
            d2 = satisfies_fuzzy_modal(Diamond(P), m2, 0)
            b1 = satisfies_fuzzy_modal(Box(P), m1, 0)
            b2 = satisfies_fuzzy_modal(Box(P), m2, 0)
            assert d2 >= d1 - 1e-9, (tnorm.name, r1, r2, d1, d2)
            assert b2 <= b1 + 1e-9, (tnorm.name, r1, r2, b1, b2)


def test_monotone_in_atom_valuation():
    """Raising an atom's valuation degree (edge weight fixed) can only increase
    BOTH Diamond P and Box P, for every t-norm (see the NOTE above: this is
    the mathematically correct direction, not the spec's claimed one)."""
    rng = random.Random(2024)
    for tnorm in _TNORMS:
        for _ in range(200):
            r = rng.random()
            v1 = rng.random()
            v2 = v1 + rng.random() * (1.0 - v1)  # v2 >= v1
            m1 = FuzzyKripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1): r}},
                                  valuation={1: {"P": v1}}, tnorm=tnorm)
            m2 = FuzzyKripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1): r}},
                                  valuation={1: {"P": v2}}, tnorm=tnorm)
            d1 = satisfies_fuzzy_modal(Diamond(P), m1, 0)
            d2 = satisfies_fuzzy_modal(Diamond(P), m2, 0)
            b1 = satisfies_fuzzy_modal(Box(P), m1, 0)
            b2 = satisfies_fuzzy_modal(Box(P), m2, 0)
            assert d2 >= d1 - 1e-9, (tnorm.name, r, v1, v2, d1, d2)
            assert b2 >= b1 - 1e-9, (tnorm.name, r, v1, v2, b1, b2)


def test_empty_accessible_worlds_boundary():
    """No alethic relation at all (every edge weight 0.0) gives Box = 1.0 and
    Diamond = 0.0 EXACTLY, matching the crisp vacuous-truth convention in
    kripke.py, for every t-norm and regardless of the (irrelevant) atom
    valuation."""
    for tnorm in _TNORMS:
        m = FuzzyKripkeModel(worlds={"w0", "w1"}, valuation={"w1": {"P": 0.73}}, tnorm=tnorm)
        assert satisfies_fuzzy_modal(Box(P), m, "w0") == 1.0
        assert satisfies_fuzzy_modal(Diamond(P), m, "w0") == 0.0


def test_missing_relation_name_is_everywhere_zero():
    """A relation name absent from relations= behaves as the everywhere-0.0
    relation (Knows here, with no 'K:a' entry at all)."""
    m = FuzzyKripkeModel(worlds={"w0", "w1"}, valuation={"w1": {"P": 1.0}})
    a = Atom("a", [])
    assert satisfies_fuzzy_modal(Knows(a, P), m, "w0") == 1.0


# ---------------------------------------------------------------------------
# Relation-name mechanism: Knows/Believes/Says/Wants all read universally
# ---------------------------------------------------------------------------

def test_knows_believes_says_wants_share_universal_reading():
    """Knows/Believes/Says/Wants each read residuated-universally over their
    own agent-keyed relation -- structurally identical to Box, just a
    different relation name/prefix (K:/B:/Say:/Want:)."""
    a = Atom("alice", [])
    for ctor, prefix in [(Knows, "K:"), (Believes, "B:"), (Says, "Say:"), (Wants, "Want:")]:
        m = FuzzyKripkeModel(
            worlds={"w0", "w1"},
            relations={prefix + "alice": {("w0", "w1"): 0.6}},
            valuation={"w1": {"P": 0.5}},
            tnorm=LUKASIEWICZ,
        )
        got = satisfies_fuzzy_modal(ctor(a, P), m, "w0")
        assert got == pytest.approx(0.9)  # same 0.9 as the Box hand-computation above


# ---------------------------------------------------------------------------
# Rejection tests: every out-of-scope node kind, by name
# ---------------------------------------------------------------------------

def _model():
    return FuzzyKripkeModel(worlds={"w0"})


def test_rejects_classical_connectives():
    m = _model()
    for f in (Not(P), And(P, Q), Or(P, Q), Implies(P, Q)):
        with pytest.raises(TypeError, match="Classical connective"):
            satisfies_fuzzy_modal(f, m, "w0")


def test_rejects_classical_connective_nested_under_box():
    m = _model()
    with pytest.raises(TypeError, match="Classical connective"):
        satisfies_fuzzy_modal(Box(And(P, Q)), m, "w0")


def test_rejects_quantifiers():
    m = _model()
    with pytest.raises(NotImplementedError, match="Quantifier"):
        satisfies_fuzzy_modal(Quantifier("forall", Variable("x"), P), m, "w0")
    with pytest.raises(NotImplementedError, match="SortedQuantifier"):
        satisfies_fuzzy_modal(
            SortedQuantifier("forall", Variable("x"), "Person", P), m, "w0")


def test_rejects_lambda_nodes():
    m = _model()
    for f in (LambdaVar("x"), Lambda(LambdaVar("x"), P), Application(P, P)):
        with pytest.raises(NotImplementedError, match="lambda"):
            satisfies_fuzzy_modal(f, m, "w0")


def test_rejects_temporal_nodes():
    m = _model()
    with pytest.raises(NotImplementedError, match="temporal"):
        satisfies_fuzzy_modal(Next(P), m, "w0")


def test_rejects_hybrid_nodes():
    m = _model()
    with pytest.raises(NotImplementedError, match="hybrid"):
        satisfies_fuzzy_modal(Nominal("i"), m, "w0")
    with pytest.raises(NotImplementedError, match="hybrid"):
        satisfies_fuzzy_modal(At(Nominal("i"), P), m, "w0")


def test_rejects_pal_nodes():
    m = _model()
    with pytest.raises(NotImplementedError, match="public announcement logic"):
        satisfies_fuzzy_modal(Announce(P, Q), m, "w0")
    with pytest.raises(NotImplementedError, match="public announcement logic"):
        satisfies_fuzzy_modal(AnnounceDiamond(P, Q), m, "w0")


def test_rejects_group_epistemic_nodes():
    m = _model()
    a = Atom("a", [])
    b = Atom("b", [])
    for f in (EverybodyKnows((a, b), P), DistributedKnowledge((a, b), P),
              CommonKnowledge((a, b), P)):
        with pytest.raises(NotImplementedError, match="group-epistemic"):
            satisfies_fuzzy_modal(f, m, "w0")


def test_rejects_deontic_nodes():
    m = _model()
    with pytest.raises(NotImplementedError, match="deontic"):
        satisfies_fuzzy_modal(Obligatory(P), m, "w0")
    with pytest.raises(NotImplementedError, match="deontic"):
        satisfies_fuzzy_modal(Permitted(P), m, "w0")


# ---------------------------------------------------------------------------
# Model construction basics
# ---------------------------------------------------------------------------

def test_model_defaults_and_clamping():
    """Weights/degrees outside [0,1] are clamped defensively, and unnamed
    worlds/relations default to the everywhere-0.0 reading."""
    m = FuzzyKripkeModel(
        worlds={"w0", "w1"},
        relations={"alethic": {("w0", "w1"): 5.0, ("w1", "w0"): -2.0}},
        valuation={"w1": {"P": 3.0}},
    )
    assert m.relation_weight("alethic", "w0", "w1") == 1.0
    assert m.relation_weight("alethic", "w1", "w0") == 0.0
    assert m.atom_degree("w1", "P") == 1.0
    assert m.relation_weight("nonexistent", "w0", "w1") == 0.0
    assert m.atom_degree("w0", "Q") == 0.0


def test_tnorm_must_be_tnorm_instance():
    with pytest.raises(TypeError, match="TNorm instance"):
        FuzzyKripkeModel(worlds={"w0"}, tnorm="lukasiewicz")


def test_mutating_caller_containers_does_not_leak_in():
    """The constructor copies its containers, so a later mutation of the
    caller's dict does not affect the model (mirrors KripkeModel's contract)."""
    edges = {("w0", "w1"): 0.5}
    valuation = {"w1": {"P": 0.5}}
    m = FuzzyKripkeModel(worlds={"w0", "w1"}, relations={"alethic": edges}, valuation=valuation)
    edges[("w0", "w1")] = 0.0
    valuation["w1"]["P"] = 0.0
    assert m.relation_weight("alethic", "w0", "w1") == 0.5
    assert m.atom_degree("w1", "P") == 0.5
