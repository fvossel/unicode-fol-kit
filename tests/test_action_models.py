"""Tests for unicode_fol_kit/semantics/action_models.py — common knowledge and
BMS action models (Dynamic Epistemic Logic).

Every truth value asserted here is either computed by hand in the docstring
(small models) or cross-checked against an independent route already tested
elsewhere in the kit (``announce`` for PAL, or a second, from-scratch
computation of the same quantity for the muddy-children puzzle). Three
sections:

1. Common knowledge (``everybody_knows`` / ``common_knowledge_holds``) on
   small hand-built frames, including the classic "E holds, C fails through a
   chain" example and a cross-check against the FHMV E-ladder fixpoint
   definition (``_e_ladder_holds`` below).
2. ``ActionModel`` construction/refusals and ``product_update`` on small
   frames, including the textbook 2-event PRIVATE announcement (one agent
   learns, the other is unaware anything happened) and the agreement between
   ``public_announcement_action`` + ``product_update`` and the kit's existing
   ``announce`` (PAL model restriction).
3. The full Muddy Children puzzle (3 children, k=2 actually muddy), run once
   through ``announce`` directly and once through ``product_update`` +
   ``public_announcement_action``, with both routes checked to agree.
"""

import itertools

import pytest

from unicode_fol_kit.semantics.action_models import (
    everybody_knows, common_knowledge_holds,
    ActionModel, product_update, public_announcement_action,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.dynamic_epistemic import announce
from unicode_fol_kit.fol.nodes import Atom, Constant, Not, And, Or, Knows

P = Atom("P", [])
Q = Atom("Q", [])


# ---------------------------------------------------------------------------
# Common knowledge: small hand-built frames
# ---------------------------------------------------------------------------

def _chain_model(p_at_2=False):
    """Worlds 0-1-2 in a CHAIN: K:a links {0,1}, K:b links {1,2}; no direct 0-2 link.

    P is true at 0 and 1 always; at 2 iff ``p_at_2``. With ``p_at_2=False``
    this is the textbook "E_{a,b} holds, C_{a,b} fails" example: everyone in
    {a,b} knows P in one step from 0 (0's only successors are {0,1}, both P),
    but P is not common knowledge because the group can "walk" from 0 to 2
    (via 1) where P is false.
    """
    return KripkeModel(
        worlds={0, 1, 2},
        relations={
            "K:a": {(0, 0), (0, 1), (1, 0), (1, 1)},
            "K:b": {(1, 1), (1, 2), (2, 1), (2, 2)},
        },
        valuation={0: {"P"}, 1: {"P"}, 2: ({"P"} if p_at_2 else set())},
    )


def test_everybody_knows_is_true_when_all_group_successors_satisfy_formula():
    """E_{a,b} P at 0: successors of 0 in K:a ∪ K:b = {0,1} (b has no edge from 0), P true at both."""
    model = _chain_model()
    assert everybody_knows(model, 0, ["a", "b"], P) is True


def test_common_knowledge_fails_through_a_chain():
    """C_{a,b} P at 0 is FALSE: reflexive-transitive closure of K:a ∪ K:b from 0 is {0,1,2}, and P is false at 2."""
    model = _chain_model(p_at_2=False)
    assert common_knowledge_holds(model, 0, ["a", "b"], P) is False


def test_common_knowledge_holds_when_formula_true_on_whole_component():
    """Same chain frame, but P true everywhere reachable (including 2): C_{a,b} P at 0 is now TRUE."""
    model = _chain_model(p_at_2=True)
    assert common_knowledge_holds(model, 0, ["a", "b"], P) is True


def test_everybody_knows_union_not_intersection_of_successors():
    """Adding an agent to the group can only ADD successors (union), never remove them.

    K:a relates 0 to {0,1} (P true both); K:b relates 0 to {0,2} (P false at 2).
    E_{a} P holds at 0 (a alone sees only P-worlds); E_{b} P fails (b sees the
    P-false world 2); E_{a,b} P — the UNION — inherits b's counterexample and
    also fails. This is why common knowledge is antitonic in group size.
    """
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={
            "K:a": {(0, 0), (0, 1), (1, 0), (1, 1)},
            "K:b": {(0, 0), (0, 2), (2, 0), (2, 2)},
        },
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )
    assert everybody_knows(model, 0, ["a"], P) is True
    assert everybody_knows(model, 0, ["b"], P) is False
    assert everybody_knows(model, 0, ["a", "b"], P) is False


def test_everybody_knows_empty_group_is_vacuously_true():
    """E_∅ φ: the union relation over zero agents is empty, so 'holds at every successor' is vacuous."""
    model = _chain_model(p_at_2=False)
    assert everybody_knows(model, 2, [], P) is True
    assert everybody_knows(model, 2, [], Not(P)) is True  # vacuous regardless of φ


def test_common_knowledge_empty_group_reduces_to_the_formula_itself():
    """C_∅ φ at w: reflexive closure of the empty relation from w is just {w}, so this IS satisfies_modal(φ, m, w)."""
    model = _chain_model(p_at_2=False)
    assert common_knowledge_holds(model, 0, [], P) == satisfies_modal(P, model, 0)
    assert common_knowledge_holds(model, 2, [], P) == satisfies_modal(P, model, 2)
    assert common_knowledge_holds(model, 2, [], P) is False  # P is false at world 2


def test_common_knowledge_gives_factivity_on_a_reflexive_frame():
    """C_G φ → φ at every world of a reflexive frame (world is always in its own reachable set)."""
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"K:alice": {(0, 0), (1, 1), (2, 2), (0, 1), (1, 0)}},
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )
    for w in model.worlds:
        if common_knowledge_holds(model, w, ["alice"], P):
            assert satisfies_modal(P, model, w) is True


def test_common_knowledge_single_agent_group_equals_reflexive_transitive_knows():
    """C_{a} φ collapses to iterated K_a, since the group union is just K:a itself."""
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"K:alice": {(0, 0), (0, 1), (1, 1), (1, 2), (2, 2)}},
        valuation={0: {"P"}, 1: {"P"}, 2: {"P"}},
    )
    # P true everywhere reachable from 0 (0,1,2 all reachable, all true) -> CK holds.
    assert common_knowledge_holds(model, 0, ["alice"], P) is True
    # Knows(alice, P) at 0 only requires the ONE-STEP successors {0,1} -- also true here,
    # but the two notions genuinely differ once we break truth further down the chain.
    assert satisfies_modal(Knows("alice", P), model, 0) is True


def test_common_knowledge_single_world_is_trivial():
    """A lone reflexive world: C_G φ at w is just φ at w, for any nonempty group."""
    model = KripkeModel(
        worlds={0},
        relations={"K:a": {(0, 0)}, "K:b": {(0, 0)}},
        valuation={0: {"P"}},
    )
    assert common_knowledge_holds(model, 0, ["a", "b"], P) is True
    assert common_knowledge_holds(model, 0, ["a", "b"], Q) is False


# --- cross-check against the FHMV E-ladder fixpoint definition -------------

def _e_ladder_holds(model, world, group, formula, n):
    """φ's truth after ``n`` nested applications of E_G, by direct recursion.

    n=0: φ itself (holds at ``world``). n=k+1: at EVERY group-successor of
    ``world`` (in the union of the group's ``K:`` relations), the k-fold
    ladder holds. This is exactly the FHMV ladder
    ``E_G φ``, ``E_G E_G φ``, ``E_G E_G E_G φ``, … evaluated at ``world`` for
    each ``n`` in turn — built by recursing over successor SETS directly
    (works for any group size), rather than by literally constructing an
    ``And(Knows(...), ...)`` AST that grows with ``n``. ``common_knowledge_holds``
    is claimed (in its own docstring) to equal this ladder's limit; this
    helper lets the tests below verify that claim independently.
    """
    if n == 0:
        return satisfies_modal(formula, model, world)
    successors = set()
    for agent in group:
        successors |= model.successors("K:" + agent, world)
    return all(_e_ladder_holds(model, w2, group, formula, n - 1) for w2 in successors)


def test_e_ladder_n1_matches_everybody_knows():
    """The n=1 rung of the ladder IS everybody_knows by construction — sanity check on the helper itself."""
    model = _chain_model(p_at_2=False)
    for n1 in (True, False):
        m = _chain_model(p_at_2=n1)
        for w in m.worlds:
            assert _e_ladder_holds(m, w, ["a", "b"], P, 1) == everybody_knows(m, w, ["a", "b"], P)


def test_e_ladder_converges_to_common_knowledge_on_the_broken_chain():
    """Hand-derived ladder at world 0 of the P-false-at-2 chain: True, True, False, False, ... (stabilises at n=2).

    n=0: P holds at 0 directly -> True.
    n=1: successors of 0 are {0,1} (b has no edge from 0), P true at both -> True.
    n=2: now must recheck the ladder-1 value AT EACH of {0,1}: ladder1(0)=True,
      but ladder1(1) = everybody_knows(model,1,{a,b},P) needs P at 1's successors
      {0,1} (via a) ∪ {1,2} (via b) = {0,1,2}, and P is FALSE at 2 -> ladder1(1)=False.
      So ladder2(0) = all([True, False]) = False.
    n=3, n=4: once it drops to the fixpoint it stays False (matches common_knowledge_holds).
    """
    model = _chain_model(p_at_2=False)
    expected = [True, True, False, False, False]
    for n, exp in enumerate(expected):
        assert _e_ladder_holds(model, 0, ["a", "b"], P, n) is exp
    assert common_knowledge_holds(model, 0, ["a", "b"], P) is False
    assert _e_ladder_holds(model, 0, ["a", "b"], P, 2) == common_knowledge_holds(model, 0, ["a", "b"], P)


def test_e_ladder_stays_true_on_the_connected_component():
    """Same chain topology, but P true everywhere: every rung of the ladder is True, matching C_G P = True."""
    model = _chain_model(p_at_2=True)
    for n in range(5):
        assert _e_ladder_holds(model, 0, ["a", "b"], P, n) is True
    assert common_knowledge_holds(model, 0, ["a", "b"], P) is True


# ---------------------------------------------------------------------------
# ActionModel: construction, copying, refusals
# ---------------------------------------------------------------------------

def test_action_model_stores_events_pre_and_relations():
    action = ActionModel(
        events=["e1", "e2"],
        pre={"e1": P, "e2": Q},
        relations={"K:a": {("e1", "e1"), ("e2", "e2")}},
    )
    assert action.events == frozenset({"e1", "e2"})
    assert action.pre == {"e1": P, "e2": Q}
    assert action.relation("K:a") == frozenset({("e1", "e1"), ("e2", "e2")})


def test_action_model_missing_relation_name_is_the_empty_relation():
    action = ActionModel(events=["e"], pre={"e": P}, relations={})
    assert action.relation("K:nobody") == frozenset()
    assert action.successors("K:nobody", "e") == set()


def test_action_model_successors_helper():
    action = ActionModel(
        events=["e1", "e2", "e3"],
        pre={"e1": P, "e2": P, "e3": P},
        relations={"K:a": {("e1", "e1"), ("e1", "e2")}},
    )
    assert action.successors("K:a", "e1") == {"e1", "e2"}
    assert action.successors("K:a", "e2") == set()


def test_action_model_copies_inputs_so_later_mutation_does_not_leak_in():
    events = ["e1", "e2"]
    pre = {"e1": P, "e2": Q}
    relations = {"K:a": {("e1", "e1")}}
    action = ActionModel(events=events, pre=pre, relations=relations)

    events.append("e3")
    pre["e3"] = P
    relations["K:a"].add(("e2", "e2"))
    relations["K:b"] = {("e1", "e2")}

    assert action.events == frozenset({"e1", "e2"})
    assert action.pre == {"e1": P, "e2": Q}
    assert action.relation("K:a") == frozenset({("e1", "e1")})
    assert action.relation("K:b") == frozenset()


def test_action_model_missing_precondition_raises_value_error():
    """Every event needs an explicit precondition -- no implicit 'always true' default."""
    with pytest.raises(ValueError, match="no precondition"):
        ActionModel(events=["e1", "e2"], pre={"e1": P}, relations={})


def test_action_model_extra_precondition_raises_value_error():
    """A precondition for an event that isn't in `events` is equally rejected."""
    with pytest.raises(ValueError, match="not in"):
        ActionModel(events=["e1"], pre={"e1": P, "ghost": Q}, relations={})


def test_action_model_repr_does_not_crash_and_mentions_events():
    action = ActionModel(events=["e1"], pre={"e1": P}, relations={"K:a": {("e1", "e1")}})
    text = repr(action)
    assert "e1" in text


# ---------------------------------------------------------------------------
# product_update: precondition filtering, relation combination, valuation
# ---------------------------------------------------------------------------

def test_product_update_worlds_are_filtered_by_precondition():
    """2 worlds x 2 events, but preconditions pin each event to exactly one world -- 2 of 4 pairs survive."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}},
        valuation={0: {"P"}},  # P true at 0, false at 1
    )
    action = ActionModel(
        events=["e1", "e2"],
        pre={"e1": P, "e2": Not(P)},
        relations={"K:a": {("e1", "e1"), ("e2", "e2")}},
    )
    result = product_update(model, action)
    assert result.worlds == frozenset({(0, "e1"), (1, "e2")})


def test_product_update_valuation_is_copied_unchanged_from_the_world():
    """No postconditions exist: (w, e)'s valuation is exactly model's valuation of w, for every surviving e."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"K:a": {(0, 0), (1, 1)}},
        valuation={0: {"P", "Q"}, 1: {"Q"}},
    )
    action = ActionModel(events=["e"], pre={"e": Or(P, Not(P))}, relations={"K:a": {("e", "e")}})
    result = product_update(model, action)
    assert result.atoms_true_at((0, "e")) == frozenset({"P", "Q"})
    assert result.atoms_true_at((1, "e")) == frozenset({"Q"})


def test_product_update_relation_requires_agreement_on_both_sides():
    """(w,e) R (w',e') needs w R w' in the model AND e R e' in the action -- restricted to survivors.

    model K:a is the UNIVERSAL relation on {0,1}; action K:a is the IDENTITY on
    {e1,e2}. Preconditions pin e1 to world 0 and e2 to world 1 (mutually
    exclusive), so only (0,e1) and (1,e2) survive, and since the action only
    ever relates an event to ITSELF, the product K:a relation is exactly the
    two reflexive loops -- agent a can tell the two surviving pairs apart even
    though the base model could not tell 0 from 1.
    """
    model = KripkeModel(
        worlds={0, 1},
        relations={"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}},
        valuation={0: {"P"}},
    )
    action = ActionModel(
        events=["e1", "e2"],
        pre={"e1": P, "e2": Not(P)},
        relations={"K:a": {("e1", "e1"), ("e2", "e2")}},
    )
    result = product_update(model, action)
    assert result.relation("K:a") == frozenset({((0, "e1"), (0, "e1")), ((1, "e2"), (1, "e2"))})


def test_product_update_one_sided_relation_names_under_the_refusal_contract():
    """Adversarial-review revision of this test's ORIGINAL expectation
    (which pinned the unsound behaviour): a relation the MODEL carries but
    the ACTION omits is REFUSED (an omitted agent would come out vacuously
    omniscient — see product_update's docstring), while a relation only the
    ACTION carries stays harmlessly empty in the product (no epistemic
    structure of the base model is destroyed by an extra action-side name)."""
    model = KripkeModel(
        worlds={0, 1},
        relations={"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}, "K:b": {(0, 0), (1, 1)}},
        valuation={},
    )
    action = ActionModel(events=["e"], pre={"e": Or(P, Not(P))}, relations={"K:a": {("e", "e")}})
    with pytest.raises(ValueError, match="K:b"):
        product_update(model, action)

    # Action-only name: model lacks K:extra entirely — empty product
    # relation, everything else unaffected.
    action_full = ActionModel(
        events=["e"], pre={"e": Or(P, Not(P))},
        relations={"K:a": {("e", "e")}, "K:b": {("e", "e")},
                   "K:extra": {("e", "e")}})
    result = product_update(model, action_full)
    assert result.relation("K:extra") == frozenset()
    assert result.relation("K:a") == frozenset({((0, "e"), (0, "e")), ((0, "e"), (1, "e")),
                                                 ((1, "e"), (0, "e")), ((1, "e"), (1, "e"))})


def test_product_update_propagates_domains_unchanged():
    """A model with per-world object domains carries D_w through unchanged onto (w, e)."""
    model = KripkeModel(
        worlds={0, 1}, relations={"K:a": {(0, 0), (1, 1)}},
        valuation={0: {"P"}}, domain=[1, 2, 3],
    )
    action = ActionModel(events=["e"], pre={"e": P}, relations={"K:a": {("e", "e")}})
    result = product_update(model, action)
    assert result.worlds == frozenset({(0, "e")})
    assert result.domain_at((0, "e")) == frozenset({1, 2, 3})


def test_product_update_without_domains_leaves_result_domain_free():
    model = KripkeModel(worlds={0}, relations={"K:a": {(0, 0)}}, valuation={0: {"P"}})
    action = ActionModel(events=["e"], pre={"e": P}, relations={"K:a": {("e", "e")}})
    result = product_update(model, action)
    assert result.domains is None


def test_product_update_neither_input_is_mutated():
    model = KripkeModel(worlds={0, 1}, relations={"K:a": {(0, 0), (0, 1)}}, valuation={0: {"P"}})
    action = ActionModel(events=["e"], pre={"e": Or(P, Not(P))}, relations={"K:a": {("e", "e")}})
    model_worlds_before, action_events_before = model.worlds, action.events
    product_update(model, action)
    assert model.worlds == model_worlds_before
    assert action.events == action_events_before


# ---------------------------------------------------------------------------
# The classic PRIVATE announcement: anne learns P, bob is unaware anything happened
# ---------------------------------------------------------------------------

def _private_announcement_to_anne(fact):
    """2-event action model: 'tell' (anne truthfully learns `fact`) vs 'skip' (nothing told).

    anne's K: relation is the IDENTITY on {tell, skip} -- she perfectly
    distinguishes which event occurred (she is the one being told, or not).
    bob's K: relation is UNIVERSAL on {tell, skip} -- he cannot tell the two
    events apart at all, so he does not even know an announcement took place
    (the textbook "private announcement", van Ditmarsch/van der Hoek/Kooi
    2007 §4.7). 'skip' is unconditionally executable (precondition is the
    tautology fact ∨ ¬fact); 'tell' requires `fact` to actually be true
    (announcements are always truthful in this construction).
    """
    return ActionModel(
        events=["tell", "skip"],
        pre={"tell": fact, "skip": Or(fact, Not(fact))},
        relations={
            "K:anne": {("tell", "tell"), ("skip", "skip")},
            "K:bob": {("tell", "tell"), ("tell", "skip"), ("skip", "tell"), ("skip", "skip")},
        },
    )


def _uncertain_base_model():
    """2 worlds, P true at w0 / false at w1; BOTH anne and bob are initially uncertain which one is actual."""
    universal = {(0, 0), (0, 1), (1, 0), (1, 1)}
    return KripkeModel(
        worlds={0, 1},
        relations={"K:anne": universal, "K:bob": universal},
        valuation={0: {"P"}},
    )


def test_private_announcement_worlds_are_tell_at_true_world_and_skip_everywhere():
    """3 surviving pairs: (w0,tell), (w0,skip), (w1,skip) -- (w1,tell) is filtered out (P false at w1)."""
    model = _uncertain_base_model()
    action = _private_announcement_to_anne(P)
    result = product_update(model, action)
    assert result.worlds == frozenset({(0, "tell"), (0, "skip"), (1, "skip")})


def test_private_announcement_anne_learns_the_fact():
    """At the actual world (w0,tell), anne's only K:anne-successor is (w0,tell) itself -- so she knows P.

    K:anne in the product needs w R w' in the model (universal, always true)
    AND e R e' in the action (identity, so e'=tell). Among the 3 surviving
    product worlds only (0,'tell') has event component 'tell' -- so anne's
    K:anne-successor set of (0,'tell') is the singleton {(0,'tell')}, where P
    holds -- Knows(anne, P) is TRUE.
    """
    model = _uncertain_base_model()
    action = _private_announcement_to_anne(P)
    result = product_update(model, action)
    actual = (0, "tell")
    assert result.successors("K:anne", actual) == {(0, "tell")}
    assert satisfies_modal(Knows("anne", P), result, actual) is True


def test_private_announcement_bob_does_not_learn_the_fact():
    """Bob's K:bob-successors of the actual world are ALL 3 surviving pairs -- P is false at one, so he's ignorant."""
    model = _uncertain_base_model()
    action = _private_announcement_to_anne(P)
    result = product_update(model, action)
    actual = (0, "tell")
    assert result.successors("K:bob", actual) == frozenset({(0, "tell"), (0, "skip"), (1, "skip")})
    assert satisfies_modal(Knows("bob", P), result, actual) is False


def test_private_announcement_bob_does_not_even_know_that_anne_knows():
    """K_bob K_anne P fails at the actual world -- bob doesn't know that anne was told.

    Among bob's 3 successors of the actual world, (0,'skip') is one: there,
    anne's own K:anne-successors are {(0,'skip'),(1,'skip')} (both surviving
    'skip'-pairs), where P is true at one and false at the other -- so
    Knows(anne, P) is FALSE at (0,'skip'). Since bob considers (0,'skip')
    possible, K_bob K_anne P fails at the actual world, even though K_anne P
    itself holds there.
    """
    model = _uncertain_base_model()
    action = _private_announcement_to_anne(P)
    result = product_update(model, action)
    actual = (0, "tell")
    assert satisfies_modal(Knows("anne", P), result, (0, "skip")) is False
    assert satisfies_modal(Knows("bob", Knows("anne", P)), result, actual) is False


# ---------------------------------------------------------------------------
# public_announcement_action agrees with the existing announce() PAL route
# ---------------------------------------------------------------------------

def _agreement_model():
    """3 worlds, 2 agents, non-trivial relations and valuation -- used to differentially test PAL agreement."""
    return KripkeModel(
        worlds={0, 1, 2},
        relations={
            "K:a": {(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)},
            "K:b": {(0, 0), (1, 1), (2, 2), (0, 2), (2, 0)},
        },
        valuation={0: {"P", "Q"}, 1: {"Q"}, 2: {"P"}},
    )


def test_public_announcement_action_agrees_with_announce_on_worlds():
    model = _agreement_model()
    restricted = announce(model, P)
    action = public_announcement_action(P, ["a", "b"])
    product = product_update(model, action)
    mapped_back = {w for (w, e) in product.worlds}
    assert mapped_back == restricted.worlds
    # explicit bijection: exactly one product world per surviving base world
    assert len(product.worlds) == len(restricted.worlds)


def test_public_announcement_action_agrees_with_announce_on_relations():
    model = _agreement_model()
    restricted = announce(model, P)
    action = public_announcement_action(P, ["a", "b"])
    product = product_update(model, action)
    for name in ("K:a", "K:b"):
        mapped = {(w1, w2) for ((w1, _), (w2, _)) in product.relation(name)}
        assert mapped == set(restricted.relation(name))


def test_public_announcement_action_agrees_with_announce_on_valuation():
    model = _agreement_model()
    restricted = announce(model, Or(P, Q))
    action = public_announcement_action(Or(P, Q), ["a", "b"])
    product = product_update(model, action)
    for (w, e) in product.worlds:
        assert product.atoms_true_at((w, e)) == restricted.atoms_true_at(w)


def test_public_announcement_action_single_event_uses_bang_glyph():
    """The one event public_announcement_action uses is the kit's own PAL glyph '!' (as in [phi!]psi)."""
    action = public_announcement_action(P, ["a"])
    assert action.events == frozenset({"!"})


# ---------------------------------------------------------------------------
# Muddy Children (3 children, k=2 actually muddy: anne and bert, carla clean)
# ---------------------------------------------------------------------------

_CHILDREN = ["anne", "bert", "carla"]


def _muddy(name):
    return Atom("Muddy", [Constant(name)])


_M_ANNE, _M_BERT, _M_CARLA = _muddy("anne"), _muddy("bert"), _muddy("carla")
_ACTUAL_WORLD = (True, True, False)  # (anne muddy, bert muddy, carla clean)


def _build_muddy_children_model():
    """8 worlds = every muddiness triple (anne, bert, carla) in {True, False}^3.

    Each child's K: relation is the EQUIVALENCE relation "agrees with w on the
    OTHER TWO children's muddiness, may differ on the child's own" -- the
    standard muddy-children observation (you see everyone else, not
    yourself). Reflexive edges are included EXPLICITLY: KripkeModel stores
    raw edge sets and satisfies_modal has no built-in reflexivity, so the
    equivalence relation must be built with (w,w) present for every w, or
    K_x(Muddy(x) -> Muddy(x)) would fail at worlds with no other successor.
    """
    worlds = list(itertools.product([True, False], repeat=3))

    def edges_for(index):
        return {
            (w, w2)
            for w in worlds
            for w2 in worlds
            if all(w[i] == w2[i] for i in range(3) if i != index)
        }

    relations = {
        "K:anne": edges_for(0),
        "K:bert": edges_for(1),
        "K:carla": edges_for(2),
    }
    valuation = {}
    for w in worlds:
        atoms = set()
        if w[0]:
            atoms.add(_M_ANNE.to_unicode_str())
        if w[1]:
            atoms.add(_M_BERT.to_unicode_str())
        if w[2]:
            atoms.add(_M_CARLA.to_unicode_str())
        valuation[w] = atoms
    return KripkeModel(worlds=worlds, relations=relations, valuation=valuation)


def _doesnt_know_own_state(agent, atom):
    """¬K_agent atom ∧ ¬K_agent ¬atom -- 'agent does not know their own muddy/clean status'."""
    return And(Not(Knows(agent, atom)), Not(Knows(agent, Not(atom))))


_AT_LEAST_ONE_MUDDY = Or(Or(_M_ANNE, _M_BERT), _M_CARLA)
_NOBODY_KNOWS_OWN_STATE = And(
    _doesnt_know_own_state("anne", _M_ANNE),
    And(_doesnt_know_own_state("bert", _M_BERT), _doesnt_know_own_state("carla", _M_CARLA)),
)


def test_muddy_children_initial_model_has_eight_worlds_and_equivalence_relations():
    model = _build_muddy_children_model()
    assert len(model.worlds) == 8
    for name in ("K:anne", "K:bert", "K:carla"):
        edges = model.relation(name)
        # equivalence: reflexive, symmetric, and each class has exactly 2 worlds
        assert all((w, w) in edges for w in model.worlds)
        assert all((w2, w) in edges for (w, w2) in edges)
        for w in model.worlds:
            assert len({w2 for (w1, w2) in edges if w1 == w}) == 2


def test_muddy_children_before_any_announcement_nobody_knows_anything():
    """No child knows their own status in the raw 8-world model -- every K-class has 2 worlds differing in own bit."""
    model = _build_muddy_children_model()
    assert satisfies_modal(Knows("anne", _M_ANNE), model, _ACTUAL_WORLD) is False
    assert satisfies_modal(Knows("anne", Not(_M_ANNE)), model, _ACTUAL_WORLD) is False


def test_muddy_children_round0_at_least_one_muddy_removes_exactly_the_all_clean_world():
    """announce('at least one muddy') keeps exactly 7 of 8 worlds -- (False,False,False) is the sole casualty."""
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    assert len(round0.worlds) == 7
    assert (False, False, False) not in round0.worlds
    assert _ACTUAL_WORLD in round0.worlds


def test_muddy_children_before_round1_actual_child_still_does_not_know():
    """At the actual world (k=2 muddy), before 'nobody knows their own state' is announced, anne is still ignorant.

    anne's K:anne-successors of (T,T,F) within round0 (7 worlds) are the
    worlds agreeing on bert=T, carla=F: (T,T,F) and (F,T,F), BOTH survive
    round0 (neither is the all-clean world) -- so anne genuinely can't tell
    which one is actual, and Muddy(anne) differs between them.
    """
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    assert round0.successors("K:anne", _ACTUAL_WORLD) == {(True, True, False), (False, True, False)}
    assert satisfies_modal(Knows("anne", _M_ANNE), round0, _ACTUAL_WORLD) is False


def test_muddy_children_nobody_knows_own_state_is_true_at_the_actual_world():
    """The round-1 announcement is genuinely TRUE at the k=2 actual world (a real, truthful public announcement)."""
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    assert satisfies_modal(_NOBODY_KNOWS_OWN_STATE, round0, _ACTUAL_WORLD) is True


def test_muddy_children_nobody_knows_own_state_is_false_at_the_lone_muddy_worlds():
    """The round-1 statement is FALSE at the 3 'exactly one muddy' worlds -- that one child would deduce their state.

    E.g. at (True,False,False) (anne alone muddy), anne's only round0-surviving
    K:anne-successor is herself (the world (False,False,False) that would make
    her uncertain was removed in round 0) -- so she'd already know she's
    muddy, and the 'nobody knows' announcement would be false there.
    """
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    for lone_muddy_world in ((True, False, False), (False, True, False), (False, False, True)):
        assert lone_muddy_world in round0.worlds
        assert satisfies_modal(_NOBODY_KNOWS_OWN_STATE, round0, lone_muddy_world) is False


def test_muddy_children_after_round1_the_two_muddy_children_know_carla_does_not():
    """The classic k=2 result: after 'nobody knows', anne and bert each deduce their own muddiness; carla still doesn't.

    round1 = announce(round0, 'nobody knows own state') keeps exactly the 4
    worlds where that statement was true: the 3 'exactly two muddy' worlds
    plus the 1 'all three muddy' world. At the actual world (T,T,F), anne's
    only remaining K:anne-successor is herself (her old alternative
    (F,T,F) was a lone-muddy world, eliminated in round1) -- likewise for
    bert. Carla's alternatives (T,T,T) and (T,T,F) BOTH survive round1 (both
    are 'two-or-three muddy' worlds), so she remains genuinely uncertain
    whether she is clean or muddy.
    """
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    round1 = announce(round0, _NOBODY_KNOWS_OWN_STATE)
    assert round1.worlds == frozenset({
        (True, True, False), (True, False, True), (False, True, True), (True, True, True),
    })
    assert satisfies_modal(Knows("anne", _M_ANNE), round1, _ACTUAL_WORLD) is True
    assert satisfies_modal(Knows("bert", _M_BERT), round1, _ACTUAL_WORLD) is True
    assert satisfies_modal(Knows("carla", _M_CARLA), round1, _ACTUAL_WORLD) is False
    assert satisfies_modal(Knows("carla", Not(_M_CARLA)), round1, _ACTUAL_WORLD) is False


def test_muddy_children_at_least_one_muddy_becomes_common_knowledge_after_round0():
    """Public announcements become common knowledge: 'at least one muddy' is C_G after round0 -- but NOT before.

    round0's 7 worlds are the full 3-cube (Q3, 3-connected / vertex-transitive)
    minus one vertex; removing a single vertex from a 3-connected graph leaves
    it connected, so every world is reachable from every other via the union
    of the three K: relations -- and 'at least one muddy' is true at all 7 by
    construction (we removed exactly the one world where it was false), so it
    is common knowledge throughout. In the ORIGINAL 8-world model, the
    all-clean world is still reachable from the actual world (the cube is
    connected before removal too), so common knowledge fails there --
    demonstrating the announcement genuinely changes what's common knowledge.

    (This does NOT contradict the well-known subtlety that a Moore-type
    announcement -- one whose truth depends on the announcement act itself,
    e.g. 'P and you don't know P' -- can fail to become common knowledge even
    though it was truthfully announced; see test_pal.py's Moore-sentence
    tests. 'At least one is muddy' has no such self-reference: it's a plain
    positive fact about the muddiness triple, so it stays common knowledge
    once announced.)
    """
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    assert common_knowledge_holds(round0, _ACTUAL_WORLD, _CHILDREN, _AT_LEAST_ONE_MUDDY) is True
    assert common_knowledge_holds(model, _ACTUAL_WORLD, _CHILDREN, _AT_LEAST_ONE_MUDDY) is False


def test_muddy_children_via_product_update_agrees_with_announce_round0():
    """product_update(model0, public_announcement_action(at-least-one, children)) matches announce() round0 exactly."""
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    action0 = public_announcement_action(_AT_LEAST_ONE_MUDDY, _CHILDREN)
    product0 = product_update(model, action0)

    mapped_worlds = {w for (w, e) in product0.worlds}
    assert mapped_worlds == round0.worlds
    for name in ("K:anne", "K:bert", "K:carla"):
        mapped_edges = {(w1, w2) for ((w1, _), (w2, _)) in product0.relation(name)}
        assert mapped_edges == set(round0.relation(name))
    actual0 = (_ACTUAL_WORLD, "!")
    assert satisfies_modal(Knows("anne", _M_ANNE), product0, actual0) == \
        satisfies_modal(Knows("anne", _M_ANNE), round0, _ACTUAL_WORLD)


def test_muddy_children_via_product_update_agrees_with_announce_round1_and_gets_k2_result():
    """Chaining product_update twice (round0 then round1) reproduces the classic k=2 result -- anne/bert know, carla doesn't."""
    model = _build_muddy_children_model()
    action0 = public_announcement_action(_AT_LEAST_ONE_MUDDY, _CHILDREN)
    product0 = product_update(model, action0)

    action1 = public_announcement_action(_NOBODY_KNOWS_OWN_STATE, _CHILDREN)
    product1 = product_update(product0, action1)

    # cross-check the world set against the announce() route, unwrapping the nested (w,"!"),"!") tuples
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    round1 = announce(round0, _NOBODY_KNOWS_OWN_STATE)
    mapped_worlds = {w for ((w, _e0), _e1) in product1.worlds}
    assert mapped_worlds == round1.worlds

    actual1 = ((_ACTUAL_WORLD, "!"), "!")
    assert actual1 in product1.worlds
    assert satisfies_modal(Knows("anne", _M_ANNE), product1, actual1) is True
    assert satisfies_modal(Knows("bert", _M_BERT), product1, actual1) is True
    assert satisfies_modal(Knows("carla", _M_CARLA), product1, actual1) is False


def test_product_update_refuses_an_action_that_omits_a_model_agent():
    """Adversarial-review regression: forgetting agent c in a public
    announcement previously EMPTIED K:c in the product (K_c φ vacuously
    true for every φ — factivity gone). product_update now refuses the
    omission loudly instead of manufacturing an omniscient agent."""
    from unicode_fol_kit.fol.nodes import Atom

    p = Atom("P", ())
    model = KripkeModel(
        worlds={0, 1},
        relations={"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)},
                   "K:c": {(0, 0), (0, 1), (1, 0), (1, 1)}},
        valuation={0: {"P"}},
    )
    action = public_announcement_action(p, ["a"])       # c forgotten
    with pytest.raises(ValueError, match="K:c"):
        product_update(model, action)
