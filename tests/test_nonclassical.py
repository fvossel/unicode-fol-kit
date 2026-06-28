"""Tests for the non-classical neighbours: free logic, public-announcement logic,
counterfactual conditionals, and circumscriptive (non-monotonic) entailment.

Each is hand-checked on its characteristic phenomena: free logic blocks universal
instantiation / existential generalisation for non-existing terms; a public
announcement turns ignorance into knowledge yet makes a Moore sentence false;
counterfactuals are non-monotonic in the antecedent; and circumscription retracts a
conclusion when premises are strengthened.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Constant, Knows,
)
from unicode_fol_kit.semantics.free_logic import FreeModel, free_holds
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.dynamic_epistemic import announce, box_announce, diamond_announce
from unicode_fol_kit.semantics.conditional import CounterfactualModel, would, might
from unicode_fol_kit.semantics.nonmonotonic import minimal_entails, minimal_models


# --------------------------------------------------------------------------- #
# Free logic.
# --------------------------------------------------------------------------- #

x = Variable("x")
c = Constant("c")
Px = lambda t: Atom("P", [t])
_ALL_P = Quantifier("∀", x, Px(x))
_EXISTS_EQ_C = Quantifier("∃", x, Atom("=", [x, c]))


def test_free_logic_blocks_universal_instantiation():
    # c denotes a non-existing object 1; the inner (existing) domain is {0}, P of 0.
    m = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 1},
                  predicates={("P", 1): frozenset({(0,)})})
    assert free_holds(_ALL_P, m) is True             # ∀x P(x) over the existing domain
    assert free_holds(Px(c), m) is False             # but P(c) fails — c is non-existing
    assert free_holds(Implies(_ALL_P, Px(c)), m) is False     # UI is invalid
    assert free_holds(Atom("E!", [c]), m) is False   # c does not exist
    assert free_holds(_EXISTS_EQ_C, m) is False      # EG ∃x(x=c) fails


def test_free_logic_guarded_rules_hold_for_existing_terms():
    m = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 0},
                  predicates={("P", 1): frozenset({(0,)})})
    assert free_holds(Atom("E!", [c]), m) is True
    assert free_holds(Implies(And(_ALL_P, Atom("E!", [c])), Px(c)), m) is True  # guarded UI
    assert free_holds(_EXISTS_EQ_C, m) is True       # c exists, so EG goes through


def test_free_logic_non_denoting_constant():
    # c is absent from the interpretation: non-denoting. Negative free logic: P(c) false.
    m = FreeModel(outer=(0,), existing=frozenset({0}), constants={})
    assert free_holds(Px(c), m) is False
    assert free_holds(Atom("E!", [c]), m) is False
    # positive policy: self-identity of a non-denoting term is true.
    assert free_holds(Atom("=", [c, c]), m, policy="positive") is True
    assert free_holds(Atom("=", [c, c]), m, policy="negative") is False


# --------------------------------------------------------------------------- #
# Public announcement logic.
# --------------------------------------------------------------------------- #

p = Atom("p", ())
_Kap = Knows("a", p)
# Agent a cannot tell world 0 (p) from world 1 (¬p).
_PAL = KripkeModel([0, 1], {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}}, {0: {"p"}})


def test_announcement_creates_knowledge():
    assert satisfies_modal(_Kap, _PAL, 0) is False           # a does not know p
    assert box_announce(_PAL, 0, p, _Kap) is True            # ...but [p!]K_a p
    # the updated model has dropped world 1.
    updated = announce(_PAL, p)
    assert 1 not in updated.worlds and satisfies_modal(_Kap, updated, 0) is True


def test_moore_sentence_is_self_refuting():
    moore = And(p, Not(_Kap))                                # p ∧ ¬K_a p
    assert satisfies_modal(moore, _PAL, 0) is True           # true before announcing
    assert diamond_announce(_PAL, 0, moore, moore) is False  # ...but false after announcing it
    assert box_announce(_PAL, 0, moore, _Kap) is True        # announcing it makes a know p


# --------------------------------------------------------------------------- #
# Counterfactual conditionals (Lewis spheres).
# --------------------------------------------------------------------------- #

A, B, C = Atom("A", ()), Atom("B", ()), Atom("C", ())
# world 0 actual; closest A-world is 1 (A,B); a farther A∧C-world 2 (A,C, no B).
_CF = CounterfactualModel(
    (0, 1, 2),
    {0: frozenset(), 1: frozenset({"A", "B"}), 2: frozenset({"A", "C"})},
    {0: [frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})]},
)


def test_counterfactual_basic():
    assert would(_CF, 0, A, B) is True               # if A were, B would
    assert would(_CF, 0, A, Not(B)) is False
    assert might(_CF, 0, A, C) is False              # the closest A-world (1) is not C


def test_counterfactual_antecedent_strengthening_fails():
    # A □→ B holds, but (A ∧ C) □→ B does NOT — the hallmark non-monotonicity.
    assert would(_CF, 0, A, B) is True
    assert would(_CF, 0, And(A, C), B) is False


def test_counterfactual_vacuously_true_with_impossible_antecedent():
    assert would(_CF, 0, And(A, Not(A)), B) is True  # no antecedent-world anywhere


# --------------------------------------------------------------------------- #
# Circumscription (non-monotonic).
# --------------------------------------------------------------------------- #

a = Constant("a")
Pa, Qa = Atom("P", [a]), Atom("Q", [a])


def test_closed_world_assumption():
    # Nothing is asserted, so minimally P is empty: ∅ ⊨_circ ¬P(a).
    assert minimal_entails([], Not(Pa), circumscribed={"P"}, max_size=2) is True
    # Classical entailment does NOT give this (P(a) could be true).


def test_circumscription_is_non_monotonic():
    # {P(a)→Q(a)} circumscriptively entails ¬Q(a) (Q minimally empty)...
    assert minimal_entails([Implies(Pa, Qa)], Not(Qa),
                           circumscribed={"P", "Q"}, max_size=2) is True
    # ...but adding P(a) forces Q(a), retracting the conclusion.
    assert minimal_entails([Implies(Pa, Qa), Pa], Not(Qa),
                           circumscribed={"P", "Q"}, max_size=2) is False


def test_circumscription_preserves_asserted_facts():
    assert minimal_entails([Pa], Pa, circumscribed={"P"}, max_size=2) is True
    assert minimal_entails([Pa], Not(Pa), circumscribed={"P"}, max_size=2) is False


def test_minimal_models_are_a_subset_of_all_models():
    # P(a) ∨ P(b) over a 2-element domain has minimal models with a singleton P.
    b = Constant("b")
    prem = [Or(Atom("P", [a]), Atom("P", [b])), Atom("≠", [a, b])]
    mods = minimal_models(prem, circumscribed={"P"}, max_size=2)
    assert mods, "expected at least one minimal model"
    # In every minimal model, P is a singleton (never {a, b}).
    for m in mods:
        ext = m.predicates.get(("P", 1), set())
        assert len(ext) == 1
