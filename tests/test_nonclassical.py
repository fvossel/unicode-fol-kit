"""Tests for the non-classical neighbours: free logic, public-announcement logic,
counterfactual conditionals, and circumscriptive (non-monotonic) entailment.

Each is hand-checked on its characteristic phenomena: free logic blocks universal
instantiation / existential generalisation for non-existing terms; a public
announcement turns ignorance into knowledge yet makes a Moore sentence false;
counterfactuals are non-monotonic in the antecedent; and circumscription retracts a
conclusion when premises are strengthened.
"""

import pytest

from unicode_fol_kit import is_modal_valid, is_valid_tableau, to_english
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Quantifier, Variable, Constant, Knows,
    Would, Might, Contrast,
)
from unicode_fol_kit.semantics.free_logic import FreeModel, free_holds
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.dynamic_epistemic import announce, box_announce, diamond_announce
from unicode_fol_kit.semantics.conditional import (
    CounterfactualModel, cf_satisfies, would, might,
)
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
# The counterfactuals as PARSED operators: □→ (Would) and ◇→ (Might).
# --------------------------------------------------------------------------- #

_MODAL = MSFLParser(modal=True)


class TestCounterfactualOperators:
    def test_the_glyphs_parse_and_round_trip(self):
        for src, cls in [("A □→ B", Would), ("A ◇→ B", Might)]:
            f = _MODAL.parse(src)
            assert isinstance(f, cls)
            assert f.to_unicode_str() == src
            assert _MODAL.parse(f.to_unicode_str()) == f
            assert Node.from_dict(f.to_dict()) == f

    def test_the_glyph_is_not_lexed_as_a_box_plus_an_arrow(self):
        # □→ starts with the box glyph, so without terminal priority "□→" would lex
        # as BOX followed by →, silently parsing the counterfactual as a modalised
        # MATERIAL conditional — the very confusion the connective exists to avoid.
        assert isinstance(_MODAL.parse("A □→ B"), Would)
        assert isinstance(_MODAL.parse("□A → B"), Implies)      # genuinely material
        assert isinstance(_MODAL.parse("□A □→ ◇B"), Would)      # both glyphs, one line
        assert _MODAL.parse("A □→ B") != _MODAL.parse("□A → B")

    def test_it_binds_tighter_than_the_material_arrow_but_looser_than_and(self):
        # `A ∧ B □→ C` must group as `(A ∧ B) □→ C` — the reading the English has.
        f = _MODAL.parse("A ∧ B □→ C")
        assert isinstance(f, Would) and f.left == And(A, B)
        # ... and → is looser still, so it stays on the outside.
        g = _MODAL.parse("A → B □→ C")
        assert isinstance(g, Implies) and isinstance(g.right, Would)

    def test_evaluation_agrees_with_the_would_might_api(self):
        # The parsed node and the function API must be the same semantics, not two.
        assert cf_satisfies(_MODAL.parse("A □→ B"), _CF, 0) == would(_CF, 0, A, B)
        assert cf_satisfies(_MODAL.parse("A ◇→ C"), _CF, 0) == might(_CF, 0, A, C)
        assert cf_satisfies(_MODAL.parse("A □→ B"), _CF, 0) is True
        assert cf_satisfies(_MODAL.parse("A ◇→ C"), _CF, 0) is False

    def test_antecedent_strengthening_fails_through_the_parser_too(self):
        assert cf_satisfies(_MODAL.parse("A □→ B"), _CF, 0) is True
        assert cf_satisfies(_MODAL.parse("A ∧ C □→ B"), _CF, 0) is False

    def test_counterfactuals_nest(self):
        # A conditional inside a conditional is evaluated at the world under
        # consideration with THAT world's spheres — not expressible before, since
        # the old evaluator took antecedent/consequent as propositional formulas.
        f = _MODAL.parse("A □→ (C □→ A)")
        assert cf_satisfies(f, _CF, 0) is True
        assert cf_satisfies(_MODAL.parse("(A □→ B) ∧ (A □→ ¬B)"), _CF, 0) is False

    def test_might_is_the_dual_of_would(self):
        for src_w, src_m in [("A □→ ¬B", "A ◇→ B"), ("A □→ ¬C", "A ◇→ C")]:
            assert (cf_satisfies(_MODAL.parse(src_w), _CF, 0)
                    is not cf_satisfies(_MODAL.parse(src_m), _CF, 0))

    def test_might_is_vacuously_FALSE_where_would_is_vacuously_true(self):
        # The duality inverts the vacuous case — worth pinning, since "vacuously
        # true" is the intuition people carry over from the material conditional.
        impossible = "A ∧ ¬A"
        assert cf_satisfies(_MODAL.parse(f"({impossible}) □→ B"), _CF, 0) is True
        assert cf_satisfies(_MODAL.parse(f"({impossible}) ◇→ B"), _CF, 0) is False

    def test_the_sphere_ordering_is_not_an_accessibility_relation(self):
        # Two honest boundaries. The Kripke evaluator must REJECT a counterfactual
        # rather than guess, and the sphere evaluator must reject a modal operator.
        km = KripkeModel(worlds=["w"], relations={}, valuation={"w": ["A", "B"]})
        with pytest.raises(NotImplementedError):
            satisfies_modal(_MODAL.parse("A □→ B"), km, "w")
        with pytest.raises(TypeError):
            cf_satisfies(_MODAL.parse("□A □→ B"), _CF, 0)

    def test_the_tableaux_refuse_rather_than_answer_wrongly(self):
        # A □→ A is a Lewis validity, but the accessibility-relation tableaux have
        # no sphere rule for it. They must RAISE with a pointer at the sphere
        # tools — a silent False here would be a wrong validity verdict, and a
        # silent True an unproved one. has_modal now counts Would/Might as modal,
        # so the classical tableau routes here and gets the same clean guard.
        identity = _MODAL.parse("A □→ A")
        with pytest.raises(NotImplementedError, match="cf_valid|cf_satisfies"):
            is_modal_valid(identity, frame="T")
        with pytest.raises(NotImplementedError, match="cf_valid|cf_satisfies"):
            is_valid_tableau(identity)

    @pytest.mark.parametrize("method", ["to_z3", "to_prover9", "to_tptp"])
    def test_no_first_order_export(self, method):
        # Collapsing □→ to the material → is exactly the mistake the connective
        # exists to avoid, so the exporters refuse instead of silently lowering.
        for src in ["A □→ B", "A ◇→ B"]:
            with pytest.raises(NotImplementedError, match="ounterfactual"):
                getattr(_MODAL.parse(src), method)()

    def test_verbalization_marks_the_subjunctive(self):
        assert to_english(_MODAL.parse("A □→ B")) == \
            "if A were the case, B would be"
        assert to_english(_MODAL.parse("A ◇→ B")) == \
            "if A were the case, B might be"

    def test_lewis_identity_holds_everywhere(self):
        # A □→ A: either some sphere holds an A-world — and then it witnesses the
        # conditional, every A-world in it being trivially an A-world — or none
        # does and the vacuous disjunct applies. Machine-checked in Isabelle by
        # tests/test_isabelle_conditional.py.
        identity = _MODAL.parse("A □→ A")
        for model in (_CF, CounterfactualModel(
                (0, 1), {0: frozenset({"A"}), 1: frozenset()},
                {0: [frozenset({0, 1})], 1: [frozenset({0, 1})]})):
            for w in model.worlds:
                assert cf_satisfies(identity, model, w) is True


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
