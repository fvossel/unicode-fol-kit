"""Inter-modality frame conditions and cross-family bridges in the FO shallow embedding.

``fol.qml`` used to emit axioms only for the alethic relation ``R`` and the agent-indexed
ones, so every temporal and deontic principle came back INVALID — while the Isabelle and
THF routes already asserted ``t_refl`` / ``t_trans`` / ``n_in_t`` / ``d_serial`` and
``satisfies_modal`` evaluated ``Always`` / ``Eventually`` over the reflexive-transitive
closure. This file pins the repaired contract from three sides:

- the principles that are now VALID by default, and the near-misses that must STAY
  invalid (a guard against an axiom set that is too strong);
- soundness against the Kripke oracle by exhaustive small-model enumeration, plus the one
  formula that is oracle-valid but out of reach here (temporal induction) and the
  ``first_step`` axiom that brings the fixpoint unfolding *into* reach;
- the opt-in ``bridges=``: each principle INVALID without its bridge, VALID with it, the
  reversed direction still invalid, the two ``D ⊆ R`` artefacts that the emitted meet
  condition must NOT carry, and the ValueError for a bridge whose partner family the
  formula never mentions.

It also pins the *gating* guarantee — for a formula in the alethic fragment the axiom list
is unchanged, member for member — because several suite queries elsewhere sit on a Z3
knife edge where any extra axiom can flip a verdict.

Formulas are built from the AST classes, never from typed operator glyphs, so no test can
fail for an encoding reason.
"""

from itertools import combinations, product

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Implies, Box, Diamond, Quantifier, Variable, Constant,
    Knows, Believes, Says, Obligatory, Permitted,
    Always, Eventually, Next, Historically, Once, Previous,
)
from unicode_fol_kit.fol.qml import (
    qml_axioms, qml_is_valid, qml_equivalent, QML_BRIDGES, QML_RELATIONS,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

P = Atom("P", ())
Q = Atom("Q", ())
agent = Constant("a")
x = Variable("x")

# A deontic non-theorem comes back False by Z3 *unknown*, not by a countermodel: the
# ∃-quantified seriality axiom defeats Z3's model finder, identically at 1 s / 2 s / 10 s
# budgets (the same behaviour frame="KD" has always had). A short budget therefore costs
# no reliability here and keeps the suite fast — the reasoning test_lj_search.py documents
# for its own timeout constant.
_UNKNOWN_TIMEOUT = 1000


# ---------------------------------------------------------------------------
# Default-on temporal frame conditions: T reflexive + transitive, N ⊆ T
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula", [
    Implies(Always(P), P),                          # G φ → φ          (T reflexive)
    Implies(Always(P), Always(Always(P))),          # G φ → G G φ      (T transitive)
    Implies(Always(P), Eventually(P)),              # G φ → F φ
    Implies(Always(P), Next(P)),                    # G φ → X φ        (N ⊆ T)
    Implies(P, Eventually(P)),                      # φ → F φ
    Implies(Historically(P), P),                    # H φ → φ
    Implies(Historically(P), Historically(Historically(P))),
    Implies(Historically(P), Previous(P)),          # H φ → Y φ
    Implies(P, Once(P)),                            # φ → Once φ
], ids=lambda f: f.to_unicode_str())
def test_temporal_principles_valid_by_default(formula):
    assert qml_is_valid(formula) is True, formula.to_unicode_str()


@pytest.mark.parametrize("formula", [
    Implies(Next(P), P),                            # X φ → φ (a step need not be back)
    Implies(Eventually(P), Always(P)),              # F φ → G φ
    Implies(P, Always(P)),                          # φ → G φ
    Implies(Always(P), Historically(P)),            # G φ → H φ (future ≠ past)
    Implies(Next(P), Eventually(P)),                # X φ → F φ (X is vacuous at a dead end)
], ids=lambda f: f.to_unicode_str())
def test_temporal_non_theorems_stay_invalid(formula):
    # Guard against an axiom set that is too strong: adding reflexivity/transitivity of T
    # and N ⊆ T must NOT collapse the future into the present, the past, or the one-step
    # successor. Each of these is refuted by the Kripke oracle too (see the differential
    # below), so a True here would be a genuine unsoundness, not mere over-approximation.
    assert qml_is_valid(formula) is False, formula.to_unicode_str()


# ---------------------------------------------------------------------------
# Default-on deontic seriality (Standard Deontic Logic, KD)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula", [
    Implies(Obligatory(P), Permitted(P)),                     # D axiom: O φ → P φ
    Implies(Obligatory(P), Not(Obligatory(Not(P)))),          # O φ → ¬O¬φ
    Implies(Obligatory(Implies(P, Q)),
            Implies(Obligatory(P), Obligatory(Q))),           # K axiom for O
], ids=lambda f: f.to_unicode_str())
def test_deontic_principles_valid_by_default(formula):
    assert qml_is_valid(formula) is True, formula.to_unicode_str()


@pytest.mark.parametrize("formula", [
    Implies(Obligatory(P), P),                                # O φ → φ: KD is not KT
    Implies(P, Obligatory(P)),                                # φ → O φ
], ids=lambda f: f.to_unicode_str())
def test_deontic_non_theorems_stay_invalid(formula):
    assert qml_is_valid(formula, timeout=_UNKNOWN_TIMEOUT) is False, formula.to_unicode_str()


def test_deontic_true_means_valid_over_serial_models_only():
    # The honest reading of the qml/oracle disagreement: qml judges O φ → P φ under the
    # default-on seriality, while satisfies_modal enforces no frame condition at all, so a
    # hand-built DEAD-END deontic model refutes it there. Neither side is wrong; the
    # verdict's meaning differs, and that is what the docstring promises.
    assert qml_is_valid(Implies(Obligatory(P), Permitted(P))) is True
    dead_end = KripkeModel(worlds={0}, relations={"deontic": set()}, valuation={0: set()})
    assert satisfies_modal(Obligatory(P), dead_end, 0) is True     # vacuously
    assert satisfies_modal(Permitted(P), dead_end, 0) is False
    assert satisfies_modal(Implies(Obligatory(P), Permitted(P)), dead_end, 0) is False


# ---------------------------------------------------------------------------
# Differential: FO embedding vs exhaustive Kripke enumeration over "temporal"
# ---------------------------------------------------------------------------

def _temporal_valid_by_enumeration(formula, max_worlds=3):
    """True iff ``formula`` holds at every world of every small model over "temporal"."""
    atoms = ["P"]
    cells = [frozenset(c) for r in range(len(atoms) + 1) for c in combinations(atoms, r)]
    for n in range(1, max_worlds + 1):
        worlds = list(range(n))
        edges = [(i, j) for i in worlds for j in worlds]
        for mask in product((False, True), repeat=len(edges)):
            rel = {e for e, inc in zip(edges, mask) if inc}
            for assignment in product(cells, repeat=n):
                model = KripkeModel(worlds=worlds, relations={"temporal": rel},
                                    valuation=dict(zip(worlds, assignment)))
                if any(not satisfies_modal(formula, model, w) for w in worlds):
                    return False
    return True


_TEMPORAL_BATTERY = [
    Implies(Always(P), P),
    Implies(Always(P), Always(Always(P))),
    Implies(Always(P), Eventually(P)),
    Implies(Always(P), Next(P)),
    Implies(P, Eventually(P)),
    Implies(Historically(P), P),
    Implies(P, Once(P)),
    Implies(Next(P), P),
    Implies(Eventually(P), Always(P)),
    Implies(P, Always(P)),
    Implies(Always(P), Historically(P)),
    Implies(Next(P), Eventually(P)),
]


@pytest.mark.parametrize("formula", _TEMPORAL_BATTERY, ids=lambda f: f.to_unicode_str())
def test_temporal_embedding_is_sound_wrt_kripke_enumeration(formula):
    # SOUNDNESS, not equality: the embedding asserts T ⊇ N* plus the first-order
    # consequence `first_step` of the converse, never the converse itself, so it may still
    # fail to prove an oracle-valid formula (temporal induction, pinned below) — but it
    # must never prove one the oracle refutes.
    if qml_is_valid(formula, timeout=_UNKNOWN_TIMEOUT):
        assert _temporal_valid_by_enumeration(formula, max_worlds=2) is True, (
            f"{formula.to_unicode_str()}: qml says valid, Kripke enumeration refutes it")


def test_temporal_induction_is_out_of_reach():
    # KNOWN GAP, pinned so it cannot silently change: (φ ∧ G(φ → Xφ)) → Gφ is true in
    # every intended model (the oracle reads Always over the reflexive-transitive CLOSURE
    # of the one-step relation), but deriving it needs the whole of T ⊆ N* — that the
    # witnessing path be FINITE — which is not first-order definable. Unrolling the first
    # step, which `first_step` licenses, gets one step and no further. Decide this one
    # with unicode_fol_kit.hol.isabelle_runner.isabelle_decide_modal, whose t_in_nstar
    # axiom pins t to rtranclp n.
    induction = Implies(And(P, Always(Implies(P, Next(P)))), Always(P))
    assert _temporal_valid_by_enumeration(induction, max_worlds=3) is True
    assert qml_is_valid(induction, timeout=_UNKNOWN_TIMEOUT) is False


@pytest.mark.parametrize("formula", [
    Implies(Always(P), And(P, Next(Always(P)))),        # → : needs only T ⊇ N*
    Implies(And(P, Next(Always(P))), Always(P)),        # ← : needs first_step
], ids=["unfold-right", "unfold-left"])
def test_both_directions_of_the_fixpoint_unfolding_are_provable(formula):
    # The ← direction used to be pinned as unreachable "because T ⊆ N* is not first-order
    # definable". That reason is right about T ⊆ N* and wrong about this principle: the
    # first-order CONSEQUENCE first_step (T(w,v) → w = v ∨ ∃u (N(w,u) ∧ T(u,v))) closes
    # it, holds in every T = N* model, and is now emitted whenever T and N co-occur.
    assert _temporal_valid_by_enumeration(formula, max_worlds=3) is True
    assert qml_is_valid(formula) is True


def test_first_step_is_emitted_only_with_both_relations_and_the_closure_flag():
    # Same gating as n_in_t (the axiom relates the two relations, so it is vacuous and
    # misleading with only one of them) and additionally off under temporal_closure=False,
    # mirroring isabelle_modal, which emits t_in_nstar only when t is the closure relation.
    def has_first_step(axioms):
        return any("w = v" in ax.to_unicode_str() for ax in axioms)

    assert has_first_step(qml_axioms(formula=Implies(Always(P), Next(P))))
    assert not has_first_step(qml_axioms(formula=Always(P)))
    assert not has_first_step(qml_axioms(formula=Next(P)))
    assert not has_first_step(qml_axioms(
        formula=Implies(Always(P), Next(P)), temporal_closure=False))
    assert qml_is_valid(Implies(And(P, Next(Always(P))), Always(P)),
                        temporal_closure=False, timeout=_UNKNOWN_TIMEOUT) is False


# ---------------------------------------------------------------------------
# Cross-family bridges (opt-in)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,formula", [
    ("knowledge_implies_belief", Implies(Knows(agent, P), Believes(agent, P))),
    ("sincerity", Implies(Says(agent, P), Believes(agent, P))),
    ("ought_implies_can", Implies(Obligatory(P), Diamond(P))),
])
def test_bridge_principle_needs_its_bridge(name, formula):
    # INVALID by default — no cross-family inclusion is forced by satisfies_modal, so none
    # may be asserted behind the user's back — and VALID once the bridge is requested.
    assert qml_is_valid(formula, timeout=_UNKNOWN_TIMEOUT) is False
    assert qml_is_valid(formula, bridges=[name]) is True


@pytest.mark.parametrize("name,converse", [
    ("knowledge_implies_belief", Implies(Believes(agent, P), Knows(agent, P))),
    ("sincerity", Implies(Believes(agent, P), Says(agent, P))),
    ("ought_implies_can", Implies(Diamond(P), Permitted(P))),
])
def test_bridge_does_not_validate_its_converse(name, converse):
    # The condition has a direction. Belief is not knowledge, belief is not assertion, and
    # a mere possibility is not a permission — a bridge that validated its converse would
    # be the wrong condition.
    assert qml_is_valid(converse, bridges=[name], timeout=_UNKNOWN_TIMEOUT) is False


@pytest.mark.parametrize("artifact", [
    Implies(Box(P), Obligatory(P)),          # "whatever is necessary is obligatory"
    Implies(Permitted(P), Diamond(P)),       # permission is not possibility
], ids=lambda f: f.to_unicode_str())
def test_ought_implies_can_carries_neither_d_subset_r_artifact(artifact):
    # The point of emitting the MEET condition ∀w ∃v (D(w,v) ∧ R(w,v)) rather than the
    # folklore inclusion D ⊆ R. The inclusion (plus the default-on d_serial) validates
    # both of these, neither of which the caller asked for; the exact correspondent
    # validates Oφ → ◇φ and nothing else. Anchored in the oracle below, not in Z3 alone.
    assert qml_is_valid(artifact, timeout=_UNKNOWN_TIMEOUT) is False
    assert qml_is_valid(artifact, bridges=["ought_implies_can"],
                        timeout=_UNKNOWN_TIMEOUT) is False


def test_ought_implies_can_matches_the_oracle_model_class():
    # One frame satisfying the meet condition at every world refutes both artefacts while
    # Oφ → ◇φ holds — so the qml verdicts above are the model class's, not Z3's mood.
    relations = {"deontic": {(0, 1), (0, 2), (1, 1), (2, 2)},
                 "alethic": {(0, 1), (1, 1), (2, 2)}}
    worlds = {0, 1, 2}
    assert all(any((w, v) in relations["deontic"] and (w, v) in relations["alethic"]
                   for v in worlds) for w in worlds), "frame must satisfy d_meets_r"
    box_to_obl = KripkeModel(worlds=worlds, relations=relations,
                             valuation={0: set(), 1: {"P"}, 2: set()})
    assert satisfies_modal(Implies(Box(P), Obligatory(P)), box_to_obl, 0) is False
    perm_to_dia = KripkeModel(worlds=worlds, relations=relations,
                              valuation={0: set(), 1: set(), 2: {"P"}})
    assert satisfies_modal(Implies(Permitted(P), Diamond(P)), perm_to_dia, 0) is False
    for model in (box_to_obl, perm_to_dia):
        assert satisfies_modal(Implies(Obligatory(P), Diamond(P)), model, 0) is True


def test_bridge_fires_for_a_quantified_agent():
    # The inclusion axiom is deliberately UNGUARDED: a guarded form (Object(a) ∧ …) would
    # not fire for a bound agent variable, since nothing types it as an Object.
    quantified = Quantifier("∀", x, Implies(Knows(x, P), Believes(x, P)))
    assert qml_is_valid(quantified, bridges=["knowledge_implies_belief"]) is True


def test_knowledge_belief_bridge_matches_the_oracle_model_class():
    # Anchor the DIRECTION in the oracle rather than in Z3 alone: with Rb ⊆ Rk the
    # principle holds, and a model violating the inclusion refutes it.
    included = KripkeModel(worlds={0, 1}, relations={"K:a": {(0, 1)}, "B:a": {(0, 1)}},
                           valuation={1: {"P"}})
    assert satisfies_modal(Implies(Knows(agent, P), Believes(agent, P)), included, 0) is True
    violating = KripkeModel(worlds={0, 1}, relations={"K:a": set(), "B:a": {(0, 1)}},
                            valuation={0: set(), 1: set()})
    assert satisfies_modal(Implies(Knows(agent, P), Believes(agent, P)), violating, 0) is False


@pytest.mark.parametrize("bad", ["belief_implies_knowledge", "", "Sincerity", "oic"])
def test_unknown_bridge_raises_listing_the_known_ones(bad):
    # An unknown name must never be silently ignored — that would answer a question the
    # caller did not ask.
    for call in (lambda: qml_axioms(bridges=[bad]),
                 lambda: qml_is_valid(P, bridges=[bad]),
                 lambda: qml_equivalent(P, P, bridges=[bad])):
        with pytest.raises(ValueError) as exc:
            call()
        assert "knowledge_implies_belief" in str(exc.value)


def test_bridge_table_is_public_and_well_formed():
    assert set(QML_BRIDGES) == {"knowledge_implies_belief", "sincerity", "ought_implies_can"}
    for name, spec in QML_BRIDGES.items():
        assert set(spec) == {"needs", "schema", "condition", "fact"}, name
        rels = [rel for rel, _op in spec["needs"]]
        assert len(rels) == 2 and rels[0] != rels[1], name
        assert all(rel in QML_RELATIONS for rel in rels), name


def test_the_option_name_denotes_the_same_logic_on_every_route():
    # The whole point of a shared option name. hol.BRIDGES and fol.QML_BRIDGES are
    # separate registries (fol must not import hol), so their agreement is asserted
    # rather than assumed — including the fact name, which is what a grep for the
    # emitted axiom finds on the HOL side.
    from unicode_fol_kit.hol.isabelle_modal import BRIDGES, _BRIDGES as _ISA_BRIDGES
    assert set(QML_BRIDGES) == set(BRIDGES)
    for name, spec in QML_BRIDGES.items():
        assert spec["fact"] in " ".join(_ISA_BRIDGES[name]["lines"]), name
    # ...and the deontic one is the MEET condition on both, never the D ⊆ R inclusion.
    assert QML_BRIDGES["ought_implies_can"]["fact"] == "d_meets_r"
    assert "∃" in QML_BRIDGES["ought_implies_can"]["condition"]


# ---------------------------------------------------------------------------
# Signature gating
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("mode", ["constant", "increasing", "decreasing"])
def test_alethic_fragment_axiom_list_is_unchanged(mode):
    # The no-op guarantee: a formula that mentions no T / N / D relation must get exactly
    # the axioms it got before the inter-modality block existed — same members, same
    # order. Several queries elsewhere in the suite sit on a Z3 knife edge under a short
    # timeout, where one extra axiom can flip a reported verdict.
    gated = qml_axioms(mode, "S4", formula=Implies(Box(P), Diamond(P)))
    assert len(gated) == 9          # 5 typing + 2 regime/non-empty + S4's refl and trans
    assert gated == qml_axioms(mode, "S4", formula=Box(Diamond(P)))
    for ax in gated:
        rendered = ax.to_unicode_str()
        for rel in ("T(", "N(", "D("):
            assert rel not in rendered, rendered


def test_gating_emits_temporal_axioms_only_when_temporal_operators_occur():
    box_only = qml_axioms(formula=Box(P))
    temporal = qml_axioms(formula=Always(P))
    assert len(temporal) == len(box_only) + 3          # T typing + t_refl + t_trans
    assert all("T(" not in ax.to_unicode_str() for ax in box_only)
    assert any("T(w, w)" in ax.to_unicode_str() for ax in temporal)


def test_gating_emits_the_next_link_only_when_both_relations_occur():
    # N ⊆ T is meaningless — and misleading — unless both relations are in play.
    next_only = qml_axioms(formula=Next(P))
    both = qml_axioms(formula=Implies(Always(P), Next(P)))
    assert all("T(" not in ax.to_unicode_str() for ax in next_only)
    linked = [ax for ax in both if "N(w, v)" in ax.to_unicode_str()
              and "T(w, v)" in ax.to_unicode_str()]
    assert len(linked) == 1, [ax.to_unicode_str() for ax in both]


def test_gating_emits_seriality_only_when_deontic_operators_occur():
    assert all("D(" not in ax.to_unicode_str() for ax in qml_axioms(formula=Box(P)))
    assert any("D(w, " in ax.to_unicode_str() and "∃" in ax.to_unicode_str()
               for ax in qml_axioms(formula=Obligatory(P)))


def test_no_formula_call_still_emits_everything():
    # qml_axioms stays callable without a formula: that is the "give me the background
    # theory" call, and it must not silently shrink to nothing.
    every = qml_axioms("constant", "K")
    rendered = "\n".join(ax.to_unicode_str() for ax in every)
    for rel in ("R(", "T(", "N(", "D("):
        assert rel in rendered, rel
    # +8: typing for T / N / D, t_refl, t_trans, n_in_t, first_step, d_serial.
    assert len(every) == len(qml_axioms("constant", "K", formula=Box(P))) + 8


@pytest.mark.parametrize("formula,name,missing", [
    (Box(P), "ought_implies_can", "Obligatory/Permitted"),
    (Obligatory(P), "ought_implies_can", "□/◇"),
    (Knows(agent, P), "knowledge_implies_belief", "Believes"),
    (Believes(agent, P), "sincerity", "Says"),
])
def test_bridge_with_an_absent_partner_family_raises(formula, name, missing):
    # A bridge is a claim about how two relations sit relative to each other, so with
    # only one family in the query there is nothing to relate. Emitting it anyway is not
    # conservative — d_meets_r entails seriality of the ALETHIC R, which would silently
    # turn □P → ◇P valid under frame="K" — and skipping it would answer for a weaker
    # logic than requested. Same rule, same reason, as to_isabelle_modal /
    # to_thf_modal_full, so one bridges= call means one thing on every route.
    for call in (lambda: qml_axioms(formula=formula, bridges=[name]),
                 lambda: qml_is_valid(formula, bridges=[name])):
        with pytest.raises(ValueError) as exc:
            call()
        assert name in str(exc.value) and missing in str(exc.value)


def test_the_whole_background_theory_call_still_honours_every_bridge():
    # qml_axioms() without a formula is the "give me the background theory" call, in
    # which every relation is in scope — so no bridge can be family-rejected there.
    rendered = [ax.to_unicode_str()
                for ax in qml_axioms(bridges=sorted(QML_BRIDGES))]
    assert any("D(w, v)" in r and "R(w, v)" in r and "∃" in r for r in rendered)
    assert any("Rb(a, w, v)" in r and "Rk(a, w, v)" in r for r in rendered)
    assert any("Rb(a, w, v)" in r and "Rs(a, w, v)" in r for r in rendered)


# ---------------------------------------------------------------------------
# temporal_closure=False — parity with the Isabelle / THF exporters
# ---------------------------------------------------------------------------

def test_temporal_closure_off_keeps_only_the_next_inclusion():
    # Same knob as isabelle_modal_theory / to_thf_modal_full: dropping refl+trans of T
    # answers for a strictly WEAKER temporal logic than satisfies_modal implements, so a
    # False under it says nothing about the oracle.
    for formula in (Implies(Always(P), P), Implies(Always(P), Always(Always(P))),
                    Implies(Always(P), Eventually(P)), Implies(Historically(P), P)):
        assert qml_is_valid(formula, temporal_closure=False) is False
    # ... but N ⊆ T survives, exactly as the THF exporter's contract states.
    assert qml_is_valid(Implies(Always(P), Next(P)), temporal_closure=False) is True
    loose = [ax.to_unicode_str() for ax in qml_axioms(
        formula=Implies(Always(P), Next(P)), temporal_closure=False)]
    assert not any("T(w, w)" in r for r in loose)
    assert any("N(w, v)" in r and "T(w, v)" in r for r in loose)


# ---------------------------------------------------------------------------
# The new keyword arguments must not disturb the existing call surface
# ---------------------------------------------------------------------------

def test_existing_positional_call_surface_is_preserved():
    # atp.resolution calls _validity_formula(combined, "constant", "K") positionally and
    # tests call qml_is_valid(f, mode, frame, systems, timeout) — the new parameters are
    # appended, so both keep working.
    from unicode_fol_kit.fol.qml import _validity_formula
    _validity_formula(Implies(Box(P), P), "constant", "K")
    assert qml_is_valid(Implies(Box(P), P), "constant", "T", None, 5000) is True


def test_qml_equivalent_accepts_bridges():
    # Sanity: the keyword threads through the equivalence wrapper too.
    assert qml_equivalent(Knows(agent, P), And(Knows(agent, P), Believes(agent, P)),
                          bridges=["knowledge_implies_belief"]) is True
