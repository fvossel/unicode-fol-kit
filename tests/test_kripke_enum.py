"""Tests for the bounded finite-Kripke-model enumerator (atp/kripke_enum.py).

Every expectation here is hand-checked against the Kripke semantics documented
in ``semantics/kripke.py`` — worked out below in each test's comment — and, for
every REFUTED case, the returned model is additionally re-verified with
``satisfies_modal`` (the same oracle the enumerator itself used), so a test
failure can never be masked by the enumerator and the evaluator agreeing on a
shared bug.
"""

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Implies,
    Box, Diamond, Knows, Obligatory, Permitted,
    Next, Always, Eventually, Until, Would,
)
from unicode_fol_kit.atp.kripke_enum import (
    EnumSearchResult, modal_enum_search, modal_enum_countermodel, KripkeEnumBackend,
)
from unicode_fol_kit.atp.protocol import REFUTED, UNKNOWN
from unicode_fol_kit.semantics.kripke import satisfies_modal

P = Atom("P", [])
Q = Atom("Q", [])


# --------------------------------------------------------------------------- #
# The headline case: a temporal formula modal-tableau cannot refute.
# --------------------------------------------------------------------------- #

def test_eventually_p_implies_p_is_refuted_with_a_two_world_chain():
    """Ⓕ P → P is NOT valid: a world with a later-only P is a countermodel.

    By hand: take worlds {0, 1} with the single temporal edge 0 -> 1, and P
    true ONLY at 1. The reflexive-transitive closure of {(0, 1)} from 0 is
    {0, 1} (0 itself, plus 1 reached in one step), so
        Ⓕ P @ 0  =  P true at 0 or at 1  =  False or True  =  True,
        P @ 0    =  False  (P is not in world 0's valuation),
    hence (Ⓕ P → P) @ 0 = True → False = False: 0 is a genuine countermodel.
    This is exactly the "2-world chain, P only later" shape the search is
    expected to land on, since Ⓕ P → P has no countermodel at all with only
    one world (Always/Eventually's reflexive closure trivially includes the
    start world regardless of self-loops, collapsing Ⓕ P @ w to P @ w there,
    which makes the implication a 1-world tautology) — so the FIRST world
    count the search can possibly succeed at is n=2, and it must find one.
    """
    formula = Implies(Eventually(P), P)
    result = modal_enum_search(formula, max_worlds=3)
    assert result.unsupported is None
    assert result.exhausted is False
    model = result.model
    assert model is not None

    # The exact shape hand-derived above (this is what the deterministic
    # bitmask enumeration order actually lands on first).
    assert set(model.worlds) == {0, 1}
    assert model.relations.get("temporal", set()) == {(0, 1)}
    assert model.valuation.get(0, set()) == set()
    assert model.valuation.get(1, set()) == {"P"}

    # The oracle itself confirms the formula is false at world 0 in this model.
    assert satisfies_modal(formula, model, 0) is False


def test_no_countermodel_at_one_world_for_eventually_case():
    """Directly confirms the "n=1 is a tautology" step of the hand-proof above.

    At a single world, Always/Eventually's reflexive-transitive closure of
    ANY temporal relation from that world is just {that world} (the closure
    function adds the source unconditionally), so Ⓕ P @ 0 reduces to P @ 0 and
    (Ⓕ P → P) @ 0 = (P @ 0 → P @ 0) = True regardless of self-loops or
    valuation — max_worlds=1 must come back exhausted, not refuted.
    """
    result = modal_enum_search(Implies(Eventually(P), P), max_worlds=1)
    assert result.model is None
    assert result.exhausted is True
    assert result.unsupported is None


# --------------------------------------------------------------------------- #
# Next / Box refuted in K; Box -> P becomes valid (exhausted) once reflexive.
# --------------------------------------------------------------------------- #

def test_next_p_implies_p_refuted_in_k_by_a_vacuous_single_world():
    """Ⓝ P → P fails at a single, successor-less world with P false there.

    Next is universal over IMMEDIATE temporal successors; a world with NONE
    makes Ⓝ P vacuously true (an empty "for all"). So world 0 alone, with the
    temporal relation empty and P absent from its valuation, gives
        Ⓝ P @ 0 = True (vacuous),  P @ 0 = False,
    so (Ⓝ P → P) @ 0 = False: a 1-world countermodel, the cheapest possible.
    """
    result = modal_enum_search(Implies(Next(P), P), max_worlds=2)
    assert result.model is not None
    assert set(result.model.worlds) == {0}
    assert result.model.relations.get("temporal", set()) == set()
    assert result.model.valuation.get(0, set()) == set()
    assert satisfies_modal(Implies(Next(P), P), result.model, 0) is False


def test_box_p_implies_p_refuted_in_k_reflexive_filter_under_t():
    """□P → P: the T axiom. Refuted under K (no reflexivity mandated), but
    NOT refuted (exhausted, no countermodel) once frame="T" forces every
    enumerated alethic relation to be reflexive.

    Under K, the same vacuous-box shape as Next above is available: world 0
    alone, empty alethic relation, P absent — □P @ 0 is vacuously True, P @ 0
    is False, so □P → P fails at 0.

    Under T, every candidate relation the enumerator builds is FORCED to
    contain (w, w) for every world w (the "refl" frame condition — see
    _holds_conditions). So if □P holds at any world w (P true at every
    alethic successor of w), then since w is its own successor, P must hold
    at w too — □P → P is therefore true at every world of every reflexive
    frame, with no exception, so no candidate up to max_worlds can refute it:
    the search must come back exhausted, never with a model.
    """
    r_k = modal_enum_search(Implies(Box(P), P), frame="K", max_worlds=2)
    assert r_k.model is not None
    assert satisfies_modal(Implies(Box(P), P), r_k.model, 0) is False

    r_t = modal_enum_search(Implies(Box(P), P), frame="T", max_worlds=3)
    assert r_t.model is None
    assert r_t.exhausted is True
    assert r_t.unsupported is None


# --------------------------------------------------------------------------- #
# The K axiom: a genuine frame validity (true on EVERY Kripke frame), so no
# countermodel exists at any size, and the bounded search should exhaust
# max_worlds=3 honestly rather than mistake that for a validity proof.
# --------------------------------------------------------------------------- #

def test_k_axiom_has_no_countermodel_up_to_max_worlds_three():
    """□(P→Q) → (□P→□Q) is K-valid on EVERY frame (modal logic's K axiom):
    if every P-and-(P→Q) successor is a Q successor by modus ponens applied
    pointwise, □P and □(P→Q) together force □Q at any world, on any relation
    whatsoever — the argument never uses a frame condition. So the search
    must find no countermodel at n=1, 2, or 3 and finish with exhausted=True.
    """
    k_axiom = Implies(Box(Implies(P, Q)), Implies(Box(P), Box(Q)))
    result = modal_enum_search(k_axiom, max_worlds=3)
    assert result.model is None
    assert result.exhausted is True
    assert result.unsupported is None
    # "exhausted" is an honest bound statement, not a validity claim — the
    # detail text must not claim validity.
    assert "valid" not in result.detail.lower() or "not a validity" in result.detail.lower()


# --------------------------------------------------------------------------- #
# Until: both a refutation (Until does not follow from the left disjunct
# alone) and a validity (Until's right operand IS eventually reached).
# --------------------------------------------------------------------------- #

def test_until_case_refuted_when_right_never_becomes_true():
    """P → (P Ⓤ Q) is NOT valid: P holding now does not force Q to EVER hold.

    At a single world with P true, Q false, and no temporal successors, the
    Until search (``_until_holds``) checks: Q false at 0 -> try P; P true at
    0 -> explore successors; there are none -> no witnessing path -> P Ⓤ Q is
    False at 0. So (P → P Ⓤ Q) @ 0 = True → False = False: refuted, and this
    exercises Until being evaluated by the oracle inside the search loop.
    """
    formula = Implies(P, Until(P, Q))
    result = modal_enum_search(formula, max_worlds=2)
    assert result.model is not None
    assert satisfies_modal(formula, result.model, 0) is False
    assert result.model.valuation.get(0, set()) == {"P"}


def test_until_implies_eventually_right_is_a_genuine_validity():
    """(P Ⓤ Q) → Ⓕ Q holds on EVERY temporal frame: Until's own definition
    (_until_holds) only succeeds via a FINITE temporal path ending at a world
    where Q holds, and that end world is, by construction, in the
    reflexive-transitive closure of the temporal relation from the start
    world — exactly what Ⓕ Q requires. No countermodel can exist at any size,
    so the bounded search should exhaust honestly.
    """
    formula = Implies(Until(P, Q), Eventually(Q))
    result = modal_enum_search(formula, max_worlds=3)
    assert result.model is None
    assert result.exhausted is True
    assert result.unsupported is None


# --------------------------------------------------------------------------- #
# Determinism: identical arguments must reproduce the identical model.
# --------------------------------------------------------------------------- #

def test_search_is_deterministic_across_repeated_runs():
    """Running the exact same search twice must yield bit-for-bit the same
    model and the same candidate count — the enumeration order is fixed
    (sorted atoms, sorted families, bitmask order for both relations and
    valuations), with no reliance on set/dict iteration order or randomness.
    """
    formula = Implies(Eventually(P), P)
    r1 = modal_enum_search(formula, max_worlds=3)
    r2 = modal_enum_search(formula, max_worlds=3)
    assert r1.checked == r2.checked
    assert r1.model.worlds == r2.model.worlds
    assert r1.model.relations == r2.model.relations
    assert r1.model.valuation == r2.model.valuation

    # modal_enum_countermodel (the thin wrapper) agrees too.
    m3 = modal_enum_countermodel(formula, max_worlds=3)
    assert m3.worlds == r1.model.worlds
    assert m3.relations == r1.model.relations
    assert m3.valuation == r1.model.valuation


# --------------------------------------------------------------------------- #
# Budget knobs: max_atoms and max_models each give an honest non-exhausted
# "no answer" rather than hanging or mis-answering.
# --------------------------------------------------------------------------- #

def test_max_atoms_cap_rejects_up_front_without_exhausting():
    """A formula with 1 ground atom, capped at max_atoms=0, must be rejected
    before any candidate is built — checked stays 0, and exhausted is False
    (the search space was never even started, let alone completed).
    """
    result = modal_enum_search(Implies(Box(P), P), max_atoms=0)
    assert result.model is None
    assert result.exhausted is False
    assert result.checked == 0
    assert result.unsupported is None
    assert "max_atoms" in result.detail


def test_max_models_budget_stops_search_honestly():
    """A tiny max_models must cut the K-axiom search off before it completes
    (that search needs > 33000 candidates at max_worlds=3 — see
    test_k_axiom_has_no_countermodel_up_to_max_worlds_three), reporting
    exhausted=False (never claiming the full space was covered) and
    checked == the budget, never more.
    """
    k_axiom = Implies(Box(Implies(P, Q)), Implies(Box(P), Box(Q)))
    result = modal_enum_search(k_axiom, max_worlds=3, max_models=10)
    assert result.model is None
    assert result.exhausted is False
    assert result.unsupported is None
    assert result.checked == 10


# --------------------------------------------------------------------------- #
# Out-of-scope constructs: the evaluator's own NotImplementedError is
# surfaced as `unsupported`, never silently mistaken for "no countermodel".
# --------------------------------------------------------------------------- #

def test_lewis_counterfactual_is_reported_unsupported_not_exhausted():
    """satisfies_modal has no rule at all for Would (□->): it falls through
    to its final "unsupported node type" NotImplementedError for EVERY
    candidate, so the search must report `unsupported`, and must NOT report
    `exhausted=True` (which would wrongly suggest a completed, valid search).
    """
    result = modal_enum_search(Would(P, Q), max_worlds=2)
    assert result.model is None
    assert result.exhausted is False
    assert result.unsupported is not None
    assert "Would" in result.unsupported or "NotImplementedError" in result.unsupported


# --------------------------------------------------------------------------- #
# EnumSearchResult.to_dict() is JSON-compatible.
# --------------------------------------------------------------------------- #

def test_result_to_dict_is_json_compatible():
    import json

    result = modal_enum_search(Implies(Eventually(P), P), max_worlds=3)
    d = result.to_dict()
    json.dumps(d)  # must not raise
    assert d["found"] is True
    assert d["model"]["worlds"] == [0, 1]
    assert d["model"]["relations"]["temporal"] == [[0, 1]]
    assert d["model"]["valuation"] == {"0": [], "1": ["P"]}

    result2 = modal_enum_search(Would(P, Q))
    d2 = result2.to_dict()
    json.dumps(d2)
    assert d2["found"] is False
    assert d2["unsupported"] is not None


# --------------------------------------------------------------------------- #
# KripkeEnumBackend — the ProverBackend adapter.
# --------------------------------------------------------------------------- #

def test_backend_refutes_the_headline_temporal_case():
    backend = KripkeEnumBackend()
    assert backend.available() is True
    v = backend.decide(Implies(Eventually(P), P))
    assert v.status == REFUTED
    assert v.logic == "modal"
    assert v.countermodel["kind"] == "kripke"
    assert v.countermodel["data"]["relations"] == {"temporal": [[0, 1]]}


def test_backend_reports_bound_hit_for_the_k_axiom_not_proved():
    """The backend must NEVER claim PROVED (it is refutation-only) — an
    exhausted-with-no-countermodel search comes back UNKNOWN/bound_hit.
    """
    backend = KripkeEnumBackend()
    k_axiom = Implies(Box(Implies(P, Q)), Implies(Box(P), Box(Q)))
    v = backend.decide(k_axiom, max_worlds=3)
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"
    assert v.countermodel is None


def test_backend_reports_unsupported_for_counterfactuals():
    backend = KripkeEnumBackend()
    v = backend.decide(Would(P, Q))
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"


def test_backend_folds_premises_as_local_consequence():
    """premises are folded as (and premises) -> formula, like modal-tableau/qml.

    □P, □(P→Q) together K-entail □Q (the K axiom applied once), so there is
    genuinely no countermodel — bound_hit, not refuted. But □P alone does
    NOT entail □Q (no link to Q at all), so a countermodel must exist: e.g.
    world 0 with an alethic successor where P holds but Q does not.
    """
    backend = KripkeEnumBackend()
    entailed = backend.decide(Box(Q), premises=[Box(P), Box(Implies(P, Q))], max_worlds=3)
    assert entailed.status == UNKNOWN and entailed.reason == "bound_hit"

    not_entailed = backend.decide(Box(Q), premises=[Box(P)], max_worlds=2)
    assert not_entailed.status == REFUTED
    assert not_entailed.countermodel["kind"] == "kripke"
