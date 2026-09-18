"""Bounded finite-frame decisions for Löb (GL), Grzegorczyk (Grz) and
McKinsey (S4.1).

These three modal axioms have no first-order frame condition valid at every
cardinality (see ``fol/frames.py``'s "What is NOT first-order definable"),
but each DOES have a finite structural characterisation — irreflexive,
antisymmetric, and "every world reaches a terminal point" respectively —
that :func:`unicode_fol_kit.fol.frames.holds_on_finite_frame` now decides
directly, and that :mod:`unicode_fol_kit.atp.kripke_enum` therefore now
refutes formulas over, exactly like it already did for every first-order
condition.

``tests/test_modal_frame_registry.py`` carries the BRUTE-FORCE correspondence
argument (the finite characterisation IS the axiom's validity, checked on
every frame up to four worlds). This file is the integration layer: the
enumerator actually deciding formulas end to end, the hand-checked cases the
roadmap item asks for, and confirmation that every route reasoning over an
UNBOUNDED domain of worlds via a single first-order sentence — the labelled
tableau included — still refuses these three by name. That first-order/
bounded-finite boundary is exactly what this change moved for
``atp.kripke_enum`` and exactly what must NOT have moved anywhere else.

Every countermodel below is additionally re-verified with
``satisfies_modal`` — the same oracle the enumerator itself used to find it —
so a bug shared between the enumerator and the evaluator could never hide
here (the same discipline ``tests/test_kripke_enum.py`` already follows).
Nothing here ever claims a formula VALID: only genuine countermodels, or an
honest ``exhausted``/``bound_hit``.
"""

import pytest

from unicode_fol_kit.atp.kripke_enum import modal_enum_search, KripkeEnumBackend
from unicode_fol_kit.atp.modal_tableau import is_modal_valid
from unicode_fol_kit.atp.protocol import REFUTED, UNKNOWN
from unicode_fol_kit.fol.frames import (
    UnsupportedFrameCondition, holds_on_finite_frame, modal_axiom,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

#: The 2-world "cluster": both worlds see each other and themselves. It is
#: reflexive and transitive but neither antisymmetric NOR does either world
#: have a terminal point (a world whose only successor is itself) among its
#: successors — the frame that falls OUT of scope for both Grz and McKinsey
#: at once, used by more than one test below.
_CLUSTER = frozenset({(0, 0), (0, 1), (1, 0), (1, 1)})


# --------------------------------------------------------------------------- #
# Hand-checked case 1: T has a GL countermodel — the cheapest possible one.
# --------------------------------------------------------------------------- #

def test_t_axiom_has_a_gl_countermodel_the_single_irreflexive_world():
    """□P → P (the T axiom) is NOT GL-valid: a GL frame is transitive +
    irreflexive, and need not be reflexive at all — indeed a reflexive world
    (a self-loop) is forbidden outright by irreflexivity. The single world
    with NO alethic relation is vacuously transitive and vacuously
    irreflexive (no edges to violate either), hence a valid GL frame; on it,
    □P holds vacuously (no successors) while P can be made false — the
    cheapest possible countermodel, at n=1.
    """
    result = modal_enum_search(modal_axiom("T"), frame="GL", max_worlds=1)
    assert result.unsupported is None
    assert result.model is not None
    model = result.model
    assert set(model.worlds) == {0}
    assert model.relations.get("alethic", set()) == set()
    assert model.valuation.get(0, set()) == set()

    # Re-verify with the oracle directly...
    assert satisfies_modal(modal_axiom("T"), model, 0) is False
    # ...and confirm the frame really is a valid GL frame via the SAME
    # finite check the enumerator itself used to build it.
    edges = frozenset(model.relations.get("alethic", set()))
    assert holds_on_finite_frame("trans", edges, 1) is True
    assert holds_on_finite_frame("loeb", edges, 1) is True


# --------------------------------------------------------------------------- #
# Hand-checked case 2: 4 and Loeb have NO countermodel on GL frames.
# --------------------------------------------------------------------------- #

def test_4_and_loeb_have_no_gl_countermodel_up_to_the_bound():
    """4 (□P → □□P) is a theorem of every transitive frame, and GL frames
    ARE transitive by definition — so no countermodel can exist at any size.
    Löb's own axiom is valid on every GL frame by the correspondence
    ``tests/test_modal_frame_registry.py`` brute-forces. Both searches must
    come back honestly ``exhausted``, never merely ``model is None`` (which
    would also describe a budget cutoff).
    """
    for axiom_name in ("4", "Loeb"):
        result = modal_enum_search(modal_axiom(axiom_name), frame="GL",
                                   max_worlds=4)
        assert result.model is None, f"{axiom_name}: spurious GL countermodel"
        assert result.exhausted is True
        assert result.unsupported is None


def test_loeb_axiom_is_refutable_off_gl_frames():
    """Non-vacuity for the case above: the SAME Löb schema DOES have a
    countermodel once the frame is not required to be irreflexive (plain
    K) — so "exhausted on GL" is a real finding about GL, not an artefact
    of Löb being a tautology that no frame could ever refute.
    """
    result = modal_enum_search(modal_axiom("Loeb"), frame="K", max_worlds=3)
    assert result.model is not None
    assert satisfies_modal(modal_axiom("Loeb"), result.model, 0) is False


# --------------------------------------------------------------------------- #
# Hand-checked case 3: T and 4 are valid (no countermodel) on Grz frames.
# --------------------------------------------------------------------------- #

def test_t_and_4_have_no_grz_countermodel_up_to_the_bound():
    """T and 4 are theorems of every reflexive-transitive (S4) frame, and
    every Grz frame IS reflexive+transitive (plus antisymmetric — a
    STRICTLY smaller frame class than S4), so both remain valid: no
    countermodel can exist at any size.
    """
    for axiom_name in ("T", "4"):
        result = modal_enum_search(modal_axiom(axiom_name), frame="Grz",
                                   max_worlds=3)
        assert result.model is None
        assert result.exhausted is True
        assert result.unsupported is None


def test_grz_schema_itself_has_no_grz_countermodel_up_to_the_bound():
    """The Grz schema is, tautologically, valid on every genuine Grz frame
    (that is what "frame=Grz" means) — confirmed directly rather than
    assumed, since ``tests/test_modal_frame_registry.py`` proves the
    correspondence but never runs the enumerator itself over frame="Grz"."""
    result = modal_enum_search(modal_axiom("Grz"), frame="Grz", max_worlds=3)
    assert result.model is None
    assert result.exhausted is True


# --------------------------------------------------------------------------- #
# Hand-checked case 4: the Grz schema (and, on the very same frame, the
# McKinsey schema) fails on a two-world cluster.
# --------------------------------------------------------------------------- #

def test_grz_and_mckinsey_both_fail_on_the_two_world_cluster():
    """``_CLUSTER`` — both worlds see each other AND themselves — is
    reflexive and transitive but neither antisymmetric (0 R 1 and 1 R 0
    with 0 != 1) nor "every world reaches a terminal point" (neither world's
    successor set is a singleton: succ(0) = succ(1) = {0, 1}). So it is
    EXCLUDED from what the enumerator builds under BOTH frame="Grz" and
    frame="S4.1", and it is a genuine countermodel to both schemas.

    Hand derivation for the Grz schema
    ``□(□(P→□P)→P)→P`` at world 0, P false at 0 and true at 1:
        - at world 1: P→□P is False (P@1=True, but □P@1 needs P at every
          successor of 1, i.e. at 0 too, where P is False) — so
          □(P→□P)@1 is False (one successor, itself, already fails it via
          the self-loop), making (□(P→□P)→P)@1 vacuously True.
        - at world 0: P→□P is vacuously True (P@0=False) at successor 0,
          and False at successor 1 (by the previous bullet) — so
          □(P→□P)@0 is False too, making (□(P→□P)→P)@0 vacuously True.
        - Both successors of 0 (0 and 1) now satisfy (□(P→□P)→P), so
          □(□(P→□P)→P)@0 is True — while P@0 is False, so the WHOLE
          schema is False at 0: a genuine countermodel.
    For McKinsey (□◇P→◇□P) the same valuation works by a parallel argument
    (◇P is True everywhere since world 1 is reachable and P holds there;
    □P is False everywhere since world 0 is reachable and P does not hold
    there — so □◇P@0 = True but ◇□P@0 = False).
    """
    assert holds_on_finite_frame("refl", _CLUSTER, 2) is True
    assert holds_on_finite_frame("trans", _CLUSTER, 2) is True
    assert holds_on_finite_frame("grz", _CLUSTER, 2) is False       # not antisymmetric
    assert holds_on_finite_frame("mckinsey", _CLUSTER, 2) is False  # no terminal point

    valuation = {0: set(), 1: {"P"}}
    model = KripkeModel(worlds=[0, 1], relations={"alethic": _CLUSTER},
                        valuation=valuation)
    assert satisfies_modal(modal_axiom("Grz"), model, 0) is False
    assert satisfies_modal(modal_axiom("McKinsey"), model, 0) is False

    # And the enumerator, once the antisymmetry/terminal-point requirement
    # is lifted (frame="S4" keeps reflexive+transitive but neither extra
    # condition), finds exactly this shape as its FIRST countermodel for
    # both schemas — the deterministic bitmask order lands here first.
    for axiom_name in ("Grz", "McKinsey"):
        result = modal_enum_search(modal_axiom(axiom_name), frame="S4",
                                   max_worlds=3)
        assert result.model is not None
        assert set(result.model.worlds) == {0, 1}
        assert result.model.relations.get("alethic") == _CLUSTER
        assert result.model.valuation == valuation
        assert satisfies_modal(modal_axiom(axiom_name), result.model, 0) is False


# --------------------------------------------------------------------------- #
# The exact integration-level pairs the roadmap item's test oracle names.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("axiom_name,own_frame,other_frame", [
    ("Loeb", "GL", "K"),
    ("McKinsey", "S4.1", "K"),
    ("Grz", "Grz", "K"),
])
def test_own_axiom_has_no_countermodel_on_its_frame_but_does_on_k(
        axiom_name, own_frame, other_frame):
    own = modal_enum_search(modal_axiom(axiom_name), frame=own_frame,
                            max_worlds=3)
    assert own.model is None
    assert own.unsupported is None

    other = modal_enum_search(modal_axiom(axiom_name), frame=other_frame,
                              max_worlds=3)
    assert other.model is not None
    assert satisfies_modal(modal_axiom(axiom_name), other.model, 0) is False


# --------------------------------------------------------------------------- #
# KripkeEnumBackend end to end: REFUTED / UNKNOWN, never PROVED, for these
# three frame names — the public ProverBackend surface must behave exactly
# like modal_enum_search underneath it.
# --------------------------------------------------------------------------- #

def test_backend_refutes_t_under_gl():
    backend = KripkeEnumBackend()
    v = backend.decide(modal_axiom("T"), frame="GL", max_worlds=1)
    assert v.status == REFUTED
    assert v.countermodel["kind"] == "kripke"


def test_backend_reports_bound_hit_for_grz_schema_under_grz():
    backend = KripkeEnumBackend()
    v = backend.decide(modal_axiom("Grz"), frame="Grz", max_worlds=3)
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"
    assert v.countermodel is None


# --------------------------------------------------------------------------- #
# The boundary that must NOT have moved: routes over an UNBOUNDED domain of
# worlds still refuse GL/S4.1/Grz by name. atp.kripke_enum's refusal loop is
# gone (tests/test_modal_frame_registry.py already pins that); this pins the
# labelled tableau, which this roadmap item's spec explicitly requires stay
# exactly as it was (only its refusal HINT text changed, pointing here).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("frame", ["GL", "S4.1", "Grz"])
def test_the_labelled_tableau_still_refuses_the_non_first_order_systems(frame):
    with pytest.raises(UnsupportedFrameCondition, match="kripke_enum"):
        is_modal_valid(modal_axiom("T"), frame=frame)
