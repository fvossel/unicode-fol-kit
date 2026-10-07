"""The hybrid backend reads the three options ``hybrid_is_valid`` reads, and the ``modal → fol`` edge says
what its axioms carry.

``hybrid_is_valid(formula, frame, systems=…, temporal_closure=…)`` decides validity over the frame
class ``frame`` for the alethic relation, over the frame systems ``systems`` for the agent-indexed
families, and with the temporal relation reflexive and transitive unless ``temporal_closure`` is False.
The backend accepts and forwards the same three keywords. Facts derived by hand:

* ``Knows(alice, P) → P`` is valid when the epistemic relation is reflexive (system S5 or T: at the
  actual world ``P`` holds because it holds at every epistemic successor, this world included) and not
  valid when it is unconstrained (a world with no epistemic successor makes ``Knows`` true and ``P``
  false there).
* ``Always(P) → P`` is valid when the temporal relation is reflexive (the default closure) and not
  valid without it (a world with no temporal successor makes ``Always`` true and ``P`` false).
* ``Always(P) → Always(Always(P))`` is valid when the temporal relation is transitive (the default
  closure) and not valid without it (``w → v → u`` with ``P`` at ``v`` and not at ``u``).
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_logic_kit.comorphism import DEFAULT_REGISTRY
from unicode_logic_kit.fol.modal_translation import hybrid_is_valid
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import Always, Atom, Constant, Implies, Knows

P = Atom("P", ())
ALICE = Constant("alice")
FACTIVE = Implies(Knows(ALICE, P), P)
INTROSPECTION = Implies(Knows(ALICE, P), Knows(ALICE, Knows(ALICE, P)))
REFLEXIVE_TIME = Implies(Always(P), P)
TRANSITIVE_TIME = Implies(Always(P), Always(Always(P)))


def decide(formula, **options):
    return get_backend("hybrid").decide(formula, [], **options)


# ---------------------------------------------------------------------------
# systems=
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("system", ["S5", "T", "S4"])
def test_an_epistemic_system_with_a_reflexive_relation_makes_knowledge_factive(system):
    assert decide(FACTIVE, systems={"epistemic": system}).status == PROVED


def test_without_a_system_the_epistemic_relation_is_unconstrained():
    verdict = decide(FACTIVE)
    assert verdict.status == REFUTED and verdict.countermodel is not None
    # A system with no reflexivity changes nothing.
    assert decide(FACTIVE, systems={"epistemic": "K"}).status == REFUTED


def test_positive_introspection_needs_a_transitive_epistemic_relation():
    assert decide(INTROSPECTION, systems={"epistemic": "S4"}).status == PROVED
    assert decide(INTROSPECTION, systems={"epistemic": "T"}).status == REFUTED


def test_an_unknown_modal_family_or_system_is_unsupported_and_not_an_exception():
    for systems in ({"nonsense": "S5"}, {"epistemic": "S99"}):
        verdict = decide(FACTIVE, systems=systems)
        assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
        assert "frame_axioms" in verdict.detail


# ---------------------------------------------------------------------------
# temporal_closure=
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula", [REFLEXIVE_TIME, TRANSITIVE_TIME])
def test_the_temporal_relation_is_closed_by_default(formula):
    assert decide(formula).status == PROVED
    assert decide(formula, temporal_closure=True).status == PROVED


@pytest.mark.parametrize("formula", [REFLEXIVE_TIME, TRANSITIVE_TIME])
def test_without_the_closure_neither_temporal_law_is_valid(formula):
    verdict = decide(formula, temporal_closure=False)
    assert verdict.status == REFUTED and verdict.countermodel is not None


# ---------------------------------------------------------------------------
# One answer with hybrid_is_valid
# ---------------------------------------------------------------------------

BATTERY = [
    (FACTIVE, "K", {}),
    (FACTIVE, "K", {"systems": {"epistemic": "S5"}}),
    (FACTIVE, "K", {"systems": {"epistemic": "K"}}),
    (INTROSPECTION, "K", {"systems": {"epistemic": "S4"}}),
    (INTROSPECTION, "K", {"systems": {"epistemic": "T"}}),
    (REFLEXIVE_TIME, "K", {}),
    (REFLEXIVE_TIME, "K", {"temporal_closure": False}),
    (TRANSITIVE_TIME, "S5", {}),
    (TRANSITIVE_TIME, "S5", {"temporal_closure": False}),
    (Implies(Atom("Q", ()), Atom("Q", ())), "K", {"temporal_closure": False}),
]


@pytest.mark.parametrize("formula, frame, options", BATTERY)
def test_the_backend_answers_as_hybrid_is_valid_does(formula, frame, options):
    verdict = decide(formula, frame=frame, **options)
    assert verdict.status in (PROVED, REFUTED)
    assert (verdict.status == PROVED) is hybrid_is_valid(formula, frame, **options)


def test_through_api_prove_the_options_reach_the_backend():
    proved = api.prove(FACTIVE, [], backends=["hybrid"], logic="hybrid", systems={"epistemic": "S5"})
    refuted = api.prove(REFLEXIVE_TIME, [], backends=["hybrid"], logic="hybrid", temporal_closure=False)
    assert proved.status == PROVED
    assert refuted.status == REFUTED


# ---------------------------------------------------------------------------
# The modal → fol edge of the comorphism registry
# ---------------------------------------------------------------------------

def test_the_modal_edge_carries_the_rigid_membership_axiom_and_says_so():
    formula = MSFLParser(modal=True, many_sorted=True).parse("□Human(carl:Human)")
    result = DEFAULT_REGISTRY.translate(formula, "modal", "fol")
    assert "∀v0 Human(carl, v0)" in [axiom.to_unicode_str() for axiom in result.axioms]
    edge = next(e for e in DEFAULT_REGISTRY.edges() if e.name == "standard_translation")
    assert "membership of every sorted constant" in edge.note and "∀v0 S(c, v0)" in edge.note
    # A formula with no sorted constant gets no membership axiom.
    plain = DEFAULT_REGISTRY.translate(Implies(P, P), "modal", "fol")
    assert not [a for a in plain.axioms if "carl" in a.to_unicode_str()]
