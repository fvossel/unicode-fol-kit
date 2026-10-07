"""Tests for HetsBackend (unicode_logic_kit.atp.hets_backend).

Offline tests stub the hets package's client/discovery attributes (the
backend resolves them lazily at call time, so ``monkeypatch.setattr`` on
``unicode_logic_kit.hets`` reaches every ``decide()`` call) and pin the
result→Verdict mapping to the wire values verified live on 2026-08-12:
``Proved``/``Disproved``/``Open`` (+ ``Consistent`` on the consistency
route). The live class replays the roadmap's acceptance criterion against
the real container: one MSFOL problem proved end-to-end by TWO different
Hets reasoners, each Verdict carrying reasoner+comorphism provenance.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit import hets as hets_pkg
from unicode_logic_kit.atp.hets_backend import HetsBackend
from unicode_logic_kit.atp.protocol import (
    BackendUnavailable,
    default_chain,
    get_backend,
)
from unicode_logic_kit.hets.docker import hets_available

from unicode_logic_kit import MSFLParser

_PARSE = MSFLParser().parse
_PARSE_MS = MSFLParser(many_sorted=True).parse


# ---------------------------------------------------------------------------
# Registry / chain policy
# ---------------------------------------------------------------------------

def test_hets_is_registered_but_never_in_a_default_chain():
    """The backend is addressable by name, marked external, and — the cost
    contract — absent from every default chain (a container start is
    minutes-expensive, exactly like the isabelle backend)."""
    backend = get_backend("hets")
    assert isinstance(backend, HetsBackend)
    assert backend.external is True
    assert "hets" not in default_chain("fol")
    assert "hets" not in default_chain("modal")


# ---------------------------------------------------------------------------
# Verdict mapping (stubbed server)
# ---------------------------------------------------------------------------

def _goal(result, prover="SPASS", translation="CASL2TPTP_FOF", output=""):
    return {"name": "Ax1", "result": result,
            "used_prover": {"identifier": prover, "name": prover},
            "used_translation": translation, "prover_output": output,
            "used_time": None, "tactic_script": None}


class _FakeClient:
    """HetsClient stand-in: canned goal list, or a raised RuntimeError."""

    goals = [_goal("Proved")]
    error = None

    def __init__(self, base_url, *, timeout=30.0):
        pass

    def upload(self, text, filename):
        _FakeClient.last_spec = text
        return "/tmp/fake/kit_problem.casl"

    def prove(self, iri, node, *, reasoner=None, translation=None,
              time_limit=10):
        if _FakeClient.error is not None:
            raise _FakeClient.error
        return _FakeClient.goals

    def consistency_check(self, iri, node, *, reasoner="darwin-non-fd",
                          time_limit=10):
        if _FakeClient.error is not None:
            raise _FakeClient.error
        return _FakeClient.goals


@pytest.fixture()
def stubbed_server(monkeypatch):
    _FakeClient.goals = [_goal("Proved")]
    _FakeClient.error = None
    monkeypatch.setattr(hets_pkg, "HetsClient", _FakeClient)
    monkeypatch.setattr(hets_pkg, "discover_hets_url",
                        lambda **kw: ("http://fake:8000", None))
    return _FakeClient


def test_proved_maps_to_proved_with_provenance(stubbed_server):
    """Hets "Proved" → kit PROVED; detail carries reasoner + comorphism
    (the provenance the roadmap's acceptance criterion demands)."""
    verdict = get_backend("hets").decide(_PARSE("P(alice)"))
    assert verdict.status == "proved"
    assert verdict.backend == "hets"
    assert "reasoner=SPASS" in verdict.detail
    assert "translation=CASL2TPTP_FOF" in verdict.detail


def test_disproved_maps_to_refuted(stubbed_server):
    stubbed_server.goals = [_goal("Disproved", prover="darwin-non-fd",
                                  translation="CASL2SoftFOL")]
    verdict = get_backend("hets").decide(_PARSE("P(alice)"))
    assert verdict.status == "refuted"
    assert "reasoner=darwin-non-fd" in verdict.detail


def test_open_maps_to_unknown_never_refuted(stubbed_server):
    """"Open" is NOT settled — in the official image it is frequently just a
    broken wrapper (eprover/Vampire), so mapping it to refuted would turn an
    infrastructure defect into a wrong logical answer."""
    stubbed_server.goals = [_goal("Open", output="/bin/sh: 1: SZS: not found")]
    verdict = get_backend("hets").decide(_PARSE("P(alice)"))
    assert verdict.status == "unknown"
    assert verdict.reason == "incomplete"
    assert "SZS: not found" in verdict.detail


def test_client_error_maps_to_error_infra(stubbed_server):
    stubbed_server.error = RuntimeError("hets: POST /prove -> HTTP 500")
    verdict = get_backend("hets").decide(_PARSE("P(alice)"))
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "HTTP 500" in verdict.detail


def test_unexpected_goal_count_is_an_infra_error(stubbed_server):
    """One conjecture in, one goal result expected: anything else means the
    server answered a different question — never guess which goal is ours."""
    stubbed_server.goals = [_goal("Proved"), _goal("Open")]
    verdict = get_backend("hets").decide(_PARSE("P(alice)"))
    assert verdict.status == "error"
    assert "2 goal results" in verdict.detail


def test_out_of_fragment_is_unsupported_before_any_network(monkeypatch):
    """A modal formula leaves the CASL FOL/MSFOL fragment: the CASL export
    refuses, and decide() reports unknown/unsupported WITHOUT touching the
    network (discovery is stubbed to explode to prove it isn't reached)."""
    def _boom(**kw):
        raise AssertionError("discovery must not run for unsupported input")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _boom)
    modal = MSFLParser(modal=True).parse("□P → P")
    verdict = get_backend("hets").decide(modal)
    assert verdict.status == "unknown"
    assert verdict.reason == "unsupported"


# ---------------------------------------------------------------------------
# A typed reading that differs from the kit's is refused, not answered
#
# The CASL export declares an unannotated constant or a function value at the sort of
# the position it is used in, and CASL's sorts are disjoint types. The kit's own reading
# of a sort: ONE universe, a sort is a non-empty subset of it, a constant `c:S` is in S,
# an unannotated constant / an unsorted variable / a function value is ANY element. So
# Hets (measured live, SPASS) PROVES `∀x:Human Mortal(x) ⊢ Mortal(socrates)`, which is
# invalid (U={0,1}, Human={0}, Mortal={0}, socrates=1), and REFUTES
# `∀x ∀y x = y ⊢ ∀x:A ∀z:A x = z`, which is valid (a one-element universe, A a subset).
# ---------------------------------------------------------------------------

_DIFFERENT_READING = [
    # premises, conclusion, what the refusal must name
    ([_PARSE_MS("∀x:Human Mortal(x)")], _PARSE("Mortal(socrates)"), "'socrates'"),
    ([_PARSE_MS("∀x:Foo R(x)"), _PARSE("Q(g(alpha))")], _PARSE("R(g(alpha))"), "'g'"),
    ([_PARSE("∀x ∀y x = y")], _PARSE_MS("∀x:A ∀z:A x = z"), "UNSORTED"),
    ([], _PARSE_MS("∃y:Car Car(y)"), "'Car'"),
]


@pytest.mark.parametrize("premises, goal, names", _DIFFERENT_READING)
def test_a_differing_typed_reading_is_unsupported_before_any_network(
        monkeypatch, premises, goal, names):
    """The verdict is unknown / unsupported, the detail names the term (or the sort) and what
    to do instead, and no server is contacted."""
    def _boom(**kw):
        raise AssertionError("discovery must not run for a problem the backend refuses")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _boom)
    verdict = get_backend("hets").decide(goal, premises)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert names in verdict.detail
    assert "fof writer" in verdict.detail


def test_a_problem_whose_typed_reading_agrees_still_reaches_the_server(stubbed_server):
    """``P(carl), Q(carl:A) ⊢ ∃x:A P(x)`` is valid in the kit (carl is ONE constant, and its
    sorted occurrence puts it in A) and the typed reading says the same: it is sent."""
    premises = [_PARSE("P(carl)"), _PARSE_MS("Q(carl:A)")]
    verdict = get_backend("hets").decide(_PARSE_MS("∃x:A P(x)"), premises)
    assert verdict.status == "proved"
    assert "carl : A" in stubbed_server.last_spec


def test_unreachable_server_raises_backend_unavailable(monkeypatch):
    """No server, no container: BackendUnavailable propagates (loud
    availability contract) instead of a silent unknown."""
    def _unavailable(**kw):
        raise BackendUnavailable("hets: no server reachable")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _unavailable)
    with pytest.raises(BackendUnavailable):
        get_backend("hets").decide(_PARSE("P(alice)"))


def test_consistency_route_maps_consistent_to_true(stubbed_server):
    stubbed_server.goals = [_goal("Consistent", prover="darwin-non-fd",
                                  translation="CASL2SoftFOL")]
    result = get_backend("hets").check_consistency([_PARSE("P(alice)")])
    assert result["consistent"] is True
    assert result["reasoner"] == "darwin-non-fd"


def test_consistency_route_unsettled_is_none(stubbed_server):
    stubbed_server.goals = [_goal("Timeout", prover="darwin-non-fd")]
    result = get_backend("hets").check_consistency([_PARSE("P(alice)")])
    assert result["consistent"] is None
    assert result["result"] == "Timeout"


# ---------------------------------------------------------------------------
# Live: the roadmap acceptance criterion
# ---------------------------------------------------------------------------

@pytest.mark.hets_live
@pytest.mark.skipif(not hets_available(), reason="no running hets-server")
class TestHetsBackendLive:
    """Serial, against the real container (see hets_live convention)."""

    def test_fol_entailment_proved_via_api_prove(self):
        """P(c) ∧ ∀x (P(x) → Q(x)) ⊨ Q(c) — modus ponens on a constant,
        hand-checked; SPASS route with full provenance in the detail."""
        premises = [_PARSE("P(alice)"), _PARSE("∀x (P(x) → Q(x))")]
        verdict = api.prove(_PARSE("Q(alice)"), premises, backends=["hets"],
                            reasoner="SPASS")
        assert verdict.status == "proved"
        assert verdict.backend == "hets"
        assert "reasoner=SPASS" in verdict.detail
        assert "translation=CASL2TPTP_FOF" in verdict.detail

    def test_msfol_problem_proved_by_two_distinct_reasoners(self):
        """THE acceptance criterion: a genuinely many-sorted problem
        (∀x:Person Mortal(x) ⊨ Mortal(socrates:Person) — sorts survive into
        CASL, no single-sort collapse) proved end-to-end by two DIFFERENT
        Hets reasoners, each verdict stamped with its own comorphism."""
        premises = [_PARSE_MS("∀x:Person Mortal(x)")]
        goal = _PARSE_MS("Mortal(socrates:Person)")

        spass = api.prove(goal, premises, backends=["hets"], reasoner="SPASS")
        darwin = api.prove(goal, premises, backends=["hets"],
                           reasoner="darwin")
        assert spass.status == "proved"
        assert darwin.status == "proved"
        assert "reasoner=SPASS" in spass.detail
        assert "translation=CASL2TPTP_FOF" in spass.detail
        assert "reasoner=darwin" in darwin.detail
        assert "translation=CASL2SoftFOL" in darwin.detail

    def test_non_theorem_disproved_by_finite_model(self):
        """P(c) ⊭ Q(c): darwin-non-fd finds the finite countermodel and the
        kit reports REFUTED (Disproved), not merely unknown."""
        verdict = api.prove(_PARSE("Q(alice)"), [_PARSE("P(alice)")],
                            backends=["hets"], reasoner="darwin-non-fd")
        assert verdict.status == "refuted"
        assert "reasoner=darwin-non-fd" in verdict.detail

    def test_consistency_check_live(self):
        result = get_backend("hets").check_consistency(
            [_PARSE("P(alice)"), _PARSE("∀x (P(x) → Q(x))")])
        assert result["consistent"] is True

    def test_a_sorted_constant_with_a_plain_occurrence_is_proved_by_two_reasoners(self):
        """``P(carl), Q(carl:A) ⊢ ∃x:A P(x)``: carl is ONE constant and its sorted occurrence puts
        it in A, so x=carl witnesses the conclusion. The typed reading agrees (carl : A), so it
        reaches Hets, and both reasoners prove it."""
        premises = [_PARSE("P(carl)"), _PARSE_MS("Q(carl:A)")]
        goal = _PARSE_MS("∃x:A P(x)")
        for reasoner in ("SPASS", "darwin"):
            verdict = api.prove(goal, premises, backends=["hets"], reasoner=reasoner)
            assert verdict.status == "proved", (reasoner, verdict.detail)

    @pytest.mark.parametrize("premises, goal, names", _DIFFERENT_READING)
    def test_a_differing_typed_reading_is_refused_with_a_server_running(
            self, premises, goal, names):
        """With a server up, the problems whose typed reading differs from the kit's are still
        refused (the answers Hets gives for them are about another problem: it proves the
        invalid ones and refutes the valid ones)."""
        verdict = api.prove(goal, premises, backends=["hets"], reasoner="SPASS")
        assert verdict.status == "unknown"
        assert "unsupported" in verdict.detail and names in verdict.detail
