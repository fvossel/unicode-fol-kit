"""Tests for the uniform prover protocol (atp/protocol.py).

The semantic contracts under test, each hand-checked:

* every route answers through the SAME Verdict type with correct status
  semantics — in particular the sound-but-bounded routes (resolution, qml,
  modelfinder) must NEVER report REFUTED/PROVED beyond what they actually
  established;
* the status/reason split keeps budget exhaustion (bound_hit) distinguishable
  from honest incompleteness and from timeouts;
* the availability contract: unknown name → ValueError, known-but-missing
  backend → BackendUnavailable, never a silent skip;
* an in-backend crash becomes an ERROR verdict, not a batch-killing exception.
"""

import json

import pytest

from unicode_fol_kit import (
    MSFLParser,
    Verdict, BackendUnavailable, ProverBackend,
    register_backend, get_backend, available_backends, default_chain,
    run_backend,
)
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, ERROR

_P = MSFLParser()
_MP = MSFLParser(modal=True)

_VALID = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")     # modus ponens, valid
_INVALID = _P.parse("∀x P(x)")                           # refutable
_ENTAILMENT = (_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)"))  # premises for Q(a)


# ---------------------------------------------------------------------------
# Verdict semantics
# ---------------------------------------------------------------------------

def test_verdict_truthiness_and_szs_derivation():
    assert bool(Verdict("proved", "z3")) is True
    assert bool(Verdict("refuted", "z3")) is False
    assert Verdict("proved", "z3").szs_status == "Theorem"
    assert Verdict("refuted", "z3").szs_status == "CounterSatisfiable"
    assert Verdict("unknown", "z3", reason="bound_hit").szs_status == "ResourceOut"
    assert Verdict("unknown", "z3", reason="timeout").szs_status == "Timeout"
    assert Verdict("unknown", "z3", reason="incomplete").szs_status == "GaveUp"
    assert Verdict("unknown", "z3", reason="unsupported").szs_status == "Inappropriate"
    assert Verdict("error", "z3", reason="infra").szs_status == "Error"


def test_verdict_rejects_unknown_status():
    with pytest.raises(ValueError, match="unknown status"):
        Verdict("maybe", "z3")


def test_verdict_to_dict_is_json_compatible():
    v = run_backend("z3", _INVALID)
    d = v.to_dict()
    json.dumps(d)
    assert d["status"] == "refuted" and d["agreement"] == ["z3"]


# ---------------------------------------------------------------------------
# Internal backends, route by route
# ---------------------------------------------------------------------------

def test_z3_proves_refutes_and_witnesses():
    assert run_backend("z3", _VALID).status == PROVED
    v = run_backend("z3", _INVALID)
    assert v.status == REFUTED
    assert v.countermodel["kind"] == "z3_model"


def test_z3_entailment_with_premises():
    premises = list(_ENTAILMENT)
    conclusion = _P.parse("Q(a)")
    assert run_backend("z3", conclusion, premises).status == PROVED


def test_tableau_proves_and_reports_bound_honestly():
    assert run_backend("tableau", _VALID).status == PROVED
    v = run_backend("tableau", _INVALID)
    assert v.status == UNKNOWN and v.reason == "bound_hit"   # never REFUTED


def test_resolution_proves_and_never_claims_refutation():
    assert run_backend("resolution", _VALID).status == PROVED
    v = run_backend("resolution", _INVALID)
    assert v.status == UNKNOWN and v.reason == "bound_hit"


def test_modelfinder_refutes_with_structure_and_never_proves():
    v = run_backend("modelfinder", _INVALID)
    assert v.status == REFUTED
    assert v.countermodel["kind"] == "finite_structure"
    v2 = run_backend("modelfinder", _VALID)
    assert v2.status == UNKNOWN and v2.reason == "bound_hit"  # cannot prove validity


def test_modal_tableau_tristate_and_frame_option():
    t_axiom = _MP.parse("□P → P")
    assert run_backend("modal-tableau", t_axiom).status == REFUTED       # K
    assert run_backend("modal-tableau", t_axiom, frame="T").status == PROVED
    v = run_backend("modal-tableau", t_axiom)
    assert v.logic == "modal" and v.countermodel["kind"] == "kripke"


def test_qml_proves_but_reports_incomplete_not_refuted():
    barcan_free = _MP.parse("□(P ∧ Q) → □P")
    assert run_backend("qml", barcan_free).status == PROVED
    v = run_backend("qml", _MP.parse("□P → P"))                          # K: not valid
    assert v.status == UNKNOWN and v.reason == "incomplete"              # sound, incomplete


def test_temporal_closure_operator_is_reported_unsupported_by_modal_tableau():
    """G/F/U have no tableau rule — the verdict must say so, not guess."""
    always = _MP.parse("Ⓖ P → P")
    v = run_backend("modal-tableau", always)
    assert v.status == UNKNOWN and v.reason == "unsupported"


# ---------------------------------------------------------------------------
# Registry and availability contract
# ---------------------------------------------------------------------------

def test_unknown_backend_name_raises_value_error():
    with pytest.raises(ValueError, match="unknown backend"):
        run_backend("nope", _VALID)


def test_default_chains_cover_their_logics():
    import importlib.util
    if importlib.util.find_spec("cvc5") is not None:
        # The one documented availability-dependent member: the optional
        # cvc5 extra joins right after z3 (see default_chain's docstring).
        assert default_chain("fol") == ("z3", "cvc5", "tableau",
                                        "resolution", "modelfinder")
    else:
        assert default_chain("fol") == ("z3", "tableau", "resolution",
                                        "modelfinder")
    assert default_chain("modal") == ("modal-tableau", "kripke-enum", "qml")
    with pytest.raises(ValueError):
        default_chain("astrology")


def test_internal_backends_are_always_available():
    for name in default_chain("fol") + default_chain("modal"):
        assert get_backend(name).available()
        assert name in available_backends()


def test_unavailable_backend_raises_backend_unavailable():
    """A registered backend whose discovery fails must raise, not skip."""
    class NeverThere(ProverBackend):
        name = "never-there"
        logics = frozenset({"fol"})
        external = True

        def available(self):
            return False

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise AssertionError("decide must not be reached")

    register_backend(NeverThere())
    try:
        with pytest.raises(BackendUnavailable, match="never-there"):
            run_backend("never-there", _VALID)
    finally:
        from unicode_fol_kit.atp.protocol import _REGISTRY
        del _REGISTRY["never-there"]


def test_backend_crash_becomes_error_verdict():
    """An unexpected in-backend exception is recorded, not propagated."""
    class Crashy(ProverBackend):
        name = "crashy"
        logics = frozenset({"fol"})

        def available(self):
            return True

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise RuntimeError("boom")

    register_backend(Crashy())
    try:
        v = run_backend("crashy", _VALID)
        assert v.status == ERROR and v.reason == "infra" and "boom" in v.detail
    finally:
        from unicode_fol_kit.atp.protocol import _REGISTRY
        del _REGISTRY["crashy"]
