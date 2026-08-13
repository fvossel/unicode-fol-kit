"""Tests for the E / Zipperposition backends (atp.eprover_backend).

Offline tests pin problem generation, discovery precedence and the
SZS→Verdict mapping against CANNED outputs in each prover's real comment
style (E prints ``# SZS status …`` with a hash — the regression the tstp
extractor grew for these backends). Live tests are ``skipif``-gated on
discovery: on this Windows box they usually skip (Ubuntu 22.04 WSL has no
eprover package); in CI (Ubuntu 24.04, ``apt install eprover``) the E ones
run for real. Zipperposition has no apt package anywhere — its live test
skips until someone opam-installs it, and that is honest, not a gap.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp import eprover_backend as eb
from unicode_fol_kit.atp.eprover_backend import (
    EProverBackend,
    ZipperpositionBackend,
    _generate_tptp_problem,
    eprover_available,
)
from unicode_fol_kit.atp.protocol import (
    BackendUnavailable,
    default_chain,
    get_backend,
)

_PARSE = MSFLParser().parse

_PREMISES = [_PARSE("P(alice)"), _PARSE("∀x (P(x) → Q(x))")]
_GOAL = _PARSE("Q(alice)")

# Real shapes: E's hash-marked status + a minimal TSTP refutation; the
# CounterSatisfiable and ResourceOut lines as E 3.x prints them.
_E_THEOREM_OUTPUT = """\
# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
fof(premise_1, axiom, p(alice), file('/tmp/x.p', premise_1)).
fof(goal, conjecture, q(alice), file('/tmp/x.p', goal)).
cnf(c_0_5, negated_conjecture, ~q(alice), inference(split_conjunct,[status(thm)],[goal])).
cnf(c_0_7, plain, $false, inference(cn,[status(thm)],[c_0_5]), ['proof']).
# SZS output end CNFRefutation
"""
_E_COUNTERSAT_OUTPUT = "# No proof found!\n# SZS status CounterSatisfiable\n"
_E_RESOURCEOUT_OUTPUT = "# Failure: Resource limit exceeded (time)\n# SZS status ResourceOut\n"
_ZIPPER_THEOREM_OUTPUT = "% SZS status Theorem for '/tmp/x.p'\n"


# ---------------------------------------------------------------------------
# Registry / problem generation / discovery
# ---------------------------------------------------------------------------

def test_both_backends_registered_never_in_default_chains():
    assert isinstance(get_backend("eprover"), EProverBackend)
    assert isinstance(get_backend("zipperposition"), ZipperpositionBackend)
    for chain_logic in ("fol", "modal"):
        assert "eprover" not in default_chain(chain_logic)
        assert "zipperposition" not in default_chain(chain_logic)


def test_problem_generation_matches_vampire_shape():
    """Hand-derived: premise_1/premise_2 axioms + one goal conjecture, TPTP
    casing from to_tptp (constants lower, variables upper)."""
    problem = _generate_tptp_problem(_PREMISES, _GOAL)
    assert problem == (
        "fof(premise_1, axiom, p(alice)).\n"
        "fof(premise_2, axiom, (![X]: (p(X) => q(X)))).\n"
        "fof(goal, conjecture, q(alice)).\n"
    )


def test_discovery_env_override_with_wsl_prefix(monkeypatch):
    """$UFK_EPROVER_CMD=wsl:/opt/eprover forces the WSL route verbatim; the
    cache is keyed so the override is visible immediately."""
    monkeypatch.setattr(eb, "_DISCOVERY_CACHE", {})
    monkeypatch.setenv("UFK_EPROVER_CMD", "wsl:/opt/eprover")
    assert eb._discover("eprover", "UFK_EPROVER_CMD") == ("/opt/eprover", True)


def test_discovery_miss_is_cached_and_unavailable(monkeypatch):
    monkeypatch.setattr(eb, "_DISCOVERY_CACHE", {})
    monkeypatch.delenv("UFK_ZIPPERPOSITION_CMD", raising=False)
    monkeypatch.setattr(eb.shutil, "which", lambda name: None)

    def _no_wsl(*a, **kw):
        raise OSError("no wsl")
    monkeypatch.setattr(eb.subprocess, "run", _no_wsl)
    assert eb.zipperposition_available() is False
    # Second call answers from the cache without re-probing (run would raise).
    assert eb.zipperposition_available() is False


def test_decide_unavailable_raises_backend_unavailable(monkeypatch):
    monkeypatch.setattr(eb, "_discover", lambda *a: None)
    with pytest.raises(BackendUnavailable, match="UFK_EPROVER_CMD"):
        get_backend("eprover").decide(_GOAL, _PREMISES)


# ---------------------------------------------------------------------------
# SZS → Verdict mapping on canned real outputs
# ---------------------------------------------------------------------------

@pytest.fixture()
def fake_run(monkeypatch):
    """Route _run_tptp_prover to a canned (output, timed_out) pair."""
    monkeypatch.setattr(eb, "_discover", lambda *a: ("eprover", False))
    holder = {}

    def _fake(problem, command, args, use_wsl, timeout_s):
        holder["problem"] = problem
        holder["args"] = list(args)
        return holder["response"]
    monkeypatch.setattr(eb, "_run_tptp_prover", _fake)
    return holder


def test_e_theorem_output_maps_to_proved_with_tstp_proof(fake_run):
    """The hash-marked '# SZS status Theorem' plus the TSTP refutation block
    must yield PROVED with a parsed derivation (4 steps in the fixture)."""
    fake_run["response"] = (_E_THEOREM_OUTPUT, False)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "proved"
    assert verdict.szs_status == "Theorem"
    assert verdict.proof is not None
    assert len(verdict.proof["steps"]) == 4
    assert "--proof-object" in fake_run["args"]


def test_e_countersatisfiable_maps_to_refuted(fake_run):
    fake_run["response"] = (_E_COUNTERSAT_OUTPUT, False)
    verdict = get_backend("eprover").decide(_GOAL, [])
    assert verdict.status == "refuted"
    assert verdict.szs_status == "CounterSatisfiable"


def test_e_resourceout_maps_to_unknown_bound_hit(fake_run):
    """ResourceOut is E's own budget exhaustion: UNKNOWN with the kit's
    established mapping reason "bound_hit" (SZS ResourceOut covers time AND
    memory, so the ontology maps it to the generic bound, not "timeout" —
    see szs_to_verdict_fields), never an error."""
    fake_run["response"] = (_E_RESOURCEOUT_OUTPUT, False)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "unknown"
    assert verdict.reason == "bound_hit"


def test_subprocess_timeout_maps_to_unknown_timeout(fake_run):
    fake_run["response"] = ("", True)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "unknown"
    assert verdict.reason == "timeout"


def test_no_szs_line_is_an_infra_error(fake_run):
    fake_run["response"] = ("eprover: unknown option --frobnicate\n", False)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "frobnicate" in verdict.detail


def test_untranslatable_node_is_unsupported_before_any_run(monkeypatch):
    """A modal formula has no to_tptp: unsupported, and the runner must not
    even be called (it is monkeypatched to explode)."""
    monkeypatch.setattr(eb, "_discover", lambda *a: ("eprover", False))

    def _boom(*a, **kw):
        raise AssertionError("runner must not be reached")
    monkeypatch.setattr(eb, "_run_tptp_prover", _boom)
    modal = MSFLParser(modal=True).parse("□P → P")
    verdict = get_backend("eprover").decide(modal)
    assert verdict.status == "unknown"
    assert verdict.reason == "unsupported"


def test_zipperposition_theorem_output_maps_to_proved(monkeypatch):
    monkeypatch.setattr(eb, "_discover", lambda *a: ("zipperposition", False))
    monkeypatch.setattr(eb, "_run_tptp_prover",
                        lambda *a, **kw: (_ZIPPER_THEOREM_OUTPUT, False))
    verdict = get_backend("zipperposition").decide(_GOAL, _PREMISES)
    assert verdict.status == "proved"
    assert verdict.szs_status == "Theorem"
    # Zipperposition printed no TSTP block: proof honestly degrades to None
    # with the parse failure noted, the Theorem status stands.
    assert verdict.proof is None


# ---------------------------------------------------------------------------
# Live (skipif-gated; runs in CI where apt installs eprover)
# ---------------------------------------------------------------------------

def _why(verdict) -> str:
    """Everything the backend knows about a verdict, as an assertion message.

    These tests only run where a real binary exists — which, for most of us,
    means CI and nowhere else. A bare ``assert verdict.status == "proved"``
    then reports ``'error' != 'proved'`` and stops, while the reason sits
    unread in ``detail``: the SZS line that was missing, the exception that
    was raised, the last 200 characters the prover printed. Diagnosing that
    from a machine without the prover costs a round trip per guess.
    """
    return (f"status={verdict.status!r} reason={verdict.reason!r} "
            f"szs={verdict.szs_status!r} detail={verdict.detail!r}")


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
class TestEProverLive:
    def test_modus_ponens_proved_live(self):
        verdict = get_backend("eprover").decide(_GOAL, _PREMISES,
                                                timeout=15000)
        assert verdict.status == "proved", _why(verdict)
        assert verdict.szs_status == "Theorem", _why(verdict)
        assert verdict.proof is not None, _why(verdict)

    def test_non_theorem_countersatisfiable_live(self):
        verdict = get_backend("eprover").decide(_GOAL, [_PARSE("P(alice)")],
                                                timeout=15000)
        assert verdict.status == "refuted", _why(verdict)


@pytest.mark.skipif(not eb.zipperposition_available(),
                    reason="no zipperposition binary found")
class TestZipperpositionLive:
    def test_modus_ponens_proved_live(self):
        verdict = get_backend("zipperposition").decide(_GOAL, _PREMISES,
                                                       timeout=15000)
        assert verdict.status == "proved"
