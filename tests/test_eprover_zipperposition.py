"""Tests for the E / Zipperposition backends (atp.eprover_backend).

Offline tests pin problem generation, discovery precedence and the
SZS→Verdict mapping. Two kinds of prover output are used, and the difference
is the point:

* CANNED outputs written by hand, in E's NATIVE style (``# SZS status …``,
  hash-marked). E prints these when it is not asked for TSTP output.
* RECORDED outputs, captured verbatim from a real E 3.5.1 run under exactly
  the argument list :class:`EProverBackend` passes
  (``--auto --tstp-format --proof-object -s --cpu-limit=N``), stored in
  ``tests/fixtures/eprover_3_5_1_*.txt``. Under ``--tstp-format`` E switches
  to TPTP comment style and marks the status with ``%``, NOT ``#`` — so the
  hand-written fixtures above are in a shape our own invocation never
  produces. Both are kept: the canned ones pin the extractor's tolerance for
  E's native style, the recorded ones pin the whole chain against what our
  arguments actually elicit.

Live tests are ``skipif``-gated on discovery and additionally skip when the
binary is present but ABORTS (Ubuntu's eprover 3.0.03 dies in
``sat_solver_init`` on every problem — see ``_skip_if_the_binary_crashed``).
Zipperposition has no apt package anywhere — its live test skips until
someone opam-installs it, and that is honest, not a gap.
"""

from pathlib import Path

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp import eprover_backend as eb
from unicode_logic_kit.atp.eprover_backend import (
    EProverBackend,
    ZipperpositionBackend,
    _generate_tptp_problem,
    eprover_available,
)
from unicode_logic_kit.atp.protocol import (
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


def test_check_entailment_eprover_detailed_reverse_maps_predicate_in_raw(fake_run):
    """R3's free-text Rückweg must restore PREDICATE names too, not just
    constants -- ``Atom.to_tptp`` folds only a name's first character
    (``tptp_fold_first_letter``), so even an already ASCII-legal,
    uppercase-initial predicate like 'Human' appears in the exported
    problem (and therefore in anything E echoes back verbatim) as 'human'.
    Regression: ``TptpNameMap.reverse()``'s predicate dict used to be keyed
    by the un-folded token, so it never matched the folded text that is
    actually present in ``result['raw']``.
    """
    premise1 = _PARSE("∀x (Human(x) → Mortal(x))")
    premise2 = _PARSE("Human(socrates)")
    conclusion = _PARSE("Mortal(socrates)")
    fake_run["response"] = (
        "# SZS status Theorem\n"
        "fof(goal, conjecture, mortal(socrates)).\n"
        "fof(premise_2, axiom, human(socrates)).\n", False)
    result = eb.check_entailment_eprover_detailed([premise1, premise2], conclusion)
    assert result["status"] == "proved"
    assert "Human(socrates)" in result["raw"]
    assert "Mortal(socrates)" in result["raw"]
    assert "human(socrates)" not in result["raw"]
    assert "mortal(socrates)" not in result["raw"]


# The TF0 route's cross-kind clash (see test_vampire_entailment.py): the TF0
# writer renames the function ``agent`` to ``agent_term`` because the predicate
# ``Agent`` renders as ``agent`` too. Hand-derived reading of text echoed from
# that problem: ``agent(agent_term(X))`` is ``Agent(agent(X))`` in kit names.
#
# The goal is ``∃y Agent(y)``, with an UNSORTED ``y``. The goal these tests used to
# have, ``∃x:Thing Agent(x)``, is not entailed by the premise in the kit's reading
# of a sort: the premise says that every Thing's agent is an Agent, nothing says
# that agent(a) is itself a Thing (a function has no declared result sort), and the
# structure U={0,1}, Thing={0}, agent(0)=1, Agent={1} makes the premise true and the
# goal false. The typed text proved it only because the TF0 inference typed
# ``agent`` as ``thing > thing``, which is the stronger reading the writer now
# refuses (and with ``tff=None`` the problem would be written as fof). The new goal
# IS entailed: Thing is not empty, so take a Thing a; agent(a) is an Agent, and
# y = agent(a) witnesses the unsorted existential. The writer accepts it
# (``agent: thing > $i``), so the tests below still run the TF0 route they are about.
_MSFOL = MSFLParser(many_sorted=True)
_CLASH_PREMISES = [_MSFOL.parse("∀x:Thing Agent(agent(x))")]
_CLASH_GOAL = MSFLParser().parse("∃y Agent(y)")   # the many-sorted parser takes only sorted binders
_CLASH_ECHO = "tff(premise_1, axiom, (![X: thing]: agent(agent_term(X))) ).\n"


def test_tf0_route_raw_is_reverse_mapped_across_a_cross_kind_clash(fake_run):
    fake_run["response"] = ("# SZS status Theorem\n" + _CLASH_ECHO, False)
    result = eb.check_entailment_eprover_detailed(_CLASH_PREMISES, _CLASH_GOAL)
    assert fake_run["problem"].startswith("tff(")       # the TF0 route, not a fof fallback
    assert "agent_term" in fake_run["problem"]          # the clash is real: the writer renamed
    assert result["status"] == "proved"
    assert "Agent(agent(X))" in result["raw"]
    assert "agent_term" not in result["raw"]


def test_tf0_route_refusal_detail_is_reverse_mapped_across_a_cross_kind_clash(fake_run):
    fake_run["response"] = ("eprover: type error near agent_term(X)\n", False)
    verdict = get_backend("eprover").decide(_CLASH_GOAL, _CLASH_PREMISES)
    assert fake_run["problem"].startswith("tff(")       # the TF0 route, not a fof fallback
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "type error near agent(X)" in verdict.detail
    assert "agent_term" not in verdict.detail


def test_tf0_route_szs_error_detail_is_reverse_mapped_across_a_cross_kind_clash(fake_run):
    fake_run["response"] = ("# SZS status InputError\n# unknown symbol agent_term\n", False)
    verdict = get_backend("eprover").decide(_CLASH_GOAL, _CLASH_PREMISES)
    assert fake_run["problem"].startswith("tff(")       # the TF0 route, not a fof fallback
    assert verdict.status == "error"
    assert "unknown symbol agent" in verdict.detail
    assert "agent_term" not in verdict.detail


def test_e_countersatisfiable_maps_to_refuted(fake_run):
    fake_run["response"] = (_E_COUNTERSAT_OUTPUT, False)
    verdict = get_backend("eprover").decide(_GOAL, [])
    assert verdict.status == "refuted"
    assert verdict.szs_status == "CounterSatisfiable"


def test_e_resourceout_at_its_cpu_limit_maps_to_unknown_timeout(fake_run):
    """E stopping at the ``--cpu-limit`` the kit derived from the call's own budget
    IS the call running out of time: ``Failure: Resource limit exceeded (time)`` +
    ``SZS status ResourceOut`` is UNKNOWN / "timeout", the verdict of a run the kit
    cut off itself, never an error. (SZS ResourceOut alone covers time AND memory;
    it is E's wording of the failure that says which limit ended the run, and the
    kit passes no limit but this one. The same status without the time wording, or
    with another limit's, stays "bound_hit": see tests/test_tptp_defined_words_and_rewrites.py.)"""
    fake_run["response"] = (_E_RESOURCEOUT_OUTPUT, False)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "unknown"
    assert verdict.reason == "timeout"
    assert verdict.szs_status == "ResourceOut"       # E's own line, verbatim


def _recorded(name: str) -> str:
    """Verbatim stdout+stderr of a real E 3.5.1 run under our own arguments."""
    path = Path(__file__).parent / "fixtures" / f"eprover_3_5_1_{name}.txt"
    return path.read_text(encoding="utf-8")


def test_recorded_e_theorem_run_maps_to_proved_with_a_real_derivation(fake_run):
    """The whole chain against output a real E actually produced.

    Recorded from E 3.5.1 on the modus-ponens problem this module generates,
    invoked with exactly ``EProverBackend._args``. Note the marker: under
    ``--tstp-format`` E writes TPTP-style ``%`` comments, so this fixture is
    NOT in the hash-marked shape the hand-written ones above use — which is
    precisely why recording one mattered. Eleven derivation steps, counted
    from the fixture.
    """
    output = _recorded("theorem")
    assert "% SZS status Theorem" in output       # the real marker, not '#'
    fake_run["response"] = (output, False)
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == "proved"
    assert verdict.szs_status == "Theorem"
    assert verdict.proof is not None
    assert len(verdict.proof["steps"]) == 11


def test_recorded_e_countersatisfiable_run_maps_to_refuted(fake_run):
    """E's saturation output for a non-theorem, recorded from the same run.

    The Saturation block parses like a derivation, so this also pins that a
    REFUTED verdict is not mistaken for a proof: status decides, the block is
    only evidence.
    """
    output = _recorded("countersatisfiable")
    assert "% SZS status CounterSatisfiable" in output
    fake_run["response"] = (output, False)
    verdict = get_backend("eprover").decide(_GOAL, [_PARSE("P(alice)")])
    assert verdict.status == "refuted"
    assert verdict.szs_status == "CounterSatisfiable"
    assert verdict.proof is None      # only a "proved" verdict carries one


def test_the_recorded_runs_used_the_arguments_the_backend_still_passes():
    """The fixtures are only evidence while the invocation matches them.

    E 3.5.1 produced them under ``--auto --tstp-format --proof-object -s
    --cpu-limit=N``. Drop ``--tstp-format`` and E reverts to hash markers;
    drop ``--proof-object`` and the derivation block disappears — either way
    the recordings would silently stop describing what we run.
    """
    args = EProverBackend()._args(15)
    for flag in ("--auto", "--tstp-format", "--proof-object", "-s"):
        assert flag in args, f"{flag} gone: re-record the E fixtures"
    assert "--cpu-limit=15" in args


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


def test_no_szs_line_detail_reverse_maps_predicate_names(fake_run):
    """The 'no SZS status line' infra-error detail string is free text (R3's
    'Erklärungstexte') built from RAW, un-reparsed prover output, so an
    ASCII-legal predicate name must be restored the same way 'raw' /
    'output_excerpt' are -- not left in ``Node.to_tptp``'s folded form.
    Regression for TptpNameMap.reverse()'s predicate dict being keyed by the
    un-folded token, which never matches the folded text actually present
    (see atp._tptp_problem.TptpNameMap.reverse_rendered's docstring).
    """
    fake_run["response"] = (
        "eprover: garbage, no status line here, but mentions human(alice)\n", False)
    verdict = get_backend("eprover").decide(_PARSE("Human(alice)"), [])
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "Human(alice)" in verdict.detail
    assert "human(alice)" not in verdict.detail


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


#: Substrings that identify a prover binary ABORTING rather than answering.
#: Ubuntu's eprover 3.0.03 dies on every problem with
#: ``che_proofcontrol.c:163: sat_solver_init: Assertion 'status' failed.``
#: — E parses the arguments and the problem, then aborts initialising its SAT
#: solver, so nothing it is asked can be answered.
_CRASH_MARKERS = ("Assertion", "assertion failed", "Segmentation fault",
                  "core dumped", "Aborted")


def _skip_if_the_binary_crashed(verdict) -> None:
    """Treat a prover that ABORTS as unavailable, not as a wrong answer.

    ``eprover_available()`` only asks whether a binary is reachable, which is
    the right question for a discovery predicate but not a sufficient one
    here: a build that dies on startup is reachable and unusable. Asserting
    against it reports a failure of THIS project for a defect in someone
    else's package, and — worse — the red run says nothing about whether our
    backend is correct, which is the only thing these tests exist to check.

    The skip carries the crash text, so a broken install is visible in the
    run rather than silently green, and the tests light up again by
    themselves once the packaged prover works.
    """
    if verdict.status == "error" and verdict.reason == "infra":
        detail = verdict.detail or ""
        if any(marker in detail for marker in _CRASH_MARKERS):
            pytest.skip(f"the eprover binary aborted, so it cannot answer "
                        f"anything: {detail}")


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
class TestEProverLive:
    def test_modus_ponens_proved_live(self):
        verdict = get_backend("eprover").decide(_GOAL, _PREMISES,
                                                timeout=15000)
        _skip_if_the_binary_crashed(verdict)
        assert verdict.status == "proved", _why(verdict)
        assert verdict.szs_status == "Theorem", _why(verdict)
        assert verdict.proof is not None, _why(verdict)

    def test_non_theorem_countersatisfiable_live(self):
        verdict = get_backend("eprover").decide(_GOAL, [_PARSE("P(alice)")],
                                                timeout=15000)
        _skip_if_the_binary_crashed(verdict)
        assert verdict.status == "refuted", _why(verdict)

    def test_tf0_cross_kind_clash_is_read_back_in_kit_names_live(self):
        """A REAL E on the TF0 route of the clash. Hand-derived: ``∀x:Thing
        Agent(agent(x))`` over a non-empty sort entails ``∃y Agent(y)`` (take any
        Thing a: agent(a) satisfies Agent, so y = agent(a) witnesses the unsorted
        existential); it does not entail ``∃x:Thing Agent(x)``, the goal this test
        used to prove, because nothing says that agent(a) is a Thing. E echoes the
        declarations of the problem; the writer's ``agent_term`` must not
        survive in what the caller is shown."""
        result = eb.check_entailment_eprover_detailed(
            _CLASH_PREMISES, _CLASH_GOAL, timeout=20)
        if result["status"] == "error" and any(
                m in (result.get("raw") or "") for m in _CRASH_MARKERS):
            pytest.skip("the eprover binary aborted")
        assert result["dialect"] == "tff", result["raw"][:500]    # TF0, not a fof fallback
        assert result["status"] == "proved", result["raw"][:500]
        assert "agent_term" not in result["raw"]
        assert "Agent" in result["raw"]

    def test_ascii_sanitisation_round_trip_live(self):
        """The task's own non-ASCII/digit-leading example, decided by a REAL
        E-prover run (through WSL) and the derivation reverse-mapped back to
        the ORIGINAL kit-level names — the strongest R5 evidence this suite
        can offer for the TPTP Hinweg+Rückweg, an actual external prover
        rather than the kit's own reader.
        """
        premise1 = _PARSE("∀x (LostTo(x, świątek) → P(x))")
        premise2 = _PARSE("LostTo(dani_Shapiro, świątek)")
        conclusion = _PARSE("P(dani_Shapiro)")
        result = eb.check_entailment_eprover_detailed(
            [premise1, premise2], conclusion, timeout=15)
        if result["status"] == "error" and any(
                m in (result.get("raw") or "") for m in _CRASH_MARKERS):
            pytest.skip("the eprover binary aborted")
        assert result["status"] == "proved"
        formula_dicts = [s["formula"] for s in result["derivation"]["steps"]
                         if s["formula"] is not None]
        assert any("świątek" in str(d) for d in formula_dicts)
        assert not any("u015b" in str(d) for d in formula_dicts)
        assert "świątek" in result["raw"]
        assert "u015b" not in result["raw"]
        # PREDICATE names must round-trip through the free-text 'raw' field
        # too, not only constants -- 'LostTo' is already TPTP-legal, so it
        # is subject to Node.to_tptp's first-letter fold ('lostTo') the same
        # way a synthesised token is (R3/R1 regression: see
        # TestReverseRenderedFreeTextRoundTrip in test_tptp_problem.py for
        # the offline/unit-level pin of this same gap).
        assert "LostTo" in result["raw"]
        assert "lostTo(" not in result["raw"]


@pytest.mark.skipif(not eb.zipperposition_available(),
                    reason="no zipperposition binary found")
class TestZipperpositionLive:
    def test_modus_ponens_proved_live(self):
        verdict = get_backend("zipperposition").decide(_GOAL, _PREMISES,
                                                       timeout=15000)
        assert verdict.status == "proved"
