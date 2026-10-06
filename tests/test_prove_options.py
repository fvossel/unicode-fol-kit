"""What ``api.prove`` does with the keyword options it is given, what its chain summary says, and
whether a backend that has to be started through WSL is reported as available.

OPTIONS. A backend declares the names it reads (``ProverBackend.accepted_options``). An option that
NO backend of the chain reads is a ``ValueError`` before anything runs. Otherwise each backend is
handed the options it reads. A backend that does not read an option that CHANGES THE QUESTION
(a modal frame, a bridge, a domain regime) while another backend of the chain does is not run: any
verdict of it would answer another question. An option that only bounds a search or says where a
binary lives is simply not handed to a backend that has no use for it.

THE EXPECTED SETS below are read off each backend's ``decide`` (the names it pops from ``options``)
and off the signature of the function it forwards the rest to, not off the code under test.
"""

import re
import subprocess
from typing import List

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import protocol
from unicode_fol_kit.atp.protocol import (
    ERROR, PROVED, REFUTED, UNKNOWN, BackendUnavailable, ProverBackend, Verdict, declared_options,
    get_backend, plan_options, run_backend,
)
from unicode_fol_kit.fol.nodes import Atom, Believes, Constant, Implies, Knows


def parse(text):
    result = api.parse_any(text)
    assert result.ok, (text, result.errors)
    return result.formula


GOAL = Implies(Atom("P", [Constant("ann")]), Atom("P", [Constant("ann")]))


class Probe(ProverBackend):
    """A backend that records the options it is handed and answers as it was built to."""

    logics = frozenset({"fol"})
    external = False

    def __init__(self, name, *, reads=None, status=UNKNOWN, reason="incomplete", detail=None,
                 calls=None):
        self.name = name
        self.reads = reads
        self._answer = (status, reason, detail)
        self.calls = calls if calls is not None else []

    def available(self):
        return True

    def accepted_options(self, logic=None):
        return None if self.reads is None else frozenset(self.reads)

    def decide(self, formula, premises=(), timeout=10000, **options):
        self.calls.append((self.name, dict(options)))
        status, reason, detail = self._answer
        return Verdict(status, self.name, reason=None if status in (PROVED, REFUTED) else reason,
                       detail=detail)


@pytest.fixture
def probes(monkeypatch):
    """Register probes under their own names; returns the shared list of ``(name, options)`` calls."""
    calls: List[tuple] = []

    def register(name, **kwargs):
        backend = Probe(name, calls=calls, **kwargs)
        monkeypatch.setitem(protocol._REGISTRY, name, backend)
        return backend
    register.calls = calls
    return register


# =============================================================================
# An option that no backend of the chain reads
# =============================================================================

def test_an_option_that_no_backend_reads_is_a_value_error_naming_it_and_the_chain_before_anything_runs(probes):
    probes("pr-one", reads={"alpha"})
    probes("pr-two", reads={"beta"})
    with pytest.raises(ValueError) as caught:
        api.prove(GOAL, backends=["pr-one", "pr-two"], gamma=1)
    message = str(caught.value)
    assert "'gamma'" in message and "pr-one" in message and "pr-two" in message
    assert "alpha" in message and "beta" in message              # what the chain DOES read
    assert probes.calls == []                                    # nothing ran


def test_a_real_backend_that_ignored_every_option_now_refuses_one_that_it_does_not_read():
    # z3 read none, and ignored `frame="S4"`: the answer was given as if it had not been passed.
    with pytest.raises(ValueError, match=r"'frame'.*z3"):
        api.prove(GOAL, backends=["z3"], frame="S4")
    # the tableau used to fail with a TypeError that surfaced as an ERROR verdict
    with pytest.raises(ValueError, match=r"'zzz_bogus'.*tableau"):
        api.prove(GOAL, backends=["tableau"], zzz_bogus=1)


def test_countermodel_refuses_such_an_option_too():
    with pytest.raises(ValueError, match="'frame'"):
        api.countermodel(GOAL, frame="S4")


def test_a_backend_that_declares_nothing_is_handed_every_option_and_never_triggers_the_refusal(probes):
    probes("pr-undeclared")                         # reads=None: nothing is known about it
    api.prove(GOAL, backends=["pr-undeclared"], anything=3)
    assert probes.calls == [("pr-undeclared", {"anything": 3})]


def test_no_options_means_no_check(probes):
    probes("pr-one", reads=set())
    api.prove(GOAL, backends=["pr-one"])
    assert probes.calls == [("pr-one", {})]


# =============================================================================
# An option that some backend reads
# =============================================================================

def test_an_option_that_only_bounds_a_search_goes_to_the_backends_that_read_it(probes):
    probes("pr-bounded", reads={"max_steps"})
    probes("pr-other", reads=set())
    api.prove(GOAL, backends=["pr-bounded", "pr-other"], max_steps=7)
    # the second backend has no use for the bound; it still answers the same question without it
    assert probes.calls == [("pr-bounded", {"max_steps": 7}), ("pr-other", {})]


def test_the_default_classical_chain_takes_a_search_bound_without_failing_on_the_backends_that_lack_it():
    # z3 and the model finder do not read max_steps, the tableau and the resolution prover do.
    assert api.prove(GOAL, max_steps=2000).status == "proved"
    verdict = api.prove(parse("∀x (P(x) → Q(x)) → ∃x (P(x) → Q(x))"),
                        backends=["tableau", "resolution", "modelfinder"], max_steps=5000, max_size=2)
    assert verdict.status in ("proved", "unknown")                # never an error from a TypeError
    assert "TypeError" not in (verdict.detail or "")


def test_a_backend_that_does_not_read_an_option_that_changes_the_question_is_not_run(probes):
    probes("pr-reads", reads={"frame"}, status=UNKNOWN, reason="incomplete", detail="no proof found")
    probes("pr-blind", reads=set(), status=REFUTED)           # would answer for the default frame
    verdict = api.prove(GOAL, backends=["pr-reads", "pr-blind"], frame="S4")
    assert probes.calls == [("pr-reads", {"frame": "S4"})]    # pr-blind never ran
    assert verdict.status == UNKNOWN                          # and its refutation was not the answer
    assert "pr-blind:unknown/unsupported" in verdict.detail
    assert "'frame'" in verdict.detail and "changes the question" in verdict.detail


def test_the_wrong_verdict_that_passing_an_option_only_to_its_readers_would_give_cannot_happen(probes):
    # `bridges=` is a frame condition: ``K φ → B φ`` is valid ONLY under the bridge. A route that does
    # not read it refutes the formula (it decides the logic without the bridge) -- and used to be run
    # anyway, ahead of the route that does read it.
    probes("pr-no-bridges", reads=set(), status=REFUTED)
    probes("pr-bridges", reads={"bridges"}, status=PROVED)
    verdict = api.prove(GOAL, backends=["pr-no-bridges", "pr-bridges"], bridges=["knowledge_implies_belief"])
    assert verdict.status == PROVED and verdict.backend == "pr-bridges"
    assert [name for name, _ in probes.calls] == ["pr-bridges"]
    # without the option the blind route answers, as it should for the question it was asked
    probes.calls.clear()
    assert api.prove(GOAL, backends=["pr-no-bridges", "pr-bridges"]).status == REFUTED


def test_a_modal_chain_with_a_bridge_is_answered_by_the_route_that_reads_it():
    agent, p = Constant("alice"), Atom("P", [])
    formula = Implies(Knows(agent, p), Believes(agent, p))     # valid exactly under the bridge
    verdict = api.prove(formula, bridges=["knowledge_implies_belief"])
    assert (verdict.status, verdict.backend) == (PROVED, "qml")
    # the bounded enumeration does not read bridges; it is listed as not run, not asked without it
    chain = api.prove(formula, backends=["modal-tableau", "kripke-enum"],
                      bridges=["knowledge_implies_belief"])
    assert chain.status == UNKNOWN
    assert "kripke-enum:unknown/unsupported" in chain.detail and "'bridges'" in chain.detail
    assert "kripke-enum:refuted" not in chain.detail


def test_a_domain_regime_only_qml_reads_is_not_answered_by_the_routes_that_cannot_read_it():
    barcan = api.parse_any("∀x □P(x) → □∀x P(x)", hint="modal").formula
    chain = api.prove(barcan, mode="varying", timeout=3000)
    assert chain.status != PROVED                              # the Barcan formula fails with varying domains
    assert "modal-tableau:unknown/unsupported" in chain.detail
    assert "kripke-enum:unknown/unsupported" in chain.detail
    assert "'mode'" in chain.detail


def test_plan_options_reports_the_options_each_backend_is_handed_and_the_reason_one_is_not(probes):
    probes("pr-reads", reads={"frame", "max_steps"})
    probes("pr-blind", reads=set())
    plan = plan_options("prove", ("pr-reads", "pr-blind"), "fol", {"frame": "K", "max_steps": 3})
    assert plan["pr-reads"] == ({"frame": "K", "max_steps": 3}, None)
    passed, refusal = plan["pr-blind"]
    assert passed == {} and "'frame'" in refusal and "'max_steps'" not in refusal


# =============================================================================
# What each stock backend reads
# =============================================================================

#: backend -> the names its ``decide`` pops, or the keyword list of the function it forwards ``**options`` to
EXPECTED = {
    "z3": set(),
    "tableau": {"max_steps", "max_terms"},                                    # prove_tableau_detailed
    "resolution": {"max_steps"},                                              # resolution.prove
    "modelfinder": {"max_size", "max_candidates", "symmetry_breaking", "subsorts"},   # find_countermodel
    "modal-tableau": {"frame", "systems", "max_worlds", "max_steps", "bridges"},      # modal_decide
    "qml": {"mode", "frame", "systems", "bridges", "temporal_closure"},       # qml_is_valid, minus its timeout
    "kripke-enum": {"frame", "systems", "max_worlds", "max_atoms", "max_models"},     # modal_enum_search
    "prover9": {"prover9_path", "use_wsl"},
    "vampire": {"vampire_path", "use_wsl", "tff", "sort", "premise_names", "axiom_names"},
    "eprover": {"tff", "sort", "premise_names"},
    "zipperposition": {"tff", "sort", "premise_names"},
    "cvc5": {"logic", "random_seed", "proof"},
    "clingo": {"max_size", "all_different", "verify"},
    "minizinc": {"minizinc_path", "max_size", "solver", "all_different"},
    "hets": {"reasoner", "translation", "url"},
    "twee": {"use_wsl", "twee_cmd"},
    "nanocop": {"logic", "domain"},
    "leo3": {"frame", "domains"},
    "ltl-tableau": {"mode", "max_atoms"},
    "intuitionistic": {"max_worlds", "domain_elements", "max_steps"},         # int_countermodel
    "lambek": set(),
    "ill": {"max_depth", "max_steps"},
    "relevant": {"max_worlds"},
    "hybrid": {"frame", "systems", "temporal_closure"},                      # hybrid_is_valid, minus its timeout
}


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_each_stock_backend_declares_the_options_its_decide_reads(name):
    assert declared_options(get_backend(name), "fol") == EXPECTED[name]


def test_every_registered_stock_backend_has_a_declaration():
    undeclared = [name for name, backend in protocol._REGISTRY.items()
                  if type(backend).__module__.startswith("unicode_fol_kit.")
                  and declared_options(backend, "fol") is None]
    assert undeclared == []
    assert set(EXPECTED) | {"isabelle"} == {
        name for name, backend in protocol._REGISTRY.items()
        if type(backend).__module__.startswith("unicode_fol_kit.")}


def test_the_isabelle_backend_reads_the_keywords_of_the_runner_of_the_logic_of_the_call():
    isabelle = get_backend("isabelle")
    classical, modal = declared_options(isabelle, "fol"), declared_options(isabelle, "modal")
    assert {"native_equality", "msfol", "methods", "refute", "card", "prove_timeout"} <= classical
    assert {"frame", "mode", "temporal_closure", "systems", "bridges", "methods", "card"} <= modal
    assert not classical & {"frame", "mode", "bridges"}
    assert not modal & {"msfol", "native_equality"}


def test_isabelle_is_refused_an_option_it_does_not_read_before_anything_runs():
    # (a ValueError at the check: nothing is started)
    with pytest.raises(ValueError, match=r"'frame'.*isabelle"):
        api.prove(GOAL, backends=["isabelle"], frame="S4")


@pytest.mark.parametrize("name", sorted(EXPECTED))
def test_a_declared_name_is_never_missing_for_an_option_the_decide_body_pops(name):
    """Every name a ``decide`` body reads from ``options`` is declared (a drift guard: a backend that
    starts reading a new option has to say so)."""
    backend = get_backend(name)
    import inspect
    source = inspect.getsource(type(backend).decide)
    read = set(re.findall(r"options\.(?:pop|get)\(\s*[\"'](\w+)[\"']", source))
    read |= set(re.findall(r"[\"'](\w+)[\"']\s+in\s+options", source))
    read -= {"logic"} if name == "isabelle" else set()
    assert read <= declared_options(backend, "fol"), (name, read - declared_options(backend, "fol"))


def test_a_subclass_declares_its_own_options_the_stock_declaration_is_not_inherited():
    class Wider(type(get_backend("z3"))):
        name = "z3-wider"

    assert declared_options(Wider(), "fol") is None            # undeclared: handed everything, as before


# =============================================================================
# The chain summary
# =============================================================================

def test_the_summary_carries_the_status_and_the_reason_text_of_every_member_that_ran(probes):
    probes("fx-bound", reason="bound_hit", detail="no countermodel up to the size bound")
    probes("fx-incomplete", reason="incomplete", detail="gave up on the quantifier prefix")
    probes("fx-unsupported", reason="unsupported", detail="no rule for Count in this route")
    probes("fx-timeout", reason="timeout")                        # no text: listed by status alone
    verdict = api.prove(GOAL, backends=["fx-bound", "fx-incomplete", "fx-unsupported", "fx-timeout"])
    assert verdict.status == UNKNOWN and verdict.backend == "chain"
    assert verdict.detail == (
        "no definitive verdict — "
        "fx-bound:unknown/bound_hit (no countermodel up to the size bound); "
        "fx-incomplete:unknown/incomplete (gave up on the quantifier prefix); "
        "fx-unsupported:unknown/unsupported (no rule for Count in this route); "
        "fx-timeout:unknown/timeout")


def test_a_member_that_failed_is_still_quoted_and_a_chain_of_failures_is_an_error(probes):
    probes("fx-err-one", status=ERROR, reason="infra", detail="prover said no")
    probes("fx-err-two", status=ERROR, reason="infra", detail="parse error")
    verdict = api.prove(GOAL, backends=["fx-err-one", "fx-err-two"])
    assert verdict.status == ERROR
    assert verdict.detail == ("no backend gave an answer — fx-err-one:error/infra (prover said no); "
                              "fx-err-two:error/infra (parse error)")


def test_a_definitive_member_that_was_not_enough_is_listed_with_its_account(probes):
    probes("fx-proves", status=PROVED, detail="closed by saturation")
    probes("fx-undecided", reason="timeout", detail="ran out of its second")
    verdict = api.prove(GOAL, backends=["fx-proves", "fx-undecided"], require_agreement=2)
    assert verdict.status == UNKNOWN
    assert verdict.detail == ("no definitive verdict — fx-proves:proved (closed by saturation); "
                              "fx-undecided:unknown/timeout (ran out of its second)")


def test_the_members_of_a_real_chain_that_gave_up_say_where_in_the_summary():
    # P(ann) is no theorem, so both searches end at their step bound; each says so in its own words
    verdict = api.prove(parse("P(ann)"), backends=["resolution", "tableau"], max_steps=3)
    assert verdict.status == UNKNOWN
    assert "resolution:unknown/bound_hit (" in verdict.detail
    assert "tableau:unknown/bound_hit (" in verdict.detail


# =============================================================================
# available() answers for the route the runner takes
# =============================================================================

class FakeWsl:
    """``wsl.exe which <binary>`` as the tests want it to answer; records every call."""

    def __init__(self, monkeypatch, found=(), error=None):
        self.found = set(found)
        self.error = error
        self.calls = []
        monkeypatch.setattr(subprocess, "run", self._run)

    def _run(self, command, **kwargs):
        self.calls.append((list(command), kwargs))
        if self.error is not None:
            raise self.error
        assert command[:2] == ["wsl.exe", "which"], command
        found = command[2] in self.found
        return subprocess.CompletedProcess(command, 0 if found else 1,
                                           stdout=b"/usr/local/bin/" + command[2].encode() + b"\n" if found else b"",
                                           stderr=b"")


@pytest.fixture
def clean(monkeypatch):
    """No discovery from the environment or from this host's PATH; an empty WSL cache."""
    for variable in ("UFK_VAMPIRE", "UFK_VAMPIRE_WSL", "UFK_PROVER9", "UFK_PROVER9_WSL"):
        monkeypatch.delenv(variable, raising=False)
    monkeypatch.setattr(protocol.shutil, "which", lambda name: None)
    monkeypatch.setattr(protocol, "_WSL_BINARY_CACHE", {})


def test_the_wsl_probe_asks_wsl_with_a_short_timeout_and_no_standard_input(monkeypatch, clean):
    wsl = FakeWsl(monkeypatch, found={"vampire"})
    assert protocol._wsl_has_binary("vampire") is True
    command, kwargs = wsl.calls[0]
    assert command == ["wsl.exe", "which", "vampire"]
    assert kwargs["stdin"] is subprocess.DEVNULL
    assert 0 < kwargs["timeout"] <= 10


def test_the_wsl_answer_is_cached_per_binary_and_a_miss_is_cached_too(monkeypatch, clean):
    wsl = FakeWsl(monkeypatch, found={"vampire"})
    assert [protocol._wsl_has_binary("vampire") for _ in range(3)] == [True] * 3
    assert [protocol._wsl_has_binary("nothere") for _ in range(2)] == [False] * 2
    assert [c[0][2] for c in wsl.calls] == ["vampire", "nothere"]      # one probe per binary


def test_a_probe_that_times_out_is_not_remembered_as_a_missing_binary(monkeypatch, clean):
    FakeWsl(monkeypatch, error=subprocess.TimeoutExpired(["wsl.exe"], 10))
    assert protocol._wsl_has_binary("vampire") is False
    wsl = FakeWsl(monkeypatch, found={"vampire"})                       # WSL was only slow to start
    assert protocol._wsl_has_binary("vampire") is True
    assert len(wsl.calls) == 1


def test_a_host_without_wsl_is_not_an_error(monkeypatch, clean):
    FakeWsl(monkeypatch, error=FileNotFoundError("wsl.exe"))
    assert protocol._wsl_has_binary("vampire") is False


@pytest.mark.parametrize("name,path_variable,wsl_variable,path_option", [
    ("vampire", "UFK_VAMPIRE", "UFK_VAMPIRE_WSL", "vampire_path"),
    ("prover9", "UFK_PROVER9", "UFK_PROVER9_WSL", "prover9_path"),
])
class TestAvailabilityIsTheRoutesOwn:

    def test_nothing_named_means_not_available_and_wsl_is_not_asked(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        wsl = FakeWsl(monkeypatch, found={name})
        assert get_backend(name).available() is False
        assert get_backend(name).available_for({}) is False
        assert wsl.calls == []

    def test_a_native_binary_is_not_looked_for_in_wsl(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        wsl = FakeWsl(monkeypatch)
        monkeypatch.setenv(path_variable, f"/opt/{name}")
        assert get_backend(name).available() is True
        assert wsl.calls == []

    def test_with_the_switch_in_the_environment_wsl_is_asked_about_the_named_binary(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        wsl = FakeWsl(monkeypatch, found={f"/opt/{name}"})
        monkeypatch.setenv(path_variable, f"/opt/{name}")
        monkeypatch.setenv(wsl_variable, "1")
        assert get_backend(name).available() is True
        assert wsl.calls[0][0] == ["wsl.exe", "which", f"/opt/{name}"]
        monkeypatch.setenv(path_variable, f"/opt/not-there")
        assert get_backend(name).available() is False             # the variable is set, the binary is not in WSL

    def test_the_switch_and_the_path_can_come_with_the_call(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        wsl = FakeWsl(monkeypatch, found={name})
        backend = get_backend(name)
        assert backend.available_for({path_option: name, "use_wsl": True}) is True
        assert backend.available_for({path_option: "elsewhere", "use_wsl": True}) is False
        # Native: the path the call names must be a file this host can start (here the fixture
        # leaves nothing on PATH, and "elsewhere" is no file). A call that names a binary the
        # run cannot start is refused at the gate, not let through to fail inside the run.
        assert backend.available_for({path_option: "elsewhere", "use_wsl": False}) is False
        assert [c[0][2] for c in wsl.calls] == [name, "elsewhere"]

    def test_the_call_overrides_the_environment_switch(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        wsl = FakeWsl(monkeypatch)
        monkeypatch.setenv(path_variable, f"/opt/{name}")
        monkeypatch.setenv(wsl_variable, "1")
        assert get_backend(name).available_for({"use_wsl": False}) is True
        assert wsl.calls == []

    def test_run_backend_asks_for_the_route_of_the_call_and_refuses_before_deciding(
            self, monkeypatch, clean, name, path_variable, wsl_variable, path_option):
        FakeWsl(monkeypatch)                                          # WSL has no such binary
        decided = []
        monkeypatch.setattr(type(get_backend(name)), "decide",
                            lambda self, *a, **k: decided.append(1))
        with pytest.raises(BackendUnavailable):
            run_backend(name, GOAL, [], **{path_option: name, "use_wsl": True})
        assert decided == []


def test_api_prove_runs_vampire_through_wsl_when_the_call_says_so():
    """Live, where Vampire can be reached through WSL (or natively): the call that names the binary and the
    route is answered, which ``available()`` used to refuse."""
    import shutil
    native = shutil.which("vampire")
    options = (dict(vampire_path=native, use_wsl=False) if native
               else dict(vampire_path="vampire", use_wsl=True))
    if not get_backend("vampire").available_for(options):
        pytest.skip("no Vampire binary the kit can run (native or WSL)")
    verdict = api.prove(GOAL, [], backends=["vampire"], timeout=60000, **options)
    assert verdict.status == "proved"
