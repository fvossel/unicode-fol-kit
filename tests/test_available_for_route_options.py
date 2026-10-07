"""``available_for`` reads the option of a call that names the binary or the route.

``run_backend`` asks :meth:`~unicode_logic_kit.atp.protocol.ProverBackend.available_for`
with the options of the call, so that the answer and the run agree. A backend whose
``decide`` reads an option that picks the binary (``minizinc_path=``), the route
(``use_wsl=``, ``twee_cmd=``), the server (``url=``) or the installation
(``install=``) must answer from that option, or a call that names a working binary is
refused and a call that names a missing one is run.

Nothing here starts a prover: availability is faked where it would spawn a process or
open a socket, and ``decide`` is replaced by a recorder, so a test only shows which
calls the gate lets through.
"""

import os
import shutil

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import protocol
from unicode_logic_kit.atp.minizinc_backend import MinizincBackend
from unicode_logic_kit.atp.protocol import (
    BackendUnavailable, declared_options, get_backend, run_backend,
)
from unicode_logic_kit.fol.nodes import Atom

GOAL = Atom("P", [])


def _recording_decide(monkeypatch, backend_class):
    """Replace ``decide`` of ``backend_class`` by a recorder; return the list of calls."""
    calls = []

    def decide(self, formula, premises=(), timeout=10000, **options):
        calls.append(dict(options))
        return protocol.Verdict("unknown", self.name)

    monkeypatch.setattr(backend_class, "decide", decide)
    return calls


# ---------------------------------------------------------------------------
# MiniZinc: minizinc_path=
# ---------------------------------------------------------------------------

@pytest.fixture
def nothing_discoverable(monkeypatch):
    """No ``$UFK_MINIZINC``, and ``minizinc`` is not on PATH."""
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    real_which = shutil.which
    monkeypatch.setattr(shutil, "which", lambda cmd, *a, **k: None if cmd == "minizinc"
                        else real_which(cmd, *a, **k))


@pytest.fixture
def executable(tmp_path):
    """The path of an existing file that is runnable as far as the OS can tell."""
    path = tmp_path / ("fake-minizinc.exe" if os.name == "nt" else "fake-minizinc")
    path.write_text("")
    path.chmod(0o755)
    return str(path)


def test_without_an_option_discovery_decides(nothing_discoverable, monkeypatch):
    backend = get_backend("minizinc")
    assert backend.available() is False
    assert backend.available_for({}) is False
    assert backend.available_for({"minizinc_path": ""}) is False       # empty: decide discovers too
    monkeypatch.setenv("UFK_MINIZINC", "/anywhere/minizinc")
    assert backend.available_for({}) is True and backend.available() is True


def test_a_named_binary_is_available_where_nothing_is_discoverable(nothing_discoverable, executable):
    backend = get_backend("minizinc")
    assert backend.available() is False
    assert backend.available_for({"minizinc_path": executable}) is True


def test_a_named_binary_that_is_not_there_is_not_available(nothing_discoverable, tmp_path, monkeypatch):
    missing = str(tmp_path / "no-such-dir" / "minizinc")
    monkeypatch.setenv("UFK_MINIZINC", "/anywhere/minizinc")           # discovery would say yes
    assert get_backend("minizinc").available_for({"minizinc_path": missing}) is False


def test_the_gate_lets_the_named_binary_through_and_stops_the_missing_one(
        nothing_discoverable, executable, tmp_path, monkeypatch):
    calls = _recording_decide(monkeypatch, MinizincBackend)
    run_backend("minizinc", GOAL, [], minizinc_path=executable)
    assert calls == [{"minizinc_path": executable}]
    with pytest.raises(BackendUnavailable, match="minizinc"):
        run_backend("minizinc", GOAL, [], minizinc_path=str(tmp_path / "missing"))
    with pytest.raises(BackendUnavailable, match="minizinc"):
        api.prove(GOAL, [], backends=["minizinc"], minizinc_path=str(tmp_path / "missing"))
    assert len(calls) == 1


def test_a_real_minizinc_named_by_path_answers_where_it_is_not_discoverable(monkeypatch):
    """Live. ``∀x ∀y (x = y)`` is not valid: the universe ``{0, 1}`` with ``x ↦ 0``, ``y ↦ 1``
    falsifies it, so a size-2 search finds a countermodel."""
    real = os.environ.get("UFK_MINIZINC") or shutil.which("minizinc")
    if not real:
        pytest.skip("no MiniZinc binary on this machine")
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    real_which = shutil.which
    monkeypatch.setattr(shutil, "which", lambda cmd, *a, **k: None if cmd == "minizinc"
                        else real_which(cmd, *a, **k))
    goal = api.parse_any("∀x ∀y (x = y)").formula
    assert get_backend("minizinc").available() is False
    verdict = api.prove(goal, [], backends=["minizinc"], minizinc_path=real, max_size=2, timeout=60000)
    assert verdict.status == "refuted"


# ---------------------------------------------------------------------------
# Twee: use_wsl= and twee_cmd=
# ---------------------------------------------------------------------------

@pytest.fixture
def twee_only_in_wsl(monkeypatch):
    """Twee exists at one place only: through WSL, at its default command."""
    calls = []

    def twee_available(use_wsl=True, twee_cmd=None):
        calls.append((use_wsl, twee_cmd))
        return use_wsl is True and twee_cmd in (None, "/home/me/.local/bin/twee")

    from unicode_logic_kit.atp import twee_entailment
    monkeypatch.setattr(twee_entailment, "twee_available", twee_available)
    return calls


def test_twee_is_asked_for_the_route_the_call_names(twee_only_in_wsl):
    backend = get_backend("twee")
    assert backend.available() is True
    assert backend.available_for({}) is True
    assert backend.available_for({"use_wsl": False}) is False                    # no native Twee
    assert backend.available_for({"twee_cmd": "/nonexistent/twee"}) is False    # no such command in WSL
    assert backend.available_for({"use_wsl": True, "twee_cmd": "/home/me/.local/bin/twee"}) is True
    assert twee_only_in_wsl == [(True, None), (True, None), (False, None),
                                (True, "/nonexistent/twee"), (True, "/home/me/.local/bin/twee")]


def test_the_gate_refuses_a_twee_route_that_cannot_run(twee_only_in_wsl, monkeypatch):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    calls = _recording_decide(monkeypatch, TweeBackend)
    for options in ({"use_wsl": False}, {"twee_cmd": "/nonexistent/twee"}):
        with pytest.raises(BackendUnavailable, match="twee"):
            run_backend("twee", GOAL, [], **options)
    assert calls == []
    run_backend("twee", GOAL, [])
    assert calls == [{}]


# ---------------------------------------------------------------------------
# Hets: url=
# ---------------------------------------------------------------------------

@pytest.fixture
def hets_only_at_one_url(monkeypatch):
    """The only HETS server that answers is at ``HETS_URL``; localhost does not."""
    from unicode_logic_kit.hets import docker
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(docker, "_probe_health", lambda url, *a, **k: url.rstrip("/") == HETS_URL)


HETS_URL = "http://hets.example:8000"


def test_hets_is_asked_about_the_server_the_call_names(hets_only_at_one_url):
    backend = get_backend("hets")
    assert backend.available() is False                          # nothing on localhost, no $UFK_HETS_URL
    assert backend.available_for({}) is False
    assert backend.available_for({"url": HETS_URL}) is True
    assert backend.available_for({"url": HETS_URL + "/"}) is True
    assert backend.available_for({"url": "http://nowhere.example:1"}) is False


def test_the_gate_lets_the_named_hets_server_through(hets_only_at_one_url, monkeypatch):
    from unicode_logic_kit.atp.hets_backend import HetsBackend
    calls = _recording_decide(monkeypatch, HetsBackend)
    run_backend("hets", GOAL, [], url=HETS_URL)
    assert calls == [{"url": HETS_URL}]
    with pytest.raises(BackendUnavailable, match="hets"):
        run_backend("hets", GOAL, [], url="http://nowhere.example:1")
    with pytest.raises(BackendUnavailable, match="hets"):
        run_backend("hets", GOAL, [])
    assert len(calls) == 1


# ---------------------------------------------------------------------------
# Isabelle: install=   (nothing here runs Isabelle)
# ---------------------------------------------------------------------------

def test_an_isabelle_installation_named_by_the_call_is_the_one_that_runs(monkeypatch):
    from unicode_logic_kit.hol import isabelle_runner
    monkeypatch.setattr(isabelle_runner, "isabelle_available", lambda *a, **k: False)
    from unicode_logic_kit.atp.protocol import IsabelleBackend
    calls = _recording_decide(monkeypatch, IsabelleBackend)
    backend = get_backend("isabelle")
    install = object()                                           # the runner takes it as it is
    assert backend.available() is False and backend.available_for({}) is False
    assert backend.available_for({"install": None}) is False
    assert backend.available_for({"install": install}) is True
    run_backend("isabelle", GOAL, [], install=install)
    assert calls == [{"install": install}]
    with pytest.raises(BackendUnavailable, match="isabelle"):
        run_backend("isabelle", GOAL, [])


# ---------------------------------------------------------------------------
# No backend that reads such an option is left to the default answer
# ---------------------------------------------------------------------------

#: The options that pick a binary, a route, a server or an installation.
ROUTE_OPTIONS = frozenset({"use_wsl", "vampire_path", "prover9_path", "twee_cmd", "minizinc_path",
                           "url", "install"})


def test_every_stock_backend_that_reads_a_route_option_answers_from_it():
    """A backend whose ``decide`` takes one of these options and whose ``available_for`` is the
    base class's answers for the default route only. Declared options are the ones ``decide`` reads
    (``tests/test_prove_options.py`` compares the two), so this finds a backend added later."""
    unanswered = []
    for name in sorted(protocol._REGISTRY):
        backend = get_backend(name)
        if not type(backend).__module__.startswith("unicode_logic_kit"):
            continue                                             # a test double registered by another test
        reads = (declared_options(backend) or frozenset()) & ROUTE_OPTIONS
        if reads and "available_for" not in vars(type(backend)):
            unanswered.append((name, sorted(reads)))
    assert unanswered == []
