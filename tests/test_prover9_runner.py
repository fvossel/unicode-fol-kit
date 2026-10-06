r"""How the kit starts Prover9, and what it makes of the way Prover9 ends.

* A Prover9 inside WSL is driven the way the Vampire runner drives Vampire:
  ``use_wsl=`` (the backend reads it from the ``use_wsl`` option and from
  ``$UFK_PROVER9_WSL=1``), ``$UFK_PROVER9`` naming the path INSIDE WSL, the Windows
  temp file translated with ``wslpath`` BEFORE the Prover9 time window opens (a slow
  ``wslpath`` is a failure to start, never a Prover9 timeout).
* Prover9 never reads the caller's standard input: given no ``-f`` (and for any flag it
  does not know, ``--version`` included) it reads its problem from stdin.
* Its output is decoded as UTF-8 with undecodable bytes replaced: the fatal message
  quotes the input around the error and can cut a multi-byte character in half.
* An exit that Prover9 never uses (the shell's 127 "no such file" and 126 "not
  executable", which is what ``wsl.exe <path>`` reports for a path that does not exist
  inside WSL) is a refusal with a message, not "no proof".

The offline tests stand in for ``subprocess.run`` (or run a real stand-in process) and
carry the claim everywhere. The live tests run the real Prover9 through the kit's own WSL
route and skip, with a reason, where there is none.
"""

import os
import shutil
import subprocess
import sys
import threading
import time

import pytest

import unicode_fol_kit
from unicode_fol_kit.atp import prover9_entailment as p9
from unicode_fol_kit.atp import protocol as proto
from unicode_fol_kit.atp.prover9_entailment import Prover9Rejected, Prover9TimedOut
from unicode_fol_kit.atp.protocol import Prover9Backend, get_backend
from unicode_fol_kit.fol.nodes import Atom, Constant, Implies, Quantifier, Variable

x = Variable("x")
_GOAL = Atom("Q", [Constant("a")])
_PREMISES = [Atom("P", [Constant("a")]), Quantifier("∀", x, Implies(Atom("P", [x]), Atom("Q", [x])))]


#: The last argument of a version probe: Prover9 has no ``--version``, its banner comes with ``-h``
#: (the probe of other tools still asks ``--version``).
_PROBES = ("--version", "-h")


class _Recorder:
    """A ``subprocess.run`` stand-in: records every call and answers with a canned result."""

    def __init__(self, returncode=0, stdout="", stderr="", raises=None):
        self.calls = []
        self.returncode, self.stdout, self.stderr, self.raises = returncode, stdout, stderr, raises

    def __call__(self, cmd, *args, **kwargs):
        self.calls.append((list(cmd), kwargs))
        if cmd[-1] in _PROBES:
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="")
        if self.raises is not None:
            raise self.raises
        return subprocess.CompletedProcess(cmd, self.returncode, stdout=self.stdout, stderr=self.stderr)

    def prover_calls(self):
        return [(cmd, kwargs) for cmd, kwargs in self.calls if cmd[-1] not in _PROBES]


@pytest.fixture()
def fresh(monkeypatch):
    """No cached version, no ambient WSL setting."""
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    monkeypatch.delenv("UFK_PROVER9_WSL", raising=False)
    monkeypatch.setenv("UFK_PROVER9", "fake-prover9")


# --------------------------------------------------------------------------- #
# The command line.
# --------------------------------------------------------------------------- #

def test_the_native_command_is_unchanged(monkeypatch):
    recorder = _Recorder(returncode=2)
    monkeypatch.setattr(subprocess, "run", recorder)
    assert p9._run_prover9("formulas(sos).\nend_of_list.\n", "prover9", timeout=7) is False
    (command, kwargs), = recorder.calls
    assert command[:2] == ["prover9", "-f"] and command[2].endswith(".in") and len(command) == 3
    assert kwargs["timeout"] == 7


def test_the_wsl_command_runs_the_binary_inside_wsl_on_the_translated_path(monkeypatch):
    recorder = _Recorder(returncode=2)
    monkeypatch.setattr(subprocess, "run", recorder)
    translated = []
    monkeypatch.setattr(p9, "_to_wsl_path", lambda path: translated.append(path) or "/mnt/c/t/problem.in")
    assert p9._run_prover9("x.", "/opt/prover9/bin/prover9", use_wsl=True) is False
    (command, _), = recorder.calls
    # The binary is the path inside WSL; the file is the translated one, not the Windows one.
    assert command == ["wsl.exe", "/opt/prover9/bin/prover9", "-f", "/mnt/c/t/problem.in"]
    assert len(translated) == 1 and translated[0].endswith(".in")


def test_the_path_is_translated_before_the_prover9_time_window_opens(monkeypatch):
    events = []

    def run(cmd, *args, **kwargs):
        events.append(("run", kwargs.get("timeout")))
        return subprocess.CompletedProcess(cmd, 2, stdout="", stderr="")

    monkeypatch.setattr(subprocess, "run", run)
    monkeypatch.setattr(p9, "_to_wsl_path", lambda path: events.append(("wslpath",)) or "/mnt/c/p.in")
    p9._run_prover9("x.", "prover9", timeout=3, use_wsl=True)
    assert events == [("wslpath",), ("run", 3)]


def test_a_slow_wslpath_is_a_failure_to_start_not_a_prover9_timeout(monkeypatch, fresh):
    # wslpath has a time limit of its own. Its TimeoutExpired must not be mistaken for the
    # Prover9 budget running out (Prover9 was never started): it is an OSError, which the
    # backend reports as an error verdict with the reason, never as UNKNOWN / "timeout".
    recorder = _Recorder()
    monkeypatch.setattr(subprocess, "run", recorder)

    def slow(path):
        raise subprocess.TimeoutExpired(["wsl.exe", "wslpath"], 20)

    monkeypatch.setattr(p9, "_to_wsl_path", slow)
    with pytest.raises(OSError, match="wslpath"):
        p9._run_prover9("x.", "prover9", timeout=3, raise_on_timeout=True, use_wsl=True)
    assert recorder.prover_calls() == []                      # Prover9 never started
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, use_wsl=True)
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "wslpath" in verdict.detail


def test_a_wslpath_that_cannot_translate_is_a_failure_to_start(monkeypatch, fresh):
    monkeypatch.setattr(subprocess, "run", _Recorder())

    def broken(path):
        raise RuntimeError(f"wslpath could not translate {path!r} (is WSL available?): ")

    monkeypatch.setattr(p9, "_to_wsl_path", broken)
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, use_wsl=True)
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "wslpath could not translate" in verdict.detail


# --------------------------------------------------------------------------- #
# stdin, decoding, exit codes.
# --------------------------------------------------------------------------- #

def test_prover9_never_reads_the_callers_stdin_and_its_output_is_decoded_as_utf8(monkeypatch):
    recorder = _Recorder(returncode=2)
    monkeypatch.setattr(subprocess, "run", recorder)
    p9._run_prover9("x.", "prover9")
    (_, kwargs), = recorder.calls
    assert kwargs["stdin"] is subprocess.DEVNULL
    assert kwargs["encoding"] == "utf-8" and kwargs["errors"] == "replace"
    assert kwargs["capture_output"] is True and kwargs["text"] is True


def test_the_problem_file_is_written_as_utf8_with_unix_line_ends(monkeypatch):
    seen = {}

    def run(cmd, *args, **kwargs):
        with open(cmd[-1], "rb") as handle:
            seen["bytes"] = handle.read()
        return subprocess.CompletedProcess(cmd, 2, stdout="", stderr="")

    monkeypatch.setattr(subprocess, "run", run)
    p9._run_prover9("P(\"é\").\nQ(a).\n", "prover9")
    assert seen["bytes"] == "P(\"é\").\nQ(a).\n".encode("utf-8")        # no BOM, no CRLF


@pytest.mark.parametrize("code", [127, 126])
def test_an_exit_prover9_never_uses_is_a_refusal_with_the_shells_message(monkeypatch, fresh, code):
    # `wsl.exe <path>` for a path that does not exist inside WSL: the shell says so on
    # stderr and exits 127 (126: found, not executable), with NO Prover9 output at all.
    # That used to read as "found no proof".
    message = "/bin/bash: line 1: /nonexistent/prover9: No such file or directory"
    monkeypatch.setattr(subprocess, "run", _Recorder(returncode=code, stderr=message))
    monkeypatch.setattr(p9, "_to_wsl_path", lambda path: "/mnt/c/p.in")
    # The historic contract of the plain call is unchanged: no proof is False.
    assert p9._run_prover9("x.", "/nonexistent/prover9", use_wsl=True) is False
    with pytest.raises(Prover9Rejected) as refused:
        p9._run_prover9("x.", "/nonexistent/prover9", raise_on_rejection=True, use_wsl=True)
    assert refused.value.returncode == code and "No such file" in refused.value.output
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, use_wsl=True)
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "No such file" in verdict.detail and "not a timeout" in verdict.detail
    assert verdict.detail.startswith("prover9 produced no verdict")


def test_a_refusal_that_prints_nothing_still_says_what_happened(monkeypatch, fresh):
    monkeypatch.setattr(subprocess, "run", _Recorder(returncode=127))
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES)
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "exit code 127" in verdict.detail and "it printed nothing" in verdict.detail


@pytest.mark.parametrize("code", [2, 3, 4, 5, 6, 7])
def test_the_exits_that_end_a_search_stay_no_proof_not_a_refusal(monkeypatch, fresh, code):
    # Prover9's documented ordinary ends of a search (sos empty, max_megs, max_seconds,
    # max_given, max_kept, an action) are UNKNOWN / incomplete, as before.
    monkeypatch.setattr(subprocess, "run", _Recorder(returncode=code, stdout="SEARCH FAILED\n"))
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES)
    assert (verdict.status, verdict.reason) == ("unknown", "incomplete")


def test_a_fatal_message_that_cuts_a_utf8_character_is_an_error_verdict(monkeypatch, fresh):
    # Prover9's fatal message quotes the input around the error: for a non-ASCII symbol it
    # can end between the two bytes of a character (a lone 0xC3 before '%%END ERROR%%'), and
    # a byte the text encoding of the host does not define (0x81) follows. A REAL process
    # writes those bytes and exits 1; only the command line is swapped, so the decoding is
    # the production decoding. It used to die in the reader thread of subprocess.run
    # (stdout None, "argument of type 'NoneType' is not iterable").
    code = ("import sys; sys.stdout.buffer.write(b'Fatal error: Unexpected character: P(\\xc3%%END ERROR%%\\x81 x'); "
            "sys.stdout.flush(); sys.exit(1)")
    real_run = subprocess.run

    def stand_in(cmd, *args, **kwargs):
        if cmd[-1] in _PROBES:
            return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="")
        return real_run([sys.executable, "-c", code], *args, **kwargs)

    monkeypatch.setattr(subprocess, "run", stand_in)
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES)
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "Fatal error" in verdict.detail and "TypeError" not in verdict.detail
    # The message carries the replacement character where the text was cut.
    with pytest.raises(Prover9Rejected) as refused:
        p9.check_logical_entailment(_PREMISES, _GOAL, "fake", raise_on_rejection=True)
    assert refused.value.returncode == 1 and "�" in refused.value.output


def test_a_run_the_kit_stops_is_still_a_timeout(monkeypatch, fresh):
    monkeypatch.setattr(subprocess, "run", _Recorder(raises=subprocess.TimeoutExpired(["prover9"], 1)))
    with pytest.raises(Prover9TimedOut):
        p9._run_prover9("x.", "prover9", raise_on_timeout=True)
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")


# --------------------------------------------------------------------------- #
# The backend and the environment.
# --------------------------------------------------------------------------- #

def test_the_backend_reads_use_wsl_from_the_environment_and_the_option(monkeypatch, fresh):
    recorder = _Recorder(returncode=2)
    monkeypatch.setattr(subprocess, "run", recorder)
    monkeypatch.setattr(p9, "_to_wsl_path", lambda path: "/mnt/c/p.in")
    backend = get_backend("prover9")

    backend.decide(_GOAL, _PREMISES)                                   # no setting: native
    assert recorder.prover_calls()[-1][0][:2] == ["fake-prover9", "-f"]
    assert Prover9Backend._uses_wsl() is False

    monkeypatch.setenv("UFK_PROVER9_WSL", "1")
    assert Prover9Backend._uses_wsl() is True
    backend.decide(_GOAL, _PREMISES)                                   # the environment says WSL
    assert recorder.prover_calls()[-1][0] == ["wsl.exe", "fake-prover9", "-f", "/mnt/c/p.in"]
    # ... and the version probe went through wsl.exe too (its own cache key).
    assert ["wsl.exe", "fake-prover9", "-h"] in [cmd for cmd, _ in recorder.calls]

    backend.decide(_GOAL, _PREMISES, use_wsl=False)                    # the option wins over the environment
    assert recorder.prover_calls()[-1][0][:2] == ["fake-prover9", "-f"]
    monkeypatch.delenv("UFK_PROVER9_WSL")
    backend.decide(_GOAL, _PREMISES, use_wsl=True)                     # and the other way round
    assert recorder.prover_calls()[-1][0][0] == "wsl.exe"


def test_solver_version_asks_the_binary_the_way_decide_runs_it(monkeypatch, fresh):
    recorder = _Recorder()
    monkeypatch.setattr(subprocess, "run", recorder)
    monkeypatch.setenv("UFK_PROVER9_WSL", "1")
    get_backend("prover9").solver_version()
    assert [cmd for cmd, _ in recorder.calls] == [["wsl.exe", "fake-prover9", "-h"]]


def test_the_version_probe_passes_a_null_stdin(monkeypatch):
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    recorder = _Recorder()
    monkeypatch.setattr(subprocess, "run", recorder)
    proto._binary_version("any-tool", False)
    (_, kwargs), = recorder.calls
    assert kwargs["stdin"] is subprocess.DEVNULL


def test_the_version_probe_does_not_wait_for_an_idle_inherited_stdin():
    # A tool that reads stdin to its end (Prover9 does, for a flag it does not know) must not
    # find the probe's own stdin: here the probe runs in a child whose stdin is a pipe that
    # stays open and silent, the situation of an MCP server whose stdin is its protocol
    # stream. Before, the tool inherited it and the probe sat out its 10 s limit, then said
    # "no version".
    package_root = os.path.dirname(os.path.dirname(os.path.abspath(unicode_fol_kit.__file__)))
    env = dict(os.environ, PYTHONPATH=os.pathsep.join(
        [package_root] + ([os.environ["PYTHONPATH"]] if os.environ.get("PYTHONPATH") else [])))
    child_code = (
        "import sys, time\n"
        "from unicode_fol_kit.atp import protocol\n"
        "tool = ('-c', \"import sys; sys.stdin.read(); print('tool 1.0')\")\n"
        "started = time.perf_counter()\n"
        "version = protocol._binary_version(sys.executable, False, args=tool)\n"
        "print(f'{version}|{time.perf_counter() - started:.2f}')\n")
    child = subprocess.Popen([sys.executable, "-c", child_code], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, env=env)
    try:
        output = child.stdout.read()
        child.wait(timeout=60)
    finally:
        child.stdin.close()
        if child.poll() is None:
            child.kill()
    version, _, seconds = output.strip().partition("|")
    assert version == "tool 1.0", output
    assert float(seconds) < 9.5, output      # the probe's own limit is 10 s; it came back by itself


# --------------------------------------------------------------------------- #
# The real binary through the kit's own WSL route.
# --------------------------------------------------------------------------- #

def _wsl_works():
    if shutil.which("wsl.exe") is None:
        return False
    try:
        return subprocess.run(["wsl.exe", "-e", "true"], capture_output=True, timeout=30).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


_REAL_BINARY = Prover9Backend._binary()
needs_wsl_binary = pytest.mark.skipif(
    not (_REAL_BINARY and Prover9Backend._uses_wsl()),
    reason="no Prover9 inside WSL: set $UFK_PROVER9 to its path inside WSL "
           "(for example /mnt/d/prover9/Prover9-LADR-2026-8A/bin/prover9) and $UFK_PROVER9_WSL=1")


_REAL_RUN = subprocess.run          # the real one, whatever a test patches into ``subprocess.run``


def _linux_process_running(pattern):
    """Whether a process whose command line matches ``pattern`` runs inside WSL (``pgrep -f``).

    The caller brackets the first character of the pattern (``[t]mp...``), which keeps the
    ``pgrep`` command line itself from matching it."""
    answer = _REAL_RUN(["wsl.exe", "-e", "pgrep", "-f", pattern], capture_output=True, text=True,
                       timeout=30)
    return answer.returncode == 0


@needs_wsl_binary
def test_live_the_budget_stops_a_prover9_inside_wsl_on_time_and_leaves_no_process_behind(monkeypatch):
    if subprocess.run(["wsl.exe", "-e", "which", "pgrep"], capture_output=True, timeout=30).returncode != 0:
        pytest.skip("no pgrep inside WSL, so a leftover Linux process cannot be looked for")
    # P(a), ∀x (P(x) → P(s(x))) ⊢ Q(a): Prover9 derives P(s(a)), P(s(s(a))), ... and never finds
    # Q(a), so only the budget ends the run. The kit's own problem text would end by itself after a
    # fraction of a second (Prover9's default max_weight of 100 discards the terms s(s(...(a))) from
    # depth 100 on, the sos list runs empty and the search fails), so the text carries
    # assign(max_weight, ...) and the writer's output is replaced by it.
    endless = ("set(prolog_style_variables).\n"
               "clear(print_given).\n"
               "assign(max_weight, 1000000).\n"
               "formulas(sos).\n  P(a).\n  (all X (P(X) -> P(s(X)))).\nend_of_list.\n"
               "formulas(goals).\n  Q(a).\nend_of_list.\n")
    monkeypatch.setattr(p9, "_generate_prover9_input", lambda premises, conclusion: endless)
    premises, goal = _PREMISES, _GOAL

    commands = []
    real_run = subprocess.run

    def recording(cmd, *args, **kwargs):
        commands.append(list(cmd))
        return real_run(cmd, *args, **kwargs)

    monkeypatch.setattr(subprocess, "run", recording)
    outcome = {}

    def work():
        started = time.perf_counter()
        outcome["verdict"] = get_backend("prover9").decide(goal, premises, timeout=6000)
        outcome["elapsed"] = time.perf_counter() - started

    worker = threading.Thread(target=work)
    worker.start()
    try:
        # The control: while the run is going its Linux process IS there, so the look for a
        # leftover afterwards has the power to find one.
        needle = None
        deadline = time.time() + 60
        while needle is None and time.time() < deadline:
            for command in list(commands):
                if command[:2] == ["wsl.exe", _REAL_BINARY] and "-f" in command:
                    name = os.path.basename(command[-1])         # the temp file of THIS run
                    needle = "[" + name[0] + "]" + name[1:]
            time.sleep(0.05)
        assert needle is not None, commands
        deadline = time.time() + 60
        while not _linux_process_running(needle) and time.time() < deadline and worker.is_alive():
            time.sleep(0.1)
        assert _linux_process_running(needle), "the Prover9 process was never seen running"
    finally:
        worker.join(timeout=120)
    assert not worker.is_alive()
    verdict = outcome["verdict"]
    assert (verdict.status, verdict.reason) == ("unknown", "timeout"), verdict
    assert outcome["elapsed"] < 60, outcome["elapsed"]          # not the minutes the search would take
    deadline = time.time() + 30
    while _linux_process_running(needle) and time.time() < deadline:
        time.sleep(0.25)
    assert not _linux_process_running(needle), "a Prover9 process outlived its budget inside WSL"


@pytest.mark.skipif(not shutil.which("wsl.exe"), reason="no wsl.exe on this machine")
def test_live_a_binary_that_does_not_exist_inside_wsl_is_an_error_not_no_proof():
    if not _wsl_works():
        pytest.skip("wsl.exe does not run a command here")
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, prover9_path="/nonexistent/dir/prover9",
                                            use_wsl=True)
    assert (verdict.status, verdict.reason) == ("error", "infra"), verdict
    assert verdict.detail.startswith("prover9 produced no verdict") and "not a timeout" in verdict.detail


@pytest.mark.skipif(not _REAL_BINARY, reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL "
                                             "with $UFK_PROVER9_WSL=1) or put 'prover9' on PATH")
def test_live_a_fatal_message_that_quotes_a_non_ascii_symbol_is_a_refusal_not_a_crash():
    # Prover9 reads ASCII only: given a non-ASCII symbol its fatal message cuts the UTF-8
    # character it quotes in half. That used to end as 'TypeError: argument of type NoneType is
    # not iterable' (the decoder died); now it is Prover9Rejected with the message. The problem
    # WRITER no longer produces such a text (it writes a non-ASCII sort name under an ASCII
    # replacement: tests/test_prover9_symbols.py), so the text here is written by hand.
    text = ("formulas(assumptions).\n  Größe(a).\nend_of_list.\n"
            "formulas(goals).\n  Größe(a).\nend_of_list.\n")
    with pytest.raises(Prover9Rejected) as refused:
        p9._run_prover9(text, _REAL_BINARY, timeout=30, raise_on_rejection=True,
                        use_wsl=Prover9Backend._uses_wsl())
    assert "Fatal error" in str(refused.value) and "TypeError" not in str(refused.value)


@needs_wsl_binary
def test_live_the_wsl_route_proves_and_does_not_prove():
    backend = get_backend("prover9")
    assert backend.decide(_GOAL, _PREMISES, timeout=30000).status == "proved"
    # Hand-derived: P(a) alone does not entail Q(a).
    verdict = backend.decide(_GOAL, [Atom("P", [Constant("a")])], timeout=30000)
    assert (verdict.status, verdict.reason) == ("unknown", "incomplete")
