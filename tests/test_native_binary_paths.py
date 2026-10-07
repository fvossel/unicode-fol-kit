"""A path that a call names for a native binary is judged by whether the run can start it.

``available_for`` answers for the route the options of a call select, so that the gate in
``run_backend`` and the run agree:

* MiniZinc: on Windows ``subprocess`` starts ``D:/Minizinc/MiniZinc/minizinc`` through
  ``CreateProcess``, which appends ``.exe`` to a name that has none. ``shutil.which`` (before
  Python 3.12) does not, for a path with a directory part. A call that names the installed
  binary without its extension is answered, not refused as "not available".
* Vampire and Prover9: a native ``vampire_path=`` / ``prover9_path=`` that names no file this
  host can start is refused by name at the gate instead of failing inside the run. With the
  WSL switch on the path is inside WSL and is asked there; what ``$UFK_VAMPIRE`` /
  ``$UFK_PROVER9`` names is the installation the user pointed at and is not second-guessed.

Nothing here starts a prover: ``decide`` is replaced by a recorder where a test shows which
calls the gate lets through.
"""

import os
import shutil

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import protocol
from unicode_logic_kit.atp.minizinc_backend import MinizincBackend
from unicode_logic_kit.atp.protocol import (
    BackendUnavailable, Prover9Backend, VampireBackend, get_backend, run_backend,
)
from unicode_logic_kit.fol.nodes import Atom

GOAL = Atom("P", [])
ON_WINDOWS = os.name == "nt"
#: The MiniZinc of this machine, read before any test removes it from the environment.
_REAL_MINIZINC = os.environ.get("UFK_MINIZINC") or shutil.which("minizinc")


@pytest.fixture
def nothing_discoverable(monkeypatch):
    """No ``$UFK_*`` variable, and none of the three binaries is on PATH."""
    for variable in ("UFK_MINIZINC", "UFK_VAMPIRE", "UFK_PROVER9", "UFK_VAMPIRE_WSL", "UFK_PROVER9_WSL"):
        monkeypatch.delenv(variable, raising=False)
    real_which = shutil.which
    monkeypatch.setattr(
        shutil, "which",
        lambda cmd, *a, **k: None if cmd in ("minizinc", "vampire", "prover9") else real_which(cmd, *a, **k))


@pytest.fixture
def installed(tmp_path):
    """An existing file that is runnable as far as the OS can tell: ``(path as the OS names it,
    the same path as a caller may spell it)``. On Windows the file is ``fake.exe`` and the caller
    may leave the extension out."""
    path = tmp_path / ("fake-binary.exe" if ON_WINDOWS else "fake-binary")
    path.write_text("")
    path.chmod(0o755)
    spelled = str(path)[:-4] if ON_WINDOWS else str(path)
    return str(path), spelled


def _recording_decide(monkeypatch, backend_class):
    calls = []

    def decide(self, formula, premises=(), timeout=10000, **options):
        calls.append(dict(options))
        return protocol.Verdict("unknown", self.name)

    monkeypatch.setattr(backend_class, "decide", decide)
    return calls


# ---------------------------------------------------------------------------
# MiniZinc
# ---------------------------------------------------------------------------

class TestMinizincPathSpellings:
    def test_the_path_as_the_os_names_it_is_available(self, nothing_discoverable, installed):
        full, _spelled = installed
        assert get_backend("minizinc").available_for({"minizinc_path": full}) is True

    @pytest.mark.skipif(not ON_WINDOWS, reason="the .exe is added by the Windows process loader")
    def test_the_path_without_the_extension_is_available(self, nothing_discoverable, installed):
        _full, spelled = installed
        assert not os.path.exists(spelled)            # the caller's spelling is not a file itself
        assert get_backend("minizinc").available_for({"minizinc_path": spelled}) is True

    @pytest.mark.skipif(not ON_WINDOWS, reason="the .exe is added by the Windows process loader")
    def test_the_gate_lets_the_extensionless_path_through(self, nothing_discoverable, installed,
                                                          monkeypatch):
        _full, spelled = installed
        calls = _recording_decide(monkeypatch, MinizincBackend)
        run_backend("minizinc", GOAL, [], minizinc_path=spelled)
        assert calls == [{"minizinc_path": spelled}]

    def test_a_path_that_names_no_file_is_not_available(self, nothing_discoverable, installed, tmp_path):
        full, spelled = installed
        backend = get_backend("minizinc")
        assert backend.available_for({"minizinc_path": str(tmp_path / "missing")}) is False
        assert backend.available_for({"minizinc_path": str(tmp_path / "missing.exe")}) is False
        assert backend.available_for({"minizinc_path": str(tmp_path)}) is False      # a directory
        # the neighbour of an existing file is no file either
        assert backend.available_for({"minizinc_path": spelled + "-other"}) is False
        assert backend.available_for({"minizinc_path": full + "-other"}) is False

    def test_a_real_minizinc_named_without_its_extension_answers(self, nothing_discoverable, monkeypatch):
        """Live, Windows only. ``∀x ∀y (x = y)`` is not valid: the universe ``{0, 1}`` with
        ``x ↦ 0`` and ``y ↦ 1`` falsifies it, so a size-2 search finds a countermodel."""
        real = _REAL_MINIZINC
        if not ON_WINDOWS or not real or not real.lower().endswith(".exe"):
            pytest.skip("needs a MiniZinc .exe on Windows")
        goal = api.parse_any("∀x ∀y (x = y)").formula
        verdict = api.prove(goal, [], backends=["minizinc"], minizinc_path=real[:-4],
                            max_size=2, timeout=60000)
        assert verdict.status == "refuted"


# ---------------------------------------------------------------------------
# Vampire and Prover9
# ---------------------------------------------------------------------------

BACKENDS = [
    pytest.param(VampireBackend, "vampire_path", "UFK_VAMPIRE", id="vampire"),
    pytest.param(Prover9Backend, "prover9_path", "UFK_PROVER9", id="prover9"),
]


@pytest.mark.parametrize("backend_class, option, variable", BACKENDS)
class TestNativeBinaryOption:
    def test_an_existing_path_is_available(self, nothing_discoverable, installed, backend_class,
                                           option, variable):
        full, _spelled = installed
        backend = backend_class()
        assert backend.available() is False                             # nothing is discoverable
        assert backend.available_for({option: full, "use_wsl": False}) is True

    @pytest.mark.skipif(not ON_WINDOWS, reason="the .exe is added by the Windows process loader")
    def test_the_extensionless_spelling_is_available(self, nothing_discoverable, installed,
                                                     backend_class, option, variable):
        _full, spelled = installed
        assert backend_class().available_for({option: spelled, "use_wsl": False}) is True

    def test_a_missing_path_is_refused(self, nothing_discoverable, tmp_path, backend_class, option,
                                       variable):
        backend = backend_class()
        assert backend.available_for({option: str(tmp_path / "missing"), "use_wsl": False}) is False
        assert backend.available_for({option: str(tmp_path), "use_wsl": False}) is False   # a directory
        assert backend.available_for({option: "no-such-command-on-path", "use_wsl": False}) is False

    def test_a_missing_path_is_refused_even_where_discovery_says_yes(
            self, nothing_discoverable, tmp_path, monkeypatch, backend_class, option, variable):
        monkeypatch.setenv(variable, "/the/installation/the/user/pointed/at")
        backend = backend_class()
        assert backend.available_for({"use_wsl": False}) is True       # the variable is taken as it is
        assert backend.available_for({option: str(tmp_path / "missing"), "use_wsl": False}) is False

    def test_a_command_on_path_is_available(self, nothing_discoverable, installed, monkeypatch,
                                            backend_class, option, variable):
        full, _spelled = installed
        name = os.path.basename(full)
        monkeypatch.setenv("PATH", os.path.dirname(full) + os.pathsep + os.environ.get("PATH", ""))
        assert backend_class().available_for({option: name, "use_wsl": False}) is True

    def test_with_wsl_the_path_is_asked_inside_wsl(self, nothing_discoverable, tmp_path, monkeypatch,
                                                   backend_class, option, variable):
        asked = []
        monkeypatch.setattr(protocol, "_wsl_has_binary", lambda binary: asked.append(binary) or True)
        inside = "/mnt/d/some/where/in/wsl"                            # no such file on this host
        assert backend_class().available_for({option: inside, "use_wsl": True}) is True
        assert asked == [inside]

    def test_the_gate_stops_the_missing_path_and_lets_the_named_one_through(
            self, nothing_discoverable, installed, tmp_path, monkeypatch, backend_class, option, variable):
        full, _spelled = installed
        calls = _recording_decide(monkeypatch, backend_class)
        name = backend_class.name
        run_backend(name, GOAL, [], **{option: full, "use_wsl": False})
        assert calls == [{option: full, "use_wsl": False}]
        missing = str(tmp_path / "missing")
        with pytest.raises(BackendUnavailable, match=name):
            run_backend(name, GOAL, [], **{option: missing, "use_wsl": False})
        with pytest.raises(BackendUnavailable, match=name):
            api.prove(GOAL, [], backends=[name], **{option: missing, "use_wsl": False})
        assert len(calls) == 1
