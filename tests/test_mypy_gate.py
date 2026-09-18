"""Tests for :mod:`tools.mypy_ratchet` — the per-file mypy error-count
ratchet behind the CI ``typecheck`` job (see ``.github/workflows/tests.yml``
and ``tools/mypy_ratchet.py``'s module docstring for the full rationale).

Most of what is tested here is pure Python (string parsing, dict diffing,
JSON round-tripping) exercised against hand-written *synthetic* mypy-style
text, never against a real mypy run over ``unicode_fol_kit`` — the ratchet
must never run mypy over the whole package inside the fast suite (a full
pass is a several-second, environment-dependent subprocess, exactly what the
dedicated CI ``typecheck`` job is for). These logic tests need no mypy
installation at all, so they are NOT skip-gated: they are what actually
protects the ratchet script itself from bugs, including in an environment
that lacks mypy.

The one exception is :func:`test_real_mypy_end_to_end`, which shells out to
a REAL mypy against a tiny two-file scratch package (never the kit itself)
as the independent oracle the spec asks for — proving the wiring (subprocess
invocation → text parsing → regression comparison) actually works against
mypy's real output, not just against strings this file made up. That one
test is skip-gated with ``pytest.importorskip("mypy")``, matching the
project's convention for an optional external tool (see e.g.
``test_clingo_backend.py``).
"""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

# tools/ is dev tooling, not part of the installed unicode_fol_kit package,
# so it is loaded directly by file path rather than relying on `tools` being
# importable (which depends on how/where pytest was invoked from).
_MODULE_PATH = Path(__file__).resolve().parent.parent / "tools" / "mypy_ratchet.py"
_spec = importlib.util.spec_from_file_location("mypy_ratchet", _MODULE_PATH)
assert _spec is not None and _spec.loader is not None
mr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mr)


# --------------------------------------------------------------------------- #
# parse_mypy_output: counting `error:` lines per file, on hand-written text.
# --------------------------------------------------------------------------- #

def test_parse_counts_only_error_severity_per_file():
    # Hand-constructed: 2 errors in a.py, 1 in b.py, plus a `note:` line (mypy
    # attaches these to a neighbouring error — e.g. its own
    # "consider using --check-untyped-defs" hint) and a `warning:` line,
    # neither of which is a finding a regression can add or remove. Expected
    # counts below are simply "how many `error:` lines I wrote", not derived
    # by running the function under test on different input.
    output = (
        'unicode_fol_kit/a.py:10: error: Incompatible types  [assignment]\n'
        'unicode_fol_kit/a.py:12: note: consider using --check-untyped-defs  [annotation-unchecked]\n'
        'unicode_fol_kit/a.py:20: error: "Node" has no attribute "x"  [attr-defined]\n'
        'unicode_fol_kit/b.py:5: error: Argument 1 has incompatible type  [arg-type]\n'
        'unicode_fol_kit/b.py:5: note: See https://example.invalid  [note]\n'
        'unicode_fol_kit/c.py:1: warning: unused "type: ignore" comment  [unused-ignore]\n'
        'Found 3 errors in 2 files (checked 3 source files)\n'
    )
    counts = mr.parse_mypy_output(output)
    assert counts == {
        "unicode_fol_kit/a.py": 2,
        "unicode_fol_kit/b.py": 1,
    }
    # A file with only a warning, and the trailing summary line, never
    # produce entries — confirms the summary line isn't misparsed as a
    # diagnostic (it has no `: error|warning|note: ` field at all).
    assert "unicode_fol_kit/c.py" not in counts


def test_parse_clean_output_is_empty():
    assert mr.parse_mypy_output("Success: no issues found in 213 source files\n") == {}
    assert mr.parse_mypy_output("") == {}


def test_parse_normalises_windows_paths_to_forward_slashes():
    # mypy on Windows prints native backslash-separated paths; the baseline
    # must compare equal regardless of which OS generated it (Windows dev
    # box vs. Linux CI), so parsing normalises unconditionally.
    output = r'unicode_fol_kit\mcp\server.py:951: error: bad literal  [arg-type]' + "\n"
    counts = mr.parse_mypy_output(output)
    assert counts == {"unicode_fol_kit/mcp/server.py": 1}
    assert not any("\\" in f for f in counts)


# --------------------------------------------------------------------------- #
# compute_regressions: the four scenarios the spec names, plus a new file.
# --------------------------------------------------------------------------- #

def test_new_error_in_tracked_file_fails():
    baseline = {"unicode_fol_kit/a.py": 1}
    current = {"unicode_fol_kit/a.py": 2}
    regressions = mr.compute_regressions(baseline, current)
    assert regressions == [("unicode_fol_kit/a.py", 1, 2)]


def test_fixed_error_passes():
    baseline = {"unicode_fol_kit/a.py": 2}
    current = {"unicode_fol_kit/a.py": 1}
    assert mr.compute_regressions(baseline, current) == []


def test_unchanged_count_passes():
    baseline = {"unicode_fol_kit/a.py": 2}
    current = {"unicode_fol_kit/a.py": 2}
    assert mr.compute_regressions(baseline, current) == []


def test_file_removed_or_fixed_to_zero_is_handled_not_a_crash():
    # a.py is in the baseline but mypy no longer reports it at all — either
    # because it was deleted, or because every error in it was fixed. Either
    # way there is nothing in `current` to compare it against, so it is
    # silently skipped: not a regression, and not an exception.
    baseline = {"unicode_fol_kit/a.py": 5, "unicode_fol_kit/b.py": 1}
    current = {"unicode_fol_kit/b.py": 1}
    assert mr.compute_regressions(baseline, current) == []


def test_file_renamed_is_handled_as_a_new_file_not_a_crash():
    # a.py (5 errors in the baseline) is renamed to a2.py, carrying its
    # errors with it unchanged. a2.py has no baseline entry, so it is
    # judged like any brand-new file: against an implicit ceiling of zero.
    # This is deliberate (a path-keyed baseline cannot know "a2.py is a.py
    # renamed" without guessing) and, per the module docstring, exactly what
    # "handled" means here — a deterministic result, never an exception —
    # not that a rename is silently exempted from the gate.
    baseline = {"unicode_fol_kit/a.py": 5}
    current = {"unicode_fol_kit/a2.py": 5}
    regressions = mr.compute_regressions(baseline, current)
    assert regressions == [("unicode_fol_kit/a2.py", 0, 5)]


def test_new_file_with_errors_fails_against_implicit_zero_baseline():
    baseline: dict = {}
    current = {"unicode_fol_kit/new_module.py": 3}
    assert mr.compute_regressions(baseline, current) == [
        ("unicode_fol_kit/new_module.py", 0, 3)
    ]


def test_multiple_regressions_are_all_reported_sorted_by_path():
    baseline = {"unicode_fol_kit/z.py": 1, "unicode_fol_kit/a.py": 1}
    current = {"unicode_fol_kit/z.py": 2, "unicode_fol_kit/a.py": 4}
    assert mr.compute_regressions(baseline, current) == [
        ("unicode_fol_kit/a.py", 1, 4),
        ("unicode_fol_kit/z.py", 1, 2),
    ]


# --------------------------------------------------------------------------- #
# Baseline JSON round-trip.
# --------------------------------------------------------------------------- #

def test_save_then_load_baseline_round_trips(tmp_path):
    path = tmp_path / "mypy_baseline.json"
    counts = {"unicode_fol_kit/b.py": 2, "unicode_fol_kit/a.py": 5}
    mr.save_baseline(path, counts, "mypy 2.3.1 (compiled: yes)")

    loaded = mr.load_baseline(path)
    assert loaded == counts

    # counts are written sorted by path, for a stable, reviewable diff.
    raw = json.loads(path.read_text(encoding="utf-8"))
    assert list(raw["counts"].keys()) == ["unicode_fol_kit/a.py", "unicode_fol_kit/b.py"]
    assert raw["mypy_version"] == "mypy 2.3.1 (compiled: yes)"


def test_load_missing_baseline_is_empty(tmp_path):
    assert mr.load_baseline(tmp_path / "does_not_exist.json") == {}


# --------------------------------------------------------------------------- #
# A blocking mypy failure (exit code outside {0, 1}) must never be read as
# "zero errors" — see MypyRunFailed's docstring. Exercised by faking the
# subprocess call, so no real mypy (or real crash) is needed to prove it.
# --------------------------------------------------------------------------- #

class _FakeCompletedProcess:
    def __init__(self, returncode, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def test_non_1_exit_code_raises_instead_of_reporting_zero_errors(monkeypatch):
    def fake_run(*args, **kwargs):
        return _FakeCompletedProcess(
            returncode=2, stdout="", stderr="mypy: INTERNAL ERROR"
        )

    monkeypatch.setattr(mr.subprocess, "run", fake_run)
    with pytest.raises(mr.MypyRunFailed):
        mr.run_mypy(command=("mypy",))


def test_exit_0_and_1_both_parse_normally(monkeypatch):
    # exit 0 (clean) and exit 1 (errors found) are mypy's two NORMAL,
    # complete-run outcomes — neither should raise.
    for code, stdout in (
        (0, "Success: no issues found in 1 source file\n"),
        (1, "unicode_fol_kit/a.py:1: error: bad  [misc]\nFound 1 error in 1 file\n"),
    ):
        monkeypatch.setattr(
            mr.subprocess, "run",
            lambda *a, returncode=code, stdout=stdout, **k: _FakeCompletedProcess(
                returncode=returncode, stdout=stdout
            ),
        )
        counts, raw = mr.run_mypy(command=("mypy",))
        assert raw == stdout
        assert counts == ({} if code == 0 else {"unicode_fol_kit/a.py": 1})


# --------------------------------------------------------------------------- #
# CLI wiring (main()): argument parsing and exit codes, with a stubbed
# run_mypy so this never shells out to a real mypy run over the kit.
# --------------------------------------------------------------------------- #

def test_main_update_writes_baseline_and_exits_0(tmp_path, monkeypatch, capsys):
    baseline_path = tmp_path / "mypy_baseline.json"
    monkeypatch.setattr(
        mr, "run_mypy", lambda: ({"unicode_fol_kit/a.py": 2}, "")
    )
    monkeypatch.setattr(mr, "get_mypy_version", lambda: "mypy 2.3.1 (fake)")

    exit_code = mr.main(["--update", "--baseline", str(baseline_path)])

    assert exit_code == 0
    assert mr.load_baseline(baseline_path) == {"unicode_fol_kit/a.py": 2}
    out = capsys.readouterr().out
    assert "updated" in out


def test_main_gate_fails_on_regression(tmp_path, monkeypatch):
    baseline_path = tmp_path / "mypy_baseline.json"
    mr.save_baseline(baseline_path, {"unicode_fol_kit/a.py": 1}, "mypy (fake)")
    monkeypatch.setattr(
        mr, "run_mypy", lambda: ({"unicode_fol_kit/a.py": 2}, "")
    )

    exit_code = mr.main(["--baseline", str(baseline_path)])
    assert exit_code == 1


def test_main_gate_passes_without_regression(tmp_path, monkeypatch):
    baseline_path = tmp_path / "mypy_baseline.json"
    mr.save_baseline(baseline_path, {"unicode_fol_kit/a.py": 2}, "mypy (fake)")
    monkeypatch.setattr(
        mr, "run_mypy", lambda: ({"unicode_fol_kit/a.py": 1}, "")
    )

    exit_code = mr.main(["--baseline", str(baseline_path)])
    assert exit_code == 0


def test_main_gate_missing_baseline_treats_every_file_as_new(tmp_path, monkeypatch):
    # No baseline file at all (e.g. a fresh checkout before the first
    # --update) behaves exactly like an empty baseline: everything current
    # mypy reports is "new" and fails, rather than crashing on a missing file.
    baseline_path = tmp_path / "does_not_exist.json"
    monkeypatch.setattr(
        mr, "run_mypy", lambda: ({"unicode_fol_kit/a.py": 1}, "")
    )
    exit_code = mr.main(["--baseline", str(baseline_path)])
    assert exit_code == 1


# --------------------------------------------------------------------------- #
# Independent oracle: a REAL mypy run over a tiny synthetic scratch package
# (never unicode_fol_kit itself), proving the actual subprocess + parsing
# pipeline works against mypy's real output. Skipped when mypy is absent.
# --------------------------------------------------------------------------- #

def test_real_mypy_end_to_end(tmp_path):
    pytest.importorskip("mypy")

    # clean.py: no error — textbook-correct, fully annotated.
    (tmp_path / "clean.py").write_text(
        "def add(a: int, b: int) -> int:\n    return a + b\n",
        encoding="utf-8",
    )
    # broken.py: a deliberate, hand-verified type error — returning a str
    # where the signature promises int is wrong under any type system,
    # nothing subtle to second-guess.
    (tmp_path / "broken.py").write_text(
        'def f() -> int:\n    return "not an int"\n',
        encoding="utf-8",
    )

    command = (
        sys.executable, "-m", "mypy",
        "--no-site-packages", "--ignore-missing-imports",
        "clean.py", "broken.py",
    )
    result = mr.subprocess.run(
        list(command), cwd=str(tmp_path), capture_output=True, text=True,
    )
    assert result.returncode == 1, result.stdout + result.stderr

    counts = mr.parse_mypy_output(result.stdout)
    assert counts == {"broken.py": 1}
    assert "clean.py" not in counts

    # Full pipeline: gate red against a baseline that has never seen
    # broken.py, green once the baseline records exactly the one error it
    # has (the "unchanged" case, differentially confirmed against real mypy
    # output rather than a hand-written fixture this time).
    assert mr.compute_regressions({}, counts) == [("broken.py", 0, 1)]
    assert mr.compute_regressions({"broken.py": 1}, counts) == []
