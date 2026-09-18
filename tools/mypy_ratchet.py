r"""Ratchet a per-file mypy error-count baseline for ``unicode_fol_kit``.

The package has never been under a type-check gate (no ``mypy``/``ruff``
config existed anywhere in the repo before this file), and a first real
``mypy`` pass surfaces several hundred pre-existing errors spread across most
of the thirteen subpackages — turning that straight into a hard ``mypy
unicode_fol_kit`` CI gate would just redden every PR from day one, including
ones that touch none of the offending code. This module is the gate instead:
it runs mypy, counts errors **per file**, and compares that against a
committed baseline (``tools/mypy_baseline.json``). A file's count is allowed
to *stay the same or drop*; it is a regression only when a file's count
*rises above* what the baseline already tolerates for it. New files start at
an implicit baseline of zero, so a freshly added module with type errors is
still caught. This is a ratchet, not a cleanup: it guarantees no *new*
regression lands, not that the pre-existing errors go away — shrinking them
module by module is separate, follow-up work.

Why per-file counts and not exact error fingerprints: line numbers shift
under any unrelated edit above an error (a docstring line added, an import
reordered), which would make a fingerprint keyed on line number flag
"regressions" that are really just the same pre-existing error moved down a
line. A plain per-file ceiling is immune to that churn while still catching
what actually matters here: a file that used to have N mypy errors now having
more than N.

Why mypy is run with ``--no-site-packages`` (see the ``[tool.mypy]`` table in
``pyproject.toml``): the ``rdkit`` release this project's ``chem`` extra
pins against ships PEP 561 stub files (the bundled ``rdkit-stubs``
distribution) that contain outright syntax errors in their generated
``.pyi`` sources (observed: a duplicated, misordered parameter list in
``Chem/rdmolfiles.pyi`` under rdkit 2026.3.5). A syntax error inside a
*followed* stub file is a **blocking** mypy error — it is not something
``ignore_errors`` or ``follow_imports = "skip"`` on that module can silence
(verified empirically: neither suppresses it), and it aborts the whole run
with exit code 2 before every file is even reached. Disabling PEP 561
site-packages discovery sidesteps the broken third-party stub entirely;
every third-party import then falls back to ``Any`` under
``ignore_missing_imports`` instead of being consulted for precise type
info. That is a real, load-bearing trade-off (this codebase's own code is
checked exactly as strictly either way; only the *fidelity of third-party
call signatures* is reduced) — not a silent loosening of the gate over our
own code, which is what this file's ratchet is protecting.

Usage
-----
Check for regressions (what CI runs)::

    python tools/mypy_ratchet.py

Regenerate the baseline — after fixing errors, after intentionally
accepting new ones (e.g. a freshly added module), or after some other change
shifts the counts::

    python tools/mypy_ratchet.py --update

Both invocations run the exact same mypy command (see ``MYPY_COMMAND``
below), from the repository root, under whichever ``[tool.mypy]`` section
``pyproject.toml`` carries (mypy auto-discovers it; nothing here hard-codes
a ``--config-file``) — "the check CI runs" and "the check you run locally"
are the same command by construction.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE_PATH = REPO_ROOT / "tools" / "mypy_baseline.json"

# The one command both this script and .github/workflows/tests.yml run —
# keep them in lockstep by construction rather than by two hand-copied
# strings that can drift apart.
MYPY_COMMAND: Tuple[str, ...] = (sys.executable, "-m", "mypy", "unicode_fol_kit")

# mypy's default text-output diagnostic line, e.g.:
#   unicode_fol_kit/mcp/server.py:709: error: Need type annotation for "used"  [var-annotated]
# `.+` is greedy, so it matches up to the LAST `:<digits>: <severity>: ` —
# safe even if a (relative, as invoked here) file path contained a colon.
_DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.+):(?P<line>\d+): (?P<severity>error|warning|note): (?P<message>.*)$"
)


class MypyRunFailed(RuntimeError):
    """mypy did not complete a normal check (exit code outside ``{0, 1}``).

    0 means a clean run and 1 means "errors found" — both are a complete,
    trustworthy pass over every file. Any other exit code (mypy uses 2 for a
    crash, a bad invocation, or a blocking parse error — including the
    third-party stub bug described in this module's docstring, if the
    ``no_site_packages`` workaround is ever missing from the config) means
    mypy may have aborted *before checking every file*. Reading an error
    count off a truncated run would silently under-report, so this is
    raised instead of ever being treated as "zero errors" or partial
    results.
    """


def parse_mypy_output(output: str) -> Dict[str, int]:
    """Count ``error:``-severity diagnostics per file.

    ``note:`` lines (e.g. the "By default the bodies of untyped functions
    are not checked" hint mypy attaches next to a real error, or a bare
    explanatory note) and ``warning:`` lines are not counted: only
    ``error:`` diagnostics are findings a regression can add or remove.
    File paths are normalised to forward slashes so the same baseline file
    compares equal whether it was generated on the Windows dev box or in
    Linux CI.
    """
    counts: Dict[str, int] = {}
    for line in output.splitlines():
        match = _DIAGNOSTIC_RE.match(line)
        if match is None or match.group("severity") != "error":
            continue
        file_path = match.group("file").replace("\\", "/")
        counts[file_path] = counts.get(file_path, 0) + 1
    return counts


def run_mypy(command: Sequence[str] = MYPY_COMMAND) -> Tuple[Dict[str, int], str]:
    """Run mypy and return ``(per-file error counts, raw stdout)``.

    Raises :class:`MypyRunFailed` if mypy's exit code is not 0 or 1 — see
    that class's docstring for why this is never downgraded to a warning.
    """
    result = subprocess.run(
        list(command), cwd=REPO_ROOT, capture_output=True, text=True,
    )
    if result.returncode not in (0, 1):
        raise MypyRunFailed(
            f"`{' '.join(command)}` exited {result.returncode} (expected 0 or 1). "
            "This is a crash or an unhandled blocking error, not a set of "
            "type-check findings — see MypyRunFailed's docstring.\n"
            f"--- stdout ---\n{result.stdout}\n--- stderr ---\n{result.stderr}"
        )
    return parse_mypy_output(result.stdout), result.stdout


def load_baseline(path: Path) -> Dict[str, int]:
    """Read the committed per-file ceilings. Missing file reads as empty
    (every file starts at an implicit ceiling of zero)."""
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    return {str(k): int(v) for k, v in data.get("counts", {}).items()}


def save_baseline(path: Path, counts: Dict[str, int], mypy_version: str) -> None:
    payload = {
        "$comment": (
            "Generated by `python tools/mypy_ratchet.py --update` — do not "
            "hand-edit (see tools/mypy_ratchet.py). Per-file mypy ERROR "
            "counts (notes/warnings excluded). The gate "
            "(tools/mypy_ratchet.py with no flags) fails a file only when "
            "its current error count exceeds the number recorded here."
        ),
        "mypy_version": mypy_version,
        "counts": dict(sorted(counts.items())),
    }
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def compute_regressions(
    baseline: Dict[str, int], current: Dict[str, int]
) -> List[Tuple[str, int, int]]:
    """Files whose CURRENT error count exceeds their BASELINE ceiling.

    A file the baseline lists that is absent from ``current`` — because it
    was fixed down to zero errors, deleted, or renamed — is simply not
    compared: with no current entry there is nothing to check it against,
    so a rename or deletion can never by itself trigger a regression (a
    renamed file that still carries its old errors is judged exactly like
    any other new file would be: against an implicit baseline of zero,
    exactly as intended).
    """
    regressions = []
    for file_path, current_n in sorted(current.items()):
        baseline_n = baseline.get(file_path, 0)
        if current_n > baseline_n:
            regressions.append((file_path, baseline_n, current_n))
    return regressions


def get_mypy_version() -> str:
    """Best-effort ``mypy --version`` string for the baseline's metadata
    (informational only — never gates anything, so a failure here is not
    fatal to ``--update``)."""
    try:
        result = subprocess.run(
            (sys.executable, "-m", "mypy", "--version"),
            cwd=REPO_ROOT, capture_output=True, text=True,
        )
        return result.stdout.strip() or "unknown"
    except OSError:
        return "unknown"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update", action="store_true",
        help="Regenerate the baseline from the current mypy run instead of gating.",
    )
    parser.add_argument(
        "--baseline", type=Path, default=DEFAULT_BASELINE_PATH,
        help="Path to the baseline JSON file (default: tools/mypy_baseline.json).",
    )
    args = parser.parse_args(argv)

    try:
        current, _raw_output = run_mypy()
    except MypyRunFailed as exc:
        print(str(exc), file=sys.stderr)
        return 2

    if args.update:
        save_baseline(args.baseline, current, get_mypy_version())
        total = sum(current.values())
        print(
            f"{args.baseline}: updated — {total} error(s) across "
            f"{len(current)} file(s)."
        )
        return 0

    baseline = load_baseline(args.baseline)
    regressions = compute_regressions(baseline, current)
    if regressions:
        print(
            "mypy ratchet: new type errors beyond the recorded baseline:\n",
            file=sys.stderr,
        )
        for file_path, baseline_n, current_n in regressions:
            print(
                f"  {file_path}: {current_n} error(s) (baseline allows {baseline_n})",
                file=sys.stderr,
            )
        print(
            "\nFix them, or if the new count is genuinely intended, run "
            "`python tools/mypy_ratchet.py --update` and commit the "
            "updated tools/mypy_baseline.json.",
            file=sys.stderr,
        )
        return 1

    total_current = sum(current.values())
    total_baseline = sum(baseline.values())
    stale = sorted(f for f in baseline if f not in current)
    print(
        f"mypy ratchet: no regressions ({total_current} error(s) across "
        f"{len(current)} file(s); baseline allows {total_baseline})."
    )
    if stale:
        print(
            f"  {len(stale)} baseline entry/entries no longer reported by mypy "
            "(fixed, deleted or renamed) — harmless; `--update` would drop them."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
