"""E and Zipperposition as external TPTP backends (one shared runner).

Both provers speak the same protocol this kit already reads for Vampire:
TPTP ``fof`` in, ``SZS status`` + (for E) a TSTP derivation out — so they
share one runner here instead of duplicating the temp-file/WSL plumbing a
third and fourth time. (Vampire keeps its own module,
:mod:`~unicode_fol_kit.atp.vampire_entailment`, because its original
bool-returning route is public API.)

Why these two (roadmap ranking): E is the classic high-diversity
superposition prover — cheap to obtain (Ubuntu 24.04 ships ``eprover``
3.0.03 in universe, so CI gets LIVE coverage from ``apt``), strong on
problems Z3's instantiation heuristics miss. Zipperposition adds a second,
OCaml-built superposition engine with higher-order ambitions.

Per-backend acquisition path (the kit-wide honesty rule: every external
backend documents how to get it, per platform):

* **E** — ``apt install eprover`` (Debian/Ubuntu; WSL: note that Ubuntu
  22.04 does NOT carry the package — 24.04 does), or build from source
  (https://github.com/eprover/eprover, ``./configure && make``). Windows:
  via WSL. Env override: ``$UFK_EPROVER_CMD`` (prefix ``wsl:`` to force the
  WSL route, e.g. ``wsl:/usr/bin/eprover``).
* **Zipperposition** — ``opam install zipperposition`` (no Debian/Ubuntu
  package exists as of 2026-08); realistically an opam-capable Linux/WSL
  box only. Env override: ``$UFK_ZIPPERPOSITION_CMD`` (same ``wsl:``
  convention). Where it is absent the backend reports unavailable — tests
  gate on that and skip, they never fake a pass.

Discovery order (each backend, cached per process): env override → native
binary on PATH → the same name inside WSL (``wsl.exe which <name>``).

Verdicts: the SZS status line is authoritative (``extract_szs_status`` —
E prints ``# SZS status …`` with a hash marker, Zipperposition ``% SZS
status …``; the extractor accepts both), mapped through
``szs_to_verdict_fields(query="conjecture")`` exactly like the Vampire
detailed route. E is additionally asked for ``--proof-object``, and a
parseable TSTP derivation lands in ``Verdict.proof``; an unparseable one
degrades to ``proof=None`` with the parse error in ``detail`` (the status
line alone already carries the verdict — a broken proof printer must not
turn a Theorem into an error, but the degradation is never silent).
"""

import os
import shutil
import subprocess
import tempfile
import time
from typing import List, Optional, Sequence, Tuple

from ..fol.nodes import Node
from ._ascii_names import reverse_map_text
from ._tptp_problem import generate_tptp_problem, generate_tptp_problem_with_mapping
from .protocol import ProverBackend, Verdict, UNKNOWN, ERROR

__all__ = ["EProverBackend", "ZipperpositionBackend",
           "check_entailment_eprover_detailed", "eprover_available",
           "zipperposition_available"]


def _generate_tptp_problem(premises: List[Node], conclusion: Node) -> str:
    """``fof(premise_<i>, axiom, …).`` lines + one ``fof(goal, conjecture, …).``

    Same shape as the Vampire route (both are thin wrappers over the shared
    :func:`atp._tptp_problem.generate_tptp_problem`); bodies come from
    ``Node.to_tptp`` and its ``NotImplementedError`` for untranslatable
    nodes — OR the shared cross-formula symbol-collision guard, see
    ``_tptp_problem``'s module docstring — propagates; the backends below
    turn that into an UNKNOWN/"unsupported" verdict.
    """
    return generate_tptp_problem(premises, conclusion)


def _to_wsl_path(windows_path: str) -> str:
    """Windows path → ``/mnt/...`` via ``wslpath`` (see vampire_entailment)."""
    result = subprocess.run(
        ["wsl.exe", "wslpath", "-u", windows_path.replace("\\", "/")],
        capture_output=True, text=True, timeout=20)
    wsl_path = result.stdout.strip()
    if not wsl_path:
        raise RuntimeError(
            f"wslpath could not translate {windows_path!r} (is WSL "
            f"available?): {result.stderr.strip()}")
    return wsl_path


# (command, use_wsl) per prover name, or None when nothing was found.
# Cached because discovery may spawn a WSL probe process.
_DISCOVERY_CACHE: dict = {}


def _discover(name: str, env_var: str) -> Optional[Tuple[str, bool]]:
    """Resolve prover ``name`` to ``(command, use_wsl)``, or ``None``.

    Order: ``$<env_var>`` (a ``wsl:`` prefix forces the WSL route) → native
    ``shutil.which`` → ``wsl.exe which <name>``. The env override is read
    FRESH on every call and never cached — that is what makes "set the env
    var to repoint" true even after an earlier miss was cached
    (review-confirmed: caching before the env read froze a process's first
    discovery forever). Only the binary probes (PATH/WSL) are cached.
    """
    override = os.environ.get(env_var)
    if override:
        if override.startswith("wsl:"):
            return (override[4:], True)
        return (override, False)

    key = (name, env_var)
    if key in _DISCOVERY_CACHE:
        return _DISCOVERY_CACHE[key]

    resolved: Optional[Tuple[str, bool]] = None
    if shutil.which(name):
        resolved = (name, False)
    else:
        try:
            probe = subprocess.run(["wsl.exe", "which", name],
                                   capture_output=True, text=True, timeout=20)
            path = probe.stdout.strip()
            if probe.returncode == 0 and path:
                resolved = (path, True)
        except (OSError, subprocess.TimeoutExpired):
            resolved = None

    _DISCOVERY_CACHE[key] = resolved
    return resolved


def eprover_available() -> bool:
    """Pure discovery: is an ``eprover`` binary reachable (native or WSL)?"""
    return _discover("eprover", "UFK_EPROVER_CMD") is not None


def zipperposition_available() -> bool:
    """Pure discovery for ``zipperposition`` (see the module docstring)."""
    return _discover("zipperposition", "UFK_ZIPPERPOSITION_CMD") is not None


def _run_tptp_prover(problem: str, command: str, args: Sequence[str],
                     use_wsl: bool, timeout_s: float) -> Tuple[str, bool]:
    """Write ``problem`` to a temp ``.p`` file and run the prover on it.

    Returns ``(stdout+stderr, timed_out)``; the temp file is always removed.
    Mirrors ``vampire_entailment._spawn_vampire`` (stderr is folded in here
    because E writes some diagnostics there).
    """
    with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(problem)
        path = tmp.name
    try:
        if use_wsl:
            cmd = ["wsl.exe", command, *args, _to_wsl_path(path)]
        else:
            cmd = [command, *args, path]
        result = subprocess.run(cmd, capture_output=True, text=True,
                                timeout=timeout_s)
        return (result.stdout or "") + (result.stderr or ""), False
    except subprocess.TimeoutExpired:
        return "", True
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def check_entailment_eprover_detailed(premises: List[Node], conclusion: Node,
                                      *, timeout: int = 30,
                                      command: Optional[str] = None,
                                      use_wsl: bool = False) -> dict:
    """Run E on ``premises ⊨ conclusion``; SZS-status + TSTP-derivation dict.

    Same result contract as ``check_entailment_vampire_detailed``:
    ``{"status", "reason", "szs_status", "derivation", "raw"}``. With
    ``command=None`` discovery runs (env → PATH → WSL) and a miss raises
    ``RuntimeError`` — use :func:`eprover_available` to probe first.

    Every symbol name in ``raw`` and in ``derivation``'s formulas has
    already been translated back from whatever ASCII-safe token
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping` may have
    substituted (a non-ASCII or digit-leading kit-level name) to the
    ORIGINAL kit-level name — see that function's module docstring. A name
    E introduced itself (a clausification symbol, e.g. ``c_0_7``) was never
    one of ours and is left as E printed it.

    Raises:
        NotImplementedError: a formula is outside the classical FOL fragment
            ``Node.to_tptp`` covers, or two distinct predicate (or
            function/constant) names would fold to the same TPTP identifier
            (see :mod:`atp._tptp_problem`'s module docstring) — surfaced by
            :func:`_generate_tptp_problem` before any subprocess is spawned;
            unlike :class:`_TptpSzsBackend.decide`, this function does NOT
            catch it into an UNKNOWN verdict.
        RuntimeError: no ``eprover`` binary found (see above).
    """
    from .tstp import (extract_szs_status, parse_tstp_derivation,
                       reverse_map_derivation, szs_to_verdict_fields)

    if command is None:
        found = _discover("eprover", "UFK_EPROVER_CMD")
        if found is None:
            raise RuntimeError(
                "eprover: no binary found (PATH, WSL, $UFK_EPROVER_CMD) — "
                "apt install eprover (Ubuntu 24.04+/Debian) or build from "
                "https://github.com/eprover/eprover")
        command, use_wsl = found

    problem, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    pred_rev, term_rev = name_map.reverse_rendered()
    args = ["--auto", "--tstp-format", "--proof-object", "-s",
            f"--cpu-limit={max(1, timeout)}"]
    # Wall clock outlasts E's own cpu budget so E reports ResourceOut itself.
    raw_output, timed_out = _run_tptp_prover(problem, command, args, use_wsl,
                                             timeout_s=timeout + 10)
    output = reverse_map_text(raw_output, pred_rev, term_rev)
    if timed_out:
        return {"status": UNKNOWN, "reason": "timeout", "szs_status": None,
                "derivation": None, "raw": output}

    szs = extract_szs_status(raw_output)
    if szs is None:
        return {"status": ERROR, "reason": "infra", "szs_status": None,
                "derivation": None, "raw": output}
    status, reason = szs_to_verdict_fields(szs, query="conjecture")
    derivation = None
    if status == "proved":
        try:
            derivation = reverse_map_derivation(
                parse_tstp_derivation(raw_output), name_map).to_dict()
        except ValueError:
            derivation = None      # never silent: backends put this in detail
    return {"status": status, "reason": reason, "szs_status": szs,
            "derivation": derivation, "raw": output}


class _TptpSzsBackend(ProverBackend):
    """Shared decide() skeleton for the two SZS-speaking TPTP provers."""

    logics = frozenset({"fol"})
    external = True

    _env_var: str = ""
    _binary: str = ""

    def _args(self, timeout_s: int) -> List[str]:      # pragma: no cover
        raise NotImplementedError

    def available(self) -> bool:
        return _discover(self._binary, self._env_var) is not None

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .tstp import (extract_szs_status, parse_tstp_derivation,
                           reverse_map_derivation, szs_to_verdict_fields)

        found = _discover(self._binary, self._env_var)
        if found is None:
            from .protocol import BackendUnavailable
            raise BackendUnavailable(
                f"{self.name}: no binary found — see "
                "unicode_fol_kit/atp/eprover_backend.py for the per-platform "
                f"acquisition paths, or set ${self._env_var}.")
        command, use_wsl = found

        try:
            problem, name_map = generate_tptp_problem_with_mapping(list(premises), formula)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           detail=str(exc))
        pred_rev, term_rev = name_map.reverse_rendered()

        timeout_s = max(1, timeout // 1000)
        start = time.perf_counter()
        try:
            raw_output, timed_out = _run_tptp_prover(
                problem, command, self._args(timeout_s), use_wsl,
                timeout_s=timeout_s + 10)
        except (OSError, RuntimeError) as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           detail=f"{type(exc).__name__}: {exc}")
        elapsed = time.perf_counter() - start

        if timed_out:
            return Verdict(UNKNOWN, self.name, reason="timeout",
                           wall_time=elapsed)
        szs = extract_szs_status(raw_output)
        if szs is None:
            return Verdict(ERROR, self.name, reason="infra",
                           wall_time=elapsed,
                           detail="no SZS status line in output: "
                                  + reverse_map_text(raw_output.strip()[-200:], pred_rev, term_rev))
        status, reason = szs_to_verdict_fields(szs, query="conjecture")
        proof = None
        detail = f"SZS status {szs}"
        if status == "proved":
            try:
                parsed = reverse_map_derivation(parse_tstp_derivation(raw_output), name_map)
                # A status line without TSTP steps (Zipperposition's default
                # output) is a verdict without a certificate — proof stays
                # None and the detail says so, the Theorem status stands.
                proof = parsed.to_dict() if parsed.steps else None
                if proof is None:
                    detail += "; no TSTP derivation in output"
            except ValueError as exc:
                detail += f"; TSTP derivation unparseable: {exc}"
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed, proof=proof, detail=detail)


class EProverBackend(_TptpSzsBackend):
    """E (superposition, https://eprover.org) — registry name ``"eprover"``."""

    name = "eprover"
    _env_var = "UFK_EPROVER_CMD"
    _binary = "eprover"

    def _args(self, timeout_s: int) -> List[str]:
        return ["--auto", "--tstp-format", "--proof-object", "-s",
                f"--cpu-limit={timeout_s}"]


class ZipperpositionBackend(_TptpSzsBackend):
    """Zipperposition (OCaml superposition) — registry name ``"zipperposition"``."""

    name = "zipperposition"
    _env_var = "UFK_ZIPPERPOSITION_CMD"
    _binary = "zipperposition"

    def _args(self, timeout_s: int) -> List[str]:
        return ["--timeout", str(timeout_s)]
