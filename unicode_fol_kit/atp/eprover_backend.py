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
from ._tff_problem import generate_tff_arith_problem
from ._tptp_problem import generate_tptp_problem, generate_tptp_problem_with_mapping
from .protocol import ProverBackend, Verdict, UNKNOWN, ERROR, _binary_version
from .tptp_tff import generate_tff_problem, problem_needs_tff

__all__ = ["EProverBackend", "ZipperpositionBackend",
           "check_entailment_eprover_detailed", "eprover_available",
           "zipperposition_available", "eprover_relevant_premises"]


def _generate_tptp_problem(premises: List[Node], conclusion: Node,
                           *, tff: Optional[bool] = None,
                           sort: Optional[str] = None) -> str:
    """``fof(premise_<i>, axiom, …).`` lines + one ``fof(goal, conjecture, …).``
    — or, when ``tff``/``sort`` selects a typed route, one of its siblings.

    ``sort`` (``None`` by default) opts into the single-numeric-sort typed
    arithmetic route (:func:`atp._tff_problem.generate_tff_arith_problem`,
    ``'real'`` or ``'int'``) UNCONDITIONALLY when given, taking priority
    over ``tff`` — activates E's/Zipperposition's native arithmetic
    reasoning on `+ - * /` and `< > ≤ ≥`, which the untyped ``fof`` route
    below cannot (see :mod:`atp._tff_problem`'s module docstring). With
    ``sort=None``, ``tff=None`` (the default) auto-selects
    :func:`atp.tptp_tff.generate_tff_problem` when ``premises``/
    ``conclusion`` contain a SortedQuantifier/SortedConstant/SortedCount
    node (see :func:`atp.tptp_tff.problem_needs_tff`); otherwise (or with
    ``tff=False``) this is a thin wrapper over the shared
    :func:`atp._tptp_problem.generate_tptp_problem` (also used by the
    Vampire route, which builds the identical ``fof`` problem shape).
    Every route's own ``NotImplementedError`` (an untranslatable node, or a
    cross-formula symbol-collision — see each module's docstring)
    propagates; the backends below turn that into an UNKNOWN/"unsupported"
    verdict.
    """
    if sort is not None:
        problem, _name_map = generate_tff_arith_problem(premises, conclusion, sort=sort)
        return problem
    use_tff = problem_needs_tff(premises, conclusion) if tff is None else tff
    if use_tff:
        return generate_tff_problem(premises, conclusion)
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
                                      use_wsl: bool = False,
                                      tff: Optional[bool] = None,
                                      sort: Optional[str] = None) -> dict:
    """Run E on ``premises ⊨ conclusion``; SZS-status + TSTP-derivation dict.

    Same result contract as ``check_entailment_vampire_detailed``:
    ``{"status", "reason", "szs_status", "derivation", "raw"}``. With
    ``command=None`` discovery runs (env → PATH → WSL) and a miss raises
    ``RuntimeError`` — use :func:`eprover_available` to probe first. ``tff``/
    ``sort`` select the TPTP dialect — see :func:`_generate_tptp_problem`.
    UNLIKE the ``tff`` route, the ``sort`` route's ``name_map`` is a genuine,
    usable :class:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap` (see
    :mod:`atp._tff_problem`'s module docstring), so ``raw`` below IS
    reverse-mapped to original kit-level names on the ``sort`` route.

    Every symbol name in ``raw`` and in ``derivation``'s formulas has
    already been translated back from whatever ASCII-safe token
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping` may have
    substituted (a non-ASCII or digit-leading kit-level name) to the
    ORIGINAL kit-level name — see that function's module docstring. A name
    E introduced itself (a clausification symbol, e.g. ``c_0_7``) was never
    one of ours and is left as E printed it. EXCEPTION — the ``tff`` route:
    reading a ``tff`` proof back into original kit-level names is an
    explicit non-goal of :mod:`atp.tptp_tff` (see its module docstring), so
    when ``tff`` is used (auto-selected or forced), ``raw`` (and any
    ``derivation``) is left exactly as E printed it, un-reversed. In fact
    ``derivation`` is CURRENTLY ALWAYS ``None`` on the ``tff`` route today,
    even for a genuine proof: :func:`atp.tstp.parse_tstp_derivation` only
    recognises ``fof``/``cnf`` statements (see its own docstring), never
    the ``tff``/``tcf`` ones E prints — a real gap (tff/tcf-proof-line
    reading is follow-up work; :mod:`atp.tstp` is a shared module outside
    this item's ownership), not merely "un-reversed".

    Raises:
        NotImplementedError: a formula is outside the fragment the selected
            route covers, or two distinct predicate (or function/constant,
            or — ``tff`` route — sort) names would fold to the same TPTP
            identifier (see :mod:`atp._tptp_problem`'s and
            :mod:`atp.tptp_tff`'s module docstrings) — surfaced by
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

    if sort is not None:
        problem, name_map = generate_tff_arith_problem(premises, conclusion, sort=sort)
    else:
        use_tff = problem_needs_tff(premises, conclusion) if tff is None else tff
        if use_tff:
            problem, name_map = generate_tff_problem(premises, conclusion), None
        else:
            problem, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    args = ["--auto", "--tstp-format", "--proof-object", "-s",
            f"--cpu-limit={max(1, timeout)}"]
    # Wall clock outlasts E's own cpu budget so E reports ResourceOut itself.
    raw_output, timed_out = _run_tptp_prover(problem, command, args, use_wsl,
                                             timeout_s=timeout + 10)
    if name_map is None:
        output = raw_output
    else:
        pred_rev, term_rev = name_map.reverse_rendered()
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
            parsed = parse_tstp_derivation(raw_output)
            resolved = parsed if name_map is None else reverse_map_derivation(parsed, name_map)
            # Empty steps -> None, matching check_entailment_vampire_detailed's
            # own contract (this function's docstring promises the same one):
            # "no fof/cnf statement recognised" (always true on the tff route
            # today, see docstring) is "no derivation to report", not "here is
            # an empty derivation".
            derivation = resolved.to_dict() if resolved.steps else None
        except ValueError:
            derivation = None      # never silent: backends put this in detail
    return {"status": status, "reason": reason, "szs_status": szs,
            "derivation": derivation, "raw": output}


def eprover_relevant_premises(premises: List[Node], conclusion: Node, *,
                              timeout: int = 30, command: Optional[str] = None,
                              use_wsl: bool = False,
                              tff: Optional[bool] = None,
                              sort: Optional[str] = None) -> Optional[Tuple[int, ...]]:
    """Which of ``premises`` did E's proof of ``premises ⊨ conclusion``
    actually rest on?

    Runs E exactly ONCE, through :func:`check_entailment_eprover_detailed`'s
    own subprocess plumbing (no second prover invocation) — and, only when
    the resulting verdict is PROVED, walks the TSTP derivation backward via
    :func:`atp.tstp.relevant_premises_from_tstp`, which descends into E's
    own nested administrative ``inference(...)`` steps (see that function's
    module comment) down to every reachable ``premise_<i>`` axiom leaf; E
    names those leaves after this module's own
    :func:`~unicode_fol_kit.atp._tptp_problem.generate_tptp_problem`
    convention VERBATIM (verified live), so index recovery is direct.

    Args:
        premises: candidate premises.
        conclusion: the goal.
        timeout: seconds — forwarded to
            :func:`check_entailment_eprover_detailed` unchanged.
        command: an explicit ``eprover`` command/path — see
            :func:`check_entailment_eprover_detailed`; when omitted,
            discovery runs the same way, and a miss is reported as ``None``
            here (NOT raised — unlike ``check_entailment_eprover_detailed``,
            this is a "can you tell me" query, so a missing binary is just
            "no answer available", exactly like an unproved verdict).

    Returns:
        A sorted tuple of 0-based indices into ``premises``, or ``None``
        when: E is not reachable; the verdict is not PROVED (there is no
        "premises used" answer for a non-theorem); or the derivation walk
        itself could not be trusted (see
        :func:`atp.tstp.relevant_premises_from_tstp`'s ``Returns``) — always
        the honest "don't know", never a guessed/under-approximated subset.

    Raises:
        NotImplementedError: a formula is outside the classical FOL fragment
            ``Node.to_tptp`` covers, or a cross-formula symbol-collision —
            same contract as :func:`check_entailment_eprover_detailed`,
            surfaced before any subprocess is spawned.
    """
    from .tstp import relevant_premises_from_tstp

    try:
        result = check_entailment_eprover_detailed(
            premises, conclusion, timeout=timeout, command=command, use_wsl=use_wsl,
            tff=tff, sort=sort)
    except RuntimeError:
        return None      # no eprover binary -- an honest "no answer", not an error
    if result["status"] != "proved":
        return None
    return relevant_premises_from_tstp(result["raw"], len(premises))


class _TptpSzsBackend(ProverBackend):
    """Shared decide() skeleton for the two SZS-speaking TPTP provers."""

    logics = frozenset({"fol", "arith"})
    external = True

    _env_var: str = ""
    _binary: str = ""

    def _args(self, timeout_s: int) -> List[str]:      # pragma: no cover
        raise NotImplementedError

    def available(self) -> bool:
        return _discover(self._binary, self._env_var) is not None

    def solver_version(self) -> Optional[str]:
        """The prover's ``--version`` banner (first line), for whichever
        binary discovery (env override, PATH, WSL — see :func:`_discover`)
        resolves to right now — the same default :meth:`available` uses.
        Memoized per ``(binary, use_wsl)`` for the life of the process via
        :func:`~unicode_fol_kit.atp.protocol._binary_version` (a cache kept
        separate from :data:`_DISCOVERY_CACHE` — see that function's own
        docstring for why). ``None`` when no binary is currently
        discoverable.
        """
        found = _discover(self._binary, self._env_var)
        if found is None:
            return None
        command, use_wsl = found
        return _binary_version(command, use_wsl)

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """``tff``/``sort`` (options forwarded via ``**options``, mirroring
        how other backends read e.g. ``frame=`` — see
        ``ProverBackend.decide``'s own docstring): which TPTP dialect to
        export as. ``sort`` (``None`` by default) opts into the
        single-numeric-sort typed arithmetic route
        (:func:`atp._tff_problem.generate_tff_arith_problem`, ``'real'`` or
        ``'int'``) UNCONDITIONALLY when given, taking priority over ``tff``
        — activates this prover's native arithmetic reasoning, which the
        untyped ``fof``/many-sorted-``tff`` routes cannot (see
        :mod:`atp._tff_problem`'s module docstring). With ``sort=None``,
        ``tff`` selects as before: ``None`` (the default, i.e. omitted)
        auto-selects the native many-sorted typed ``tff`` route whenever
        ``premises``/``formula`` use a sort — see
        :func:`_generate_tptp_problem` — ``True``/``False`` force one route.
        On the many-sorted ``tff`` route, ``proof``/``detail`` are left with
        whatever (sanitised, TPTP-legal) symbol tokens the prover itself
        printed — reading a ``tff`` proof back into original kit-level names
        is an explicit non-goal of :mod:`atp.tptp_tff` (see its module
        docstring). UNLIKE that route, the ``sort`` route's ``name_map`` is
        a genuine mapping (see :mod:`atp._tff_problem`'s module docstring),
        so ``proof``/``detail`` ARE reverse-mapped to original kit-level
        names there.
        """
        from .tstp import (extract_szs_status, parse_tstp_derivation,
                           reverse_map_derivation, szs_to_verdict_fields)

        tff = options.pop("tff", None)
        sort = options.pop("sort", None)

        found = _discover(self._binary, self._env_var)
        if found is None:
            from .protocol import BackendUnavailable
            raise BackendUnavailable(
                f"{self.name}: no binary found — see "
                "unicode_fol_kit/atp/eprover_backend.py for the per-platform "
                f"acquisition paths, or set ${self._env_var}.")
        command, use_wsl = found
        # Memoized (see _binary_version): the first EProverBackend/
        # ZipperpositionBackend decide() call for this (command, use_wsl)
        # pays one subprocess spawn, every later one for the same pair is
        # free — including across the two backend CLASSES, since the cache
        # key is the resolved binary path, not the registry name.
        solver_version = _binary_version(command, use_wsl)

        try:
            if sort is not None:
                problem, name_map = generate_tff_arith_problem(list(premises), formula, sort=sort)
            else:
                use_tff = problem_needs_tff(list(premises), formula) if tff is None else tff
                if use_tff:
                    problem, name_map = generate_tff_problem(list(premises), formula), None
                else:
                    problem, name_map = generate_tptp_problem_with_mapping(list(premises), formula)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        if name_map is not None:
            pred_rev, term_rev = name_map.reverse_rendered()

        timeout_s = max(1, timeout // 1000)
        start = time.perf_counter()
        try:
            raw_output, timed_out = _run_tptp_prover(
                problem, command, self._args(timeout_s), use_wsl,
                timeout_s=timeout_s + 10)
        except (OSError, RuntimeError) as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=f"{type(exc).__name__}: {exc}")
        elapsed = time.perf_counter() - start

        if timed_out:
            return Verdict(UNKNOWN, self.name, reason="timeout",
                           wall_time=elapsed, solver_version=solver_version)
        szs = extract_szs_status(raw_output)
        if szs is None:
            tail = raw_output.strip()[-200:]
            if name_map is not None:
                tail = reverse_map_text(tail, pred_rev, term_rev)
            return Verdict(ERROR, self.name, reason="infra",
                           wall_time=elapsed, solver_version=solver_version,
                           detail="no SZS status line in output: " + tail)
        status, reason = szs_to_verdict_fields(szs, query="conjecture")
        proof = None
        detail = f"SZS status {szs}"
        if status == "proved":
            try:
                parsed = parse_tstp_derivation(raw_output)
                if name_map is not None:
                    parsed = reverse_map_derivation(parsed, name_map)
                # A status line without TSTP steps (Zipperposition's default
                # output) is a verdict without a certificate — proof stays
                # None and the detail says so, the Theorem status stands.
                proof = parsed.to_dict() if parsed.steps else None
                if proof is None:
                    detail += "; no TSTP derivation in output"
            except ValueError as exc:
                detail += f"; TSTP derivation unparseable: {exc}"
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed, solver_version=solver_version,
                       proof=proof, detail=detail)


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
