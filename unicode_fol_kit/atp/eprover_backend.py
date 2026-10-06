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

**E's own time limit is the call running out of time.** The kit hands E its call
budget as ``--cpu-limit=<seconds>`` and nothing else, so when E stops at that limit
(it prints ``Failure: Resource limit exceeded (time)`` and ``SZS status ResourceOut``)
the call ran out of time: UNKNOWN / ``"timeout"``, the same verdict as a run the kit
cut off itself, and as Vampire's. A ``ResourceOut`` that is not that limit stays
``"bound_hit"``: E's wording for its memory limit is ``(memory)``, and for a limit the
kit never passes (``--processed-clauses-limit``, ``--soft-cpu-limit``) ``User resource
limit exceeded!``.

**Typed arithmetic (``sort="int"`` / ``"real"``) is not E's arithmetic.** The option writes the
problem as typed TPTP (:func:`~unicode_fol_kit.atp._tff_problem.generate_tff_arith_problem`),
which Vampire reads with its own arithmetic. E 3.5.1 reads the typed text and then does
three things (measured on that build) that its caller must not mistake for arithmetic: it
types ``$sum``, ``$difference``, ``$product``, ``$quotient``, ``$quotient_e`` and ``$uminus`` as
functions into the individuals and stops with ``Type error`` on every term that uses one
(``$sum(1,1) = 2`` is a type error, not a theorem); it reads a ``$real`` literal only
approximately and calls two close ones equal (``1.0 = 1.0000001``, ``0.1 = 0.1000001`` and
``9007199254740993.0 = 9007199254740992.0`` are theorems for it, ``0.1 = 0.101`` is not), where
``$int`` literals are exact; and it reads ``$less``, ``$lesseq``, ``$greater`` and ``$greatereq`` as predicates it never
evaluates, so it proves only what holds of them as uninterpreted symbols and answers ``GaveUp``
(``unknown``) for the rest. So E is refused by name, as ``unknown`` / ``unsupported`` (an
exception on a direct call), for a problem with an arithmetic function symbol, and for a numeral
under ``sort="real"``. What is left is a problem that E answers soundly, usually without using any
arithmetic: use Vampire or Z3 (``z3_arith``) for arithmetic. Zipperposition is not refused:
its behaviour on typed arithmetic is not measured here.
"""

import os
import re
import shutil
import subprocess
import tempfile
import time
from typing import List, Optional, Sequence, Tuple

from ..fol.nodes import Function, Node, Number
from ._ascii_names import reverse_map_text
from ._tff_problem import generate_tff_arith_problem
from ._tptp_problem import generate_tptp_problem_for_prover, generate_tptp_problem_with_mapping
from ._writer_support import names_kwargs
from .protocol import (
    ProverBackend, Verdict, UNKNOWN, ERROR, _binary_version, _rejection_detail,
)

__all__ = ["EProverBackend", "ZipperpositionBackend",
           "check_entailment_eprover_detailed", "eprover_available",
           "zipperposition_available", "eprover_relevant_premises"]

#: What E 3.5.1 prints when it stops at the ``--cpu-limit`` the kit passed (recorded:
#: ``%% Failure: Resource limit exceeded (time)`` then ``%% SZS status ResourceOut``,
#: after ``eprover: CPU time limit exceeded, terminating`` on stderr).
_E_OWN_TIME_LIMIT = re.compile(r"Failure:\s*Resource limit exceeded \(time\)")


def _eprover_verdict_fields(szs: str, raw_output: str) -> Tuple[str, Optional[str]]:
    """``(status, reason)`` of E's SZS status, with ONE difference from
    :func:`~unicode_fol_kit.atp.tstp.szs_to_verdict_fields`: a ``ResourceOut`` that
    is E stopping at the ``--cpu-limit`` the kit derived from the call's budget IS
    the call running out of time (UNKNOWN / ``"timeout"``), not a bound that was hit
    (see the module docstring). ``raw_output`` is E's output, stdout and stderr."""
    from .tstp import szs_to_verdict_fields

    if szs == "ResourceOut" and _E_OWN_TIME_LIMIT.search(raw_output):
        return UNKNOWN, "timeout"
    return szs_to_verdict_fields(szs, query="conjecture")


#: What E 3.5.1 does with a function symbol of TPTP's arithmetic (measured: ``$sum(1,1) = 2``
#: gives ``terms $sum(1,1): $i and 2: $int should have the same sort`` and no SZS status).
_E_NO_ARITHMETIC_FUNCTIONS = (
    "eprover: the typed arithmetic text of this problem uses the operator {name!r} ({word}), "
    "which E 3.5.1 cannot read: it types TPTP's arithmetic functions as functions into the "
    "individuals and stops with 'Type error' on every term that uses one, whatever the sort, "
    "so it has no answer to give. E does not evaluate arithmetic. Ask Vampire "
    "(backends=['vampire']) or Z3 with sort=, which do."
)

#: What E 3.5.1 does with a ``$real`` literal (measured: ``0.1 = 0.1000001``, ``1.0 = 1.0000001``
#: and ``9007199254740993.0 = 9007199254740992.0`` are theorems for it; ``$int`` literals of any
#: size are exact).
_E_NO_REAL_NUMERALS = (
    "eprover: the typed arithmetic text of this problem has the numeral {value!r} under "
    "sort='real', and E 3.5.1 reads a $real literal only approximately: it calls two close ones "
    "equal (0.1 = 0.1000001 and 9007199254740993.0 = 9007199254740992.0 are theorems for it), so "
    "it could prove what is false of the real numbers. Use sort='int' (E reads integer literals "
    "exactly), or Vampire (backends=['vampire']) or Z3 with sort=, which read a real exactly."
)


def _eprover_arithmetic_refusal(premises: Sequence[Node], conclusion: Optional[Node],
                                sort: Optional[str]) -> Optional[str]:
    """Why E 3.5.1 is not given the typed arithmetic text of this problem, or ``None``.

    Measured on E 3.5.1 (see the module docstring): an arithmetic function symbol is a type error
    and a ``$real`` literal is read approximately, so a problem with either is refused by name.
    A comparison (``< > ≤ ≥``) is read as an uninterpreted predicate, which can only make E
    prove less than the arithmetic reading does, never more, and E answers ``GaveUp`` and never
    ``CounterSatisfiable`` for a text with an interpreted symbol (measured on a battery of valid
    and invalid comparisons, with and without integer literals), so it is not refused. ``None``
    for ``sort=None`` (the route does not apply) and for a sort the writer itself refuses.
    """
    if sort not in ("int", "real"):
        return None
    formulas = list(premises) + ([] if conclusion is None else [conclusion])
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Function) and node.name in Function.TPTP_ARITH_OPS:
                return _E_NO_ARITHMETIC_FUNCTIONS.format(
                    name=node.name, word=Function.TPTP_ARITH_OPS[node.name])
            if sort == "real" and isinstance(node, Number):
                return _E_NO_REAL_NUMERALS.format(value=node.value)
    return None


def _generate_tptp_problem(premises: List[Node], conclusion: Node,
                           *, tff: Optional[bool] = None,
                           sort: Optional[str] = None,
                           premise_names: Optional[Sequence[str]] = None) -> str:
    """``fof(premise_<i>, axiom, …).`` lines + one ``fof(goal, conjecture, …).``
    — or, when ``tff``/``sort`` selects a typed route, one of its siblings.

    ``sort`` (``None`` by default) opts into the single-numeric-sort typed
    arithmetic route (:func:`atp._tff_problem.generate_tff_arith_problem`,
    ``'real'`` or ``'int'``) UNCONDITIONALLY when given, taking priority
    over ``tff``. It writes the TEXT of that route, which Vampire reads with its own
    arithmetic on `+ - * /` and `< > ≤ ≥`; E 3.5.1 does not (see the module docstring:
    :meth:`EProverBackend.decide` and :func:`check_entailment_eprover_detailed` refuse by name
    what E cannot read, and this function only writes the text), and the untyped ``fof`` route
    below cannot (see :mod:`atp._tff_problem`'s module docstring): without
    ``sort`` a numeral is a constant identified by its value and those
    symbols are uninterpreted, written under ordinary words by the problem
    writers (see :mod:`atp._tptp_problem`), so ``1 ≠ 2`` is not provable. With
    ``sort=None``, ``tff=None`` (the default) tries
    :func:`atp.tptp_tff.generate_tff_problem` when ``premises``/
    ``conclusion`` contain a SortedQuantifier/SortedConstant/SortedCount
    node (see :func:`atp.tptp_tff.problem_needs_tff`) and writes the ``fof``
    problem instead when the typed writer refuses it
    (a :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal`: its text would ask another
    question than the kit's; or a node it does not cover that the ``fof`` writer does:
    a counting quantifier, ``Contrast``, ``Measure``; see :func:`atp._tptp_problem
    .generate_tptp_problem_for_prover`); without a sorted node (or with
    ``tff=False``) this is the shared ``fof`` writer
    (:func:`atp._tptp_problem.generate_tptp_problem`, also used by the
    Vampire route, which builds the identical ``fof`` problem shape);
    ``tff=True`` raises the typed writer's refusal.
    Every route's own ``NotImplementedError`` (an untranslatable node, or a
    cross-formula symbol-collision — see each module's docstring)
    propagates; the backends below turn that into an UNKNOWN/"unsupported"
    verdict. ``premise_names`` names the premises' ``axiom`` lines in whichever route
    is written (see :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`),
    ``premise_<i>`` when it is ``None``.
    """
    if sort is not None:
        problem, _name_map = generate_tff_arith_problem(
            premises, conclusion, sort=sort, **names_kwargs(premise_names))
        return problem
    return generate_tptp_problem_for_prover(
        premises, conclusion, tff=tff, fof_writer=generate_tptp_problem_with_mapping,
        premise_names=premise_names).text


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
                                      sort: Optional[str] = None,
                                      premise_names: Optional[Sequence[str]] = None) -> dict:
    """Run E on ``premises ⊨ conclusion``; SZS-status + TSTP-derivation dict.

    Same result contract as ``check_entailment_vampire_detailed``:
    ``{"status", "reason", "szs_status", "derivation", "raw"}``, and the two keys
    ``"dialect"`` (``"fof"``, ``"tff"`` or ``"tfa"``: which writer produced the
    problem E was given) and ``"tff_fallback"`` (``None``, or the sentence that says
    ``tff=None`` tried the typed writer, was refused, and wrote ``fof`` instead,
    with the typed writer's reason). For a PROVED answer ``"relevant_premises"`` holds
    the sorted 0-based indices of the premises the proof's axiom leaves are, read through
    the problem's name map (``None`` otherwise, and when the proof cannot be read that
    way) and ``"background_used"`` the ``(name, meaning)`` pairs of the background axioms
    the writer added on its own (the non-emptiness of a sort, the membership of a sorted
    constant) that the proof used: background, not premises. ``premise_names`` names the
    premises' ``axiom`` lines instead of ``premise_<i>`` (see
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`); E prints them back as
    the names of the proof's leaves. With
    ``command=None`` discovery runs (env → PATH → WSL) and a miss raises
    ``RuntimeError`` — use :func:`eprover_available` to probe first. ``tff``/
    ``sort`` select the TPTP dialect — see :func:`_generate_tptp_problem`. ``sort`` is the typed
    arithmetic text, which E 3.5.1 does not evaluate: a problem with an arithmetic function
    (``+ - * /``) or, under ``sort='real'``, a numeral is refused (see the module docstring).
    Every route (``fof``, ``tff``, ``sort``) hands back a
    :class:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap`, so ``raw`` below
    IS reverse-mapped to original kit-level names on all of them.

    Every symbol name in ``raw`` and in ``derivation``'s formulas has
    already been translated back from whatever ASCII-safe token the problem
    writer may have substituted (a non-ASCII or digit-leading kit-level name,
    or a function/constant renamed because its word is a predicate's:
    ``agent`` -> ``agent_term``) to the ORIGINAL kit-level name — see
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping` and
    :func:`atp.tptp_tff.generate_tff_problem_with_mapping`. A name E
    introduced itself (a clausification symbol, e.g. ``c_0_7``) was never one
    of ours and is left as E printed it, and so is a SORT name on the ``tff``
    route (the TF0 map covers predicates, functions and constants, not
    sorts). ``derivation`` is CURRENTLY ALWAYS ``None`` on the ``tff`` route,
    even for a genuine proof: :func:`atp.tstp.parse_tstp_derivation` only
    recognises ``fof``/``cnf`` statements (see its own docstring), never the
    ``tff``/``tcf`` ones E prints — a real gap (tff/tcf-proof-line reading is
    follow-up work in :mod:`atp.tstp`), not merely "un-reversed".

    Raises:
        NotImplementedError: a formula is outside the fragment the selected
            route covers, or two distinct predicate (or function/constant,
            or — ``tff`` route — sort) names would fold to the same TPTP
            identifier (see :mod:`atp._tptp_problem`'s and
            :mod:`atp.tptp_tff`'s module docstrings), or — ``sort`` route — the problem
            has an arithmetic function symbol or, under ``sort='real'``, a numeral, which E
            3.5.1 cannot read or reads approximately — surfaced before any subprocess is spawned;
            unlike :class:`_TptpSzsBackend.decide`, this function does NOT
            catch it into an UNKNOWN verdict. With ``tff=True`` that includes
            the typed writer's refusal, a
            :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal` (also a
            ``ValueError``).
        RuntimeError: no ``eprover`` binary found (see above).
    """
    from .tstp import (_premise_use_from_tstp, extract_szs_status, parse_tstp_derivation,
                       reverse_map_derivation, szs_to_verdict_fields)

    refusal = _eprover_arithmetic_refusal(premises, conclusion, sort)
    if refusal is not None:
        raise NotImplementedError(refusal)

    if command is None:
        found = _discover("eprover", "UFK_EPROVER_CMD")
        if found is None:
            raise RuntimeError(
                "eprover: no binary found (PATH, WSL, $UFK_EPROVER_CMD) — "
                "apt install eprover (Ubuntu 24.04+/Debian) or build from "
                "https://github.com/eprover/eprover")
        command, use_wsl = found

    if sort is not None:
        problem, name_map = generate_tff_arith_problem(
            premises, conclusion, sort=sort, **names_kwargs(premise_names))
        dialect, fallback_note = "tfa", None
    else:
        built = generate_tptp_problem_for_prover(
            premises, conclusion, tff=tff, fof_writer=generate_tptp_problem_with_mapping,
            premise_names=premise_names)
        problem, name_map = built.text, built.name_map
        dialect, fallback_note = built.dialect, built.fallback_note
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
                "derivation": None, "raw": output,
                "dialect": dialect, "tff_fallback": fallback_note,
                "relevant_premises": None, "background_used": ()}

    szs = extract_szs_status(raw_output)
    if szs is None:
        return {"status": ERROR, "reason": "infra", "szs_status": None,
                "derivation": None, "raw": output,
                "dialect": dialect, "tff_fallback": fallback_note,
                "relevant_premises": None, "background_used": ()}
    status, reason = _eprover_verdict_fields(szs, raw_output)
    derivation = None
    relevant: Optional[Tuple[int, ...]] = None
    background_used: Tuple[Tuple[str, str], ...] = ()
    if status == "proved":
        # The axiom leaves by the names the problem gave them, from the text E printed
        # (a premise name is not a symbol, so never the renamed ``output``).
        use = _premise_use_from_tstp(raw_output, len(premises), name_map, eprover=True)
        if use is not None:
            relevant, background_used = use
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
            "derivation": derivation, "raw": output,
            "dialect": dialect, "tff_fallback": fallback_note,
            "relevant_premises": relevant, "background_used": background_used}


def eprover_relevant_premises(premises: List[Node], conclusion: Node, *,
                              timeout: int = 30, command: Optional[str] = None,
                              use_wsl: bool = False,
                              tff: Optional[bool] = None,
                              sort: Optional[str] = None,
                              premise_names: Optional[Sequence[str]] = None
                              ) -> Optional[Tuple[int, ...]]:
    """Which of ``premises`` did E's proof of ``premises ⊨ conclusion``
    actually rest on?

    Runs E exactly ONCE, through :func:`check_entailment_eprover_detailed`'s
    own subprocess plumbing (no second prover invocation) — and, only when
    the resulting verdict is PROVED, walks the TSTP derivation backward via
    :func:`atp.tstp.relevant_premises_from_tstp`, which descends into E's
    own nested administrative ``inference(...)`` steps (see that function's
    module comment) down to every reachable axiom leaf; E names those leaves
    after the names the problem's writer gave its lines (``premise_<i>``, or
    ``premise_names``; E prints a quoted name back as it was written, except for
    an apostrophe, which :func:`atp.tstp.relevant_premises_from_tstp` allows for), so
    index recovery goes through the writer's record of them. A leaf that is a
    background axiom of a sorted problem (``nonempty_sort_<i>``, ``sort_member_<i>``) is
    not one of ``premises``: it is left out of the result, and
    :func:`check_entailment_eprover_detailed` says which were used.

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
    try:
        result = check_entailment_eprover_detailed(
            premises, conclusion, timeout=timeout, command=command, use_wsl=use_wsl,
            tff=tff, sort=sort, premise_names=premise_names)
    except RuntimeError:
        return None      # no eprover binary -- an honest "no answer", not an error
    if result["status"] != "proved":
        return None
    return result["relevant_premises"]


class _TptpSzsBackend(ProverBackend):
    """Shared decide() skeleton for the two SZS-speaking TPTP provers."""

    logics = frozenset({"fol", "arith"})
    external = True

    _env_var: str = ""
    _binary: str = ""

    def _args(self, timeout_s: int) -> List[str]:      # pragma: no cover
        raise NotImplementedError

    def _verdict_fields(self, szs: str, raw_output: str) -> Tuple[str, Optional[str]]:
        """``(status, reason)`` of this prover's SZS status; E overrides it."""
        from .tstp import szs_to_verdict_fields
        return szs_to_verdict_fields(szs, query="conjecture")

    #: Whether the prover prints a premise name back the way E does (see
    #: :func:`atp.tstp.relevant_premises_from_tstp`'s ``eprover``).
    _prints_names_like_eprover: bool = False

    def _background_note(self, raw_output: str, n_premises: int, name_map) -> str:
        """The sentence for a proved verdict's ``detail`` that names the background axioms
        of a sorted problem the proof used (the non-emptiness of a sort, the membership
        of a sorted constant), or ``""`` when it used none or its leaves cannot be read
        through the problem's name map."""
        from .tstp import _premise_use_from_tstp
        use = _premise_use_from_tstp(raw_output, n_premises, name_map,
                                     eprover=self._prints_names_like_eprover)
        if use is None or not use[1]:
            return ""
        facts = ", ".join(f"{name} ({meaning})" if meaning else name for name, meaning in use[1])
        return (f"; the proof used the background facts of the sorted reading, which are "
                f"not premises: {facts}")

    def _arithmetic_refusal(self, premises: Sequence[Node], formula: Optional[Node],
                            sort: Optional[str]) -> Optional[str]:
        """Why this prover is not given the typed arithmetic text of the problem (``sort=``), or
        ``None``. A prover whose reading of that text has not been measured is never refused."""
        return None

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
        ``'int'``) UNCONDITIONALLY when given, taking priority over ``tff``.
        That is the text Vampire reads with its own arithmetic, which the
        untyped ``fof``/many-sorted-``tff`` routes cannot give it (see
        :mod:`atp._tff_problem`'s module docstring); E 3.5.1 does not evaluate
        it, so ``EProverBackend`` answers ``unknown`` / ``"unsupported"``, naming the operator or
        the numeral, for a problem with an arithmetic function symbol (E stops with a type
        error on one) or, under ``sort='real'``, a numeral (E reads a ``$real`` literal
        approximately) — see the module docstring; the other problems it answers soundly, and
        ``unknown`` for what needs arithmetic. Zipperposition is asked as it always was (its
        reading of the typed text is not measured). With ``sort=None``,
        ``tff`` selects as before: ``None`` (the default, i.e. omitted)
        tries the native many-sorted typed ``tff`` route whenever
        ``premises``/``formula`` use a sort — see
        :func:`_generate_tptp_problem` — and writes ``fof`` instead when the
        typed writer refuses the problem (its text would ask another question
        than the kit's: :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal`; or it holds a
        node the typed writer does not cover and the ``fof`` writer does), saying
        so and why in the verdict's ``detail``; ``True``/``False`` force one route
        (with ``True`` the refusal is the verdict, UNKNOWN / ``"unsupported"``
        with the writer's message).
        Every route hands back a
        :class:`~unicode_fol_kit.atp._tptp_problem.TptpNameMap`, so
        ``proof``/``detail`` are reverse-mapped to original kit-level names
        on the ``fof``, the many-sorted ``tff`` and the ``sort`` route alike
        (a SORT name on the ``tff`` route is not in the TF0 map and stays as
        the prover printed it).
        """
        from .tstp import (extract_szs_status, parse_tstp_derivation,
                           reverse_map_derivation, szs_to_verdict_fields)

        tff = options.pop("tff", None)
        sort = options.pop("sort", None)
        premise_names = options.pop("premise_names", None)

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
                refusal = self._arithmetic_refusal(premises, formula, sort)
                if refusal is not None:
                    raise NotImplementedError(refusal)
                problem, name_map = generate_tff_arith_problem(
                    list(premises), formula, sort=sort, **names_kwargs(premise_names))
                fallback_note = None
            else:
                built = generate_tptp_problem_for_prover(
                    list(premises), formula, tff=tff,
                    fof_writer=generate_tptp_problem_with_mapping,
                    premise_names=premise_names)
                problem, name_map, fallback_note = built.text, built.name_map, built.fallback_note
        except NotImplementedError as exc:
            # tff=True: the typed writer's own refusal (Tf0Refusal is a
            # NotImplementedError too) is the verdict, with its message.
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        if name_map is not None:
            pred_rev, term_rev = name_map.reverse_rendered()

        def noted(text: str) -> str:
            # tff=None tried the typed writer for a sorted problem and it refused:
            # the answer is that of the fof text, and the detail says so and why.
            return text if fallback_note is None else f"{text}; {fallback_note}"

        timeout_s = max(1, timeout // 1000)
        start = time.perf_counter()
        try:
            raw_output, timed_out = _run_tptp_prover(
                problem, command, self._args(timeout_s), use_wsl,
                timeout_s=timeout_s + 10)
        except (OSError, RuntimeError) as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=noted(f"{type(exc).__name__}: {exc}"))
        elapsed = time.perf_counter() - start

        if timed_out:
            return Verdict(UNKNOWN, self.name, reason="timeout",
                           wall_time=elapsed, solver_version=solver_version,
                           detail=noted(
                               f"{self.name} had not stopped when the budget of this call "
                               f"({timeout_s} s) plus 10 s of grace had passed, so the kit "
                               "stopped it before it printed a verdict"))
        szs = extract_szs_status(raw_output)
        if szs is None:
            # The prover read the problem and refused it (E: a parse error on
            # stderr, exit 3), or died: a failure that carries the prover's
            # own text, never an "unknown" that reads like a timeout.
            shown = raw_output
            if name_map is not None:
                shown = reverse_map_text(shown, pred_rev, term_rev)
            return Verdict(ERROR, self.name, reason="infra",
                           wall_time=elapsed, solver_version=solver_version,
                           detail=noted(_rejection_detail(
                               self.name, shown, "no SZS status line in its output")))
        status, reason = self._verdict_fields(szs, raw_output)
        proof = None
        detail = f"SZS status {szs}"
        if szs == "ResourceOut" and reason == "timeout":
            detail += (f"; {self.name} stopped itself at its --cpu-limit of {timeout_s} s, "
                       "which is the budget of this call")
        if status == ERROR:
            # An SZS status that itself names a failure (Error, InputError,
            # SyntaxError): quote what the prover said about it.
            shown = raw_output
            if name_map is not None:
                shown = reverse_map_text(shown, pred_rev, term_rev)
            detail = _rejection_detail(self.name, shown, f"SZS status {szs}")
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
            detail += self._background_note(raw_output, len(premises), name_map)
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed, solver_version=solver_version,
                       proof=proof, detail=noted(detail))


class EProverBackend(_TptpSzsBackend):
    """E (superposition, https://eprover.org) — registry name ``"eprover"``."""

    name = "eprover"
    _env_var = "UFK_EPROVER_CMD"
    _binary = "eprover"
    _prints_names_like_eprover = True

    def _arithmetic_refusal(self, premises: Sequence[Node], formula: Optional[Node],
                            sort: Optional[str]) -> Optional[str]:
        return _eprover_arithmetic_refusal(premises, formula, sort)

    def _args(self, timeout_s: int) -> List[str]:
        return ["--auto", "--tstp-format", "--proof-object", "-s",
                f"--cpu-limit={timeout_s}"]

    def _verdict_fields(self, szs: str, raw_output: str) -> Tuple[str, Optional[str]]:
        return _eprover_verdict_fields(szs, raw_output)


class ZipperpositionBackend(_TptpSzsBackend):
    """Zipperposition (OCaml superposition) — registry name ``"zipperposition"``."""

    name = "zipperposition"
    _env_var = "UFK_ZIPPERPOSITION_CMD"
    _binary = "zipperposition"

    def _args(self, timeout_s: int) -> List[str]:
        return ["--timeout", str(timeout_s)]
