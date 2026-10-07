"""Uniform prover protocol: one Verdict type over every decision route.

The kit decides validity/entailment through many routes — its OWN calculi and
semantic model searches (Z3-free tableau, resolution, finite model finder,
modal labelled tableau, the QML embedding) and EXTERNAL provers (Z3, Isabelle,
Prover9, Vampire). Each grew its own return convention (bare bool,
``"valid"/"invalid"/"unknown"`` strings, ``ModalVerdict``/``FolVerdict``).
This module adds the layer a pipeline needs on top, without touching any
existing signature:

* :class:`Verdict` — the one result type: a semantic ``status`` (proved /
  refuted / unknown / error), a ``reason`` axis that distinguishes budget
  exhaustion from honest incompleteness from timeouts, the SZS status string,
  provenance (which backend, how long), and JSON-able witnesses.
* :class:`ProverBackend` — the adapter contract (``available()`` +
  ``decide()``), with the kit's internal calculi and semantic searches as
  first-class backends alongside the external provers.
* a registry (:func:`register_backend`, :func:`get_backend`,
  :func:`available_backends`, :func:`default_chain`) that the ``prove()``
  facade in :mod:`unicode_logic_kit.api` dispatches over.

Error contract: requesting an UNKNOWN backend name raises ``ValueError``;
requesting a known backend whose prerequisites are missing (no binary, no
install) raises :class:`BackendUnavailable` — never a silent skip, because a
silently skipped backend makes evaluation results irreproducible.

The status/reason split is deliberate: ``status`` answers "what do we know
about the formula" (only four values, easy to branch on), ``reason`` answers
"why do we not know more" (``bound_hit`` ≠ ``timeout`` ≠ ``incomplete`` ≠
``unsupported`` — a benchmark table must not conflate them).
"""

import re
import shutil
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from typing import Dict, Optional, Sequence, Tuple

from ..fol.nodes import Node, And, Implies

__all__ = [
    "PROVED", "REFUTED", "UNKNOWN", "ERROR", "STATUSES",
    "Verdict", "BackendUnavailable", "ProverBackend",
    "register_backend", "get_backend", "available_backends", "default_chain",
    "run_backend",
    "z3_relevant_premises",
]

# ---------------------------------------------------------------------------
# Statuses, reasons, and their SZS image
# ---------------------------------------------------------------------------

PROVED = "proved"      # validity / entailment established
REFUTED = "refuted"    # a genuine countermodel witnesses invalidity
UNKNOWN = "unknown"    # neither, within this backend's budget/strength
ERROR = "error"        # the backend failed for an infrastructure reason
STATUSES = (PROVED, REFUTED, UNKNOWN, ERROR)

# reason values (for UNKNOWN/ERROR): why we do not know more.
#   "timeout"     — a wall-clock budget expired
#   "bound_hit"   — a step/size bound expired (max_steps, max_worlds, …)
#   "incomplete"  — the method is sound but incomplete on this fragment and
#                   gave up honestly (no bound was hit)
#   "unsupported" — the backend has no rule/translation for this fragment
#   "infra"       — subprocess/JVM/syntax failure (ERROR only). A prover that
#                   REJECTS its input (a syntax or type error, Vampire's "User
#                   error: ..." line, E's parse error, Twee's usage error,
#                   Prover9's fatal error) and prints no verdict lands here, with
#                   the prover's own message in ``detail``: refusing to read a
#                   problem is not the same as running out of time, and a
#                   benchmark table that files the two together reads a writer
#                   defect as "undecided".

_SZS = {
    (PROVED, None): "Theorem",
    (REFUTED, None): "CounterSatisfiable",
    (UNKNOWN, "timeout"): "Timeout",
    (UNKNOWN, "bound_hit"): "ResourceOut",
    (UNKNOWN, "incomplete"): "GaveUp",
    (UNKNOWN, "unsupported"): "Inappropriate",
    (UNKNOWN, None): "Unknown",
    (ERROR, "infra"): "Error",
    (ERROR, None): "Error",
}


def _szs_for(status: str, reason: Optional[str]) -> str:
    """Return the SZS ontology value for a (status, reason) pair."""
    return _SZS.get((status, reason), _SZS[(status, None)])


# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Verdict:
    """One decision result, whatever route produced it.

    Fields:

    * status: ``"proved"`` / ``"refuted"`` / ``"unknown"`` / ``"error"``.
      Truthiness follows ``status == "proved"``.
    * backend: name of the backend that produced this verdict.
    * logic: the logic the query was decided in (``"fol"``, ``"modal"``, …).
    * reason: the why-not-more axis for UNKNOWN/ERROR (see module docstring);
      ``None`` for definitive verdicts.
    * szs_status: SZS ontology value; derived from (status, reason) unless a
      backend sets it explicitly (e.g. verbatim from a TSTP line).
    * wall_time: seconds spent inside the backend call.
    * countermodel: JSON-able witness for REFUTED (shape is backend-specific
      but always a dict with a ``"kind"`` key), else ``None``.
    * proof: JSON-able proof object where the backend yields one, else None.
      A ``"kind": "z3_unsat_core"`` or ``"kind": "cvc5_alethe"`` proof
      carries an unsat CORE — sound (re-asserting just that subset is still
      unsat) but not necessarily MINIMAL (the underlying solver is free to
      track more than the smallest sufficient subset) — see
      :func:`z3_relevant_premises` for the same caveat on the dedicated
      premise-relevance query.
    * detail: short free-text note (method that closed it, bound that was
      hit, tried-backends summary, …).
    * agreement: backend names that reported the SAME status, filled by the
      portfolio layer; a single-backend verdict lists just its own.
    * relevant_premises: 0-based indices into the caller's ``premises`` that
      a premise-relevance query found necessary for a PROVED verdict (see
      :func:`z3_relevant_premises`, :mod:`atp.tstp`'s ancestor walk, and
      :mod:`atp.eprover_backend`'s ``eprover_relevant_premises``); ``None``
      when nobody computed it (the default) — NOT a claim that every premise
      was needed. Like ``proof``'s unsat core, a reported set is sound but
      not guaranteed minimal.
    * solver_version: the underlying external tool's own version string
      (Vampire's/Prover9's/E's/Zipperposition's ``--version`` banner, the
      reachable HETS server's ``GET /version`` text, the installed ``cvc5``
      package's distribution version), captured once per process per
      backend/binary and reported here unchanged — see
      :meth:`ProverBackend.solver_version` and :func:`_binary_version` for
      the memoization contract. ``None`` for the kit's own internal
      backends (Z3/tableau/resolution/modelfinder/QML/…, which have no
      external tool to version) and for an external backend whose version
      lookup itself failed or found nothing (the tool's PROOF/DISPROOF
      verdict is unaffected either way — a missing version string is never
      grounds to downgrade a sound answer).
    """

    status: str
    backend: str
    logic: str = "fol"
    reason: Optional[str] = None
    szs_status: Optional[str] = None
    wall_time: float = 0.0
    countermodel: Optional[dict] = None
    proof: Optional[dict] = None
    detail: Optional[str] = None
    agreement: Tuple[str, ...] = ()
    relevant_premises: Optional[Tuple[int, ...]] = None
    # New fields go last: positional construction by callers must keep working.
    solver_version: Optional[str] = None

    def __post_init__(self):
        if self.status not in STATUSES:
            raise ValueError(f"Verdict: unknown status {self.status!r} (use one of {STATUSES})")
        if self.szs_status is None:
            object.__setattr__(self, "szs_status", _szs_for(self.status, self.reason))
        if not self.agreement:
            object.__setattr__(self, "agreement", (self.backend,))

    def __bool__(self) -> bool:
        return self.status == PROVED

    @property
    def is_definitive(self) -> bool:
        """True iff the verdict settles the question (proved or refuted)."""
        return self.status in (PROVED, REFUTED)

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (all fields, names as keys)."""
        return {
            "status": self.status,
            "backend": self.backend,
            "logic": self.logic,
            "reason": self.reason,
            "szs_status": self.szs_status,
            "wall_time": self.wall_time,
            "countermodel": self.countermodel,
            "proof": self.proof,
            "detail": self.detail,
            "agreement": list(self.agreement),
            "relevant_premises": (list(self.relevant_premises)
                                  if self.relevant_premises is not None else None),
            "solver_version": self.solver_version,
        }


class BackendUnavailable(RuntimeError):
    """A KNOWN backend was requested but its prerequisites are missing.

    Raised instead of silently skipping, because a pipeline whose backend
    quietly vanished produces irreproducible numbers. The message names the
    backend and what discovery looked for (env var / binary / install).
    """


# ---------------------------------------------------------------------------
# The backend contract
# ---------------------------------------------------------------------------

class ProverBackend(ABC):
    """Adapter contract for one decision route.

    ``name`` is the registry key; ``logics`` the set of logic labels the
    backend accepts (``"fol"``, ``"modal"``). ``available()`` performs
    discovery without side effects. ``decide()`` answers "do ``premises``
    entail ``formula``?" (validity when ``premises`` is empty) and must NEVER
    raise for an in-contract input — undecidable/unsupported fragments come
    back as an UNKNOWN verdict with the honest ``reason``. Extra keyword
    options are forwarded verbatim to the underlying route (``frame=``,
    ``systems=``, ``max_steps=``, …), so the adapters stay thin and nothing
    of the existing signatures is hidden. A backend that names the options it
    reads (:meth:`accepted_options`) is handed only those by
    :func:`~unicode_logic_kit.api.prove`, which refuses an option that no backend
    of the chain reads; :meth:`available_for` answers for the route the options
    of a call select.

    For the modal backends, a non-empty ``premises`` is the LOCAL consequence
    ``⊨ (∧ premises) → φ`` — the standard finite-premise reading; global
    consequence is out of scope here.
    """

    name: str = ""
    logics: frozenset = frozenset({"fol"})
    external: bool = False           # needs a binary/install outside this venv

    @abstractmethod
    def available(self) -> bool:
        """Return whether this backend can run right now (pure discovery)."""

    def available_for(self, options: dict) -> bool:
        """Return whether this backend can run a call made with ``options``.

        :meth:`available` answers for the defaults. An option that picks the
        route (``use_wsl=``, the path of a binary) can change the answer, so the
        dispatcher asks THIS method, with the options of the call, and the answer
        and the run agree. The default ignores ``options`` and returns
        :meth:`available`.
        """
        return self.available()

    def accepted_options(self, logic: Optional[str] = None) -> Optional[frozenset]:
        """Return the names of the keyword options :meth:`decide` reads, or ``None``.

        ``None`` (the default) means the backend declares nothing: the dispatcher
        then passes it every option and cannot tell whether one is read. A
        backend that declares its names lets :func:`~unicode_logic_kit.api.prove`
        refuse an option that no backend of the chain reads, and pass each backend
        only the options it reads. ``logic`` is the logic of the call, for a
        backend whose options depend on it.
        """
        return None

    @abstractmethod
    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` and return a :class:`Verdict`."""

    def solver_version(self) -> Optional[str]:
        """The underlying external tool's own version string, or ``None``.

        Default (this base implementation): always ``None`` — the kit's own
        internal calculi and semantic searches (Z3 aside: its Python BINDING
        version is not "the solver's version" in the sense this method
        means, and :class:`Z3Backend` does not override this) have no
        external tool to version. An external backend overrides this with a
        lookup that is PROCESS-LOCAL MEMOIZED (see :func:`_binary_version`
        for the subprocess-spawning backends, and each override's own
        docstring for the HETS/cvc5 routes) — probed at most once per
        distinct binary/server/package for the life of this process, so
        neither this method nor :meth:`decide` (which populates
        ``Verdict.solver_version`` from it) ever pays a second lookup.
        Never raises and never changes any verdict's status/reason — this
        is provenance only, queried both from ``decide()`` and, independently,
        from :func:`unicode_logic_kit.eval.batch.batch_decide`'s cache key (so
        a solver upgrade invalidates stale cache entries).
        """
        return None


# ---------------------------------------------------------------------------
# Solver-version provenance: a process-local memoized ``--version`` lookup,
# shared by every subprocess-spawning backend below (Vampire, Prover9, and —
# via atp.eprover_backend's own import of this function — E/Zipperposition).
# HETS (an HTTP server, not a spawned binary) and cvc5 (a pip binding, not a
# spawned binary) have their own analogous, separately-memoized routes in
# their own modules (hets_backend.py, cvc5_backend.py) — see
# ProverBackend.solver_version's docstring.
# ---------------------------------------------------------------------------

#: (command, use_wsl) -> the tool's version string, or None on a failed
#: lookup — a MISS is cached too (never retried), matching item 5's "never
#: spawn a subprocess per decide() call after the first" requirement.
#: Deliberately separate from atp.eprover_backend._DISCOVERY_CACHE: discovery
#: (does a binary exist at all?) and version (what does it print?) answer
#: different questions and can fail independently — collapsing them into one
#: cache would make a version-lookup failure look like the binary vanished,
#: or vice versa.
_VERSION_CACHE: Dict[Tuple[str, bool], Optional[str]] = {}


def _binary_version(command: str, use_wsl: bool,
                    args: Tuple[str, ...] = ("--version",)) -> Optional[str]:
    """Process-local memoized ``<command> <args>`` version lookup.

    Spawns the subprocess (through ``wsl.exe`` when ``use_wsl``) at most ONCE
    per ``(command, use_wsl)`` pair for the life of this process; every
    later call for the same pair — including one that failed — returns the
    cached result without spawning again. On a ZERO exit, returns the first
    non-blank line of stdout, falling back to stderr (some tools print
    version banners there), stripped. ``None`` on any failure: binary
    missing, a timeout, WSL unreachable, a non-zero exit — an unrecognized
    flag commonly prints an error/usage line to stdout or stderr on a
    non-zero exit, and accepting that text as a version string would be
    worse than reporting no provenance at all (mirrors the returncode check
    :func:`unicode_logic_kit.atp.eprover_backend._discover` already applies to
    its own subprocess probe) — OR the banner not being valid text under
    ``subprocess.run(..., text=True)``'s decoding (``UnicodeError``, e.g. a
    tool that writes a non-UTF-8 locale-encoded byte in its ``--version``
    output): decoding happens INSIDE ``subprocess.run`` here, so this is
    caught exactly like any other failure to read the banner, never left to
    propagate as a bare ``ValueError`` out of a caller's ``decide()``. This
    is best-effort provenance, so nothing here ever raises or turns into an
    ERROR verdict.
    """
    key = (command, use_wsl)
    if key in _VERSION_CACHE:
        return _VERSION_CACHE[key]

    import subprocess

    result: Optional[str] = None
    try:
        cmd = ["wsl.exe", command, *args] if use_wsl else [command, *args]
        # The tool never reads this process's stdin: Prover9 reads its problem from
        # stdin for any flag it does not know (``--version`` included), and would
        # block on an inherited pipe (an MCP server's own protocol stream) or read it.
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                              stdin=subprocess.DEVNULL)
        if proc.returncode == 0:
            text = (proc.stdout or "").strip() or (proc.stderr or "").strip()
            if text:
                result = text.splitlines()[0].strip()
    except (OSError, subprocess.TimeoutExpired, UnicodeError):
        result = None
    _VERSION_CACHE[key] = result
    return result


#: binary -> whether ``wsl.exe which <binary>`` found it. An answer is cached for
#: the life of the process, like :data:`_VERSION_CACHE`, so a discovery that
#: spawns ``wsl.exe`` is paid once per binary. A probe that TIMED OUT is not an
#: answer and is not cached: WSL may only have been slow to start.
_WSL_BINARY_CACHE: Dict[str, bool] = {}

#: Seconds the WSL probe of :func:`_wsl_has_binary` may take.
_WSL_PROBE_TIMEOUT = 10


def _wsl_has_binary(binary: str) -> bool:
    """Whether ``binary`` (a name on the PATH inside WSL, or a path inside WSL)
    exists there and is executable.

    This is what ``available()`` has to ask when a backend will run its binary
    through ``wsl.exe``: the host's own PATH says nothing about a Linux binary.
    Asks ``wsl.exe which <binary>`` -- the command the runners themselves use to
    start it -- with a short timeout and an empty standard input, so the probe
    never blocks on, or reads, this process's input. ``False`` when ``wsl.exe``
    cannot be started (no WSL on this host), when it times out, and when the
    binary is not found; never raises.
    """
    if binary in _WSL_BINARY_CACHE:
        return _WSL_BINARY_CACHE[binary]

    import subprocess

    try:
        proc = subprocess.run(["wsl.exe", "which", binary], capture_output=True,
                              timeout=_WSL_PROBE_TIMEOUT, stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        return False
    except OSError:
        found = False
    else:
        found = proc.returncode == 0 and bool(
            (proc.stdout or b"").decode("utf-8", errors="replace").replace("\x00", "").strip())
    _WSL_BINARY_CACHE[binary] = found
    return found


def _native_command_exists(command: str) -> bool:
    """Whether this host can start ``command``: an executable file at that path, or a
    name that is on ``PATH``.

    ``shutil.which`` answers both, except for one spelling that the run accepts: on
    Windows a path with a directory part and no extension is looked up exactly as
    written by ``shutil.which`` (before Python 3.12), whereas ``subprocess`` starts it
    through ``CreateProcess``, which appends ``.exe`` to a name that has no extension.
    A caller who names the installed ``minizinc.exe`` as ``D:/Minizinc/MiniZinc/minizinc``
    names a binary the run starts, so that spelling is tried too. Never starts anything.
    """
    import os

    if shutil.which(command) is not None:
        return True
    if os.name == "nt" and not os.path.splitext(command)[1]:
        return shutil.which(command + ".exe") is not None
    return False


def _implication(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ φ`` into the single formula ``(∧ premises) → φ``."""
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


def _timed(fn):
    """Run ``fn()`` returning ``(result, seconds)``."""
    start = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - start


# ---------------------------------------------------------------------------
# A prover that REFUSES its input is an error, not a timeout.
#
# Every subprocess backend reads a verdict off its prover's output: an SZS
# status line (Vampire, E, Zipperposition), a ``RESULT:`` line (Twee), a
# ``THEOREM PROVED`` line (Prover9). A prover that cannot read the problem
# prints none of those -- it prints its own complaint instead (Vampire 5.0.1:
# ``User error: Non-boolean term agent(agent(X0)) of sort $i is used in a
# formula context``; E 3.5.1: ``eprover: <file>:1:(Column 45): ... expected,
# but Closing bracket (')') read``; Twee 2.6.1: ``Error in <file> (line 2,
# column 1): Unexpected fof``) -- and a backend that reads "no verdict" as
# "did not get there in time" reports a defect in the problem WRITER as an
# undecided question. One wording, shared by every backend, keeps the three
# readings (timeout / honest give-up / refusal) apart wherever the outcome is
# shown.
# ---------------------------------------------------------------------------

#: Lines of a prover's output that explain a failure. Used only to choose
#: WHERE to start quoting a long output; a short one is quoted whole.
_FAILURE_LINE = re.compile(
    r"error|exception|assertion|fatal|abort|segmentation|core dumped|cannot|"
    r"unexpected|expected|failed|invalid", re.IGNORECASE)

#: How much of the prover's own output a refusal's ``detail`` quotes.
_REJECTION_QUOTE_CHARS = 600


def _rejection_detail(prover: str, output: str, evidence: str) -> str:
    """The ``detail`` of an ERROR verdict for a prover that gave no verdict.

    ``evidence`` says what was missing (``"no SZS status line in its output"``,
    ``"no RESULT line in its output"``, ...). The prover's OWN text follows,
    one line per ``|``-separated item, unmodified apart from stripping blank
    lines, NUL bytes (a Windows ``wsl.exe`` diagnostic arrives UTF-16 decoded
    as 8-bit) and trailing whitespace. An output longer than
    :data:`_REJECTION_QUOTE_CHARS` is quoted from its first failure-looking
    line, or from its tail when no line looks like one -- the explanation of a
    refusal is at the start (Vampire) and that of a crash at the end (E's
    ``Assertion ... failed``), and a run that printed pages of statistics
    first would otherwise bury either.
    """
    lines = [ln.strip() for ln in output.replace("\x00", "").splitlines()]
    lines = [ln for ln in lines if ln]
    message = " | ".join(lines)
    if len(message) > _REJECTION_QUOTE_CHARS:
        start = next((i for i, ln in enumerate(lines) if _FAILURE_LINE.search(ln)), None)
        if start is None:
            message = "... " + message[-_REJECTION_QUOTE_CHARS:]
        else:
            message = " | ".join(lines[start:])
            if len(message) > _REJECTION_QUOTE_CHARS:
                message = message[:_REJECTION_QUOTE_CHARS] + " ..."
    if not message:
        message = "(it printed nothing)"
    return (f"{prover} produced no verdict ({evidence}); this is a failure, "
            f"not a timeout. Its own output: {message}")


def _no_definitive_verdict(pseudo_backend: str, logic: str,
                           verdicts: Sequence[Verdict], empty: str) -> Verdict:
    """The collective verdict of a chain/portfolio in which nobody settled it.

    ``"<backend>:<status>[/<reason>] (<detail>)"`` for EVERY member that ran:
    its status and reason, and its own account of them when it gave one. A member
    that FAILED (ERROR, or any member whose reason is ``"infra"`` -- the Isabelle
    adapter reports that as UNKNOWN) quotes its ``detail``, so a prover's
    refusal reaches the caller instead of being flattened into the bare
    ``vampire:error/infra`` that reads like any other "no answer"; so does a
    member that REFUSED the question (reason ``"unsupported"``): the writer's
    message says what it would not write and what to write instead, and without it
    the caller has only the word "unsupported"; so does a member that gave up
    (``"bound_hit"``, ``"incomplete"``, ``"timeout"``): the bound that was hit, or
    the point where the search ended, is what tells the caller which budget to
    raise. A member without a ``detail`` is listed by status and reason alone. When EVERY
    member failed there is no honest ``unknown`` to report -- nothing was asked
    and answered -- so the collective verdict is itself an ERROR; with at least
    one member that really answered "unknown" it stays UNKNOWN and the failures
    sit in the detail beside it.
    """
    if not verdicts:
        return Verdict(UNKNOWN, pseudo_backend, logic=logic, detail=empty)
    summary = "; ".join(
        f"{v.backend}:{v.status}" + (f"/{v.reason}" if v.reason else "")
        + (f" ({v.detail})" if v.detail else "")
        for v in verdicts)
    if all(v.status == ERROR for v in verdicts):
        return Verdict(ERROR, pseudo_backend, logic=logic, reason="infra",
                       detail=f"no backend gave an answer — {summary}")
    return Verdict(UNKNOWN, pseudo_backend, logic=logic,
                   detail=f"no definitive verdict — {summary}")


def _z3_sort_axioms(formula: Node, premises: Sequence[Node], env=None) -> list:
    """``sort_axioms(formula, *premises)``, each translated via ``to_z3(env)``.

    ``env`` is the :class:`~unicode_logic_kit.fol.nodes.Z3Env` the goal and the
    premises were translated with (the caller's one environment for the whole
    problem).

    That is every sort's non-emptiness AND the membership atom ``S(c)`` of every
    sorted constant ``c:S`` of the goal or of a premise: ``to_z3()`` reads a
    sorted constant as the plain constant, so without the atom the guard
    reading forgets which sort it was written in. Shared by :class:`Z3Backend`
    and :func:`z3_relevant_premises` so both decide the exact same many-sorted
    entailment — see :func:`_z3_track_and_check`'s ``z3_sort_axioms`` parameter
    for why these are added UNTRACKED rather than as more ``p<i>``-tagged
    premises. Empty for an unsorted query.
    """
    from ..fol._msfl_nodes import sort_axioms
    return [axiom.to_z3(env) for axiom in sort_axioms(formula, *premises)]


# ---------------------------------------------------------------------------
# Internal backends: the kit's own calculi and semantic searches
# ---------------------------------------------------------------------------

#: The tracking literals of :func:`_z3_track_and_check` are Boolean constants whose Z3
#: symbol is an INTEGER symbol (``Z3_mk_int_symbol``), numbered from this base. Every name
#: the kit writes into a Z3 expression is a STRING symbol, so no formula of any caller --
#: whatever its propositions, predicates and sorts are called -- can hold a symbol equal to a
#: tag: a proposition named ``goal`` or ``p0`` is another constant. The base keeps the numbers
#: clear of the ones Z3 itself gives its own fresh constants (small counters).
_Z3_TAG_BASE = 1 << 29


def _z3_tag(number: int):
    """The tracking literal number ``number``: 0 is the negated goal's, ``1 + i`` premise ``i``'s."""
    from z3 import BoolRef, BoolSort, Z3_mk_const, Z3_mk_int_symbol, main_ctx

    ctx = main_ctx()
    symbol = Z3_mk_int_symbol(ctx.ref(), _Z3_TAG_BASE + number)
    return BoolRef(Z3_mk_const(ctx.ref(), symbol, BoolSort(ctx).ast), ctx)


def _z3_tag_number(decl) -> Optional[int]:
    """The number of the tracking literal that the Z3 declaration ``decl`` is, or ``None``.

    A declaration is a tracking literal exactly when it has no argument, returns ``Bool`` and
    is named by an integer symbol of the band :data:`_Z3_TAG_BASE` and above (see there), which
    no symbol of a kit formula is.
    """
    from z3 import BoolSort, Z3_INT_SYMBOL, Z3_get_decl_name, Z3_get_symbol_int, Z3_get_symbol_kind

    if decl.arity() != 0 or decl.range() != BoolSort(decl.ctx):
        return None
    ref = decl.ctx.ref()
    symbol = Z3_get_decl_name(ref, decl.ast)
    if Z3_get_symbol_kind(ref, symbol) != Z3_INT_SYMBOL:
        return None
    value = Z3_get_symbol_int(ref, symbol)
    return value - _Z3_TAG_BASE if value >= _Z3_TAG_BASE else None


def _z3_core_numbers(solver) -> list:
    """The numbers of the tracking literals in ``solver.unsat_core()`` (0 is the goal, ``1 + i`` premise ``i``)."""
    numbers = (_z3_tag_number(tag.decl()) for tag in solver.unsat_core())
    return sorted(number for number in numbers if number is not None)


def _z3_core_names(solver) -> list:
    """The unsat core of ``solver`` as the names a proof reports: ``"goal"`` and ``"p<i>"`` (0-based)."""
    return [("goal" if number == 0 else f"p{number - 1}") for number in _z3_core_numbers(solver)]


def _z3_track_and_check(z3_formula, z3_premises: Sequence, timeout: int,
                        z3_sort_axioms: Sequence = ()):
    """Run ONE per-call Z3 ``Solver``, tracking every assertion by name.

    Asserts ``Not(z3_formula)`` under the tag ``"goal"`` and each of
    ``z3_premises`` under ``"p<i>"`` (0-based), via ``assert_and_track``,
    with ``unsat_core=True`` set on THIS solver instance only — never
    ``z3.set_param(proof=True)``, which is a process-wide global that would
    change solving behaviour for every other Z3 consumer in the kit
    (semantics evaluators, dl, chem, finite-model, modal/second/third-order
    — anything sharing the module-level ``_SORT``/default context in
    ``fol/_fol_nodes.py``) for the rest of the process.

    ``z3_sort_axioms`` (see
    :func:`~unicode_logic_kit.fol._msfl_nodes.sort_axioms`: every sort is
    non-empty, and a sorted constant ``c:S`` is in ``S``) are added with a
    plain, UNTRACKED ``solver.add`` — they are background MSFOL convention,
    never one of the caller's own premises, so they must never gain a ``p<i>``
    tag: that would make an untranslatable, caller-invisible synthetic sentence
    show up in :class:`Z3Backend`'s ``proof`` unsat core or in
    :func:`z3_relevant_premises`'s reported indices, which are defined purely
    over the CALLER's own ``premises`` list. They are asserted OUTSIDE the
    negated goal: a membership atom under the goal's negation would be
    something to prove. Empty (the default) for an unsorted query, so the
    solver call is byte-for-byte the same as before this parameter existed.

    **The tags are named by integer symbols.** A proposition of a problem can be
    called anything, ``goal`` and ``p0`` included (the Prover9 and SMT-LIB readers
    produce such propositions); a tag spelled like one would be the very proposition,
    assumed true, and would prove any goal. So a tag is a Boolean constant with an
    integer symbol (:func:`_z3_tag`), a kind of name that no string a formula carries
    can be, and the names ``"goal"`` / ``"p<i>"`` are only what a proof REPORTS
    (:func:`_z3_core_names`).

    Built once and shared by :class:`Z3Backend` (C12: a per-verdict
    ``z3_unsat_core`` proof certificate) and :func:`z3_relevant_premises`
    (C11: which premises a PROVED entailment actually needed) so both read
    the exact same assert-and-track call shape rather than drifting apart —
    including the identical sort axioms, so the two can never disagree about
    whether a many-sorted entailment holds.

    Returns ``(result, solver)`` — ``result`` is Z3's own
    ``sat``/``unsat``/``unknown``; on ``unsat``, ``solver.unsat_core()``
    holds the tracked-name subset Z3 actually used. That subset is SOUND
    (re-asserting just it is still unsat) but not necessarily MINIMAL (Z3's
    core extraction is not obliged to find the smallest one) — callers that
    need "used" language should say "relevant"/"a sufficient subset", never
    "the minimal set".
    """
    from z3 import Solver, Not as _ZNot

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.set(unsat_core=True)
    for axiom in z3_sort_axioms:
        solver.add(axiom)
    for i, p in enumerate(z3_premises):
        solver.assert_and_track(p, _z3_tag(1 + i))
    solver.assert_and_track(_ZNot(z3_formula), _z3_tag(0))
    return solver.check(), solver


def _z3_model_assignment(model, n_premises: int = 0) -> Dict[str, str]:
    """Read a satisfying ``z3.ModelRef`` back into a ``{name: value}`` dict.

    ``assert_and_track``'s own tracking booleans (see :func:`_z3_track_and_check`)
    are 0-ary Bool-sorted Z3 declarations, so they show up in ``model.decls()``
    right alongside the formula's real symbols and would otherwise leak into a
    REFUTED verdict's witness as spurious extra keys. They are excluded by what
    they are, not by their spelling: a tag is a constant with an integer symbol
    (:func:`_z3_tag_number`), and no symbol of a formula is, so a proposition
    named ``goal`` or ``p0`` is reported like any other. ``n_premises`` is not
    needed to recognise a tag and is accepted for the callers that pass it.

    A name that the model declares more than once (``P`` at two arities, a
    function and a predicate of one name) is two symbols and is reported under
    ``"P/1"`` / ``"P/2"`` keys instead of one overwriting the other — see
    :func:`~unicode_logic_kit.atp.z3_models.declaration_keys`; a name declared
    once keeps its plain name.
    """
    from .z3_models import model_assignment

    return model_assignment(model, skip=lambda d: _z3_tag_number(d) is not None)


def z3_relevant_premises(formula: Node, premises: Sequence[Node] = (),
                         timeout: int = 10000) -> Optional[Tuple[int, ...]]:
    """Which of ``premises`` did Z3 actually need to prove ``⊨ formula``?

    Runs the same :func:`_z3_track_and_check` per-``Solver`` assert-and-track
    call :class:`Z3Backend` uses for its own ``proof`` certificate — including
    the same many-sorted axioms (non-emptiness of every sort, membership of
    every sorted constant) when ``formula``/``premises`` use a sort
    (:func:`_z3_sort_axioms`), so this always agrees with
    :class:`Z3Backend` about whether the entailment holds — but reports only
    the premise side of the core, as 0-based indices into ``premises`` (never
    including the ``"goal"`` tag itself — the negated conclusion is always
    "needed" trivially, so it carries no information about which PREMISES
    were relevant; the sort axioms are untracked, so they can never appear in
    the core either — see :func:`_z3_track_and_check`).

    Args:
        formula: the goal.
        premises: candidate premises (same fragment ``Z3Backend``/
            ``Node.to_z3`` decides — uninterpreted sort + equality, no
            arithmetic; substructural nodes are outside it).
        timeout: milliseconds, forwarded to the solver exactly as
            ``Z3Backend.decide`` forwards its own ``timeout``.

    Returns:
        A sorted tuple of 0-based premise indices, or ``None`` when there is
        nothing sound to report: the entailment does not hold (Z3 finds it
        SAT or times out UNKNOWN — there is no "used premises" answer for a
        non-theorem), or the fragment is unsupported (``to_z3`` raises
        ``NotImplementedError`` on ``formula`` or any premise). ``None`` is
        the honest "don't know" answer here, never a guessed subset.

        The returned set is SOUND but not necessarily MINIMAL — see
        :func:`_z3_track_and_check`'s docstring; a genuinely redundant
        premise (one that, alone, already suffices) need not appear
        alongside the other route to the same conclusion, but two premises
        that are each independently sufficient are not guaranteed to be
        pruned down to a single one either — only that the returned subset
        itself is enough.
    """
    from ..fol.nodes import Z3Env

    premises = list(premises)
    try:
        env = Z3Env()
        z3_formula = formula.to_z3(env)
        z3_premises = [p.to_z3(env) for p in premises]
        z3_sorts = _z3_sort_axioms(formula, premises, env)
    except NotImplementedError:
        return None

    from z3 import unsat

    res, solver = _z3_track_and_check(z3_formula, z3_premises, timeout, z3_sorts)
    if res != unsat:
        return None
    return tuple(sorted({number - 1 for number in _z3_core_numbers(solver) if number > 0}))


class Z3Backend(ProverBackend):
    """Classical FOL/MSFOL via Z3 — tri-state, with a model on refutation.

    Many-sorted input: a sort's non-emptiness and the membership of every
    sorted constant in its sort (the MSFOL convention — see the
    classical-reasoning guide's many-sorted section) are asserted as extra,
    untracked, UNNEGATED premises alongside ``premises`` — see
    :func:`_z3_sort_axioms` and :func:`_z3_track_and_check` — never folded
    inside ``Node.to_z3()`` itself, which stays polarity-blind. This is what
    makes a REFUTED verdict's countermodel always a legal MSFOL structure (no
    sort empty, every sorted constant inside its sort) instead of exploiting a
    loophole ``semantics.modelfinder`` never considers, and what makes
    ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` PROVED.
    """

    name = "z3"
    logics = frozenset({"fol"})
    external = False                 # z3-solver is a hard dependency

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from z3 import sat, unsat
        from ..fol.nodes import Z3Env

        premises = list(premises)
        try:
            # ONE environment for the goal and every premise: a numeral and a
            # constant of the same text are refused wherever they meet, and
            # one name at two arities stays two symbols across the problem.
            env = Z3Env()
            z3_formula = formula.to_z3(env)
            z3_premises = [p.to_z3(env) for p in premises]
            z3_sorts = _z3_sort_axioms(formula, premises, env)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))

        (res, solver), elapsed = _timed(
            lambda: _z3_track_and_check(z3_formula, z3_premises, timeout, z3_sorts))
        if res == unsat:
            # A tracked-name unsat core, per _z3_track_and_check's docstring:
            # sound (re-asserting just these is still unsat, see the C12
            # soundness self-check test) but not necessarily minimal.
            core = sorted(_z3_core_names(solver))
            proof = {"kind": "z3_unsat_core", "core": core}
            return Verdict(PROVED, self.name, wall_time=elapsed, proof=proof)
        if res == sat:
            assignment = _z3_model_assignment(solver.model(), len(z3_premises))
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "z3_model", "assignment": assignment})
        why = solver.reason_unknown()
        reason = "timeout" if ("timeout" in why or "cancel" in why) else "incomplete"
        return Verdict(UNKNOWN, self.name, reason=reason, wall_time=elapsed, detail=why)


class TableauBackend(ProverBackend):
    """The kit's own classical analytic tableau (Z3-free).

    Complete and decidable propositionally; on first-order inputs a
    non-closure is only "no closed tableau within the bounds" → bound_hit.
    The bounds are ``max_steps`` (which also bounds the length of a branch: the
    search is a loop over a branch, it does not depend on the interpreter's
    recursion limit), ``max_terms`` and the call's ``timeout`` (a run that used it
    up is ``timeout``, not ``bound_hit``). A formula nested deeper than the helpers
    that walk it can follow within the recursion limit is a bound too: the verdict
    is ``unknown`` / ``bound_hit`` and its ``detail`` names the nesting depth
    (:func:`~unicode_logic_kit.atp.tableau.nesting_depth`). Many-sorted input is
    searched through its guard image with the sort axioms as further formulas to
    refute (see :func:`~unicode_logic_kit.atp.tableau.tableau_closed`).
    """

    name = "tableau"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        # The detailed route records a TableauProof alongside the same
        # search (recording never changes the verdict — regression-pinned
        # in test_tableau_check.py), so a PROVED Verdict can carry the
        # independently checkable proof dict.
        from .tableau import _search_detailed

        try:
            (proof, nesting), elapsed = _timed(
                lambda: _search_detailed(list(premises), formula,
                                         timeout=timeout, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if proof is not None:
            try:
                encoded = proof.to_dict()
            except RecursionError:
                encoded = None       # a proof too deeply nested to serialise is still a proof
            return Verdict(PROVED, self.name, wall_time=elapsed, proof=encoded)
        if nesting is not None:
            import sys
            return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                           detail=f"a formula nested {nesting} levels deep is deeper than "
                                  "the tableau's recursive helpers can walk within the "
                                  f"interpreter's recursion limit ({sys.getrecursionlimit()}): "
                                  "no closed tableau was found")
        if elapsed * 1000 >= timeout:
            return Verdict(UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                           detail=f"no closed tableau within the {timeout} ms limit")
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="no closed tableau within max_steps/max_terms")


class ResolutionBackend(ProverBackend):
    """The kit's own resolution prover (given-clause saturation).

    The underlying bool API cannot distinguish saturation from a hit step
    bound, so a False is reported as UNKNOWN/bound_hit — never as REFUTED.
    Many-sorted input gets its sort axioms (every sort non-empty, every sorted
    constant in its sort) as premise clauses from
    :func:`~unicode_logic_kit.atp.resolution.prove`. The call's ``timeout`` bounds the
    saturation; a run that used it up is ``timeout``, not ``bound_hit``.
    """

    name = "resolution"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .resolution import prove as resolution_prove

        try:
            proved, elapsed = _timed(
                lambda: resolution_prove(list(premises), formula, timeout=timeout,
                                         **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, wall_time=elapsed)
        if elapsed * 1000 >= timeout:
            return Verdict(UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                           detail=f"not refuted within the {timeout} ms limit")
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="not refuted within max_steps (saturation not distinguished)")


class ModelFinderBackend(ProverBackend):
    """The kit's finite model finder — a refutation-only semantic backend.

    Finding a finite structure that satisfies the premises but not the
    conclusion REFUTES the entailment; exhausting the size bound proves
    nothing (FOL has no finite model property) → bound_hit. The call's
    ``timeout`` ends the search at a candidate structure; a search that it cut
    off is ``timeout``, not ``bound_hit``.
    """

    name = "modelfinder"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..semantics.modelfinder import search_countermodel

        try:
            search, elapsed = _timed(
                lambda: search_countermodel(list(premises), formula, timeout=timeout,
                                            **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if search.structure is not None:
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "finite_structure",
                                         "repr": repr(search.structure)})
        if search.timed_out:
            return Verdict(UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                           detail=f"no countermodel found within the {timeout} ms limit")
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="no countermodel up to the size bound")


class ModalTableauBackend(ProverBackend):
    """The kit's labelled modal tableau — tri-state with Kripke witnesses."""

    name = "modal-tableau"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .modal_tableau import _decide_explained, modal_countermodel

        goal = _implication(formula, premises)
        try:
            (status, too_deep), elapsed = _timed(
                lambda: _decide_explained(goal, timeout=timeout, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="modal",
                           reason="unsupported", detail=str(exc))
        if status == "valid":
            return Verdict(PROVED, self.name, logic="modal", wall_time=elapsed)
        if status == "invalid":
            # The witness is a second search; it gets what is left of the limit.
            cm = modal_countermodel(goal, timeout=max(1, int(timeout - elapsed * 1000)),
                                    **options)
            witness = None
            if cm is not None:
                from .kripke_enum import kripke_model_to_dict
                witness = {"kind": "kripke", "repr": repr(cm),
                           "data": kripke_model_to_dict(cm)}
            return Verdict(REFUTED, self.name, logic="modal", wall_time=elapsed,
                           countermodel=witness)
        # modal_decide answers "unknown" both for an exhausted budget and for
        # the temporal-closure operators it has no rule for (G/F/U/H/O/P/S,
        # classified "unsupported" internally) — tell them apart here so the
        # reason axis stays honest.
        from .modal_tableau import _TEMPORAL_CLOSURE
        if any(isinstance(n, _TEMPORAL_CLOSURE) for n in goal.walk()):
            return Verdict(UNKNOWN, self.name, logic="modal", reason="unsupported",
                           wall_time=elapsed,
                           detail="temporal closure operators (G/F/U/…) have no "
                                  "tableau rule here for the kit's general Kripke "
                                  "frame — for the STANDARD linear-time reading, "
                                  "the 'ltl-tableau' backend (atp.ltl_tableau) is "
                                  "a complete decision procedure and the "
                                  "definitive route; 'qml' and 'isabelle' decide "
                                  "the general (possibly non-linear) frame "
                                  "instead, soundly but not completely")
        if too_deep:
            # One of the tableau's walks over the formula ran into the interpreter's recursion
            # limit, which is one of its bounds: the formula was not read to its end.
            import sys
            from .tableau import nesting_depth
            return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                           wall_time=elapsed,
                           detail=f"a formula nested {nesting_depth(goal)} levels deep is deeper "
                                  "than the tableau's recursive walks can follow within the "
                                  f"interpreter's recursion limit ({sys.getrecursionlimit()}): "
                                  "nothing was decided")
        if elapsed * 1000 >= timeout:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no verdict within the {timeout} ms limit")
        return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                       wall_time=elapsed,
                       detail="tableau budget exhausted (max_worlds/max_steps)")


class QmlBackend(ProverBackend):
    """Quantified modal logic via the FO embedding + Z3 — sound, incomplete.

    ``True`` is a proof; ``False`` only means "not proven" (undecidable
    fragment), so it is reported as UNKNOWN/incomplete, never as REFUTED.
    """

    name = "qml"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..fol.qml import qml_is_valid

        goal = _implication(formula, premises)
        try:
            proved, elapsed = _timed(
                lambda: qml_is_valid(goal, timeout=timeout, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="modal",
                           reason="unsupported", detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, logic="modal", wall_time=elapsed)
        return Verdict(UNKNOWN, self.name, logic="modal", reason="incomplete",
                       wall_time=elapsed,
                       detail="Z3 did not close the embedded goal (FO modal logic is undecidable)")


# ---------------------------------------------------------------------------
# External backends
# ---------------------------------------------------------------------------

class IsabelleBackend(ProverBackend):
    """Isabelle/HOL via the kit's runner — the most trusted external route.

    Deliberately NOT in any default chain: one decision spawns a real
    ``isabelle build`` (minutes of wall time), so it runs only when requested
    by name. ``ModalVerdict``/``FolVerdict`` map 1:1 onto :class:`Verdict`
    (their ``infra_error`` becomes reason="infra" detail on UNKNOWN).

    The classical route decides with ``native_equality=True``: ``=`` is HOL
    identity, as in every other backend's semantics. With the embedding's
    uninterpreted ``feq`` a nitpick countermodel is one for FOL *without*
    identity, so ``∀x (x = x)`` came back REFUTED. Passing
    ``native_equality=False`` is refused for that reason. The modal route makes
    the same choice by a different road: since 0.30.0 its embedding reads ``=``
    as RIGID identity (HOL's own, no world argument) and the Kripke evaluator it
    falls back on for a countermodel refuses an identity atom by name rather
    than reading it as an ordinary atom, so neither half of that route can
    answer a question about identity without interpreting it.
    """

    name = "isabelle"
    logics = frozenset({"fol", "modal"})
    external = True

    def available(self) -> bool:
        from ..hol.isabelle_runner import isabelle_available
        return isabelle_available()

    def available_for(self, options: dict) -> bool:
        """Whether the installation :meth:`decide` will run is there: the one a call
        names with ``install=`` (an :class:`~unicode_logic_kit.hol.isabelle_runner.IsabelleInstall`,
        which the runner uses instead of looking), else :meth:`available`."""
        if options.get("install") is not None:
            return True
        return self.available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        goal = _implication(formula, premises)
        logic = options.pop("logic", None) or (
            "modal" if _looks_modal(goal) else "fol")

        if logic == "modal":
            from ..hol.isabelle_runner import isabelle_decide_modal
            verdict, elapsed = _timed(lambda: isabelle_decide_modal(goal, **options))
        else:
            from ..hol.isabelle_runner import isabelle_decide_fol
            if not options.pop("native_equality", True):
                raise ValueError(
                    "isabelle backend: native_equality=False would decide FOL without "
                    "identity (uninterpreted feq), so a REFUTED verdict could contradict "
                    "every other backend; call hol.isabelle_runner.isabelle_decide_fol "
                    "directly for that reading.")
            verdict, elapsed = _timed(
                lambda: isabelle_decide_fol(goal, native_equality=True, **options))

        if verdict.status == "valid":
            return Verdict(PROVED, self.name, logic=logic, wall_time=elapsed,
                           detail=verdict.method)
        if verdict.status == "invalid":
            witness = ({"kind": "nitpick" if logic == "fol" else "kripke",
                        "repr": verdict.countermodel}
                       if verdict.countermodel else None)
            return Verdict(REFUTED, self.name, logic=logic, wall_time=elapsed,
                           countermodel=witness)
        reason = "infra" if verdict.infra_error else "incomplete"
        return Verdict(UNKNOWN, self.name, logic=logic, reason=reason,
                       wall_time=elapsed, detail=verdict.infra_error)


class Prover9Backend(ProverBackend):
    """Prover9 via subprocess. Discovery: $UFK_PROVER9, then PATH.

    Set ``UFK_PROVER9_WSL=1`` when the binary is a Linux build reached through
    WSL on a Windows host (``$UFK_PROVER9`` then names the path INSIDE WSL, for
    example ``/mnt/d/prover9/Prover9-LADR-2026-8A/bin/prover9``); the ``use_wsl``
    option does the same for one call, as for the Vampire backend.

    A run without ``THEOREM PROVED`` is UNKNOWN / ``"incomplete"`` (Prover9's
    exit does not certify invalidity), EXCEPT a problem Prover9 refused to read
    (its fatal-error exit) or a binary that could not be started (a path that
    does not exist inside WSL): that is ERROR / ``"infra"`` with Prover9's own
    (or the shell's) message in ``detail``, and a run the kit stopped because the
    ``timeout`` (milliseconds, as for every backend) ran out: that is UNKNOWN /
    ``"timeout"``.

    A free variable of the problem is one unknown element, the same in every premise and in
    the conclusion (the problem writer replaces it by a constant of its own: Prover9 itself
    would close each formula universally, which is another question), so ``P(x) ⊢ P(alpha)``
    is not proved. A Łukasiewicz connective has no classical reading and is refused:
    UNKNOWN / ``"unsupported"`` with the name of the connective in ``detail``.
    """

    name = "prover9"
    logics = frozenset({"fol"})
    external = True

    @staticmethod
    def _binary() -> Optional[str]:
        import os
        return os.environ.get("UFK_PROVER9") or shutil.which("prover9")

    @staticmethod
    def _uses_wsl() -> bool:
        """Whether ``$UFK_PROVER9_WSL`` says the binary lives inside WSL."""
        import os
        return os.environ.get("UFK_PROVER9_WSL") == "1"

    def available(self) -> bool:
        return self.available_for({})

    def available_for(self, options: dict) -> bool:
        """Whether the binary the run will use is there: the one :meth:`decide`
        resolves (``prover9_path=``, else ``$UFK_PROVER9``, else ``prover9`` on
        PATH), looked for where :meth:`decide` will run it. With the WSL switch on
        (``use_wsl=True`` in ``options``, else ``$UFK_PROVER9_WSL=1``) that is
        inside WSL (see :func:`_wsl_has_binary`), not on this host's PATH. A native
        ``prover9_path=`` that names no file this host can start, and no command on
        PATH, is refused here by name instead of failing inside the run; what
        ``$UFK_PROVER9`` names is taken as the installation the user pointed at."""
        explicit = options.get("prover9_path")
        path = explicit or self._binary()
        if path is None:
            return False
        if options.get("use_wsl", self._uses_wsl()):
            return _wsl_has_binary(path)
        if explicit:
            return _native_command_exists(explicit)
        return True

    #: The banner line Prover9 prints first: ``Prover9 (64) version 2026-8A, August 2026.``
    _BANNER_LINE = re.compile(r"^[ \t]*(Prover9\b[^\r\n]*\bversion\b[^\r\n]*?)[ \t]*$", re.MULTILINE)

    @classmethod
    def _banner(cls, path: str, use_wsl: bool) -> Optional[str]:
        """The banner line of the Prover9 at ``path`` (through ``wsl.exe`` when
        ``use_wsl``), or ``None``.

        Prover9 has no ``--version``: it takes the flag for a resume directory and
        ends with a fatal error (exit 1), so :func:`_binary_version` reads nothing
        from it. ``-h`` prints the banner first and exits 0 at once; the line that
        names the version is the one that starts with ``Prover9`` and holds the word
        ``version``. The tool never reads this process's standard input (``stdin`` is
        the null device) and the probe has a time limit, so it cannot block. The
        result, a miss too, is memoized per ``(path, use_wsl)`` in the process-local
        version cache that :func:`_binary_version` fills for the other tools, never
        probed twice; nothing here raises.
        """
        key = (path, use_wsl)
        if key in _VERSION_CACHE:
            return _VERSION_CACHE[key]
        import subprocess

        banner: Optional[str] = None
        try:
            cmd = ["wsl.exe", path, "-h"] if use_wsl else [path, "-h"]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                                  stdin=subprocess.DEVNULL)
            for stream in (proc.stdout, proc.stderr):
                found = cls._BANNER_LINE.search(stream or "")
                if found:
                    banner = found.group(1)
                    break
        except (OSError, subprocess.TimeoutExpired, UnicodeError):
            banner = None
        _VERSION_CACHE[key] = banner
        return banner

    def solver_version(self) -> Optional[str]:
        """Prover9's banner line (``Prover9 (64) version 2026-8A, August 2026.``), for
        whichever binary discovery (``$UFK_PROVER9``/PATH, ``$UFK_PROVER9_WSL``)
        resolves to right now — the same default :meth:`available` uses. Read by
        :meth:`_banner` (``prover9 -h``: the binary has no ``--version``), memoized
        per ``(binary, use_wsl)`` for the life of the process, never reading this
        process's standard input and never blocking. ``None`` when no binary is
        currently discoverable or the banner cannot be read; a per-call
        ``prover9_path=``/``use_wsl=`` override is reflected in THAT call's own
        ``Verdict.solver_version`` (see :meth:`decide`), not here —
        see :func:`_binary_version`'s module-level docstring section for why
        this method answers for the default binary only.
        """
        path = self._binary()
        if path is None:
            return None
        return self._banner(path, self._uses_wsl())

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .prover9_entailment import (
            Prover9Rejected, Prover9TimedOut, check_logical_entailment,
        )

        path = options.pop("prover9_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "prover9: no binary found (set $UFK_PROVER9 or put 'prover9' on PATH)")
        use_wsl = options.pop("use_wsl", self._uses_wsl())
        solver_version = self._banner(path, use_wsl)
        start = time.perf_counter()
        try:
            proved, elapsed = _timed(
                lambda: check_logical_entailment(list(premises), formula, path,
                                                 raise_on_rejection=True,
                                                 timeout=max(1, timeout // 1000),
                                                 raise_on_timeout=True,
                                                 use_wsl=use_wsl))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        except Prover9TimedOut as exc:
            # The kit's wall-clock budget ran out and the kit stopped Prover9: a
            # timeout, said as one -- not a search that "found no proof".
            return Verdict(UNKNOWN, self.name, reason="timeout",
                           wall_time=time.perf_counter() - start,
                           solver_version=solver_version, detail=str(exc))
        except Prover9Rejected as exc:
            # Prover9 refused to read the problem (its documented fatal exit):
            # an error carrying Prover9's own message, not "found no proof".
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=_rejection_detail(
                               "prover9", exc.output,
                               f"exit code {exc.returncode} and no THEOREM PROVED line"))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version, detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           solver_version=solver_version)
        return Verdict(UNKNOWN, self.name, reason="incomplete", wall_time=elapsed,
                       solver_version=solver_version,
                       detail="Prover9 found no proof (its exit does not certify invalidity)")


class VampireBackend(ProverBackend):
    """Vampire via subprocess. Discovery: $UFK_VAMPIRE, then PATH.

    Set ``UFK_VAMPIRE_WSL=1`` when the binary is a Linux build reached
    through WSL on a Windows host.

    Decides through the SZS/TSTP route
    (:func:`~unicode_logic_kit.atp.vampire_entailment.check_entailment_vampire_detailed`):
    the verdict's ``szs_status`` is Vampire's own status line verbatim, a
    ``CounterSatisfiable`` answer becomes an honest REFUTED (Vampire's
    saturation certifies invalidity, though it yields no model structure —
    ``countermodel`` stays ``None``), and a PROVED verdict carries the parsed
    TSTP derivation DAG in ``proof``. A problem Vampire REFUSES to read (its
    ``User error: ...`` or parse error, with no SZS status line) is ERROR /
    ``"infra"`` with Vampire's own message in ``detail`` — never an UNKNOWN
    that reads like a timeout; its own ``GaveUp`` / ``ResourceOut`` /
    ``Unknown`` and a real subprocess timeout keep their UNKNOWN verdicts. So
    does a run that printed no SZS line but DID print how its search ended
    (``Termination reason: Refutation not found, incomplete strategy`` —
    Vampire's way of giving up on a non-theorem of a typed-arithmetic problem):
    UNKNOWN / ``"incomplete"``, with the termination reason in ``detail``.

    Options (through ``**options``, like the E / Zipperposition backend, and
    read the same way): ``vampire_path`` / ``use_wsl`` pick the binary, and
    ``tff`` / ``sort`` pick the TPTP dialect it is given. ``sort`` (``'real'``
    or ``'int'``; ``None`` by default) opts into the single-numeric-sort typed
    arithmetic route UNCONDITIONALLY when given, taking priority over ``tff``;
    with ``sort=None``, ``tff=None`` tries the many-sorted typed route whenever
    the problem uses a sort, and ``True`` / ``False`` force the typed / the
    ``fof`` route. The typed writer refuses a problem whose typed text would not
    ask the kit's question (see :class:`~unicode_logic_kit.atp.tptp_tff.Tf0Refusal`):
    with ``tff=None`` the problem is then written as ``fof`` and the verdict's
    ``detail`` says that it was, and why; with ``tff=True`` the refusal is the
    verdict, ``UNKNOWN`` / ``"unsupported"`` with the writer's message in
    ``detail`` (never an exception). The options reach
    :func:`~unicode_logic_kit.atp.vampire_entailment.check_entailment_vampire_detailed`
    unchanged.

    **Which premises a proof used.** Vampire prints ``unknown`` for the name of an
    axiom unless it is asked for the names, so the backend asks (``axiom_names=``,
    on unless a call turns it off) and names the premises' ``axiom`` lines
    (``premise_names=``, ``premise_<i>`` when not given). A PROVED verdict then
    carries the caller's premise indices that the proof's axiom leaves are in
    ``relevant_premises`` (the sorted 0-based indices into the caller's ``premises``,
    ``()`` for a proof that needs none), and its ``detail`` names the background facts
    of a sorted reading the proof used (the non-emptiness of a sort, the membership
    of a sorted constant), which are not premises. ``relevant_premises`` stays
    ``None`` for a verdict that is not PROVED, and for a proof whose axiom leaves
    cannot be read back through the problem's own names (never a guess). The set is
    sound but not necessarily minimal, like every report of this kind.
    """

    name = "vampire"
    logics = frozenset({"fol"})
    external = True

    @staticmethod
    def _binary() -> Optional[str]:
        import os
        return os.environ.get("UFK_VAMPIRE") or shutil.which("vampire")

    def available(self) -> bool:
        return self.available_for({})

    def available_for(self, options: dict) -> bool:
        """Whether the binary the run will use is there: the one :meth:`decide`
        resolves (``vampire_path=``, else ``$UFK_VAMPIRE``, else ``vampire`` on
        PATH), looked for where :meth:`decide` will run it. With the WSL switch on
        (``use_wsl=True`` in ``options``, else ``$UFK_VAMPIRE_WSL=1``) that is
        inside WSL (see :func:`_wsl_has_binary`), not on this host's PATH. A native
        ``vampire_path=`` that names no file this host can start, and no command on
        PATH, is refused here by name instead of failing inside the run; what
        ``$UFK_VAMPIRE`` names is taken as the installation the user pointed at."""
        import os

        explicit = options.get("vampire_path")
        path = explicit or self._binary()
        if path is None:
            return False
        if options.get("use_wsl", os.environ.get("UFK_VAMPIRE_WSL") == "1"):
            return _wsl_has_binary(path)
        if explicit:
            return _native_command_exists(explicit)
        return True

    def solver_version(self) -> Optional[str]:
        """Vampire's ``--version`` banner (first line), for whichever binary
        discovery (``$UFK_VAMPIRE``/PATH, ``$UFK_VAMPIRE_WSL``) resolves to
        right now — the same default :meth:`available` uses. Memoized per
        ``(binary, use_wsl)`` for the life of the process via
        :func:`_binary_version`. ``None`` when no binary is currently
        discoverable; a per-call ``vampire_path=``/``use_wsl=`` override is
        reflected in THAT call's own ``Verdict.solver_version`` (see
        :meth:`decide`), not here — see :func:`_binary_version`'s
        module-level docstring section for why this method answers for the
        default binary only.
        """
        import os

        path = self._binary()
        if path is None:
            return None
        use_wsl = os.environ.get("UFK_VAMPIRE_WSL") == "1"
        return _binary_version(path, use_wsl)

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        import os
        from .vampire_entailment import _ended_by_itself, check_entailment_vampire_detailed
        from .tstp import background_use_note

        path = options.pop("vampire_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "vampire: no binary found (set $UFK_VAMPIRE or put 'vampire' on PATH)")
        use_wsl = options.pop("use_wsl", os.environ.get("UFK_VAMPIRE_WSL") == "1")
        tff = options.pop("tff", None)
        if tff not in (None, True, False):
            raise ValueError(
                f"vampire: tff= is None (decide from the formula), True or False, "
                f"got {tff!r}.")
        sort = options.pop("sort", None)
        premise_names = options.pop("premise_names", None)
        axiom_names = options.pop("axiom_names", True)
        solver_version = _binary_version(path, use_wsl)
        try:
            result, elapsed = _timed(lambda: check_entailment_vampire_detailed(
                list(premises), formula, path,
                timeout=max(1, timeout // 1000), use_wsl=use_wsl,
                tff=tff, sort=sort, premise_names=premise_names,
                axiom_names=axiom_names))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version, detail=str(exc))
        status, reason, szs = result["status"], result["reason"], result["szs_status"]
        if status == ERROR:
            # Vampire read the problem and refused it (a type or syntax error:
            # "User error: ..."), or failed outright. Its own message goes in
            # the detail -- a refusal must not read like running out of time.
            evidence = ("no SZS status line in its output" if szs is None
                        else f"SZS status {szs}")
            detail = _rejection_detail("vampire", result.get("output_excerpt", ""),
                                       evidence)
        else:
            detail = (f"SZS status {szs}" if szs is not None
                      else "no SZS status line in Vampire's output")
            if szs is None and status == UNKNOWN:
                # No SZS line: say what DID happen, not what is missing. Either it
                # read the problem and said how its search ended, or the kit's own
                # budget ran out and the kit stopped it before it printed a verdict.
                ended = _ended_by_itself(result.get("output_excerpt", ""))
                if ended is not None:
                    detail = (f"Vampire's search ended on its own (Termination reason: "
                              f"{ended[1]})")
                elif reason == "timeout":
                    detail = (f"the budget of this call ({max(1, timeout // 1000)} s) ran "
                              "out and the kit stopped Vampire before it printed a verdict")
        relevant = None
        if status == PROVED:
            # The caller's premises the proof's axiom leaves are, and the background
            # facts of a sorted reading it used (not premises), as the proof printed them.
            if result.get("relevant_premises") is not None:
                relevant = tuple(result["relevant_premises"])
            detail += background_use_note(tuple(result.get("background_used") or ()))
        if result.get("tff_fallback"):
            # tff=None tried the typed writer for a sorted problem and it refused:
            # the answer is that of the fof text, and the caller is told so and why.
            detail = f"{detail}; {result['tff_fallback']}"
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed, solver_version=solver_version,
                       proof=result["derivation"] if status == PROVED else None,
                       detail=detail, relevant_premises=relevant)


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

def _looks_modal(node: Node) -> bool:
    """Route helper: does the formula contain any modal-family operator?"""
    from .modal_tableau import has_modal
    return has_modal(node)


_REGISTRY: Dict[str, ProverBackend] = {}


def register_backend(backend: ProverBackend) -> None:
    """Register (or replace) a backend under ``backend.name``.

    Third-party code can plug in its own :class:`ProverBackend` here and it
    becomes addressable by every ``prove(backends=[...])`` call.
    """
    if not backend.name:
        raise ValueError("register_backend: backend must set a non-empty name")
    _REGISTRY[backend.name] = backend


_b: ProverBackend      # one name for both registration loops: each backend is a ProverBackend
for _b in (Z3Backend(), TableauBackend(), ResolutionBackend(),
           ModelFinderBackend(), ModalTableauBackend(), QmlBackend(),
           IsabelleBackend(), Prover9Backend(), VampireBackend()):
    register_backend(_b)

# The remaining stock backends live in their own modules (an optional
# dependency, a heavier search, an external prover family) and import THIS
# module's public contract — so they are pulled in here, after that contract
# is fully defined. A deliberate bottom-of-registration import, not an
# accident: keeping the whole stock registry in one place guarantees that
# `default_chain` and `_REGISTRY` can never disagree about what exists,
# whichever submodule a process imports first.
from .clingo_backend import ClingoBackend      # noqa: E402
from .cvc5_backend import Cvc5Backend          # noqa: E402
from .eprover_backend import EProverBackend, ZipperpositionBackend  # noqa: E402
from .hets_backend import HetsBackend          # noqa: E402
from .kripke_enum import KripkeEnumBackend     # noqa: E402
from .leo3_backend import Leo3Backend          # noqa: E402
from .ltl_tableau import LtlTableauBackend     # noqa: E402
from .minizinc_backend import MinizincBackend  # noqa: E402
from .nanocop_backend import NanocopBackend    # noqa: E402
from .twee_backend import TweeBackend          # noqa: E402
# Five individually-reasoned per-logic adapters (C10) — see logic_backends'
# module docstring for why these are NOT a uniform bulk registration.
from .logic_backends import (                  # noqa: E402
    IntBackend, LambekBackend, IllBackend, RelevantBackend, HybridBackend,
)

for _b in (ClingoBackend(), Cvc5Backend(), EProverBackend(), HetsBackend(),
           KripkeEnumBackend(), Leo3Backend(), LtlTableauBackend(), MinizincBackend(),
           NanocopBackend(), TweeBackend(), ZipperpositionBackend(),
           IntBackend(), LambekBackend(), IllBackend(), RelevantBackend(),
           HybridBackend()):
    register_backend(_b)


def get_backend(name: str) -> ProverBackend:
    """Return the backend registered under ``name`` (ValueError if unknown)."""
    if name not in _REGISTRY:
        raise ValueError(
            f"get_backend: unknown backend {name!r} (registered: {sorted(_REGISTRY)})")
    return _REGISTRY[name]


def available_backends(logic: Optional[str] = None) -> Tuple[str, ...]:
    """Names of the currently-available backends, optionally per logic."""
    names = []
    for name, backend in _REGISTRY.items():
        if logic is not None and logic not in backend.logics:
            continue
        if backend.available():
            names.append(name)
    return tuple(sorted(names))


# Default chains: fast, deterministic, and NEVER silently expensive — the
# external minutes-per-call route (isabelle) must be requested by name.
# "kripke-enum" sits between the tableau and qml on purpose: it is the only
# default-chain member that can REFUTE a temporal-closure formula (the
# tableau reports those unsupported, qml is proof-only), and its bounded
# enumeration settles the refutation side before qml's Z3 call can burn its
# full timeout failing to prove an invalid goal.
#
# The five substructural/non-classical entries (C10) are each a SINGLETON
# chain: every one of these logics currently has exactly one decision route
# in the kit, so there is no actual "portfolio race" to order here (unlike
# "fol"/"modal" above) — see logic_backends' module docstring for why these
# five are individually-reasoned adapters, not a uniform bulk registration.
_DEFAULT_CHAINS = {
    "fol": ("z3", "tableau", "resolution", "modelfinder"),
    "modal": ("modal-tableau", "kripke-enum", "qml"),
    "intuitionistic": ("intuitionistic",),
    "lambek": ("lambek",),
    "ill": ("ill",),
    "relevant": ("relevant",),
    "hybrid": ("hybrid",),
}


def default_chain(logic: str) -> Tuple[str, ...]:
    """The default backend order for ``logic`` (ValueError if unknown).

    The chains are static, with ONE documented availability-dependent member:
    when the optional ``cvc5`` extra is installed
    (``pip install unicode-logic-kit[cvc5]``), the FOL chain gains ``"cvc5"``
    directly after ``"z3"`` — a second, fully independent SMT decision
    procedure whose quantifier instantiation (E-matching/enumerative/CEGQI)
    often closes goals Z3's MBQI leaves UNKNOWN, and vice versa. It cannot be
    an unconditional member: a missing backend in the DEFAULT chain would
    make every plain ``prove()`` call raise :class:`BackendUnavailable` on a
    machine without the extra. Every verdict names the backend that actually
    answered (``backend`` / ``agreement``), so provenance stays exact even
    though the chain adapts to the install.
    """
    if logic not in _DEFAULT_CHAINS:
        raise ValueError(
            f"default_chain: unknown logic {logic!r} (use one of {sorted(_DEFAULT_CHAINS)})")
    chain = _DEFAULT_CHAINS[logic]
    if logic == "fol" and _REGISTRY["cvc5"].available():
        chain = chain[:1] + ("cvc5",) + chain[1:]
    return chain


# ---------------------------------------------------------------------------
# Options: which backend of a chain reads which keyword
#
# ``api.prove(f, premises, frame="S4")`` hands ``frame`` to every backend of the
# chain, and what a backend does with a keyword it does not know used to differ
# from one to the next: Z3, E and Zipperposition ignored it, the tableau, the
# resolution prover and the model finder failed with a ``TypeError`` that surfaced
# as an ERROR verdict. An ignored option answers a different question than the
# caller asked. Every stock backend therefore DECLARES the names it reads (below),
# and the dispatcher checks a call against the declarations before anything runs.
# ---------------------------------------------------------------------------

from typing import Callable, FrozenSet  # noqa: E402


def _keywords_of(function, skip: Sequence[str] = ()) -> FrozenSet[str]:
    """The names ``function`` takes by keyword, without ``skip``.

    A backend that forwards ``**options`` to a function with its own keyword list
    reads exactly that list; deriving the set from the signature keeps the
    declaration from drifting away from the function it describes.
    """
    import inspect

    return frozenset(
        name for name, parameter in inspect.signature(function).parameters.items()
        if parameter.kind in (parameter.POSITIONAL_OR_KEYWORD, parameter.KEYWORD_ONLY)
        and name not in skip)


def _keywords(*targets: str, skip: Sequence[str] = ()) -> Callable[[Optional[str]], FrozenSet[str]]:
    """A lazy reader of the keyword names of the functions at ``"module:name"``.

    Several targets give the names ALL of them take (a backend that forwards the
    same options to two functions reads what both read). Lazy, because a backend
    is rarely in the chain and its module is heavy.
    """
    def read(logic: Optional[str] = None) -> FrozenSet[str]:
        import importlib

        names = None
        for target in targets:
            module, _, function = target.partition(":")
            found = _keywords_of(getattr(importlib.import_module(module), function), skip)
            names = found if names is None else names & found
        return names if names is not None else frozenset()
    return read


def _names(*names: str) -> Callable[[Optional[str]], FrozenSet[str]]:
    """A reader of a fixed set of option names."""
    fixed = frozenset(names)

    def read(logic: Optional[str] = None) -> FrozenSet[str]:
        return fixed
    return read


def _isabelle_options(logic: Optional[str] = None) -> FrozenSet[str]:
    """What :class:`IsabelleBackend` reads: the keywords of the runner for the
    logic of the call (both when the logic is not known), plus ``native_equality``,
    which the backend checks itself."""
    from ..hol.isabelle_runner import isabelle_decide_fol, isabelle_decide_modal

    modal = _keywords_of(isabelle_decide_modal, ("formula",))
    classical = _keywords_of(isabelle_decide_fol, ("formula",)) | {"native_equality"}
    if logic == "modal":
        return modal
    if logic == "fol":
        return classical
    return modal | classical


#: The options each stock backend reads, as lazy readers keyed by the backend's
#: class (an exact class: a subclass has to declare its own, through
#: :meth:`ProverBackend.accepted_options`). Every name here is read in the
#: backend's ``decide`` or by the function it forwards ``**options`` to; the test
#: suite compares the two.
_STOCK_OPTIONS: Dict[type, Callable[[Optional[str]], FrozenSet[str]]] = {
    Z3Backend: _names(),
    TableauBackend: _keywords("unicode_logic_kit.atp.tableau:prove_tableau_detailed",
                              skip=("premises", "conclusion", "timeout")),
    ResolutionBackend: _keywords("unicode_logic_kit.atp.resolution:prove",
                                 skip=("premises", "conclusion", "timeout")),
    ModelFinderBackend: _keywords("unicode_logic_kit.semantics.modelfinder:find_countermodel",
                                  skip=("premises", "conclusion", "timeout")),
    ModalTableauBackend: _keywords("unicode_logic_kit.atp.modal_tableau:modal_decide",
                                   "unicode_logic_kit.atp.modal_tableau:modal_countermodel",
                                   skip=("formula", "timeout")),
    QmlBackend: _keywords("unicode_logic_kit.fol.qml:qml_is_valid", skip=("formula", "timeout")),
    IsabelleBackend: _isabelle_options,
    Prover9Backend: _names("prover9_path", "use_wsl"),
    VampireBackend: _keywords("unicode_logic_kit.atp.vampire_entailment:check_entailment_vampire_detailed",
                              skip=("premises", "conclusion", "timeout")),
    EProverBackend: _names("tff", "sort", "premise_names"),
    ZipperpositionBackend: _names("tff", "sort", "premise_names"),
    Cvc5Backend: _names("logic", "random_seed", "proof"),
    ClingoBackend: _names("max_size", "all_different", "verify"),
    MinizincBackend: _names("minizinc_path", "max_size", "solver", "all_different"),
    HetsBackend: _names("reasoner", "translation", "url"),
    TweeBackend: _names("use_wsl", "twee_cmd"),
    NanocopBackend: _names("logic", "domain"),
    Leo3Backend: _names("frame", "domains"),
    KripkeEnumBackend: _keywords("unicode_logic_kit.atp.kripke_enum:modal_enum_search",
                                 skip=("formula", "timeout")),
    LtlTableauBackend: _names("mode", "max_atoms"),
    IntBackend: _keywords("unicode_logic_kit.semantics.intuitionistic:int_countermodel",
                          skip=("formula",)),
    LambekBackend: _names(),
    IllBackend: _keywords("unicode_logic_kit.atp.linear:ill_derivable",
                          skip=("antecedents", "goal")),
    RelevantBackend: _names("max_worlds"),
    HybridBackend: _names("frame", "systems", "temporal_closure"),
}

#: Options that only bound how far a search goes, say how a solver is driven and
#: where it lives, or ask for more to be reported about the same answer (the names
#: of the premises, a proof text). A backend that does not read one still answers the same
#: question without it, so it runs when another backend of the chain reads the
#: option. Every other option changes WHICH question is asked (a modal frame, a
#: domain regime, a bridge, the reading of numerals, a subsort edge): a backend
#: that does not read one would answer a different question, and is not run.
_NEUTRAL_OPTIONS = frozenset({
    "max_steps", "max_terms", "max_worlds", "max_atoms", "max_models", "max_depth",
    "max_size", "max_candidates", "symmetry_breaking", "domain_elements",
    "methods", "refute", "card", "prove_timeout", "refute_timeout",
    "random_seed", "solver", "verify", "install",
    "use_wsl", "vampire_path", "prover9_path", "twee_cmd", "minizinc_path",
    "url", "reasoner", "translation", "tff",
    "premise_names", "axiom_names", "proof",
})


def declared_options(backend: ProverBackend, logic: Optional[str] = None) -> Optional[FrozenSet[str]]:
    """The names of the options ``backend`` reads, or ``None`` when it declares none.

    The backend's own :meth:`~ProverBackend.accepted_options` first, then the
    declaration of the stock class of exactly that type. ``None`` means that
    nothing is known about the backend and it is handed every option.
    """
    own = getattr(backend, "accepted_options", lambda logic=None: None)(logic)
    if own is not None:
        return frozenset(own)
    reader = _STOCK_OPTIONS.get(type(backend))
    return reader(logic) if reader is not None else None


def plan_options(caller: str, chain: Sequence[str], logic: str,
                 options: dict) -> Dict[str, Tuple[dict, Optional[str]]]:
    """Decide which of ``options`` each backend of ``chain`` is handed.

    Returns, per backend name, ``(options to pass, refusal)``. ``refusal`` is
    ``None`` when the backend runs, and otherwise the text of the reason it must
    not: it does not read an option that changes the question (see
    :data:`_NEUTRAL_OPTIONS`) which another backend of the chain does read, so any
    answer of it would be about a different question.

    Raises:
        ValueError: when an option is read by NO backend of the chain, naming the
            option, the chain and what its backends do read, before anything runs.
            A backend that declares no options counts as reading everything.
    """
    if not options:
        return {name: ({}, None) for name in chain}
    declared = {name: declared_options(get_backend(name), logic) for name in chain}
    for option in options:
        if not any(names is None or option in names for names in declared.values()):
            reads = "; ".join(
                f"{name}: " + (", ".join(sorted(names)) if names else "no options")
                for name, names in declared.items())
            raise ValueError(
                f"{caller}: option {option!r} is read by no backend of the chain "
                f"{list(chain)} -- nothing would use it, and the answer would be "
                f"given as if it had not been passed. The options each backend reads: "
                f"{reads}.")
    plan: Dict[str, Tuple[dict, Optional[str]]] = {}
    for name in chain:
        names = declared[name]
        if names is None:
            plan[name] = (dict(options), None)
            continue
        passed = {key: value for key, value in options.items() if key in names}
        unread = sorted(key for key in options
                        if key not in names and key not in _NEUTRAL_OPTIONS)
        if unread:
            shown = ", ".join(repr(key) for key in unread)
            plan[name] = ({}, f"{name} does not read the option {shown}, which "
                              f"changes the question; another backend of the chain "
                              f"reads it, and answering without it would decide a "
                              f"different question, so {name} was not run")
        else:
            plan[name] = (passed, None)
    return plan


def _available_for(backend: ProverBackend, options: dict) -> bool:
    """:meth:`ProverBackend.available_for` of ``backend``, or its ``available()``
    for an object that has no such method."""
    method = getattr(backend, "available_for", None)
    return bool(method(options)) if method is not None else bool(backend.available())


def run_backend(name: str, formula: Node, premises: Sequence[Node] = (),
                timeout: int = 10000, **options) -> Verdict:
    """Run one backend by name, enforcing the availability contract.

    Raises ``ValueError`` for an unknown name and :class:`BackendUnavailable`
    for a known-but-unavailable one; whether it is available is asked for the
    route this call's ``options`` select (:meth:`ProverBackend.available_for`).
    Any unexpected exception inside the
    backend is converted to an ERROR verdict (reason="infra") so a batch run
    over thousands of formulas records the failure instead of dying.
    """
    backend = get_backend(name)
    if not _available_for(backend, options):
        raise BackendUnavailable(
            f"{name}: backend is not available on this machine "
            f"(external={backend.external}) — install it or drop it from `backends`.")
    try:
        return backend.decide(formula, premises, timeout=timeout, **options)
    except (ValueError, BackendUnavailable):
        raise                                    # caller errors stay loud
    except Exception as exc:                     # infra failure → recorded, not fatal
        return Verdict(ERROR, name, reason="infra",
                       detail=f"{type(exc).__name__}: {exc}")
