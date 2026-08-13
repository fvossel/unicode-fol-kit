"""Portfolio scheduling: race several backends, take the first agreed answer.

:mod:`unicode_fol_kit.api`'s ``prove()`` runs a fixed backend chain IN ORDER,
one call at a time — cheap, deterministic, and the right default. This module
is the opposite tool: given an EXPLICIT list of backends, it runs them
CONCURRENTLY and returns as soon as enough of them agree. It is deliberately
opt-in (:func:`portfolio_prove` has no default backend list, unlike
``default_chain``) — racing backends burns more CPU than a sequential chain
for the same query, so a caller must name the routes it wants raced.

Why processes, not threads
---------------------------
Every backend that goes through Z3 shares one process-global Z3 context;
:class:`z3.Solver` is documented as not thread-safe, so two ``decide()``
calls racing in threads of the SAME process can corrupt each other's state
invisibly. Equally important: a native solver call in flight (Z3's C core,
a Prover9/Vampire subprocess wait) cannot be cancelled from a Python thread
— there is no safe way to interrupt it once started. A separate OS process
sidesteps both problems: no shared solver state, and "the loser is still
running" is handled by simply not waiting for it, never by trying to kill
its native call out from under it. Hence ``concurrent.futures.
ProcessPoolExecutor``, exactly like :func:`unicode_fol_kit.eval.batch.
batch_decide` — and the same project-wide cap applies (see memory: "cap all
parallelism at 8"): ``jobs`` is clamped to ``min(jobs, 8)``.

Contract
--------
* ``backends`` is REQUIRED — an unknown name raises ``ValueError`` and a
  known-but-unavailable one raises
  :class:`~unicode_fol_kit.atp.protocol.BackendUnavailable`, checked for
  EVERY name before anything is spawned (never a partial run that discovers
  a bad name three processes in).
* ``require_agreement=1`` (the default): the first DEFINITIVE (proved /
  refuted) verdict wins immediately; every other backend is left running
  (see above) and the executor is shut down without waiting for them.
* ``require_agreement=n>1``: verdicts are tallied by status until ``n``
  backends report the SAME definitive status; the winning ``Verdict`` carries
  ``agreement`` as the tuple of backend names that concurred.
* **Contradiction is a soundness alarm, not something to smooth over.** If
  one backend reports PROVED and another reports REFUTED for the same
  query, that is a live bug in one of the two calculi (or their translation
  to/from the shared AST) — auto-resolving it (e.g. "trust the majority")
  would hide exactly the kind of bug this module exists to catch. The
  result is ``Verdict(status="error", reason="infra", ...)`` naming both
  backends, never a silent pick.
* No backend reaches a definitive verdict within ``require_agreement``
  copies → an UNKNOWN verdict from the pseudo-backend ``"portfolio"``,
  ``detail`` summarising every backend's own answer (mirrors ``prove()``'s
  ``"chain"`` pseudo-backend).
* ``jobs=1`` (forced, or the natural result of a single-element
  ``backends``) never touches ``ProcessPoolExecutor`` — it runs the SAME
  backends sequentially in THIS process. This is not just an optimisation:
  it is also the only way to portfolio-race a backend that was registered
  ad hoc in the calling process (e.g. a test double) and would not be
  importable by name inside a spawned worker.
"""

from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import replace
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol.nodes import Node
from ..fol.serialize import deserialize as _fol_deserialize
from ..fol.serialize import serialize as _fol_serialize
from .protocol import (
    ERROR, PROVED, REFUTED, UNKNOWN,
    BackendUnavailable, Verdict, get_backend, run_backend,
)

__all__ = ["portfolio_prove"]

# Project-wide parallelism cap (see memory: "cap all parallelism at 8").
_MAX_JOBS = 8


# ---------------------------------------------------------------------------
# Agreement tally: shared by the sequential and process-pool paths
# ---------------------------------------------------------------------------

class _Contradiction(Exception):
    """Raised internally when two definitive verdicts disagree.

    Carries the PROVED and REFUTED verdicts that clashed so the caller can
    build the soundness-alarm ``Verdict`` naming both backends.
    """

    def __init__(self, proved: Verdict, refuted: Verdict):
        super().__init__(f"{proved.backend} says proved, {refuted.backend} says refuted")
        self.proved = proved
        self.refuted = refuted


def _feed(agreeing: Dict[str, List[Verdict]], verdict: Verdict,
         require_agreement: int) -> Optional[Verdict]:
    """Fold one DEFINITIVE verdict into the running tally.

    Returns the winning ``Verdict`` (agreement reached), raises
    :class:`_Contradiction` (a proved/refuted split), or returns ``None``
    (keep collecting) — the three, and only three, outcomes of adding one
    more definitive vote.
    """
    if verdict.status == PROVED and agreeing.get(REFUTED):
        raise _Contradiction(verdict, agreeing[REFUTED][0])
    if verdict.status == REFUTED and agreeing.get(PROVED):
        raise _Contradiction(agreeing[PROVED][0], verdict)
    group = agreeing.setdefault(verdict.status, [])
    group.append(verdict)
    if len(group) >= require_agreement:
        first = group[0]
        if len(group) == 1:
            return first
        return replace(first, agreement=tuple(v.backend for v in group))
    return None


def _contradiction_verdict(logic: str, proved: Verdict, refuted: Verdict) -> Verdict:
    """Build the ERROR verdict for a proved/refuted split between backends."""
    return Verdict(
        ERROR, "portfolio", logic=logic, reason="infra",
        detail=(f"soundness alarm: {proved.backend!r} reports proved but "
                f"{refuted.backend!r} reports refuted for the same query — "
                f"not auto-resolved, investigate both backends"),
        agreement=(proved.backend, refuted.backend),
    )


def _unknown_verdict(logic: str, verdicts: List[Verdict]) -> Verdict:
    """Build the collective UNKNOWN verdict when nobody reached agreement."""
    summary = "; ".join(
        f"{v.backend}:{v.status}" + (f"/{v.reason}" if v.reason else "")
        for v in verdicts)
    return Verdict(UNKNOWN, "portfolio", logic=logic,
                   detail=f"no definitive verdict — {summary}" if summary
                   else "empty backend list")


# ---------------------------------------------------------------------------
# Sequential path (jobs == 1): same process, no pool
# ---------------------------------------------------------------------------

def _run_sequential(formula: Node, premises: Sequence[Node], backends: Sequence[str],
                    logic: str, timeout: int, require_agreement: int,
                    options: dict) -> Verdict:
    """Run ``backends`` one at a time in THIS process.

    Used whenever ``jobs`` resolves to 1: either the caller forced it (e.g.
    to portfolio-race a locally-registered test backend that a spawned
    worker could not import) or a single-element ``backends`` made pooling
    pointless.
    """
    agreeing: Dict[str, List[Verdict]] = {}
    verdicts: List[Verdict] = []
    for name in backends:
        extra = dict(options)
        if name == "isabelle":
            extra["logic"] = logic
        verdict = run_backend(name, formula, premises, timeout=timeout, **extra)
        verdicts.append(verdict)
        if verdict.is_definitive:
            try:
                won = _feed(agreeing, verdict, require_agreement)
            except _Contradiction as exc:
                return _contradiction_verdict(logic, exc.proved, exc.refuted)
            if won is not None:
                return won
    return _unknown_verdict(logic, verdicts)


# ---------------------------------------------------------------------------
# Process-pool path (jobs > 1)
# ---------------------------------------------------------------------------

def _verdict_from_dict(d: dict) -> Verdict:
    """Reconstruct a ``Verdict`` from ``Verdict.to_dict()`` (round-trips all fields)."""
    return Verdict(
        status=d["status"], backend=d["backend"], logic=d["logic"],
        reason=d["reason"], szs_status=d["szs_status"], wall_time=d["wall_time"],
        countermodel=d["countermodel"], proof=d["proof"], detail=d["detail"],
        agreement=tuple(d["agreement"]),
    )


def _worker_decide(payload: dict) -> dict:
    """``ProcessPoolExecutor`` target — MUST stay module-level for Windows
    spawn (it pickles the target by qualified name, not by closure).

    ``payload`` carries only JSON-safe, picklable data: the formula and
    premises travel as :mod:`unicode_fol_kit.fol.serialize` envelopes rather
    than raw ``Node`` objects, so this worker does not depend on ``Node``'s
    own pickle-ability. Deserialises, decides through
    :func:`~unicode_fol_kit.atp.protocol.run_backend` (the SAME
    availability/error contract as any other caller), and returns a plain
    ``{"backend", "verdict"}`` dict — itself picklable back to the parent.
    """
    formula = _fol_deserialize(payload["formula"])
    premises = [_fol_deserialize(p) for p in payload["premises"]]
    name = payload["backend"]
    extra = dict(payload["options"])
    if name == "isabelle":
        extra["logic"] = payload["logic"]
    verdict = run_backend(name, formula, premises, timeout=payload["timeout"], **extra)
    return {"backend": name, "verdict": verdict.to_dict()}


def _run_parallel(formula: Node, premises: Sequence[Node], backends: Sequence[str],
                  logic: str, timeout: int, require_agreement: int, n_jobs: int,
                  options: dict) -> Verdict:
    """Race ``backends`` across ``n_jobs`` worker processes.

    Every backend is submitted up front; verdicts are folded into the
    agreement tally in COMPLETION order (``as_completed``), so the winner is
    genuinely whichever finishes first, not submission order. On a win or a
    contradiction the executor is shut down with ``wait=False,
    cancel_futures=True``: futures not yet started are dropped, and futures
    already running are simply abandoned — a running native solver call
    cannot be interrupted from here (see module docstring), so the orphaned
    worker process just finishes on its own and exits.
    """
    formula_env = _fol_serialize(formula)
    premise_envs = [_fol_serialize(p) for p in premises]

    agreeing: Dict[str, List[Verdict]] = {}
    verdicts: List[Verdict] = []
    executor = ProcessPoolExecutor(max_workers=n_jobs)
    try:
        future_to_name = {}
        for name in backends:
            payload = {
                "backend": name,
                "formula": formula_env,
                "premises": premise_envs,
                "logic": logic,
                "timeout": timeout,
                "options": options,
            }
            future_to_name[executor.submit(_worker_decide, payload)] = name

        for future in as_completed(future_to_name):
            name = future_to_name[future]
            try:
                result = future.result()
                verdict = _verdict_from_dict(result["verdict"])
            except Exception as exc:      # worker crash (e.g. broken pool) -> recorded
                verdict = Verdict(ERROR, name, logic=logic, reason="infra",
                                  detail=f"{type(exc).__name__}: {exc}")
            verdicts.append(verdict)
            if verdict.is_definitive:
                try:
                    won = _feed(agreeing, verdict, require_agreement)
                except _Contradiction as exc2:
                    return _contradiction_verdict(logic, exc2.proved, exc2.refuted)
                if won is not None:
                    return won
        return _unknown_verdict(logic, verdicts)
    finally:
        executor.shutdown(wait=False, cancel_futures=True)


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def portfolio_prove(formula: Node, premises: Sequence[Node] = (), *,
                    backends: Sequence[str], logic: str = "fol",
                    timeout: int = 10000, require_agreement: int = 1,
                    jobs: Optional[int] = None, **options) -> Verdict:
    """Decide ``premises ⊨ formula`` by racing ``backends`` concurrently.

    Unlike :func:`unicode_fol_kit.api.prove`, this is an explicit-opt-in
    tool: there is no default backend list, so a caller always names exactly
    which routes it wants raced against each other.

    Args:
        formula: the goal to decide.
        premises: local premises; folded into ``(∧ premises) → formula``
            exactly as every other backend entry point does.
        backends: REQUIRED, non-empty. Every name is validated (unknown name
            → ``ValueError``, known-but-unavailable → ``BackendUnavailable``)
            and checked against ``logic`` (mismatched → ``ValueError``)
            BEFORE anything is spawned — never a partial run that discovers
            a bad name mid-flight.
        logic: the logic every backend in ``backends`` must support
            (``"fol"``, ``"modal"``, ...). No auto-detection here (contrast
            ``prove(logic="auto")``) — a portfolio's whole point is a
            caller-chosen, homogeneous backend set.
        timeout: forwarded to every backend, in milliseconds.
        require_agreement: how many backends must report the SAME definitive
            status before their verdict is returned (default 1: first
            definitive answer wins). The returned ``Verdict.agreement``
            lists exactly those backend names.
        jobs: worker processes. ``None`` (default) picks
            ``min(len(backends), 8)``; any explicit value is clamped to
            ``min(jobs, 8)`` (project-wide cap) and floored at 1. ``jobs==1``
            runs sequentially in THIS process — no
            ``ProcessPoolExecutor`` — which is also the only way to race a
            backend registered ad hoc in the caller's own process (a spawned
            worker cannot import a name that only exists there).
        **options: forwarded to every backend's ``decide()``, exactly as in
            ``prove()`` — only sensible with backends that share an option
            vocabulary, or a single-backend list.

    Returns:
        The winning ``Verdict`` on agreement; a ``Verdict(status="error",
        reason="infra", ...)`` naming both sides if two backends disagree
        (PROVED vs REFUTED — a soundness alarm, never silently resolved);
        otherwise a collective ``Verdict(status="unknown", backend=
        "portfolio", ...)`` whose ``detail`` summarises every backend's own
        answer.

    Raises:
        ValueError: ``backends`` is empty, ``require_agreement < 1``, a
            backend name is unregistered, or a named backend does not
            support ``logic``.
        BackendUnavailable: a named backend is registered but its
            prerequisites (binary, install) are missing.
    """
    if not backends:
        raise ValueError(
            "portfolio_prove: `backends` must be a non-empty explicit list — "
            "the portfolio is opt-in, there is no default chain "
            "(use unicode_fol_kit.api.prove for that).")
    if require_agreement < 1:
        raise ValueError(
            f"portfolio_prove: require_agreement must be >= 1, got {require_agreement!r}")

    backends = list(backends)
    premises = list(premises)

    for name in backends:
        backend = get_backend(name)                       # ValueError on unknown name
        if not backend.available():
            raise BackendUnavailable(
                f"{name}: backend is not available on this machine "
                f"(external={backend.external}) — install it or drop it from `backends`.")
        if logic not in backend.logics:
            raise ValueError(
                f"portfolio_prove: backend {name!r} does not support logic {logic!r} "
                f"(it handles {sorted(backend.logics)})")

    if jobs is None:
        n_jobs = min(len(backends), _MAX_JOBS)
    else:
        n_jobs = max(1, min(int(jobs), _MAX_JOBS))

    if n_jobs == 1:
        return _run_sequential(formula, premises, backends, logic, timeout,
                               require_agreement, options)
    return _run_parallel(formula, premises, backends, logic, timeout,
                         require_agreement, n_jobs, options)
