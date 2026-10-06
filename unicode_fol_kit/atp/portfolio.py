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
  a bad name three processes in). Availability is asked for the route the
  call's own options select (``use_wsl=``, ``minizinc_path=``, ...), as
  ``run_backend`` asks it.
* The options are planned exactly as ``prove()`` plans them
  (:func:`~unicode_fol_kit.atp.protocol.plan_options`): a member is handed only
  the options it reads, an option no member reads is a ``ValueError``, and a
  member that cannot read an option that changes the question (a ``subsorts=``
  edge, a modal ``frame=``) is not run -- it is listed as
  ``unknown/unsupported`` and casts no vote, so no member ever answers a
  question other than the one that was asked.
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
  ``"chain"`` pseudo-backend, including its treatment of a member that
  FAILED: quoted by its own message, and an ERROR verdict when every member
  failed).
* ``jobs=1`` (forced, or the natural result of a single-element
  ``backends``) never touches ``ProcessPoolExecutor`` — it runs the SAME
  backends sequentially in THIS process. This is not just an optimisation:
  it is also the only way to portfolio-race a backend that was registered
  ad hoc in the calling process (e.g. a test double) and would not be
  importable by name inside a spawned worker.
* **A caller's error is raised, whatever ``jobs`` is.** A member that refuses the
  CALL — a modal ``frame=`` it does not know, a ``premise_names=`` list that does not
  match the premises — raises ``ValueError`` (or
  :class:`~unicode_fol_kit.atp.protocol.BackendUnavailable`) out of
  :func:`portfolio_prove`: :func:`~unicode_fol_kit.atp.protocol.run_backend` keeps a
  caller's error loud, and so do the sequential path and ``api.prove``. In a race the
  error that is raised is the first one a member reports, and a member that has
  already won when another reports its error wins, as the first member of
  ``api.prove``'s chain that answers does. Only a failure that is NOT the caller's — a
  worker process that died, an answer that cannot be read back — is recorded as
  ``error`` / ``infra`` and quoted in the collective verdict.
* The premises are counted as ``api.prove`` counts them: the caller's own premises are
  the ones ``premise_names=`` names and the ones an index (``relevant_premises``, a
  Z3 core) refers to; the sentences of ``signature=`` and the side axioms of a
  :class:`~unicode_fol_kit.logic.Sentence` are background, named for the writer and
  never reported back.
"""

from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import replace
from typing import Dict, List, Mapping, Optional, Sequence, Tuple

from ..fol.nodes import Node
from ..fol.serialize import deserialize as _fol_deserialize
from ..fol.serialize import serialize as _fol_serialize
from .protocol import (
    ERROR, PROVED, REFUTED, UNKNOWN,
    BackendUnavailable, Verdict, get_backend, plan_options, run_backend,
    _available_for, _no_definitive_verdict,
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
    """Build the collective verdict when nobody reached agreement.

    The same rule as ``api.prove``'s chain (they must not answer one question
    two ways): UNKNOWN, with a member that failed quoted by its own message,
    and ERROR when every member failed -- see
    :func:`~unicode_fol_kit.atp.protocol._no_definitive_verdict`.
    """
    return _no_definitive_verdict("portfolio", logic, verdicts, "empty backend list")


# ---------------------------------------------------------------------------
# Sequential path (jobs == 1): same process, no pool
# ---------------------------------------------------------------------------

def _refused_verdict(name: str, logic: str, refusal: str) -> Verdict:
    """The verdict of a member that was not run because it cannot read an option
    that changes the question (the same verdict ``api.prove`` lists for it)."""
    return Verdict(UNKNOWN, name, logic=logic, reason="unsupported", detail=refusal)


def _run_sequential(formula: Node, premises: Sequence[Node], backends: Sequence[str],
                    logic: str, timeout: int, require_agreement: int,
                    plan: Dict[str, Tuple[dict, Optional[str]]]) -> Verdict:
    """Run ``backends`` one at a time in THIS process.

    Used whenever ``jobs`` resolves to 1: either the caller forced it (e.g.
    to portfolio-race a locally-registered test backend that a spawned
    worker could not import) or a single-element ``backends`` made pooling
    pointless. ``plan`` is what :func:`~unicode_fol_kit.atp.protocol.plan_options`
    decided: the options each member is handed, or the reason it is not run.
    """
    agreeing: Dict[str, List[Verdict]] = {}
    verdicts: List[Verdict] = []
    for name in backends:
        passed, refusal = plan[name]
        if refusal is not None:
            verdicts.append(_refused_verdict(name, logic, refusal))
            continue
        extra = dict(passed)
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
    """Reconstruct a ``Verdict`` from ``Verdict.to_dict()`` — round-trips
    EVERY field, including ``relevant_premises`` and ``solver_version``
    (both were silently dropped here before K1: a real bug, since this is
    the process-pool path's only way back from a worker's JSON-safe dict to
    a live ``Verdict``, so both fields vanished on every ``jobs>1``
    portfolio race — see ``tests/test_portfolio.py``'s full-fields round
    trip, which pins ``Verdict.to_dict()`` unchanged by this reconstruction).
    """
    return Verdict(
        status=d["status"], backend=d["backend"], logic=d["logic"],
        reason=d["reason"], szs_status=d["szs_status"], wall_time=d["wall_time"],
        solver_version=d["solver_version"],
        countermodel=d["countermodel"], proof=d["proof"], detail=d["detail"],
        agreement=tuple(d["agreement"]),
        relevant_premises=(tuple(d["relevant_premises"])
                           if d["relevant_premises"] is not None else None),
    )


def _crash_verdict(name: str, logic: str, exc: BaseException) -> Verdict:
    """The verdict recorded for a member whose worker failed for a reason that is not the
    caller's: a broken pool, an answer that does not come back as a verdict."""
    return Verdict(ERROR, name, logic=logic, reason="infra",
                   detail=f"{type(exc).__name__}: {exc}")


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


def _as_plain_data(value):
    """``value`` with every read-only mapping inside it as a plain ``dict``.

    An option travels to a worker process by pickling. A mapping that is not a ``dict``
    need not pickle: :attr:`~unicode_fol_kit.fol.signature.Signature.subsorts` is a
    read-only view (``mappingproxy``), and ``subsorts=sig.subsorts`` is how a caller
    passes it. The copy has the same keys and values, which is all a backend reads.
    """
    if isinstance(value, Mapping) and type(value) is not dict:
        return {key: _as_plain_data(item) for key, item in value.items()}
    return value


def _run_parallel(formula: Node, premises: Sequence[Node], backends: Sequence[str],
                  logic: str, timeout: int, require_agreement: int, n_jobs: int,
                  plan: Dict[str, Tuple[dict, Optional[str]]]) -> Verdict:
    """Race ``backends`` across ``n_jobs`` worker processes.

    Every backend is submitted up front, each with the options ``plan`` hands it
    (a member that ``plan`` refuses is not submitted; its refusal is listed with
    the verdicts); verdicts are folded into the
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
    for name in backends:
        refusal = plan[name][1]
        if refusal is not None:
            verdicts.append(_refused_verdict(name, logic, refusal))
    executor = ProcessPoolExecutor(max_workers=n_jobs)
    try:
        future_to_name = {}
        for name in backends:
            if plan[name][1] is not None:
                continue
            payload = {
                "backend": name,
                "formula": formula_env,
                "premises": premise_envs,
                "logic": logic,
                "timeout": timeout,
                "options": {key: _as_plain_data(value) for key, value in plan[name][0].items()},
            }
            future_to_name[executor.submit(_worker_decide, payload)] = name

        for future in as_completed(future_to_name):
            name = future_to_name[future]
            try:
                result = future.result()
            except (ValueError, BackendUnavailable):
                # A member refused the CALL (an unknown frame, a premise_names list of the
                # wrong length). run_backend keeps that loud, and so do the sequential path
                # and api.prove: it is raised here too, not recorded as a failure of the
                # infrastructure.
                raise
            except Exception as exc:      # worker crash (e.g. broken pool) -> recorded
                verdict = _crash_verdict(name, logic, exc)
            else:
                try:
                    verdict = _verdict_from_dict(result["verdict"])
                except Exception as exc:
                    verdict = _crash_verdict(name, logic, exc)
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
                    jobs: Optional[int] = None, signature=None,
                    **options) -> Verdict:
    """Decide ``premises ⊨ formula`` by racing ``backends`` concurrently.

    Unlike :func:`unicode_fol_kit.api.prove`, this is an explicit-opt-in
    tool: there is no default backend list, so a caller always names exactly
    which routes it wants raced against each other.

    Args:
        formula: the goal to decide. A :class:`~unicode_fol_kit.logic.Sentence` in
            classical first-order logic is accepted as :func:`unicode_fol_kit.api.prove`
            accepts it: its side axioms are added to the premises.
        premises: local premises; folded into ``(∧ premises) → formula``
            exactly as every other backend entry point does. A Sentence among
            them brings its side axioms, as for ``formula``.
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
        signature: a :class:`~unicode_fol_kit.fol.signature.Signature`, read
            exactly as :func:`unicode_fol_kit.api.prove` reads it: the sentences
            :func:`~unicode_fol_kit.fol.signature_axioms` returns are added to the
            premises of every member, and a premise index that comes back
            (``relevant_premises``, a Z3 core) stays an index into ``premises``.
            ``premise_names=`` names the caller's own premises only; the sentences the
            signature adds are named for the writer. Classical first-order routes only.
        **options: planned exactly as :func:`unicode_fol_kit.api.prove` plans
            them (:func:`~unicode_fol_kit.atp.protocol.plan_options`). A member is
            handed only the options it reads. An option that NO member reads is a
            ``ValueError`` naming it, raised before anything runs: it would
            otherwise be ignored and the answer given to a question the caller
            did not ask. A member that does not read an option that changes the
            question (a modal ``frame=``, a ``subsorts=`` edge, ``bridges=``)
            while another member does is NOT run: it is listed in the collective
            verdict's ``detail`` as ``unknown/unsupported`` with the option
            named, and it never casts a vote. An option that only bounds a search
            or says where a binary lives (``max_steps=``, ``use_wsl=``) is simply
            not handed to a member that has no use for it.

    Returns:
        The winning ``Verdict`` on agreement; a ``Verdict(status="error",
        reason="infra", ...)`` naming both sides if two backends disagree
        (PROVED vs REFUTED — a soundness alarm, never silently resolved);
        otherwise a collective ``Verdict(status="unknown", backend=
        "portfolio", ...)`` whose ``detail`` summarises every backend's own
        answer.

    Raises:
        ValueError: ``backends`` is empty, ``require_agreement < 1``, a
            backend name is unregistered, a named backend does not
            support ``logic``, an option is read by no member, a Sentence is
            in a logic other than classical first-order logic, ``signature``
            is given for a logic other than ``"fol"``, or a member refuses the
            call itself (an unknown ``frame=``, a ``premise_names=`` list of the
            wrong length) — the same ``ValueError`` for every ``jobs``.
        TypeError: ``signature`` is not a
            :class:`~unicode_fol_kit.fol.signature.Signature`.
        BackendUnavailable: a named backend is registered but its
            prerequisites (binary, install) are missing, asked for the route
            this call's own options select
            (:meth:`~unicode_fol_kit.atp.protocol.ProverBackend.available_for`).
    """
    if not backends:
        raise ValueError(
            "portfolio_prove: `backends` must be a non-empty explicit list — "
            "the portfolio is opt-in, there is no default chain "
            "(use unicode_fol_kit.api.prove for that).")
    if require_agreement < 1:
        raise ValueError(
            f"portfolio_prove: require_agreement must be >= 1, got {require_agreement!r}")

    from ..api import (                                   # lazy: api imports this package
        _name_background, _signature_premises, _unwrap_sentences, _without_background,
    )

    backends = list(backends)
    premises = list(premises)
    given = len(premises)                                 # the caller's own premises
    formula, premises = _unwrap_sentences(formula, premises, "portfolio_prove")

    for name in backends:
        backend = get_backend(name)                       # ValueError on unknown name
        if logic not in backend.logics:
            raise ValueError(
                f"portfolio_prove: backend {name!r} does not support logic {logic!r} "
                f"(it handles {sorted(backend.logics)})")

    if signature is not None:
        premises = [*premises, *_signature_premises("portfolio_prove", signature, logic)]
    # What was appended to the caller's premises (a signature's sentences, the side
    # axioms of a Sentence) is background: the caller's premise_names cover the caller's
    # premises, and the background is named for the writer, exactly as api.prove does.
    options = _name_background(options, given, len(premises), "portfolio_prove")

    # The options of the call are planned as api.prove plans them: a member is
    # handed what it reads, an option nobody reads is a ValueError, and a member
    # that cannot read an option that changes the question is not run at all.
    plan = plan_options("portfolio_prove", backends, logic, options)

    for name in backends:
        backend = get_backend(name)
        if not _available_for(backend, plan[name][0]):    # the route this call selects
            raise BackendUnavailable(
                f"{name}: backend is not available on this machine "
                f"(external={backend.external}) — install it or drop it from `backends`.")

    if jobs is None:
        n_jobs = min(len(backends), _MAX_JOBS)
    else:
        n_jobs = max(1, min(int(jobs), _MAX_JOBS))

    if n_jobs == 1:
        verdict = _run_sequential(formula, premises, backends, logic, timeout,
                                  require_agreement, plan)
    else:
        verdict = _run_parallel(formula, premises, backends, logic, timeout,
                                require_agreement, n_jobs, plan)
    if len(premises) > given:
        verdict = _without_background(verdict, given)
    return verdict
