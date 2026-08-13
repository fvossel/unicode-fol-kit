"""Batch/cache infrastructure for mass evaluation (10k+ formulas).

:func:`batch_decide` runs :func:`unicode_fol_kit.api.prove` over many tasks at
once, adding three things a single ``prove()`` call does not need but a
10k-formula evaluation run cannot do without:

* **Never abort the batch.** A task is a raw ``{"id", "formula", "premises"}``
  dict; ``formula``/each ``premises`` entry may be a parsed
  :class:`~unicode_fol_kit.fol.nodes.Node` or raw text. Text goes through
  :func:`unicode_fol_kit.api.parse_any`. A parse failure becomes an
  ``"error"``/``"parse"`` result for THAT task — it is recorded, never raised,
  and never stops the remaining tasks from running. (Backend-level
  configuration errors — an unknown backend name, a backend/logic mismatch —
  are a different thing: those are caller bugs, not per-formula noise, and
  still raise, exactly as :func:`~unicode_fol_kit.api.prove` does.)
* **Content-addressed caching.** With ``cache_dir`` set, every task's decision
  is looked up under a key derived from everything that could change the
  answer: the formula, the premises, the backend selection, the logic, the
  timeout, and the extra options — all of it, not just the formula, because
  the same formula decided with a different backend chain or a tighter
  timeout is not the same cache entry. A hit returns the stored
  :class:`~unicode_fol_kit.atp.protocol.Verdict` dict WITHOUT calling any
  backend. Only definitive/UNKNOWN verdicts are cached — an ``"error"``
  verdict (infra failure, e.g. a subprocess crash) is never cached, so a
  transient failure does not poison the cache for a formula that would
  otherwise decide cleanly on retry.
* **Process-based parallelism.** ``jobs > 1`` fans the (post-cache, post-parse)
  work out over a ``ProcessPoolExecutor``, never threads: Z3's ``Solver`` and
  the kit's other backends share process-global state (Z3 contexts in
  particular are documented as not thread-safe), so THREADS would risk
  cross-task interference invisible in a small test but real at 10k-formula
  scale. Processes are the correct isolation unit. Per the project's
  parallelism cap, ``jobs`` is clamped to ``min(jobs, 8)`` regardless of what
  is requested. ``jobs=1`` (the default) never touches
  ``ProcessPoolExecutor`` — no spawn overhead for the common single-worker
  case.

Result shape: ``batch_decide`` returns a ``list[dict]``, one entry per input
task, in INPUT ORDER (parallel execution does not reorder results) —
``{"id": ..., "verdict": Verdict.to_dict(), "cached": bool}``. With
``results_path`` set, the same list is also appended to that path as JSONL
(one JSON object per line, in the same order).
"""

import hashlib
import json
import os
import tempfile
from typing import Dict, Iterable, List, Optional, Sequence

from ..atp.protocol import ERROR, Verdict, default_chain
from ..fol.nodes import Node
from ..fol.serialize import deserialize as _fol_deserialize
from ..fol.serialize import serialize as _fol_serialize

__all__ = ["batch_decide"]

# Project-wide parallelism cap (see memory: "cap all parallelism at 8").
_MAX_JOBS = 8


# ---------------------------------------------------------------------------
# Task resolution: Node | str -> Node, never raising
# ---------------------------------------------------------------------------

def _resolve_one(value) -> "tuple[Optional[Node], Optional[str]]":
    """Resolve one formula/premise value to a ``Node``, or an error message.

    Returns ``(node, None)`` on success, ``(None, message)`` on failure.
    Never raises: a parser exception is caught and turned into ``message``.
    """
    if isinstance(value, Node):
        return value, None
    if isinstance(value, str):
        from .. import api          # lazy: avoid import-time cost/cycles

        parsed = api.parse_any(value)
        if not parsed.ok:
            message = parsed.errors[-1]["message"] if parsed.errors else "unparseable"
            return None, message
        return parsed.formula, None
    return None, f"unsupported formula/premise type: {type(value).__name__}"


def _resolve_task(task: dict):
    """Resolve a task dict to ``(id, formula, premises, error)``.

    ``error`` is ``None`` on success; on failure ``formula``/``premises`` are
    ``None`` and ``error`` is a human-readable message (formula error, or
    ``"premise <i>: ..."`` for a bad premise).
    """
    task_id = task["id"]
    formula, err = _resolve_one(task["formula"])
    if err is not None:
        return task_id, None, None, err
    premises: List[Node] = []
    for i, raw in enumerate(task.get("premises") or []):
        node, perr = _resolve_one(raw)
        if perr is not None:
            return task_id, None, None, f"premise {i}: {perr}"
        premises.append(node)
    return task_id, formula, premises, None


def _error_result(task_id: str, message: str) -> dict:
    """Build the per-task result dict for a parse failure (status=error)."""
    verdict = Verdict(ERROR, "batch", reason="parse", detail=message)
    return {"id": task_id, "verdict": verdict.to_dict(), "cached": False}


# ---------------------------------------------------------------------------
# Content-addressed cache
# ---------------------------------------------------------------------------

def _cache_key(formula: Node, premises: Sequence[Node],
              backends: Optional[Sequence[str]], logic: str, timeout: int,
              options: dict) -> str:
    """sha256 of the canonical JSON of everything that can change the answer.

    Two properties matter for correctness (both pinned by tests):

    - The backend list enters the key IN THE CALLER'S ORDER — ``prove``'s
      chain is order-sensitive (the first definitive backend wins), so
      ``["z3", "resolution"]`` and ``["resolution", "z3"]`` are different
      queries and must never share a cache entry.
    - ``backends=None`` (the caller wants the default chain) is resolved to
      the CONCRETE chain that would run — ``default_chain`` over the
      detected logic — because the default chain is install-dependent (the
      optional cvc5 extra joins it when importable): a cache populated
      before an install change must not keep answering for the old chain.

    ``json.dumps(..., sort_keys=True)`` canonicalises dict-key order
    recursively, so ``options`` needs no manual sorting.
    """
    if backends is not None:
        backend_material = list(backends)
    else:
        effective_logic = logic
        if logic == "auto":
            # Mirror api.prove's own routing: modal operators anywhere in
            # the query select the modal chain.
            from ..atp.modal_tableau import has_modal
            effective_logic = ("modal" if has_modal(formula)
                               or any(has_modal(p) for p in premises)
                               else "fol")
        backend_material = ["default", effective_logic,
                           *default_chain(effective_logic)]
    material = {
        "formula": _fol_serialize(formula),
        "premises": [_fol_serialize(p) for p in premises],
        "backends": backend_material,
        "logic": logic,
        "timeout": timeout,
        "options": options,
    }
    blob = json.dumps(material, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def _cache_path(cache_dir: str, key: str) -> str:
    return os.path.join(cache_dir, f"{key}.json")


def _cache_read(cache_dir: str, key: str) -> Optional[dict]:
    """Return the cached verdict dict, or ``None`` on a miss.

    A corrupt/unreadable cache entry is treated as a miss (never raises) —
    a damaged file must not take down a 10k-task batch.
    """
    path = _cache_path(cache_dir, key)
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except FileNotFoundError:
        return None
    except (OSError, json.JSONDecodeError):
        return None


def _cache_write(cache_dir: str, key: str, verdict_dict: dict) -> None:
    """Write ``verdict_dict`` under ``key``, atomically (tmp file + replace)."""
    os.makedirs(cache_dir, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(prefix=".batch-cache-", suffix=".json",
                                    dir=cache_dir)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(verdict_dict, fh)
        os.replace(tmp_path, _cache_path(cache_dir, key))
    except BaseException:
        try:
            os.remove(tmp_path)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# Deciding: sequential (jobs=1) and per-process worker (jobs>1)
# ---------------------------------------------------------------------------

def _decide(formula: Node, premises: Sequence[Node],
           backends: Optional[Sequence[str]], logic: str, timeout: int,
           options: dict) -> Verdict:
    """Call :func:`unicode_fol_kit.api.prove` for one resolved task."""
    from .. import api          # lazy: avoid import-time cost/cycles

    return api.prove(formula, list(premises), logic=logic, backends=backends,
                     timeout=timeout, **options)


def _worker_decide(payload: dict) -> dict:
    """``ProcessPoolExecutor`` target — MUST stay module-level for Windows
    spawn (it pickles the target by qualified name, not by closure).

    ``payload`` carries only JSON-safe, picklable data: formulas/premises
    serialised via :mod:`unicode_fol_kit.fol.serialize` rather than raw
    ``Node`` objects, so the payload does not depend on ``Node``'s own
    pickle-ability (which the batch layer should not have to assume).
    Deserialises, decides, and returns ``{"id", "verdict"}`` (a plain dict,
    itself picklable back to the parent process).
    """
    formula = _fol_deserialize(payload["formula"])
    premises = [_fol_deserialize(p) for p in payload["premises"]]
    verdict = _decide(formula, premises, payload["backends"], payload["logic"],
                      payload["timeout"], payload["options"])
    return {"id": payload["id"], "verdict": verdict.to_dict()}


# ---------------------------------------------------------------------------
# batch_decide
# ---------------------------------------------------------------------------

def batch_decide(tasks: Iterable[dict], *,
                 backends: Optional[Sequence[str]] = None,
                 logic: str = "auto", timeout: int = 10000, jobs: int = 1,
                 cache_dir: Optional[str] = None,
                 results_path: Optional[str] = None,
                 options: Optional[dict] = None) -> List[dict]:
    """Decide a batch of entailment tasks, with caching and process fan-out.

    Args:
        tasks: an iterable of ``{"id": str, "formula": Node | str,
            "premises": optional list[Node | str]}`` dicts. Text values go
            through :func:`unicode_fol_kit.api.parse_any`; a parse failure is
            recorded as an ``"error"``/``"parse"`` result for that task alone
            — it never aborts the batch.
        backends: forwarded to :func:`unicode_fol_kit.api.prove` for every
            task (``None`` = the logic's default chain).
        logic: forwarded to ``prove`` for every task (``"auto"`` routes each
            formula by its own syntax, independently per task).
        timeout: forwarded to ``prove`` for every task, in milliseconds.
        jobs: worker processes for the decide step. Clamped to
            ``min(jobs, 8)``. ``jobs<=1`` runs sequentially in this process
            (no ``ProcessPoolExecutor``, no spawn overhead); ``jobs>1`` uses
            one because Z3 (and the kit's other backends) are not
            thread-safe — see the module docstring. CAVEAT for CUSTOM
            backends: worker processes are SPAWNED (fresh interpreters), so
            a backend registered at RUNTIME via ``register_backend`` (e.g.
            inside a script's ``__main__`` block or a test body) does not
            exist in the workers and its tasks come back as unknown-backend
            errors; with ``jobs>1``, register custom backends at the top
            level of an importable module (imported by the workers when they
            re-import this package), or run with ``jobs=1`` — the same
            constraint ``atp.portfolio.portfolio_prove`` documents for its
            own process pool.
        cache_dir: when set, a content-addressed on-disk cache (see
            :func:`_cache_key`). A hit returns the stored verdict WITHOUT
            calling any backend; a miss decides normally and writes the
            result (unless its status is ``"error"``).
        results_path: when set, the full ordered result list is also
            appended to this path as JSONL (one JSON object per line).
        options: extra keyword options forwarded to every backend in every
            task's chain (mirrors ``prove``'s ``**options``); also folded
            into the cache key.

    Returns:
        A ``list[dict]``, one entry per task, in INPUT ORDER:
        ``{"id": task_id, "verdict": Verdict.to_dict(), "cached": bool}``.

    Note:
        A backend-configuration error from ``prove`` itself (unknown backend
        name, a named backend that does not support the detected logic) is a
        caller bug, not per-formula noise, and still raises — exactly as a
        direct ``prove()`` call would. Only PARSE failures are absorbed into
        per-task error results.
    """
    options = dict(options) if options else {}
    jobs = max(1, min(int(jobs), _MAX_JOBS))

    resolved = [_resolve_task(task) for task in tasks]
    results: List[Optional[dict]] = [None] * len(resolved)

    # Pass 1: parse errors -> immediate results; cache lookups -> immediate
    # hits; everything else queued for the decide step (sequential or pool).
    pending_indices: List[int] = []
    pending: List[tuple] = []          # (task_id, formula, premises, cache_key)
    for i, (task_id, formula, premises, err) in enumerate(resolved):
        if err is not None:
            results[i] = _error_result(task_id, err)
            continue
        key = (_cache_key(formula, premises, backends, logic, timeout, options)
               if cache_dir else None)
        if key is not None:
            cached_dict = _cache_read(cache_dir, key)
            if cached_dict is not None:
                results[i] = {"id": task_id, "verdict": cached_dict, "cached": True}
                continue
        pending_indices.append(i)
        pending.append((task_id, formula, premises, key))

    # Pass 2: decide the cache misses.
    if pending:
        if jobs <= 1:
            verdict_dicts = []
            for task_id, formula, premises, _key in pending:
                verdict = _decide(formula, premises, backends, logic, timeout, options)
                verdict_dicts.append(verdict.to_dict())
        else:
            from concurrent.futures import ProcessPoolExecutor

            payloads = [
                {
                    "id": task_id,
                    "formula": _fol_serialize(formula),
                    "premises": [_fol_serialize(p) for p in premises],
                    "backends": list(backends) if backends is not None else None,
                    "logic": logic,
                    "timeout": timeout,
                    "options": options,
                }
                for task_id, formula, premises, _key in pending
            ]
            with ProcessPoolExecutor(max_workers=jobs) as executor:
                # .map preserves input order in its output, so the zip below
                # below stays index-aligned with `pending`.
                worker_results = list(executor.map(_worker_decide, payloads))
            verdict_dicts = [wr["verdict"] for wr in worker_results]

        for idx, (task_id, _formula, _premises, key), verdict_dict in zip(
                pending_indices, pending, verdict_dicts):
            if cache_dir and key is not None and verdict_dict.get("status") != ERROR:
                _cache_write(cache_dir, key, verdict_dict)
            results[idx] = {"id": task_id, "verdict": verdict_dict, "cached": False}

    assert all(r is not None for r in results)     # every index was filled exactly once

    if results_path:
        with open(results_path, "a", encoding="utf-8") as fh:
            for r in results:
                fh.write(json.dumps(r) + "\n")

    return results
