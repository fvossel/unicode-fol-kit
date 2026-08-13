"""Tests for unicode_fol_kit/eval/batch.py — batch/cache infrastructure.

Hand-checked contracts:

* Three ground-EUF FOL tasks (no quantifiers, so Z3 decides them instantly
  and deterministically) exercise the status mapping end to end:
    - "P(a) -> P(a)" (no premises) is a tautology -> proved.
    - "Q(a)" from premise "P(a) -> Q(a)" is NOT entailed: the model
      P(a)=False, Q(a)=False satisfies the premise (F->F = T) while
      falsifying the goal -> refuted.
    - "Q(a)" from premises "P(a) -> Q(a)", "P(a)" IS entailed (modus ponens)
      -> proved.
* Caching: a first run populates cache_dir with one file per distinct task
  (formula+premises+backends+logic+timeout+options key); a second run over
  the SAME tasks/cache_dir, with unicode_fol_kit.api.prove monkeypatched to
  raise immediately, still returns the identical verdicts purely from the
  cache (proving no backend call happened) and flags them cached=True.
* A parse failure for one task never aborts the batch: it comes back as its
  own {"status": "error", "reason": "parse"} entry while sibling tasks in
  the same call still decide normally.
* jobs=2 (ProcessPoolExecutor) over 4 tasks yields the same ids/statuses, IN
  THE SAME ORDER, as jobs=1 (sequential) — wall_time is excluded from the
  comparison since it is inherently a run-to-run timing value, not part of
  the logical result.
* results_path: JSONL has exactly N lines, each independently json.loads-able.
"""

import json

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.eval.batch import batch_decide

# Three ground (quantifier-free) tasks: Z3 decides these instantly and
# deterministically, so the expected status is a fact about classical FOL
# semantics, not an artifact of solver heuristics (see module docstring for
# the per-task justification).
_TASKS = [
    {"id": "tautology", "formula": "P(a) → P(a)"},
    {"id": "not_entailed", "formula": "Q(a)", "premises": ["P(a) → Q(a)"]},
    {"id": "modus_ponens", "formula": "Q(a)",
     "premises": ["P(a) → Q(a)", "P(a)"]},
]
_EXPECTED_STATUS = {
    "tautology": "proved",
    "not_entailed": "refuted",
    "modus_ponens": "proved",
}


def _by_id(results):
    return {r["id"]: r for r in results}


# ---------------------------------------------------------------------------
# sequential (jobs=1): status mapping
# ---------------------------------------------------------------------------

def test_batch_decide_sequential_statuses():
    results = batch_decide(_TASKS)
    assert [r["id"] for r in results] == [t["id"] for t in _TASKS]   # order preserved
    by_id = _by_id(results)
    for task_id, expected in _EXPECTED_STATUS.items():
        assert by_id[task_id]["verdict"]["status"] == expected
        assert by_id[task_id]["cached"] is False
    json.dumps(results)                                              # JSON-compatible


# ---------------------------------------------------------------------------
# caching
# ---------------------------------------------------------------------------

def test_batch_decide_cache_hit_avoids_backend_call(tmp_path, monkeypatch):
    cache_dir = str(tmp_path / "cache")

    run1 = batch_decide(_TASKS, cache_dir=cache_dir)
    assert all(r["cached"] is False for r in run1)
    # One distinct cache key per distinct (formula, premises) combination —
    # all three tasks above differ in at least one of those.
    cache_files = list((tmp_path / "cache").glob("*.json"))
    assert len(cache_files) == len(_TASKS)

    def _boom(*args, **kwargs):
        raise RuntimeError("api.prove must not be called on a cache hit")

    monkeypatch.setattr(api, "prove", _boom)

    run2 = batch_decide(_TASKS, cache_dir=cache_dir)   # must come entirely from cache
    assert all(r["cached"] is True for r in run2)

    by1, by2 = _by_id(run1), _by_id(run2)
    for task_id in _EXPECTED_STATUS:
        assert by2[task_id]["verdict"] == by1[task_id]["verdict"]     # byte-identical
        assert by1[task_id]["cached"] is False and by2[task_id]["cached"] is True


# ---------------------------------------------------------------------------
# parse errors never abort the batch
# ---------------------------------------------------------------------------

def test_batch_decide_parse_error_is_isolated():
    tasks = [
        {"id": "broken", "formula": "∀x (P(x) →"},     # truncated: no dialect parses it
        {"id": "fine", "formula": "P(a) → P(a)"},
    ]
    results = batch_decide(tasks)
    by_id = _by_id(results)

    broken = by_id["broken"]["verdict"]
    assert broken["status"] == "error"
    assert broken["reason"] == "parse"
    assert by_id["broken"]["cached"] is False

    assert by_id["fine"]["verdict"]["status"] == "proved"             # sibling unaffected


# ---------------------------------------------------------------------------
# jobs=2 (process pool) matches jobs=1 (sequential)
# ---------------------------------------------------------------------------

def _strip_timing(verdict_dict):
    return {k: v for k, v in verdict_dict.items() if k != "wall_time"}


def test_batch_decide_parallel_matches_sequential():
    tasks = _TASKS + [{"id": "another_tautology", "formula": "R(a) ∨ ¬R(a)"}]

    sequential = batch_decide(tasks, jobs=1)
    parallel = batch_decide(tasks, jobs=2)

    assert [r["id"] for r in parallel] == [r["id"] for r in sequential]   # order preserved
    for seq_r, par_r in zip(sequential, parallel):
        assert seq_r["id"] == par_r["id"]
        assert _strip_timing(seq_r["verdict"]) == _strip_timing(par_r["verdict"])
        assert seq_r["cached"] is False and par_r["cached"] is False


def test_batch_decide_jobs_clamped_to_project_cap(monkeypatch):
    """jobs is capped at 8 (project-wide parallelism rule) regardless of request."""
    seen_max_workers = []

    class _FakeExecutor:
        def __init__(self, max_workers=None):
            seen_max_workers.append(max_workers)

        def __enter__(self):
            return self

        def __exit__(self, *exc):
            return False

        def map(self, fn, payloads):
            return [fn(p) for p in payloads]

    monkeypatch.setattr(
        "concurrent.futures.ProcessPoolExecutor", _FakeExecutor)
    batch_decide(_TASKS, jobs=100)
    assert seen_max_workers == [8]


# ---------------------------------------------------------------------------
# results_path: JSONL sink
# ---------------------------------------------------------------------------

def test_batch_decide_results_path_writes_jsonl(tmp_path):
    path = tmp_path / "results.jsonl"
    results = batch_decide(_TASKS, results_path=str(path))

    lines = path.read_text(encoding="utf-8").strip("\n").split("\n")
    assert len(lines) == len(_TASKS)
    parsed_lines = [json.loads(line) for line in lines]
    assert [p["id"] for p in parsed_lines] == [r["id"] for r in results]
    for p in parsed_lines:
        assert set(p.keys()) == {"id", "verdict", "cached"}


def test_cache_key_is_backend_order_sensitive():
    """Found by adversarial review: prove()'s chain is order-sensitive (the
    first definitive backend wins), so ["z3", "resolution"] and
    ["resolution", "z3"] are DIFFERENT queries and must never share a cache
    entry — the old sorted() key collapsed them and served the wrong
    provenance from cache."""
    from unicode_fol_kit.eval.batch import _cache_key
    from unicode_fol_kit import MSFLParser

    formula = MSFLParser().parse("P(alice) → P(alice)")
    key_a = _cache_key(formula, [], ["z3", "resolution"], "fol", 10000, {})
    key_b = _cache_key(formula, [], ["resolution", "z3"], "fol", 10000, {})
    assert key_a != key_b


def test_cache_key_resolves_the_default_chain_concretely():
    """backends=None must key on the CONCRETE default chain (which is
    install-dependent: the optional cvc5 extra joins it when importable), so
    a cache populated under one install state cannot silently answer for
    another. The key therefore (a) differs from an explicit list spelling
    the same chain (different query descriptions stay distinct) and (b)
    changes if the resolved chain changes."""
    from unicode_fol_kit.eval.batch import _cache_key
    from unicode_fol_kit import MSFLParser, default_chain

    formula = MSFLParser().parse("P(alice) → P(alice)")
    key_default = _cache_key(formula, [], None, "fol", 10000, {})
    key_default_again = _cache_key(formula, [], None, "fol", 10000, {})
    assert key_default == key_default_again          # deterministic
    key_explicit = _cache_key(formula, [], list(default_chain("fol")),
                              "fol", 10000, {})
    assert key_default != key_explicit
    # "auto" routes by the formula's own syntax, mirroring api.prove: a
    # modal formula under logic="auto" must not share the fol default key.
    modal = MSFLParser(modal=True).parse("□P → P")
    key_auto_modal = _cache_key(modal, [], None, "auto", 10000, {})
    key_auto_fol = _cache_key(formula, [], None, "auto", 10000, {})
    assert key_auto_modal != key_auto_fol
