"""Tests for the portfolio scheduler (atp/portfolio.py).

Hand-checked contracts, each pinned to why the expected value is correct:

* ``∀x (P(x) → Q(x)) ∧ P(a) → Q(a)`` is modus ponens instantiated at a
  ground term — a classical tautology that Z3, the kit's tableau, AND its
  resolution prover all decide instantly and soundly (same fixture as
  ``test_protocol.py``'s ``_VALID``). Racing any subset of
  ``{z3, tableau, resolution}`` on it MUST come back ``proved`` — there is no
  fragment-specific reason any of the three could fail to close it.
* ``require_agreement=n`` must make the WINNING verdict's ``agreement`` tuple
  list exactly ``n`` DISTINCT backend names, all of which actually reported
  the same status — not a repeated name, not a name that never ran.
* A contradiction (one backend PROVED, another REFUTED, same query) is
  ENGINEERED with a backend that is REGISTERED to lie — ``_VALID`` is
  genuinely valid, so any backend reporting REFUTED on it is wrong by
  construction, which is exactly the scenario the contradiction path exists
  to catch and refuse to auto-resolve. It runs at ``jobs=1`` because the
  lying backend is registered only in THIS process and a spawned worker
  could not import it by name — this is not a workaround, it demonstrates
  the documented reason ``jobs=1`` stays a first-class, fully-sequential path.
* The availability contract (unknown name -> ValueError, unavailable ->
  BackendUnavailable, empty/invalid config -> ValueError) is checked BEFORE
  anything is spawned, mirroring ``run_backend``'s contract exactly.
"""

from concurrent.futures import Future

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.portfolio import portfolio_prove
from unicode_fol_kit.atp.protocol import (
    BackendUnavailable, ProverBackend, Verdict, _REGISTRY, register_backend,
)

_P = MSFLParser()

# Modus ponens instantiated at a ground term — valid, and ground/quantified
# enough that Z3, the tableau, and resolution each close it outright (see
# module docstring). Identical fixture to test_protocol.py's `_VALID`.
_MP = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")

_TRIO = ("z3", "tableau", "resolution")


# ---------------------------------------------------------------------------
# Happy path: process-pool race over a genuinely valid formula
# ---------------------------------------------------------------------------

def test_first_definitive_answer_wins():
    v = portfolio_prove(_MP, backends=list(_TRIO))
    assert v.status == "proved"
    assert len(v.agreement) == 1
    assert v.agreement[0] in _TRIO
    assert v.backend == v.agreement[0]         # the winner names itself


def test_require_agreement_two_collects_two_distinct_backends():
    v = portfolio_prove(_MP, backends=list(_TRIO), require_agreement=2)
    assert v.status == "proved"
    assert len(v.agreement) == 2
    assert len(set(v.agreement)) == 2          # two DISTINCT backends
    assert set(v.agreement) <= set(_TRIO)


# ---------------------------------------------------------------------------
# Contradiction: a registered liar vs. a sound backend, jobs=1 fallback
# ---------------------------------------------------------------------------

class _LyingBackend(ProverBackend):
    """Always reports REFUTED, regardless of the query.

    On ``_MP`` (genuinely valid) this is wrong by construction — exactly the
    engineered disagreement needed to exercise the contradiction path.
    """

    name = "fake-liar"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula, premises=(), timeout=10000, **options) -> Verdict:
        return Verdict("refuted", self.name)


def test_contradiction_between_backends_is_a_soundness_alarm_not_resolved():
    # require_agreement=2 forces BOTH backends to be consulted: at the
    # default require_agreement=1, whichever backend answers first would
    # win immediately and the second would never run, so no contradiction
    # could ever surface (this is correct — agreement across 1 is trivially
    # itself, there is nothing yet to contradict).
    register_backend(_LyingBackend())
    try:
        v = portfolio_prove(_MP, backends=["z3", "fake-liar"], jobs=1,
                            require_agreement=2)
        assert v.status == "error"
        assert v.reason == "infra"
        assert v.backend == "portfolio"
        assert set(v.agreement) == {"z3", "fake-liar"}
    finally:
        del _REGISTRY["fake-liar"]


def test_jobs_1_never_spawns_a_process_pool():
    """A backend registered only in THIS process must be usable at jobs=1.

    If jobs=1 routed through ProcessPoolExecutor anyway, the spawned worker
    could not import `_LyingBackend` (it only exists in this test module's
    local registration) and the call would error instead of returning the
    engineered contradiction — so this doubles as a regression guard on the
    "jobs=1 stays fully sequential" contract.
    """
    register_backend(_LyingBackend())
    try:
        v = portfolio_prove(_MP, backends=["fake-liar"], jobs=1)
        assert v.status == "refuted"
        assert v.backend == "fake-liar"
    finally:
        del _REGISTRY["fake-liar"]


# ---------------------------------------------------------------------------
# jobs is clamped to the project-wide cap of 8
# ---------------------------------------------------------------------------

def test_jobs_clamped_to_project_cap(monkeypatch):
    """jobs is capped at min(jobs, 8) regardless of the request."""
    seen_max_workers = []

    class _FakeExecutor:
        def __init__(self, max_workers=None):
            seen_max_workers.append(max_workers)

        def submit(self, fn, payload):
            fut: Future = Future()
            fut.set_result(fn(payload))
            return fut

        def shutdown(self, wait=True, cancel_futures=False):
            pass

    monkeypatch.setattr("unicode_fol_kit.atp.portfolio.ProcessPoolExecutor", _FakeExecutor)

    v = portfolio_prove(_MP, backends=list(_TRIO), jobs=100)
    assert seen_max_workers == [8]
    assert v.status == "proved"                # the fake executor still ran everything inline


# ---------------------------------------------------------------------------
# Availability / validation contract, checked before spawning anything
# ---------------------------------------------------------------------------

def test_unknown_backend_name_raises_value_error():
    with pytest.raises(ValueError, match="unknown backend"):
        portfolio_prove(_MP, backends=["nope"])


def test_unavailable_backend_raises_backend_unavailable():
    class NeverThere(ProverBackend):
        name = "portfolio-never-there"
        logics = frozenset({"fol"})
        external = True

        def available(self):
            return False

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise AssertionError("decide must not be reached")

    register_backend(NeverThere())
    try:
        with pytest.raises(BackendUnavailable, match="portfolio-never-there"):
            portfolio_prove(_MP, backends=["portfolio-never-there"])
    finally:
        del _REGISTRY["portfolio-never-there"]


def test_empty_backends_raises_value_error():
    with pytest.raises(ValueError, match="non-empty"):
        portfolio_prove(_MP, backends=[])


def test_require_agreement_below_one_raises_value_error():
    with pytest.raises(ValueError, match="require_agreement"):
        portfolio_prove(_MP, backends=["z3"], require_agreement=0)


def test_backend_logic_mismatch_raises_value_error():
    """modal-tableau only decides "modal" — asking for "fol" is a caller bug."""
    with pytest.raises(ValueError, match="logic"):
        portfolio_prove(_MP, backends=["modal-tableau"], logic="fol")
