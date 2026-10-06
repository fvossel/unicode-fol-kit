"""``portfolio_prove`` plans the options of a call the way ``api.prove`` does.

A portfolio hands its members the options of the call. Handing every member every
option answers a question the caller did not ask: a member that cannot read an
option that changes the question (a subsort edge, a modal frame) decides the
problem WITHOUT it. These tests derive each expectation by hand.

The problem used throughout: ``∀x:B P(x) ⊨ ∀x:A P(x)``.

* With the subsort edge ``A < B`` (``A ⊆ B``) it is VALID: every element of ``A`` is
  an element of ``B``, and ``P`` holds of every element of ``B``.
* Without the edge it is not valid: take the universe ``{0, 1}``, ``A = {0, 1}``,
  ``B = {1}``, ``P = {1}``. Then ``∀x:B P(x)`` holds and ``∀x:A P(x)`` does not.

So with the edge no member may answer ``refuted``. The model finder reads the edge and
finds no countermodel (it cannot prove validity); Z3 does not read it and would
refute, which is the answer to the other question.
"""

from concurrent.futures import Future

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.portfolio import portfolio_prove
from unicode_fol_kit.atp.protocol import (
    BackendUnavailable, ProverBackend, Verdict, _REGISTRY, register_backend,
)
from unicode_fol_kit.fol._msfl_nodes import SortedQuantifier
from unicode_fol_kit.fol.nodes import Atom, Variable
from unicode_fol_kit.fol.signature import Signature

_X = Variable("x")
GOAL = SortedQuantifier("∀", _X, "A", Atom("P", [_X]))
PREMISES = [SortedQuantifier("∀", _X, "B", Atom("P", [_X]))]
EDGE = {"A": ["B"]}


class _InlineExecutor:
    """A process pool that runs every task in this process (see test_portfolio.py).

    ``_worker_decide`` is the function the real pool would run in a worker, so the
    payload each member is handed is the one that crosses the process boundary."""

    payloads: list = []

    def __init__(self, max_workers=None):
        pass

    def submit(self, fn, payload):
        type(self).payloads.append(payload)
        future: Future = Future()
        future.set_result(fn(payload))
        return future

    def shutdown(self, wait=True, cancel_futures=False):
        pass


@pytest.fixture
def inline_pool(monkeypatch):
    _InlineExecutor.payloads = []
    monkeypatch.setattr("unicode_fol_kit.atp.portfolio.ProcessPoolExecutor", _InlineExecutor)
    return _InlineExecutor


class _Reads(ProverBackend):
    """A member that declares the options it reads and records what it is handed."""

    logics = frozenset({"fol"})
    external = False
    calls: list

    def __init__(self, name, reads, verdict_status="unknown"):
        self.name = name
        self._reads = frozenset(reads)
        self._status = verdict_status
        self.calls = []

    def available(self):
        return True

    def accepted_options(self, logic=None):
        return self._reads

    def decide(self, formula, premises=(), timeout=10000, **options):
        self.calls.append(dict(options))
        return Verdict(self._status, self.name)


@pytest.fixture
def registered():
    names = []

    def register(backend):
        register_backend(backend)
        names.append(backend.name)
        return backend

    yield register
    for name in names:
        _REGISTRY.pop(name, None)


# ---------------------------------------------------------------------------
# A member that cannot read the subsort edge does not answer without it
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("order", [["z3", "modelfinder"], ["modelfinder", "z3"]])
def test_no_member_answers_the_problem_without_the_subsort_edge(order):
    verdict = portfolio_prove(GOAL, PREMISES, backends=order, subsorts=EDGE, timeout=5000, jobs=1)
    assert verdict.status != "refuted"          # with the edge the problem is valid
    assert verdict.status == "unknown"
    assert "z3:unknown/unsupported" in verdict.detail
    assert "subsorts" in verdict.detail          # the refusal names the option it could not read


def test_the_pool_path_plans_the_options_too(inline_pool):
    verdict = portfolio_prove(GOAL, PREMISES, backends=["z3", "modelfinder"], subsorts=EDGE,
                              timeout=5000, jobs=2)
    assert verdict.status == "unknown"
    assert "z3:unknown/unsupported" in verdict.detail
    submitted = {payload["backend"]: payload["options"] for payload in inline_pool.payloads}
    assert set(submitted) == {"modelfinder"}              # z3 was never sent to a worker
    assert submitted["modelfinder"] == {"subsorts": EDGE}


def test_a_real_process_pool_does_not_answer_without_the_edge():
    verdict = portfolio_prove(GOAL, PREMISES, backends=["z3", "modelfinder"], subsorts=EDGE,
                              timeout=5000, jobs=2)
    assert verdict.status == "unknown"
    assert "z3:unknown/unsupported" in verdict.detail


def test_the_portfolio_answers_like_the_chain():
    # Two routes must not answer one question two ways.
    chain = api.prove(GOAL, PREMISES, backends=["z3", "modelfinder"], subsorts=EDGE, timeout=5000)
    portfolio = portfolio_prove(GOAL, PREMISES, backends=["z3", "modelfinder"], subsorts=EDGE,
                                timeout=5000, jobs=1)
    assert portfolio.status == chain.status == "unknown"
    assert portfolio.detail == chain.detail


def test_the_edge_through_a_signature_is_read_by_the_prover_that_cannot_read_options():
    signature = Signature.from_dict({"sorts": ["A", "B"], "subsorts": EDGE})
    verdict = portfolio_prove(GOAL, PREMISES, backends=["z3"], signature=signature,
                              timeout=5000, jobs=1)
    assert verdict.status == "proved"                   # with the edge the problem is valid
    assert verdict.backend == "z3"
    assert api.prove(GOAL, PREMISES, backends=["z3"], timeout=5000).status == "refuted"  # without it


def test_a_signature_is_a_signature_object_and_for_classical_logic_only():
    with pytest.raises(TypeError, match="Signature.from_dict"):
        portfolio_prove(GOAL, PREMISES, backends=["z3"], signature={"subsorts": EDGE})
    with pytest.raises(ValueError, match="classical first-order"):
        portfolio_prove(GOAL, PREMISES, backends=["modal-tableau"], logic="modal",
                        signature=Signature.from_dict({"sorts": ["A"]}))


# ---------------------------------------------------------------------------
# An option no member reads is refused, as api.prove refuses it
# ---------------------------------------------------------------------------

def test_an_option_no_member_reads_is_a_value_error_naming_it():
    valid = Atom("P", [])                              # not valid; the point is that nothing runs
    with pytest.raises(ValueError, match="option 'frame' is read by no backend"):
        portfolio_prove(valid, backends=["z3"], frame="S4", jobs=1)
    with pytest.raises(ValueError, match="option 'frame' is read by no backend"):
        api.prove(valid, backends=["z3"], frame="S4")      # the same refusal as the chain's


def test_the_refusal_comes_before_anything_runs(registered):
    seen = registered(_Reads("opt-seen", reads={"colour"}))
    with pytest.raises(ValueError, match="option 'size' is read by no backend"):
        portfolio_prove(GOAL, backends=["opt-seen"], colour=1, size=2, jobs=1)
    assert seen.calls == []


# ---------------------------------------------------------------------------
# Each member is handed only what it reads
# ---------------------------------------------------------------------------

def test_a_member_that_cannot_read_a_question_changing_option_is_not_run(registered):
    reads_colour = registered(_Reads("opt-colour", reads={"colour"}))
    reads_steps = registered(_Reads("opt-steps", reads={"max_steps"}))
    verdict = portfolio_prove(GOAL, backends=["opt-colour", "opt-steps"], colour=1, max_steps=5,
                              jobs=1)
    # `colour` changes the question: opt-steps cannot read it, so it would answer another one.
    assert reads_steps.calls == []
    assert "opt-steps:unknown/unsupported" in verdict.detail and "colour" in verdict.detail
    # `max_steps` only bounds a search: opt-colour is simply not handed it.
    assert reads_colour.calls == [{"colour": 1}]


def test_a_member_that_is_not_run_casts_no_vote(registered):
    registered(_Reads("opt-yes", reads={"colour"}, verdict_status="proved"))
    registered(_Reads("opt-other", reads={"size"}, verdict_status="proved"))
    verdict = portfolio_prove(GOAL, backends=["opt-yes", "opt-other"], colour=1, size=2,
                              require_agreement=2, jobs=1)
    # Each reads ONE of the two options and refuses the other's: nobody answers the question
    # that was asked, so there is nothing to agree on.
    assert verdict.status == "unknown" and verdict.backend == "portfolio"
    assert "opt-yes:unknown/unsupported" in verdict.detail
    assert "opt-other:unknown/unsupported" in verdict.detail


# ---------------------------------------------------------------------------
# Availability is asked for the route the options of the call select
# ---------------------------------------------------------------------------

class _RouteBackend(_Reads):
    """Available only through the route the call names: ``route="via-wsl"``."""

    def __init__(self, name, available_by_default, available_via):
        super().__init__(name, reads={"route"})
        self._default = available_by_default
        self._via = available_via

    def available(self):
        return self._default

    def available_for(self, options):
        return self._via if options.get("route") == "via-wsl" else self._default


def test_a_call_that_names_a_runnable_route_is_not_refused_for_the_default_route(registered):
    backend = registered(_RouteBackend("route-only-named", available_by_default=False, available_via=True))
    verdict = portfolio_prove(GOAL, backends=["route-only-named"], route="via-wsl", jobs=1)
    assert verdict.status == "unknown"
    assert backend.calls == [{"route": "via-wsl"}]
    with pytest.raises(BackendUnavailable, match="route-only-named"):
        portfolio_prove(GOAL, backends=["route-only-named"], jobs=1)


def test_a_call_that_names_a_route_that_cannot_run_is_refused_before_anything_runs(registered):
    backend = registered(_RouteBackend("route-default-only", available_by_default=True, available_via=False))
    with pytest.raises(BackendUnavailable, match="route-default-only"):
        portfolio_prove(GOAL, backends=["route-default-only"], route="via-wsl", jobs=1)
    assert backend.calls == []
    assert portfolio_prove(GOAL, backends=["route-default-only"], jobs=1).status == "unknown"
