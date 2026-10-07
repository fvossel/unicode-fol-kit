"""``portfolio_prove`` reads the caller's input as ``api.prove`` does, and a caller's error is
the same outcome whatever ``jobs`` is.

* The premises are the caller's own premises plus what the call appends (the sentences of
  ``signature=``, the side axioms of a ``Sentence``). ``premise_names=`` names the caller's
  premises, and the appended ones are named for the writer: one name per premise reaches the
  member, with the caller's names first and in place.
* A member that refuses the CALL (an unknown modal frame, a ``premise_names`` list of the wrong
  length) raises ``ValueError`` out of ``portfolio_prove`` for ``jobs=1``, for a process pool and
  for ``api.prove`` alike. A worker that fails for a reason that is not the caller's is
  recorded as ``error`` / ``infra``, as before.

The problem used for the signature: the subsort edge ``A < B``, the premise ``∀x:B P(x)`` and the
goal ``∀x:A P(x)`` — valid, because every element of ``A`` is an element of ``B``.
"""

from concurrent.futures import Future
from concurrent.futures.process import BrokenProcessPool

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import portfolio as portfolio_module
from unicode_logic_kit.atp.portfolio import portfolio_prove
from unicode_logic_kit.atp.protocol import (
    BackendUnavailable, ProverBackend, Verdict, _REGISTRY, get_backend, register_backend,
)
from unicode_logic_kit.fol._msfl_nodes import SortedQuantifier
from unicode_logic_kit.fol.nodes import Atom, Constant, Variable
from unicode_logic_kit.fol.signature import Signature
from unicode_logic_kit.logic import Sentence

_X = Variable("x")
GOAL = SortedQuantifier("∀", _X, "A", Atom("P", [_X]))
PREMISES = [SortedQuantifier("∀", _X, "B", Atom("P", [_X]))]
SIGNATURE = Signature.from_dict({"sorts": ["A", "B"], "subsorts": {"A": ["B"]}})

ALPHA = Constant("alpha")
P_ALPHA = Atom("P", [ALPHA])
Q_ALPHA = Atom("Q", [ALPHA])


class _Recorder(ProverBackend):
    """A first-order member that reads ``premise_names`` and records what it is handed."""

    logics = frozenset({"fol"})
    external = False

    def __init__(self, name):
        self.name = name
        self.calls = []

    def available(self):
        return True

    def accepted_options(self, logic=None):
        return frozenset({"premise_names"})

    def decide(self, formula, premises=(), timeout=10000, **options):
        self.calls.append((formula, list(premises), options.get("premise_names")))
        return Verdict("unknown", self.name)


@pytest.fixture
def recorder():
    backend = _Recorder("caller-input-recorder")
    register_backend(backend)
    yield backend
    _REGISTRY.pop(backend.name, None)


class _InlineExecutor:
    """A pool that runs every task in this process (the worker function is the real one)."""

    def __init__(self, max_workers=None):
        pass

    def submit(self, fn, payload):
        future: Future = Future()
        try:
            future.set_result(fn(payload))
        except BaseException as exc:         # the way a pool hands a worker's exception back
            future.set_exception(exc)
        return future

    def shutdown(self, wait=True, cancel_futures=False):
        pass


def _executor_failing_with(exc):
    class _Failing(_InlineExecutor):
        def submit(self, fn, payload):
            future: Future = Future()
            future.set_exception(exc)
            return future
    return _Failing


# ---------------------------------------------------------------------------
# The caller's premises are counted as api.prove counts them
# ---------------------------------------------------------------------------

class TestPremiseNamesWithBackground:
    @pytest.mark.parametrize("jobs", [1, 2])
    def test_signature_and_names_reach_the_member_as_api_prove_hands_them(
            self, recorder, monkeypatch, jobs):
        monkeypatch.setattr(portfolio_module, "ProcessPoolExecutor", _InlineExecutor)
        api.prove(GOAL, PREMISES, backends=[recorder.name], signature=SIGNATURE,
                  premise_names=["h"], logic="fol")
        via_prove = recorder.calls.pop()
        portfolio_prove(GOAL, PREMISES, backends=[recorder.name], signature=SIGNATURE,
                        premise_names=["h"], logic="fol", jobs=jobs)
        via_portfolio = recorder.calls.pop()

        _goal, premises, names = via_portfolio
        assert len(premises) > len(PREMISES)               # the signature added sentences
        assert len(names) == len(premises)                 # one name per premise
        assert names[0] == "h"                             # the caller's name stays first
        assert len(set(names)) == len(names)               # and no name is used twice
        assert via_portfolio[1:] == via_prove[1:]          # the same premises, the same names

    def test_a_wrong_number_of_names_is_the_callers_error_before_any_member_runs(self, recorder):
        for call in (portfolio_prove, api.prove):
            kwargs = {"jobs": 1} if call is portfolio_prove else {}
            with pytest.raises(ValueError, match="premise_names"):
                call(GOAL, PREMISES, backends=[recorder.name], signature=SIGNATURE,
                     premise_names=["h", "k"], logic="fol", **kwargs)
        assert recorder.calls == []

    @pytest.mark.skipif(not get_backend("vampire").available(), reason="Vampire is not installed")
    @pytest.mark.parametrize("jobs", [1, 2])
    def test_vampire_proves_the_signature_problem_with_a_name_for_the_premise(self, jobs):
        # Valid by hand (see the module docstring), and the caller named its one premise.
        verdict = portfolio_prove(GOAL, PREMISES, backends=["vampire"], signature=SIGNATURE,
                                  premise_names=["h"], timeout=8000, jobs=jobs)
        assert verdict.status == "proved"
        assert verdict.relevant_premises in (None, (0,))   # an index into the caller's premises


class TestSentences:
    def test_the_side_axioms_of_a_sentence_are_premises_named_for_the_writer(self, recorder):
        sentence = Sentence(term=Q_ALPHA, logic="fol", axioms=(P_ALPHA,))
        api.prove(P_ALPHA, [sentence], backends=[recorder.name], premise_names=["a"], logic="fol")
        via_prove = recorder.calls.pop()
        portfolio_prove(P_ALPHA, [sentence], backends=[recorder.name], premise_names=["a"],
                        logic="fol", jobs=1)
        via_portfolio = recorder.calls.pop()
        _goal, premises, names = via_portfolio
        assert premises == [Q_ALPHA, P_ALPHA]              # the term, then the side axiom
        assert len(names) == 2 and names[0] == "a"
        assert via_portfolio[1:] == via_prove[1:]

    def test_a_goal_that_only_the_side_axiom_gives_is_proved(self):
        # The premise is Q(alpha) with the side axiom P(alpha); the goal P(alpha) follows from the
        # axiom alone. Without the axiom (a bare Q(alpha)) it does not follow.
        sentence = Sentence(term=Q_ALPHA, logic="fol", axioms=(P_ALPHA,))
        assert portfolio_prove(P_ALPHA, [sentence], backends=["z3"], jobs=1).status == "proved"
        assert portfolio_prove(P_ALPHA, [Q_ALPHA], backends=["z3"], jobs=1).status == "refuted"

    def test_a_sentence_of_another_logic_is_refused_by_name(self):
        modal = Sentence(term=P_ALPHA, logic="modal")
        with pytest.raises(ValueError, match="convert it first"):
            portfolio_prove(P_ALPHA, [modal], backends=["z3"], jobs=1)


# ---------------------------------------------------------------------------
# A caller's error is raised whatever jobs is
# ---------------------------------------------------------------------------

class TestCallerErrorsAreRaised:
    FORMULA = api.parse_any("□P → P").formula
    MODAL = ["modal-tableau", "kripke-enum"]

    @pytest.mark.parametrize("order", [MODAL, MODAL[::-1]], ids=["tableau-first", "enum-first"])
    @pytest.mark.parametrize("jobs", [1, 2])
    def test_an_unknown_frame_is_a_value_error_for_every_jobs(self, order, jobs):
        with pytest.raises(ValueError, match="unknown frame"):
            portfolio_prove(self.FORMULA, backends=order, logic="modal", frame="S9",
                            timeout=8000, jobs=jobs)

    def test_api_prove_raises_the_same_error(self):
        with pytest.raises(ValueError, match="unknown frame"):
            api.prove(self.FORMULA, backends=self.MODAL, logic="modal", frame="S9", timeout=8000)

    def test_a_value_error_out_of_a_worker_is_raised(self, monkeypatch):
        monkeypatch.setattr(portfolio_module, "ProcessPoolExecutor",
                            _executor_failing_with(ValueError("the call is wrong")))
        with pytest.raises(ValueError, match="the call is wrong"):
            portfolio_prove(P_ALPHA, backends=["z3", "modelfinder"], jobs=2)

    def test_an_unavailable_backend_out_of_a_worker_is_raised(self, monkeypatch):
        monkeypatch.setattr(portfolio_module, "ProcessPoolExecutor",
                            _executor_failing_with(BackendUnavailable("gone since the check")))
        with pytest.raises(BackendUnavailable, match="gone since the check"):
            portfolio_prove(P_ALPHA, backends=["z3", "modelfinder"], jobs=2)

    @pytest.mark.parametrize("failure", [RuntimeError("worker died"), BrokenProcessPool("pool broke")],
                             ids=["runtime-error", "broken-pool"])
    def test_a_failure_that_is_not_the_callers_is_recorded_as_infrastructure(
            self, monkeypatch, failure):
        monkeypatch.setattr(portfolio_module, "ProcessPoolExecutor", _executor_failing_with(failure))
        verdict = portfolio_prove(P_ALPHA, backends=["z3", "modelfinder"], jobs=2)
        assert verdict.status == "error" and verdict.reason == "infra"
        assert f"{type(failure).__name__}: {failure}" in verdict.detail
