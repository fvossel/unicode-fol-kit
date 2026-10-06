"""The finite model finder ends at its deadline (``timeout``, milliseconds), and says that it did.

``find_model`` / ``find_countermodel`` take ``timeout`` (default ``None``: no limit, the search is
the one it always was) and answer ``None`` for a search it cut off, like for a search that found
nothing; ``search_model`` / ``search_countermodel`` return a ``ModelSearch`` whose ``timed_out``
tells the two apart. The ``modelfinder`` backend reports ``unknown`` with reason ``timeout`` for the
first and ``bound_hit`` for the second.

The workload is a theory with NO finite model, so that the search can only end at its bounds or at
its deadline. "Every element has an ``R``-successor, ``R`` is transitive and ``R`` is irreflexive":
following successors from any element of a finite domain leads to a cycle, and transitivity then
makes the elements of the cycle ``R``-related to themselves, which irreflexivity forbids. Over
domains of up to four elements the search enumerates ``2 ** 16`` relations in its last size, and
takes about 50 seconds (measured) to give up.
"""

import inspect
import time

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.protocol import UNKNOWN, get_backend
from unicode_fol_kit.semantics import modelfinder
from unicode_fol_kit.semantics.modelfinder import (
    find_countermodel, find_model, is_satisfiable_finite, is_valid_finite,
)

#: A call must end within its limit plus this much.
SLACK = 1.0


def F(text):
    return api.parse_any(text).formula


SERIAL_ORDER = [F("∀x ∃y R(x, y)"), F("∀x ∀y ∀z (R(x, y) ∧ R(y, z) → R(x, z))"), F("∀x ¬R(x, x)")]
GOAL = F("∃x P(x)")

#: the same theory over the sort A
SORTED_SERIAL_ORDER = [F("∀x:A ∃y:A R(x, y)"), F("∀x:A ∀y:A ∀z:A (R(x, y) ∧ R(y, z) → R(x, z))"),
                       F("∀x:A ¬R(x, x)")]
SORTED_GOAL = F("∃x:A R(x, x)")


def test_a_countermodel_search_without_an_end_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    search = modelfinder.search_countermodel(SERIAL_ORDER, GOAL, timeout=300)
    elapsed = time.perf_counter() - start
    assert search == modelfinder.ModelSearch(None, True)
    assert elapsed < 0.3 + SLACK


def test_a_model_search_without_an_end_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    search = modelfinder.search_model(SERIAL_ORDER, timeout=300)
    assert search == modelfinder.ModelSearch(None, True)
    assert time.perf_counter() - start < 0.3 + SLACK


def test_find_countermodel_answers_none_for_a_search_that_was_cut_off():
    start = time.perf_counter()
    assert find_countermodel(SERIAL_ORDER, GOAL, timeout=300) is None
    assert find_model(SERIAL_ORDER, timeout=300) is None
    assert time.perf_counter() - start < 2 * (0.3 + SLACK)


def test_a_many_sorted_search_without_an_end_is_cut_off_at_its_deadline():
    # Over four elements it enumerates 15 sort choices times 2 ** 16 relations; none is a model.
    start = time.perf_counter()
    search = modelfinder.search_countermodel(SORTED_SERIAL_ORDER, SORTED_GOAL, timeout=300)
    assert search == modelfinder.ModelSearch(None, True)
    assert time.perf_counter() - start < 0.3 + SLACK


@pytest.mark.parametrize("symmetry_breaking", [True, False])
def test_both_unsorted_enumerations_are_cut_off_at_their_deadline(symmetry_breaking):
    start = time.perf_counter()
    search = modelfinder.search_countermodel(SERIAL_ORDER, GOAL, symmetry_breaking=symmetry_breaking, timeout=300)
    assert search == modelfinder.ModelSearch(None, True)
    assert time.perf_counter() - start < 0.3 + SLACK


@pytest.mark.parametrize("formulas, symmetry_breaking", [
    ([F("P(alpha)")], True),                           # the LNH enumeration
    ([F("P(alpha)")], False),                          # the plain enumeration
    ([F("P(alpha)"), F("∀x:A Q(x)")], True),           # the many-sorted enumeration
])
def test_a_deadline_that_has_passed_ends_the_search_before_the_first_candidate(formulas, symmetry_breaking):
    # ``P(alpha)`` has a model over one element, and the first candidate there is one: it is not
    # even looked at, in any of the three enumerations
    assert modelfinder.search_model(formulas, symmetry_breaking=symmetry_breaking, timeout=-1) == modelfinder.ModelSearch(None, True)
    assert find_model(formulas, symmetry_breaking=symmetry_breaking, timeout=-1) is None


def test_a_search_that_is_complete_before_its_deadline_is_not_a_timeout():
    # ``P ∧ ¬P`` has no model of any size: sizes 1 and 2 are searched in full, then the bound
    contradiction = F("P(alpha) ∧ ¬P(alpha)")
    assert modelfinder.search_model([contradiction], max_size=2, timeout=60_000) == modelfinder.ModelSearch(None, False)
    # and a search that finds a model says so, with no timeout
    found = modelfinder.search_model([F("P(alpha)")], timeout=60_000)
    assert found.structure is not None and found.timed_out is False


def test_a_call_without_a_timeout_searches_as_it_always_did():
    assert find_model([F("P(alpha)")]) is not None
    assert find_model([F("P(alpha) ∧ ¬P(alpha)")], max_size=2) is None
    assert find_countermodel([], F("P(alpha) ∨ ¬P(alpha)")) is None
    assert find_countermodel([], F("P(alpha)")) is not None
    # the same structure with and without a generous limit
    plain = find_model([F("R(alpha, beta) ∧ ¬R(beta, alpha)")])
    timed = find_model([F("R(alpha, beta) ∧ ¬R(beta, alpha)")], timeout=60_000)
    assert repr(plain) == repr(timed)


def test_the_boolean_wrappers_take_no_timeout():
    # a bool has no value for "no answer": a search cut off would read as "no model" or as "valid"
    assert "timeout" not in inspect.signature(is_satisfiable_finite).parameters
    assert "timeout" not in inspect.signature(is_valid_finite).parameters


# ---------------------------------------------------------------------------------------------
# the backend
# ---------------------------------------------------------------------------------------------
def test_the_backend_reports_a_cut_off_search_as_a_timeout():
    start = time.perf_counter()
    verdict = get_backend("modelfinder").decide(GOAL, SERIAL_ORDER, timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"
    assert "300 ms" in verdict.detail


def test_the_backend_reports_an_exhausted_bound_as_bound_hit():
    # two sizes, searched in full, in less than a second: the limit is not what ended the search
    verdict = get_backend("modelfinder").decide(GOAL, SERIAL_ORDER, timeout=60_000, max_size=2)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"


def test_the_backend_still_refutes_with_a_limit():
    verdict = get_backend("modelfinder").decide(F("P(alpha)"), [], timeout=60_000)
    assert verdict.status == "refuted"


def test_a_chain_of_one_backend_ends_at_the_limit_of_the_call():
    start = time.perf_counter()
    verdict = api.prove(GOAL, SERIAL_ORDER, backends=["modelfinder"], timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN
    assert "modelfinder:unknown/timeout" in verdict.detail


def test_the_limit_is_not_an_option_the_backend_declares():
    # ``timeout`` is the parameter of ``decide`` itself, as for every backend
    from unicode_fol_kit.atp.protocol import declared_options
    assert "timeout" not in declared_options(get_backend("modelfinder"), "fol")
    assert {"max_size", "max_candidates", "symmetry_breaking", "subsorts"} <= declared_options(
        get_backend("modelfinder"), "fol")
