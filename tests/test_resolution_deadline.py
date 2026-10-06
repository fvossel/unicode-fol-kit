"""The resolution prover's deadline covers the whole call: the normal forms, the seed clauses, the search.

``prove(premises, conclusion, timeout=ms)`` takes the limit from the moment it is called. The conversion
of a formula to clauses can be exponentially larger than the formula, and the preparation of a large set of
seed clauses (sorting them, removing the subsumed ones) is not a step of the search; both used to run
without a clock, so a call with a limit of a second could take minutes. Now everything runs under the
deadline, and the search that follows is given what is left.

Three workloads, each far beyond the limits used here:

* ``(A0 ∧ B0) ∨ (A1 ∧ B1) ∨ … ∨ (A21 ∧ B21)``: its conjunctive normal form has ``2 ** 22`` clauses of
  22 literals (every way of choosing one of the two atoms of each disjunct);
* a chain of 23 equivalences ``((q0 ↔ q1) ↔ q2) ↔ …``: the negation normal form of ``a ↔ b`` mentions each
  of ``a`` and ``b`` twice, so the formula doubles with every equivalence and has about ``2 ** 23``
  occurrences of ``q0``;
* 3000 unit clauses ``P0(a)``, …, ``P2999(a)`` about different predicates: no empty clause can be derived
  (they are jointly satisfiable), and sorting and subsuming the seeds alone is millions of pairwise tests.
"""

import time

from unicode_fol_kit import api
from unicode_fol_kit.atp.protocol import PROVED, UNKNOWN, get_backend
from unicode_fol_kit.atp.resolution import is_valid_resolution, prove, refute
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Iff, Implies, Not, Or

#: A call must end within its limit plus this much.
SLACK = 1.0

GOAL = Atom("Goal", [])


def _disjunction(parts):
    out = parts[0]
    for part in parts[1:]:
        out = Or(out, part)
    return out


def _normal_form_blow_up(width):
    """``(A0 ∧ B0) ∨ … ∨ (A(w-1) ∧ B(w-1))``: its CNF has ``2 ** width`` clauses."""
    return _disjunction([And(Atom(f"A{i}", []), Atom(f"B{i}", [])) for i in range(width)])


def _equivalence_chain(length):
    formula = Atom("q0", [])
    for i in range(1, length):
        formula = Iff(formula, Atom(f"q{i}", []))
    return formula


def test_a_call_whose_clausification_has_no_end_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    assert prove([_normal_form_blow_up(22)], GOAL, timeout=300) is False
    assert time.perf_counter() - start < 0.3 + SLACK


def test_a_call_whose_negation_normal_form_has_no_end_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    assert prove([_equivalence_chain(23)], GOAL, timeout=300) is False
    assert time.perf_counter() - start < 0.3 + SLACK


def test_the_validity_wrapper_is_cut_off_at_its_deadline_too():
    # ¬((A0 ∧ B0) ∨ …) ∨ ... : the negation of the wrapper's argument is clausified
    start = time.perf_counter()
    assert is_valid_resolution(Not(_normal_form_blow_up(22)), timeout=300) is False
    assert time.perf_counter() - start < 0.3 + SLACK


def test_seed_clauses_that_nothing_resolves_are_not_prepared_past_the_deadline():
    a = Constant("a")
    clauses = [frozenset({Atom(f"P{i}", [a])}) for i in range(3000)]
    start = time.perf_counter()
    assert refute(clauses, max_steps=10 ** 9, timeout=300) is False
    assert time.perf_counter() - start < 0.3 + SLACK


def test_a_call_that_is_complete_in_time_answers_as_it_does_without_a_limit():
    # (A0 ∧ B0) ∨ … ∨ (A4 ∧ B4) entails A0 ∨ … ∨ A4 (32 clauses to resolve), and does not entail A0
    premise = _normal_form_blow_up(5)
    some_a = _disjunction([Atom(f"A{i}", []) for i in range(5)])
    for timeout in (None, 60_000):
        assert prove([premise], some_a, timeout=timeout) is True
        assert prove([premise], Atom("A0", []), timeout=timeout) is False
        assert prove([], Implies(Atom("p", []), Atom("p", [])), timeout=timeout) is True
    assert refute([frozenset()], timeout=60_000) is True


def test_a_limit_that_has_passed_is_not_proved():
    assert prove([], Implies(Atom("p", []), Atom("p", [])), timeout=-1) is False
    assert refute([frozenset()], timeout=-1) is False


def test_a_set_that_saturates_is_not_proved_within_a_generous_limit():
    # p ∨ q and ¬p ∨ r do not entail ¬q (p, q and r may all be true): the clauses p ∨ q, ¬p ∨ r, q
    # saturate with no empty clause
    p, q, r = Atom("p", []), Atom("q", []), Atom("r", [])
    assert prove([Or(p, q), Or(Not(p), r)], Not(q), timeout=60_000) is False


# ---------------------------------------------------------------------------------------------
# the backend
# ---------------------------------------------------------------------------------------------
def test_the_backend_reports_a_cut_off_call_as_a_timeout():
    start = time.perf_counter()
    verdict = get_backend("resolution").decide(GOAL, [_normal_form_blow_up(22)], timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def test_the_backend_reports_an_exhausted_step_budget_as_bound_hit():
    # the four clauses p ∨ q, ¬p ∨ q, p ∨ ¬q, ¬p ∨ ¬q are unsatisfiable, and no refutation of them is one step long
    p, q = Atom("p", []), Atom("q", [])
    premises = [Or(p, q), Or(Not(p), q), Or(p, Not(q)), Or(Not(p), Not(q))]
    stopped = get_backend("resolution").decide(GOAL, premises, timeout=60_000, max_steps=1)
    assert stopped.status == UNKNOWN and stopped.reason == "bound_hit"
    assert get_backend("resolution").decide(GOAL, premises, timeout=60_000).status == PROVED


def test_a_chain_of_the_backend_ends_at_the_limit_of_the_call():
    start = time.perf_counter()
    verdict = api.prove(GOAL, [_normal_form_blow_up(22)], backends=["resolution"], timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN
    assert "resolution:unknown/timeout" in verdict.detail
