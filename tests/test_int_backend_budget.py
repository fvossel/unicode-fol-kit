# -*- coding: utf-8 -*-
"""The intuitionistic backend reports a spent step budget as a bound, not as a failure.

``int_prove`` (Dyckhoff's G4ip) terminates, but the number of steps it takes is exponential in the nesting of
implications; it counts its steps and stops at a budget. A search that stopped there has not decided the
sequent: it is ``unknown`` with the reason ``bound_hit``, which is what exhausting a search budget is for
every other backend. It was an ``error`` / ``infra`` verdict: the backend did not fail, the question was
too large for the budget.

A recursion that ran out of stack is a ``RuntimeError`` too, and a spent budget it is not: it is not
reported as one. By hand, ``P → (Q → P)`` is decided in two steps (the step of the sequent, and the step of
the sequent that the implication on the right leaves), so a budget of one step is spent on it, and a budget
of 200000 steps is not.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import lj
from unicode_fol_kit.atp.protocol import ERROR, PROVED, UNKNOWN, get_backend
from unicode_fol_kit.fol.nodes import Atom, Implies, Not

P = Atom("P", [])
Q = Atom("Q", [])


def peirce_chain(depth):
    """Nested Peirce implications: not intuitionistically valid, and exponentially costly for G4ip."""
    formula = Atom("p0", [])
    for k in range(1, depth + 1):
        formula = Implies(Implies(formula, Atom(f"p{k}", [])), formula)
    return formula


def test_a_spent_step_budget_is_a_bound_not_an_error(monkeypatch):
    monkeypatch.setattr(lj, "_MAX_STEPS", 1)
    # P → (Q → P) is valid, but not within one step
    goal = Implies(P, Implies(Q, P))
    verdict = get_backend("intuitionistic").decide(goal, [], timeout=20000)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"
    assert "step budget (1 steps)" in verdict.detail


def test_the_same_sequent_is_proved_within_the_real_budget():
    goal = Implies(P, Implies(Q, P))
    assert get_backend("intuitionistic").decide(goal, [], timeout=20000).status == PROVED


def test_through_the_api_it_is_unknown_and_not_error(monkeypatch):
    monkeypatch.setattr(lj, "_MAX_STEPS", 1)
    goal = Implies(P, Implies(Q, P))
    verdict = api.prove(goal, [], logic="intuitionistic", backends=["intuitionistic"])
    assert verdict.status == UNKNOWN
    assert "intuitionistic:unknown/bound_hit" in verdict.detail


def test_a_nested_peirce_chain_that_spends_the_budget_is_unknown_through_the_api(monkeypatch):
    # a small budget keeps the test short; the chain has four nested implications and needs more
    # than three steps
    monkeypatch.setattr(lj, "_MAX_STEPS", 3)
    verdict = api.prove(peirce_chain(4), [], logic="intuitionistic", backends=["intuitionistic"])
    assert verdict.status == UNKNOWN
    assert "bound_hit" in verdict.detail and verdict.status != ERROR


def test_another_runtime_error_is_still_a_failure(monkeypatch):
    def broken(premises, conclusion):
        raise RuntimeError("something else broke")

    monkeypatch.setattr(lj, "int_prove", broken)
    with pytest.raises(RuntimeError, match="something else broke"):
        get_backend("intuitionistic").decide(P, [], timeout=20000)
    verdict = api.prove(P, [], logic="intuitionistic", backends=["intuitionistic"])
    assert verdict.status == ERROR
    assert "something else broke" in verdict.detail


def test_a_recursion_that_ran_out_is_a_bound_of_its_own_and_not_the_spent_budget(monkeypatch):
    def too_deep(premises, conclusion):
        raise RecursionError("maximum recursion depth exceeded")

    monkeypatch.setattr(lj, "int_prove", too_deep)
    verdict = get_backend("intuitionistic").decide(P, [], timeout=20000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit")
    assert "recursion limit" in verdict.detail
    assert "step budget" not in verdict.detail


def test_a_search_longer_than_the_stack_ends_as_a_bound_and_never_as_an_exception():
    # f0 = p0, fk = ((f(k-1) -> pk) -> f(k-1)): the nesting of f8 is 17 levels, but the search
    # for it applies rules along branches about a thousand frames long and runs for hundreds
    # of thousands of steps. Whichever bound it meets first, the answer is that bound.
    formula = Atom("p0", [])
    for k in range(1, 9):
        formula = Implies(Implies(formula, Atom(f"p{k}", [])), formula)
    verdict = get_backend("intuitionistic").decide(formula, [], timeout=120000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit")
    assert "recursion limit" in verdict.detail or "step budget" in verdict.detail
