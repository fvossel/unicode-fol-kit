# -*- coding: utf-8 -*-
"""The verbs of ``api`` answer for a formula nested thousands of levels deep: a verdict, never an exception.

The interpreter's recursion limit (1000) stops a recursive reader of a formula at a nesting of a few
hundred levels. A verb that takes a formula must not let that surface as a ``RecursionError``: a formula
nested at least a hundred levels deep is read on a worker thread whose stack and recursion limit are sized
for it, and one that is still too deep for a reader says so by its nesting depth.

The questions are derived by hand. ``¬`` applied an even number of times is the identity, so with the
premise ``P`` the chain of 3000 negations over ``P`` is valid, and equivalent to ``P``. Applied an odd
number of times it is ``¬P``, which ``P`` does not entail (the structure with one element where ``P``
holds is a countermodel), and which is not equivalent to ``P``. The nesting depth of ``Not^n(P)`` is
``n + 1``: the atom is one level.

What a verb may answer for a deep formula is the hand-derived answer, or, from a reader that cannot follow
it, ``unknown`` with the nesting depth named: never the opposite answer, never an exception. On the
interpreters measured (CPython before 3.12) the worker manages every formula here, so the answer must be the
hand-derived one; CPython 3.12 and later keep a separate limit on recursion that goes through C, which a
worker's raised limit does not move, and there a reader may still stop and say so.
"""

import sys
import threading

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import ERROR, PROVED, REFUTED, UNKNOWN, Verdict
from unicode_logic_kit.fol.nodes import And, Atom, Box, Constant, Not, Quantifier, Variable

P = Atom("P", [])

#: whether the deep worker is known to manage every formula below
MANAGED = sys.version_info < (3, 12)


def chain(count, base=P):
    formula = base
    for _ in range(count):
        formula = Not(formula)
    return formula


EVEN = chain(3000)
ODD = chain(3001)

# deeper than a deep run takes on: the readers that cannot follow it say so by the nesting depth
TOO_DEEP = 9000


def assert_answer(verdict, expected):
    """``verdict`` is the hand-derived ``expected`` status, or an ``unknown`` that names the depth."""
    if verdict.status in (PROVED, REFUTED):
        assert verdict.status == expected
    else:
        assert not MANAGED, verdict
        assert verdict.status == UNKNOWN and "levels deep" in verdict.detail


def test_the_depth_that_is_too_deep_is_beyond_what_a_deep_run_takes_on():
    assert TOO_DEEP > api._DEEP_MAX_LEVELS


def test_detecting_the_logic_of_a_deep_formula_does_not_recurse():
    assert api._detect_logic(chain(100000, Box(P)), []) == "modal"
    assert api._detect_logic(chain(100000), []) == "fol"
    assert api._detect_logic(P, [chain(100000)]) == "fol"


def test_an_even_chain_of_negations_follows_from_its_atom():
    assert_answer(api.prove(EVEN, [P], backends=["z3"]), PROVED)


def test_an_odd_chain_of_negations_does_not_follow_from_its_atom():
    assert_answer(api.prove(ODD, [P], backends=["z3"]), REFUTED)


def test_the_default_chain_answers_both_chains_correctly():
    assert_answer(api.prove(EVEN, [P]), PROVED)
    assert_answer(api.prove(ODD, [P]), REFUTED)


def test_a_deep_premise_is_read_as_well_as_a_deep_conclusion():
    assert_answer(api.prove(P, [EVEN], backends=["z3"]), PROVED)
    assert api.prove(P, [ODD], backends=["z3"]).status != PROVED         # ¬P does not entail P


def test_a_deep_formula_under_a_quantifier_is_refuted_where_it_is_not_valid():
    # ∀x ¬^3000 P(x) is ∀x P(x), which is not valid: the one-element structure with P empty falsifies it
    px = Atom("P", [Variable("x")])
    formula = Quantifier("∀", Variable("x"), chain(3000, px))
    assert_answer(api.prove(formula, [], backends=["z3"]), REFUTED)


def test_a_right_nested_conjunction_under_a_quantifier_entails_its_instance():
    # ∀x (P(x) ∧ (P(x) ∧ (… ∧ P(x)))) with 400 conjuncts entails P(alpha)
    body = Atom("P", [Variable("x")])
    for _ in range(399):
        body = And(Atom("P", [Variable("x")]), body)
    premise = Quantifier("∀", Variable("x"), body)
    goal = Atom("P", [Constant("alpha")])
    assert_answer(api.prove(goal, [premise], backends=["z3"]), PROVED)
    assert_answer(api.prove(goal, [premise]), PROVED)


def test_the_intuitionistic_route_reads_a_deep_chain():
    # P ⊢ ¬¬¬¬P, and so on for every even count (P ⊢ ¬¬P, and ¬¬P ⊢ ¬¬¬¬P); but P ⊬ ¬P, and an odd
    # chain is ¬P in intuitionistic logic as well (¬¬¬A and ¬A are interderivable)
    even = api.prove(EVEN, [P], logic="intuitionistic", backends=["intuitionistic"])
    odd = api.prove(ODD, [P], logic="intuitionistic", backends=["intuitionistic"])
    assert_answer(even, PROVED)
    assert_answer(odd, REFUTED)


def test_a_countermodel_is_found_for_the_odd_chain_and_not_for_the_even_one():
    odd, even = api.countermodel(ODD, [P]), api.countermodel(EVEN, [P])
    assert even.found is False                      # nothing can be found for a valid entailment
    if not odd.found:
        assert not MANAGED and "levels deep" in odd.reason
    if even.reason is not None:
        assert not MANAGED and "levels deep" in even.reason


def test_a_deep_formula_is_checked():
    report = api.check(EVEN)
    assert report.error is None or (not MANAGED and "levels deep" in report.error)
    if report.error is None:
        assert report.ok and report.is_closed
    open_formula = chain(3000, Atom("P", [Variable("x")]))
    report = api.check(open_formula)
    if report.error is None:
        assert report.ok is False and report.free_variables == ("x",)      # x is free
    else:
        assert not MANAGED and "levels deep" in report.error


def test_equivalence_of_a_deep_formula_with_its_atom():
    even = api.equivalent(EVEN, P)                  # double negations cancel
    odd = api.equivalent(ODD, P)                    # ¬P is not P
    for result, expected in ((even, True), (odd, False)):
        if result.equivalent is None:
            assert not MANAGED and "levels deep" in result.reason
        else:
            assert result.equivalent is expected
    if odd.equivalent is False:
        assert odd.counterexample is not None


def test_a_deep_formula_is_translated():
    deep = chain(3000, Box(P))
    try:
        translated = api.translate(deep, "modal", "fol")
    except ValueError as refused:
        assert not MANAGED and "levels deep" in str(refused)
    else:
        assert isinstance(translated.result, Not)   # the image of a negation is a negation


# -- beyond what a deep run takes on: a verdict that names the nesting depth ---------------------------

def test_a_formula_too_deep_for_every_reader_is_unknown_with_its_depth_named():
    verdict = api.prove(chain(TOO_DEEP), [P], backends=["z3"])
    assert verdict.status == UNKNOWN
    assert f"{TOO_DEEP + 1} levels deep" in verdict.detail
    assert "recursion limit" in verdict.detail


def test_the_depth_is_named_for_every_backend_that_cannot_read_the_formula():
    verdict = api.prove(chain(TOO_DEEP), [P], backends=["z3", "resolution", "modelfinder"])
    assert verdict.status == UNKNOWN
    for backend in ("z3", "resolution", "modelfinder"):
        assert f"{backend}:unknown/bound_hit" in verdict.detail
    assert verdict.detail.count(f"{TOO_DEEP + 1} levels deep") == 3


def test_a_formula_too_deep_for_the_checks_is_reported_with_its_depth():
    report = api.check(chain(TOO_DEEP))
    assert report.ok is False and report.parseable is True
    assert f"{TOO_DEEP + 1} levels deep" in report.error


def test_a_countermodel_search_that_could_not_read_the_formula_says_so():
    result = api.countermodel(chain(TOO_DEEP + 1), [P])
    assert result.found is False
    assert f"{TOO_DEEP + 2} levels deep" in result.reason
    assert result.to_dict()["reason"] == result.reason


def test_an_equivalence_that_could_not_read_the_formula_is_undecided():
    result = api.equivalent(chain(TOO_DEEP), P)
    assert result.equivalent is None
    assert f"{TOO_DEEP + 1} levels deep" in result.reason


def test_a_translation_too_deep_to_read_is_a_value_error_that_names_the_depth():
    with pytest.raises(ValueError, match=f"{TOO_DEEP + 2} levels deep"):
        api.translate(chain(TOO_DEEP, Box(P)), "modal", "fol")


# -- how a member that could not read a deep formula is reported ---------------------------------------

def test_a_member_that_ran_out_of_recursion_is_unknown_with_the_depth():
    ran_out = Verdict(ERROR, "demo", reason="infra",
                      detail="RecursionError: maximum recursion depth exceeded")
    named = api._name_nesting(ran_out, 500)
    assert (named.status, named.reason) == (UNKNOWN, "bound_hit")
    assert "500 levels deep" in named.detail and "demo backend" in named.detail


def test_a_member_that_mentions_the_recursion_limit_gets_the_depth_added():
    said = Verdict(UNKNOWN, "demo", reason="bound_hit",
                   detail="the formula is nested deeper than the recursion limit lets it read it")
    named = api._name_nesting(said, 500)
    assert named.status == UNKNOWN and named.reason == "bound_hit"
    assert named.detail.startswith(said.detail) and "500 levels deep" in named.detail
    # one that already names a depth is left alone
    named_already = Verdict(UNKNOWN, "demo", detail="nested 3002 levels deep: recursion limit (1000)")
    assert api._name_nesting(named_already, 500) is named_already


def test_nothing_else_is_rewritten():
    infra = Verdict(ERROR, "demo", reason="infra", detail="RecursionError: maximum recursion depth exceeded")
    assert api._name_nesting(infra, 99) is infra                     # a shallow formula: a bug elsewhere
    proved = Verdict(PROVED, "demo")
    assert api._name_nesting(proved, 5000) is proved
    other = Verdict(ERROR, "demo", reason="infra", detail="ValueError: no")
    assert api._name_nesting(other, 5000) is other
    unrelated = Verdict(UNKNOWN, "demo", reason="bound_hit", detail="tail recursion was not enough")
    assert api._name_nesting(unrelated, 5000) is unrelated


# -- the worker leaves the process as it found it ------------------------------------------------------

def test_the_recursion_limit_and_the_thread_stack_size_are_restored():
    limit, stack = sys.getrecursionlimit(), threading.stack_size()
    api.prove(EVEN, [P], backends=["z3"])
    api.check(EVEN)
    api.prove(chain(TOO_DEEP), [P], backends=["z3"])
    assert sys.getrecursionlimit() == limit
    assert threading.stack_size() == stack


def test_what_the_work_raises_is_raised_on_the_calling_thread_and_the_limit_is_restored():
    limit = sys.getrecursionlimit()
    with pytest.raises(ZeroDivisionError):
        api._call_deep(3000, lambda: 1 // 0)
    assert sys.getrecursionlimit() == limit


def test_a_deep_call_made_from_the_worker_runs_where_it_is():
    # waiting for the lock that its own caller holds would wait for itself
    assert api._call_deep(3000, lambda: api._call_deep(5000, lambda: "inner")) == "inner"


def test_a_shallow_formula_is_decided_on_the_calling_thread():
    seen = []
    api._call_deep(50, lambda: seen.append(threading.current_thread()))
    api._call_deep(3000, lambda: seen.append(threading.current_thread()))
    assert seen[0] is threading.current_thread()
    assert seen[1] is not threading.current_thread()


def test_an_option_that_no_backend_reads_is_still_a_value_error_for_a_deep_formula():
    with pytest.raises(ValueError):
        api.prove(EVEN, [P], backends=["z3"], no_such_option=1)
