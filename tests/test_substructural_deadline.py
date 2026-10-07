"""The intuitionistic linear logic and Lambek backends end at the call's limit.

Both searches are exhaustive over the rule instances of a sequent, and the number of instances is exponential
in its size, so a decision procedure that always terminates can still run for minutes. A backend takes the
call's ``timeout`` (milliseconds) like the other in-house backends and reports UNKNOWN with reason
``timeout`` when the search has not finished: the search that was cut off proves nothing, so it is never
REFUTED.

Two inputs whose unbounded search runs far past the limit, each measured at several seconds (about 4 s at the
time of writing):

* intuitionistic linear logic: ``A0 ⊸ B0, …, A4 ⊸ B4, A0, …, A4 ⊢ Z``. No rule produces ``Z`` from antecedents
  that do not mention it, so the sequent is not derivable, but the ⊸L rule splits the context in every possible
  way for each of the five implications and the search visits all of those splits first.
* the Lambek calculus: ``A0•B0, …, A15•B15 ⊢ Z``. ``Z`` occurs nowhere on the left, so there is no derivation, and
  each •L unfolds one product in place, so the sequences reached are the 2^16 subsets of unfolded products.

Every assertion on time is an upper bound (limit + max(1 s, 25 %)): a slow machine only makes the search
reach the limit sooner, never later.
"""

import time

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_logic_kit.fol._lambek_nodes import Product
from unicode_logic_kit.fol._linear_nodes import LinearImplies
from unicode_logic_kit.fol.nodes import Atom

LIMIT_MS = 300


def atom(name):
    return Atom(name, [])


def within(limit_ms):
    """The longest a call with ``limit_ms`` may take: the limit plus max(1 s, 25 %)."""
    seconds = limit_ms / 1000.0
    return seconds + max(1.0, 0.25 * seconds)


def ill_input():
    premises = [LinearImplies(atom(f"A{i}"), atom(f"B{i}")) for i in range(5)] + [atom(f"A{i}") for i in range(5)]
    return premises, atom("Z")


def lambek_input():
    return [Product(atom(f"A{i}"), atom(f"B{i}")) for i in range(16)], atom("Z")


INPUTS = {"ill": ill_input, "lambek": lambek_input}


@pytest.mark.parametrize("backend", sorted(INPUTS))
def test_a_search_far_above_the_limit_ends_at_the_limit_with_unknown_timeout(backend):
    premises, goal = INPUTS[backend]()
    started = time.perf_counter()
    verdict = get_backend(backend).decide(goal, premises, timeout=LIMIT_MS)
    elapsed = time.perf_counter() - started
    assert elapsed <= within(LIMIT_MS)
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"
    assert verdict.status != REFUTED and verdict.countermodel is None
    assert str(LIMIT_MS) in verdict.detail
    assert 0 <= verdict.wall_time <= within(LIMIT_MS)


@pytest.mark.parametrize("backend", sorted(INPUTS))
def test_through_api_prove_the_chain_ends_at_the_limit_and_says_timeout(backend):
    premises, goal = INPUTS[backend]()
    started = time.perf_counter()
    verdict = api.prove(goal, premises, logic=backend, backends=[backend], timeout=LIMIT_MS)
    assert time.perf_counter() - started <= within(LIMIT_MS)
    assert verdict.status == UNKNOWN and "timeout" in verdict.detail


@pytest.mark.parametrize("backend, patched", [("ill", "unicode_logic_kit.atp.linear.ill_derivable"),
                                              ("lambek", "unicode_logic_kit.atp.lambek.lambek_prove")])
def test_a_search_that_does_not_return_is_cut_off_whatever_the_speed_of_the_machine(backend, patched, monkeypatch):
    # A stand-in search that runs in pure Python for three seconds, then reports a derivation: the backend must
    # not wait for it, and must not turn the answer it never got into a verdict.
    def slow(*args, **kwargs):
        end = time.perf_counter() + 3.0
        while time.perf_counter() < end:
            pass
        return True

    monkeypatch.setattr(patched, slow)
    started = time.perf_counter()
    verdict = get_backend(backend).decide(atom("B"), [atom("A")], timeout=LIMIT_MS)
    assert time.perf_counter() - started <= within(LIMIT_MS)
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


@pytest.mark.parametrize("backend", ["ill", "lambek"])
def test_a_limit_that_has_already_passed_gives_no_verdict(backend):
    # A ⊢ A is the axiom, derivable in no time at all; with no time given the answer is still "no answer".
    verdict = get_backend(backend).decide(atom("A"), [atom("A")], timeout=0)
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


@pytest.mark.parametrize("backend", ["ill", "lambek"])
def test_a_search_that_finishes_in_time_is_answered_as_before(backend):
    # A ⊢ A is derivable (the axiom); A ⊢ B is not (no rule connects two different atoms).
    assert get_backend(backend).decide(atom("A"), [atom("A")], timeout=10000).status == PROVED
    assert get_backend(backend).decide(atom("B"), [atom("A")], timeout=10000).status == REFUTED


@pytest.mark.parametrize("backend", ["ill", "lambek"])
def test_no_limit_runs_the_search_to_its_end(backend):
    assert get_backend(backend).decide(atom("A"), [atom("A")], timeout=None).status == PROVED
    assert get_backend(backend).decide(atom("B"), [atom("A")], timeout=None).status == REFUTED
