"""The labelled modal tableau reads its clock inside the frame closure and the box rule, not only between steps.

A step of the search is cheap, and the deadline is read at every step. But a frame condition is closed over
the whole edge set of a branch in one step: transitivity is a loop over every pair of edges, repeated until
nothing is added, so for a chain of ``n`` worlds it is a number of operations of the order of ``n ** 5``
(measured: 0.03 s for 40 worlds, 0.7 s for 80, 4 s for 120, and 40 s for 200). A search that
read its clock only between two steps could therefore run past its deadline by that long. The closure and
the box rule now read it themselves (``_Ctx.poll``), and the search answers ``unknown`` at the deadline.

The workload is the branch of a chain ``0 → 1 → … → 199`` under K4: its transitive closure is the 19900
pairs ``i < j``.
"""

import time

import pytest

from unicode_logic_kit._deadline import DeadlineReached
from unicode_logic_kit.atp import modal_tableau as mt
from unicode_logic_kit.fol.nodes import Atom, Box, Implies

SLACK = 5.0


def _chain_branch(worlds, relation="alethic"):
    """A branch with ``worlds`` worlds, the edges ``w → w + 1`` of one relation, and no formula."""
    branch = mt._Branch()
    branch.tv = {w: set() for w in range(worlds)}
    branch.wcount = worlds
    branch.rels = {relation: {(w, w + 1) for w in range(worlds - 1)}}
    return branch


def test_the_transitive_closure_of_a_long_chain_is_cut_off_at_the_deadline():
    branch = _chain_branch(200)
    ctx = mt._Ctx("K4", None, 400, 10 ** 9, timeout=300)
    start = time.perf_counter()
    with pytest.raises(DeadlineReached):
        mt._frame_close(branch, ctx)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert ctx.exhausted is True and ctx.steps == 0           # the search is over: no step is left


def test_the_transitive_closure_of_a_short_chain_is_the_set_of_pairs_in_order():
    for timeout in (None, 60_000):
        branch = _chain_branch(6)
        ctx = mt._Ctx("K4", None, 400, 10 ** 9, timeout=timeout)
        assert mt._frame_close(branch, ctx) is True
        assert branch.rels["alethic"] == {(i, j) for i in range(6) for j in range(i + 1, 6)}   # 15 pairs
        assert mt._frame_close(branch, ctx) is False                                           # closed
        assert ctx.exhausted is False


def test_reflexivity_symmetry_and_euclideanness_are_closed_as_before_under_a_limit():
    # S5 on the chain 0 → 1 → 2: reflexive, symmetric, transitive and euclidean, so the relation is
    # all nine pairs of the three worlds
    branch = _chain_branch(3)
    ctx = mt._Ctx("S5", None, 400, 10 ** 9, timeout=60_000)
    while mt._frame_close(branch, ctx):
        pass
    assert branch.rels["alethic"] == {(i, j) for i in range(3) for j in range(3)}


def test_the_box_rule_reads_the_clock_once_per_obligation():
    p = Atom("p", [])
    branch = _chain_branch(3)
    branch.boxes = {(0, "alethic", p)}
    expired = mt._Ctx("K", None, 400, 10 ** 9, timeout=-1)
    with pytest.raises(DeadlineReached):
        mt._apply_boxes(branch, expired)
    assert p not in branch.tv[1]                                # nothing was pushed
    live = mt._Ctx("K", None, 400, 10 ** 9, timeout=60_000)
    assert mt._apply_boxes(branch, live) is True
    assert p in branch.tv[1] and p not in branch.tv[2]          # 0 → 1 is the only edge from world 0
    assert mt._apply_boxes(branch) is False                     # a call without a context is as it was


def test_polling_costs_no_step_and_raises_only_after_the_deadline():
    ctx = mt._Ctx("K", None, 400, 1000, timeout=60_000)
    for _ in range(50):
        ctx.poll()
    assert ctx.steps == 1000 and ctx.exhausted is False
    assert mt._Ctx("K", None, 400, 1000).poll() is None         # no deadline: never raises


def test_a_search_whose_deadline_has_passed_is_unknown_and_never_open():
    # the answer of a search that stopped in the middle of a frame closure is not read off its branch
    box = Box(Atom("p", []))
    assert mt.modal_decide(Implies(box, box), frame="K4", timeout=-1) == "unknown"
    assert mt.is_modal_valid(Implies(box, box), frame="K4", timeout=-1) is False
    assert mt.modal_countermodel(Implies(box, box), frame="K4", timeout=-1) is None


def test_a_search_with_a_generous_deadline_decides_as_without_one():
    box = Box(Atom("p", []))
    for timeout in (None, 60_000):
        assert mt.modal_decide(Implies(box, box), frame="K4", timeout=timeout) == "valid"
        assert mt.modal_decide(Box(Atom("p", [])), frame="K4", timeout=timeout) == "invalid"
