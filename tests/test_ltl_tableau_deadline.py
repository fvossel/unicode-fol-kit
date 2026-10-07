"""The LTL tableau reads its clock in every phase: the atoms, the graph between them, and what follows.

The decision builds every locally consistent atom of the closure (``2 ** k`` of them for ``k`` free elements),
the graph of the steps between atoms, and then searches the graph: reachability from the start atoms, the
pruning of atoms with no successor, the strongly connected components, the fairness test of each, and the
walk that makes the witness. Only the first two used to read the clock, so a limit that ran out after the
graph was built was not looked at again, and the search could run for a minute past it.

The workload is ``¬GF(…)`` over a conjunction of ``p ∨ Xp`` for five atoms ``p`` and one more atom ``q ∨ Xq``:
``GF`` of it is satisfiable (every atom true at every position), so the answer is ``invalid``, but the closure has
13 free elements, so the graph has 8192 atoms, and the search after the graph takes about a minute
(measured). With a limit of three seconds the graph is complete and the search that follows is cut off.
"""

import time

import pytest

from unicode_logic_kit.atp import ltl_tableau as lt
from unicode_logic_kit.atp.ltl_tableau import ltl_decide, ltl_valid
from unicode_logic_kit.atp.protocol import REFUTED, UNKNOWN, get_backend
from unicode_logic_kit.fol.nodes import And, Always, Atom, Eventually, Next, Not, Or

SLACK = 5.0



def _deadline():
    """The module of the shared limit, imported where it is used."""
    from unicode_logic_kit import _deadline as module
    return module


def _conjunction(parts):
    out = parts[0]
    for part in parts[1:]:
        out = And(out, part)
    return out


def _wide_formula():
    """``¬GF((P0 ∨ XP0) ∧ … ∧ (P4 ∨ XP4) ∧ (q ∨ Xq))``."""
    letters = [Atom(f"P{i}", []) for i in range(5)] + [Atom("q", [])]
    return Not(Always(Eventually(_conjunction([Or(a, Next(a)) for a in letters]))))


MAX_ATOMS = 1 << 14


def test_a_decision_whose_search_after_the_graph_has_no_end_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    status = ltl_decide(_wide_formula(), max_atoms=MAX_ATOMS, timeout=3000)
    elapsed = time.perf_counter() - start
    assert status in ("unknown", "invalid")           # never "valid": the formula is not valid
    assert elapsed < 3.0 + SLACK


def test_the_backend_ends_at_the_limit_of_the_call():
    start = time.perf_counter()
    verdict = get_backend("ltl-tableau").decide(_wide_formula(), [], timeout=3000, max_atoms=MAX_ATOMS)
    assert time.perf_counter() - start < 3.0 + SLACK
    assert verdict.status in (UNKNOWN, REFUTED)
    if verdict.status == UNKNOWN:
        assert verdict.reason == "timeout"


def test_a_deadline_that_has_passed_gives_no_answer():
    p = Atom("p", [])
    assert lt._run([Not(Or(p, Not(p)))], "initial", 4096, timeout=-1) == ("unknown", None)
    assert ltl_decide(Or(p, Not(p)), timeout=-1) == "unknown"
    assert ltl_valid(Or(p, Not(p)), timeout=-1) is False


def test_a_generous_deadline_decides_as_none_does():
    p = Atom("p", [])
    for timeout in (None, 60_000):
        assert ltl_decide(Or(p, Not(p)), timeout=timeout) == "valid"
        assert ltl_decide(p, timeout=timeout) == "invalid"
        assert ltl_decide(Eventually(Always(p)), timeout=timeout) == "invalid"


# ---------------------------------------------------------------------------------------------
# the graph algorithms, one by one: a ring of five atoms 0 → 1 → 2 → 3 → 4 → 0
# ---------------------------------------------------------------------------------------------
RING = [{(i + 1) % 5} for i in range(5)]


def test_reachability_in_a_ring_is_the_whole_ring_unless_the_deadline_has_passed():
    assert lt._bfs_reachable({0}, RING) == {0, 1, 2, 3, 4}
    assert lt._bfs_reachable({0}, RING, _deadline().instant(60_000)) == {0, 1, 2, 3, 4}
    with pytest.raises(_deadline().DeadlineReached):
        lt._bfs_reachable({0}, RING, _deadline().instant(-1))


def test_the_shortest_path_in_a_ring_is_the_arc_unless_the_deadline_has_passed():
    edges = {i: RING[i] for i in range(5)}
    assert lt._bfs_path(0, {3}, edges) == [0, 1, 2, 3]
    assert lt._bfs_path(0, {3}, edges, _deadline().instant(60_000)) == [0, 1, 2, 3]
    with pytest.raises(_deadline().DeadlineReached):
        lt._bfs_path(0, {3}, edges, _deadline().instant(-1))


def test_pruning_a_ring_keeps_every_atom_unless_the_deadline_has_passed():
    assert lt._prune({0, 1, 2, 3, 4}, RING) == {0, 1, 2, 3, 4}
    assert lt._prune({0, 1, 2, 3, 4}, RING, _deadline().instant(60_000)) == {0, 1, 2, 3, 4}
    # an atom with no successor in the set goes, and its predecessors with it: 0 → 1 → 2, 3 → 3
    chain = [{1}, {2}, set(), {3}]
    assert lt._prune({0, 1, 2, 3}, chain) == {3}
    with pytest.raises(_deadline().DeadlineReached):
        lt._prune({0, 1, 2, 3, 4}, RING, _deadline().instant(-1))


def test_a_ring_is_one_strongly_connected_component_unless_the_deadline_has_passed():
    nodes = {0, 1, 2, 3, 4}
    assert lt._sccs(nodes, RING) == [nodes]
    assert lt._sccs(nodes, RING, _deadline().instant(60_000)) == [nodes]
    with pytest.raises(_deadline().DeadlineReached):
        lt._sccs(nodes, RING, _deadline().instant(-1))


def test_the_closed_walk_around_a_ring_visits_every_atom_unless_the_deadline_has_passed():
    scc = {0, 1, 2, 3, 4}
    edges = {i: RING[i] for i in range(5)}
    assert lt._cycle_visiting_all(0, scc, edges) == [0, 1, 2, 3, 4, 0]
    assert lt._cycle_visiting_all(0, scc, edges, _deadline().instant(60_000)) == [0, 1, 2, 3, 4, 0]
    with pytest.raises(_deadline().DeadlineReached):
        lt._cycle_visiting_all(0, scc, edges, _deadline().instant(-1))


def test_a_fair_witness_in_a_ring_is_found_unless_the_deadline_has_passed():
    # every promise is kept somewhere on the ring (the one fairness set holds atom 2), and the ring is
    # one component: it is the witness, entered at any of its atoms
    atoms = [frozenset()] * 5
    found, entry, scc, _ = lt._has_fair_witness({0}, atoms, RING, [{2}])
    assert found is True and scc == {0, 1, 2, 3, 4} and entry in scc
    found, *_ = lt._has_fair_witness({0}, atoms, RING, [{2}], _deadline().instant(60_000))
    assert found is True
    with pytest.raises(_deadline().DeadlineReached):
        lt._has_fair_witness({0}, atoms, RING, [{2}], _deadline().instant(-1))
    # a promise that is kept nowhere on the ring has no fair witness
    assert lt._has_fair_witness({0}, atoms, RING, [set()])[0] is False


def test_the_fairness_sets_are_read_under_the_deadline():
    promise = Eventually(Atom("p", []))
    atoms = [frozenset(), frozenset({Atom("p", []), promise})]
    # the promise is kept at an atom that does not hold it, and at one that holds its body
    assert lt._fairness_sets(frozenset({promise}), atoms) == [{0, 1}]
    assert lt._fairness_sets(frozenset({promise}), atoms, _deadline().instant(60_000)) == [{0, 1}]
    with pytest.raises(_deadline().DeadlineReached):
        lt._fairness_sets(frozenset({promise}), atoms, _deadline().instant(-1))


# ---------------------------------------------------------------------------------------------
# the search after the graph, on a graph that is given: a ring of n atoms that all make ``p`` true
# ---------------------------------------------------------------------------------------------
def _ring_of_atoms(monkeypatch, size):
    """Make the atoms and the graph of the next decision a ring of ``size`` atoms, each making ``p`` true."""
    p = Atom("p", [])
    atoms = [frozenset({p})] * size
    edges = [{(i + 1) % size} for i in range(size)]
    monkeypatch.setattr(lt, "_all_atoms", lambda cl, max_atoms, deadline=None: atoms)
    monkeypatch.setattr(lt, "_build_graph", lambda a, next_terms, prev_terms, deadline=None: edges)
    return p


def test_a_ring_of_six_atoms_gives_the_lasso_that_goes_once_around(monkeypatch):
    p = _ring_of_atoms(monkeypatch, 6)
    status, trace = lt._run([p], "initial", 4096)
    # every atom is a start, the first is taken, and the walk that visits all of the ring and returns
    # to its start is the cycle: six positions, each with p; the prefix is the start alone
    assert status == "sat"
    assert trace.prefix == (frozenset({"p"}),)
    assert trace.cycle == (frozenset({"p"}),) * 6
    assert lt._run([p], "initial", 4096, timeout=60_000) == (status, trace)


def test_the_search_after_the_graph_of_a_large_ring_repeats_no_reachability_search_per_atom(monkeypatch):
    # Five thousand atoms. The witness needs the atoms reachable from the start atom once, and a search
    # that computed that set again for every one of the atoms took 7.8 seconds (measured) for this ring;
    # the search now takes a few milliseconds, and in any case ends at its limit.
    p = _ring_of_atoms(monkeypatch, 5000)
    start = time.perf_counter()
    status, trace = lt._run([p], "initial", 1 << 20, timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert status in ("unknown", "sat")
