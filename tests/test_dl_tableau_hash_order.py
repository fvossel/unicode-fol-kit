r"""The tableau searches in an order that does not depend on ``PYTHONHASHSEED``.

The completion rules each take "the first" unresolved disjunction, existential,
≥-restriction, choice or merge they meet. A branch kept its labels and its edges in
``set`` s, and a ``set`` of strings (or of concepts, which hash their names) iterates
in an order that follows the hash seed of the process, so one knowledge base was
searched in a different order from one run to the next: a different number of steps
and, near the step budget, a verdict on one run and "step budget exhausted" on the
next. The verdict itself never changed (an order is a choice among complete rules);
the budget outcome did.

What is checked is a property of the process, so it is checked in child processes
under several hash seeds, each of which reports the outcome and the number of
tableau steps it used:

* PHP(4, 3), the pigeonhole concept (four pigeons, three holes, every pigeon in some
  hole, no two in one hole), which is UNSATISFIABLE by the pigeonhole principle, as a
  conjunction of 4 + 3·6 = 22 disjunctions. It is the shape where the order of the
  choices decides the size of the search. The step count ``S`` of one run is
  measured, and every hash seed must then (a) decide it with a budget of ``S + 1``
  steps, using exactly ``S``, and (b) exhaust a budget of ``S``: the budget outcome
  is the same under every seed.
* A battery of 60 small random problems (concepts and knowledge bases with GCIs,
  disjunctions, existentials, number restrictions, a role hierarchy, transitive and
  functional roles, ABoxes), each reporting its outcome and its step count: the
  whole table is the same under every hash seed.
"""

import json
import os
import subprocess
import sys

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import tableau

HASH_SEEDS = (0, 1, 2, 3, 4)

_CHILD = r'''
import json
import random
import sys

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import tableau as T

spec = json.loads(sys.argv[1])


class Recording(T._Ctx):
    last = None

    def __init__(self, n):
        super().__init__(n)
        Recording.last = self
        self.start = n


T._Ctx = Recording


def run(solve, budget):
    T.MAX_STEPS = budget
    try:
        outcome = "sat" if solve() else "unsat"
    except RuntimeError:
        outcome = "budget"
    return [outcome, Recording.last.start - Recording.last.steps]


def pigeonhole(n_pigeons, n_holes):
    letter = {(i, k): dl.Atomic(f"InHole{k}Pigeon{i}")
              for i in range(n_pigeons) for k in range(n_holes)}
    clauses = []
    for i in range(n_pigeons):
        clause = letter[(i, 0)]
        for k in range(1, n_holes):
            clause = dl.Or(clause, letter[(i, k)])
        clauses.append(clause)
    for k in range(n_holes):
        for i in range(n_pigeons):
            for j in range(i + 1, n_pigeons):
                clauses.append(dl.Or(dl.Not(letter[(i, k)]), dl.Not(letter[(j, k)])))
    concept = clauses[0]
    for clause in clauses[1:]:
        concept = dl.And(concept, clause)
    return concept


NAMES = ["A", "B", "C", "D", "E", "F"]
ROLES = ["r", "s", "t"]


def concept(rng, depth, numbers):
    if depth == 0 or rng.random() < 0.25:
        c = dl.Atomic(rng.choice(NAMES))
        return dl.Not(c) if rng.random() < 0.3 else c
    kind = rng.choice(["and", "or", "or", "some", "all", "not"]
                      + (["atleast", "atmost"] if numbers else []))
    if kind == "and":
        return dl.And(concept(rng, depth - 1, numbers), concept(rng, depth - 1, numbers))
    if kind == "or":
        return dl.Or(concept(rng, depth - 1, numbers), concept(rng, depth - 1, numbers))
    if kind == "some":
        return dl.Exists(rng.choice(ROLES), concept(rng, depth - 1, numbers))
    if kind == "all":
        return dl.ForAll(rng.choice(ROLES), concept(rng, depth - 1, numbers))
    if kind == "atleast":
        return dl.AtLeast(rng.choice([1, 2]), rng.choice(ROLES), concept(rng, depth - 1, numbers))
    if kind == "atmost":
        return dl.AtMost(rng.choice([1, 2]), rng.choice(ROLES), concept(rng, depth - 1, numbers))
    return dl.Not(concept(rng, depth - 1, numbers))


def problem(seed):
    rng = random.Random(seed)
    numbers = rng.random() < 0.4
    tbox = dl.TBox()
    for _ in range(rng.randint(2, 6)):
        tbox.add(concept(rng, 2, numbers), concept(rng, 2, numbers))
    if rng.random() < 0.4:
        tbox.add_role_inclusion("s", "r")
    if rng.random() < 0.3 and not numbers:
        tbox.add_transitive_role("t")
    if rng.random() < 0.3:
        tbox.add_functional_role("s")
    goal = concept(rng, 3, numbers)
    abox = None
    if rng.random() < 0.4:
        abox = dl.ABox()
        for ind in ("a", "b", "c")[: rng.randint(1, 3)]:
            abox.assert_concept(ind, concept(rng, 2, numbers))
        if rng.random() < 0.7:
            abox.assert_role("a", "b", rng.choice(ROLES))
    return tbox, goal, abox


if spec["job"] == "pigeonhole":
    c = pigeonhole(spec["pigeons"], spec["holes"])
    print(json.dumps([run(lambda: T.concept_satisfiable(c), budget) for budget in spec["budgets"]]))
else:
    table = {}
    for seed in range(spec["first"], spec["first"] + spec["count"]):
        tbox, goal, abox = problem(seed)
        if abox is None:
            table[str(seed)] = run(lambda: T.concept_satisfiable(goal, tbox), spec["budget"])
        else:
            table[str(seed)] = run(lambda: T.abox_consistent(abox, tbox), spec["budget"])
    print(json.dumps(table))
'''


def _child(hash_seed, spec):
    """What a child process started under ``PYTHONHASHSEED=hash_seed`` prints for ``spec``."""
    env = dict(os.environ, PYTHONHASHSEED=str(hash_seed), PYTHONDONTWRITEBYTECODE="1",
               PYTHONIOENCODING="utf-8",
               PYTHONPATH=os.pathsep.join(path for path in sys.path if path))
    done = subprocess.run([sys.executable, "-c", _CHILD, json.dumps(spec)], env=env,
                          capture_output=True, text=True, timeout=900)
    assert done.returncode == 0, done.stderr[-2000:]
    return json.loads(done.stdout.strip().splitlines()[-1])


def test_the_step_budget_outcome_of_a_pigeonhole_concept_is_the_same_under_every_hash_seed():
    spec = {"job": "pigeonhole", "pigeons": 4, "holes": 3}
    [[outcome, steps]] = _child(0, dict(spec, budgets=[1_000_000]))
    assert outcome == "unsat"                 # the pigeonhole principle, PHP(4, 3)
    assert steps > 100                        # a search, not a one-step clash
    for hash_seed in HASH_SEEDS:
        enough, one_short = _child(hash_seed, dict(spec, budgets=[steps + 1, steps]))
        assert enough == ["unsat", steps], (hash_seed, enough, steps)
        assert one_short[0] == "budget", (hash_seed, one_short, steps)


def test_the_outcome_and_step_count_of_random_problems_are_the_same_under_every_hash_seed():
    spec = {"job": "battery", "first": 0, "count": 60, "budget": 400}
    tables = {hash_seed: _child(hash_seed, spec) for hash_seed in HASH_SEEDS}
    reference = tables[HASH_SEEDS[0]]
    for hash_seed in HASH_SEEDS[1:]:
        differing = sorted((seed for seed in reference if reference[seed] != tables[hash_seed][seed]),
                           key=int)
        assert not differing, (hash_seed, [(seed, reference[seed], tables[hash_seed][seed])
                                           for seed in differing[:5]])
    # the table has teeth: both verdicts occur, and so do searches of more than a step
    outcomes = {outcome for outcome, _steps in reference.values()}
    assert {"sat", "unsat"} <= outcomes
    assert sum(steps > 20 for _outcome, steps in reference.values()) >= 10


# --------------------------------------------------------------------------- #
# The container the order is made of.
# --------------------------------------------------------------------------- #

def test_an_ordered_set_iterates_in_the_order_of_first_insertion():
    members = tableau._OrderedSet()
    for name in ("zeta", "alpha", "mid", "alpha", "beta", "zeta"):
        members.add(name)
    assert list(members) == ["zeta", "alpha", "mid", "beta"]
    members.update(["omega", "alpha", "beta", "gamma"])
    assert list(members) == ["zeta", "alpha", "mid", "beta", "omega", "gamma"]
    members |= ["delta", "zeta"]
    assert list(members) == ["zeta", "alpha", "mid", "beta", "omega", "gamma", "delta"]
    assert "mid" in members and "nu" not in members and len(members) == 7


def test_an_ordered_set_is_a_superset_of_any_set_it_contains():
    members = tableau._OrderedSet(["a", "b", "c"])
    assert members >= {"a", "c"} and members >= tableau._OrderedSet(["c", "b"])
    assert members >= set() and members >= members
    assert not members >= {"a", "d"} and not members >= tableau._OrderedSet(["a", "d"])
    assert not tableau._OrderedSet(["a"]) >= members


def test_the_copy_of_an_ordered_set_keeps_its_order_and_shares_nothing():
    members = tableau._OrderedSet(["x", "a", "m"])
    duplicate = members.copy()
    assert list(duplicate) == ["x", "a", "m"] and isinstance(duplicate, tableau._OrderedSet)
    duplicate.add("b")
    members.add("c")
    assert list(members) == ["x", "a", "m", "c"] and list(duplicate) == ["x", "a", "m", "b"]


def test_a_branch_copy_shares_no_label_and_no_edge_with_its_parent():
    branch = tableau._Branch()
    root = branch.fresh()
    other = branch.fresh()
    branch.label[root].add(dl.Atomic("A"))
    branch.edges.add((root, "r", other))
    child = branch.copy()
    child.label[root].add(dl.Atomic("B"))
    child.edges.add((other, "r", root))
    assert list(branch.label[root]) == [dl.Atomic("A")]
    assert list(branch.edges) == [(root, "r", other)]
    assert list(child.label[root]) == [dl.Atomic("A"), dl.Atomic("B")]
    assert list(child.edges) == [(root, "r", other), (other, "r", root)]


def test_a_merge_keeps_the_order_of_the_edges_it_rewrites():
    branch = tableau._Branch()
    for node in ("a", "b", "c"):
        branch.add_node(node)
    for edge in (("a", "r", "c"), ("a", "r", "b"), ("c", "s", "a")):
        branch.edges.add(edge)
    tableau._merge(branch, "b", "c")
    # c is b now: the first edge becomes a→b, which the second already is
    assert list(branch.edges) == [("a", "r", "b"), ("b", "s", "a")]


def test_the_transitive_roles_of_a_role_box_are_listed_in_a_fixed_order():
    rbox = tableau._RBox([], {"zeta", "alpha", "mid"})
    assert rbox.transitive_in_order == ("alpha", "mid", "zeta")
    assert rbox.transitive == frozenset({"zeta", "alpha", "mid"})
