r"""Which unresolved disjunction the tableau splits first.

The ⊔-rule may be applied to ANY unresolved disjunction of a branch, and a
branch closes however they are ordered, so the verdict never depends on the
choice; the SIZE of the search does. The pigeonhole concept PHP(n+1, n) (n+1
pigeons, n holes, every pigeon in some hole, no two in one hole) is unsatisfiable
by the pigeonhole principle, and the order decides how much work proving that
takes: split the "no two pigeons share hole k" clauses first and the search
enumerates every way to choose one of two negations for each pair; split the
disjunction one of whose disjuncts the branch has ALREADY refuted and it costs one
step, because the other disjunct is the only one that can hold.

The rule the tableau uses, hand-derived from that:

1. a disjunction with at most ONE alternative that is not contradicted by its
   node's label (an alternative is contradicted when it is ⊥ or its complement
   is in the label) comes first -- the first such one, nodes in creation order,
   a node's labels in insertion order;
2. otherwise the first unresolved disjunction in that same order.

Both clauses are functions of the insertion order alone, never of a hash.
"""

import random

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl import tableau

A, B, C, D = (dl.Atomic(n) for n in "ABCD")
NOT_A = dl.Not(A)


def _branch(**labels):
    """A branch whose nodes (in the order given) carry the labels given, in order."""
    branch = tableau._Branch()
    for node, concepts in labels.items():
        branch.add_node(node)
        for concept in concepts:
            branch.label[node].add(concept)
    return branch


# --------------------------------------------------------------------------- #
# The choice, on hand-built branches
# --------------------------------------------------------------------------- #

def test_the_first_unresolved_disjunction_is_chosen_when_none_is_forced():
    first, second = dl.Or(A, B), dl.Or(C, D)
    assert tableau._find_disjunction(_branch(n=[first, second])) == ("n", first)
    assert tableau._find_disjunction(_branch(n=[second, first])) == ("n", second)


def test_a_disjunction_with_a_refuted_disjunct_comes_before_an_earlier_free_one():
    # A is in the label, so ¬A can never hold: ¬A ⊔ B has ONE live alternative (B)
    free, forced = dl.Or(C, D), dl.Or(NOT_A, B)
    assert tableau._find_disjunction(_branch(n=[free, A, forced])) == ("n", forced)


def test_a_nested_disjunction_is_forced_when_all_but_one_leaf_is_refuted():
    # (¬A ⊔ ¬B) ⊔ C with A and B in the label: the leaves ¬A and ¬B are refuted,
    # C is the one live alternative
    free, forced = dl.Or(C, D), dl.Or(dl.Or(NOT_A, dl.Not(B)), C)
    assert tableau._find_disjunction(_branch(n=[free, A, B, forced])) == ("n", forced)


def test_a_nested_disjunction_with_two_live_leaves_is_not_forced():
    # (¬A ⊔ B) ⊔ C with A in the label: B and C are both live
    free, two_live = dl.Or(C, D), dl.Or(dl.Or(NOT_A, B), C)
    assert tableau._find_disjunction(_branch(n=[free, A, two_live])) == ("n", free)


def test_a_bottom_disjunct_counts_as_refuted():
    free, forced = dl.Or(C, D), dl.Or(dl.Bottom(), B)
    assert tableau._find_disjunction(_branch(n=[free, forced])) == ("n", forced)


def test_a_complement_of_a_negated_disjunct_refutes_it():
    # ¬A is refuted by A's presence, and A is refuted by ¬A's: both polarities
    free, forced = dl.Or(C, D), dl.Or(A, B)
    assert tableau._find_disjunction(_branch(n=[free, NOT_A, forced])) == ("n", forced)


def test_the_first_of_two_forced_disjunctions_is_chosen():
    one, two = dl.Or(NOT_A, B), dl.Or(NOT_A, C)
    assert tableau._find_disjunction(_branch(n=[A, one, two])) == ("n", one)


def test_a_forced_disjunction_at_a_later_node_comes_before_a_free_one_at_an_earlier_node():
    free, forced = dl.Or(C, D), dl.Or(NOT_A, B)
    assert tableau._find_disjunction(_branch(n=[free], m=[A, forced])) == ("m", forced)


def test_a_resolved_disjunction_is_not_chosen():
    # B is already in the label: nothing to split, however refuted the other side is
    resolved = dl.Or(NOT_A, B)
    assert tableau._find_disjunction(_branch(n=[A, B, resolved])) is None


# --------------------------------------------------------------------------- #
# The pigeonhole concept
# --------------------------------------------------------------------------- #

def pigeonhole(pigeons, holes):
    """Every pigeon in some hole (an n-ary disjunction, left-nested), no two pigeons
    in one hole; the clauses of the pigeons first, as a left-nested conjunction."""
    letter = {(i, k): dl.Atomic(f"InHole{k}Pigeon{i}") for i in range(pigeons) for k in range(holes)}
    clauses = []
    for i in range(pigeons):
        clause = letter[(i, 0)]
        for k in range(1, holes):
            clause = dl.Or(clause, letter[(i, k)])
        clauses.append(clause)
    for k in range(holes):
        for i in range(pigeons):
            for j in range(i + 1, pigeons):
                clauses.append(dl.Or(dl.Not(letter[(i, k)]), dl.Not(letter[(j, k)])))
    concept = clauses[0]
    for clause in clauses[1:]:
        concept = dl.And(concept, clause)
    return concept


@pytest.fixture
def steps_used(monkeypatch):
    """A function that decides a concept and returns (verdict, steps used)."""
    recorded = []

    class Recording(tableau._Ctx):
        def __init__(self, n):
            super().__init__(n)
            self.start = n
            recorded.append(self)

    monkeypatch.setattr(tableau, "_Ctx", Recording)

    def run(concept, budget=None):
        if budget is not None:
            monkeypatch.setattr(tableau, "MAX_STEPS", budget)
        verdict = tableau.concept_satisfiable(concept)
        return verdict, recorded[-1].start - recorded[-1].steps

    return run


def test_pigeonhole_4_3_is_refuted_within_the_steps_the_worst_hash_order_needed(steps_used):
    # four pigeons, three holes: unsatisfiable. 3884 is the largest step count any
    # hash seed gave for it when the order still followed the hash of the names.
    verdict, steps = steps_used(pigeonhole(4, 3))
    assert verdict is False
    assert steps <= 3884


def test_pigeonhole_5_4_is_refuted_well_within_the_default_budget(steps_used):
    # five pigeons, four holes: unsatisfiable. Splitting the clauses in insertion
    # order did not finish within the default budget of a million steps; here a
    # tenth of it is the ceiling, so that a slower search ends the test early.
    assert 100_000 < tableau.MAX_STEPS
    verdict, steps = steps_used(pigeonhole(5, 4), budget=100_000)
    assert verdict is False
    assert steps < 100_000


def _pigeonhole_clauses(pigeons, holes):
    letter = {(i, k): dl.Atomic(f"P{i}H{k}") for i in range(pigeons) for k in range(holes)}
    clauses = []
    for i in range(pigeons):
        clause = letter[(i, 0)]
        for k in range(1, holes):
            clause = dl.Or(clause, letter[(i, k)])
        clauses.append(clause)
    for k in range(holes):
        for i in range(pigeons):
            for j in range(i + 1, pigeons):
                clauses.append(dl.Or(dl.Not(letter[(i, k)]), dl.Not(letter[(j, k)])))
    return clauses


def _conjunction(clauses):
    concept = clauses[0]
    for clause in clauses[1:]:
        concept = dl.And(concept, clause)
    return concept


@pytest.mark.parametrize("pigeons, holes", [(2, 1), (3, 2), (4, 3)])
def test_the_pigeonhole_concept_is_unsatisfiable_whatever_order_its_clauses_are_written_in(
        pigeons, holes):
    clauses = _pigeonhole_clauses(pigeons, holes)
    rng = random.Random(pigeons * 10 + holes)
    for _ in range(3):
        rng.shuffle(clauses)
        assert tableau.concept_satisfiable(_conjunction(clauses)) is False


@pytest.mark.parametrize("pigeons", [1, 2, 3, 4])
def test_as_many_holes_as_pigeons_is_satisfiable(pigeons):
    # pigeon i in hole i, hand-derived: a model exists, so the search must find one
    clauses = _pigeonhole_clauses(pigeons, pigeons)
    rng = random.Random(pigeons)
    for _ in range(3):
        rng.shuffle(clauses)
        assert tableau.concept_satisfiable(_conjunction(clauses)) is True


# --------------------------------------------------------------------------- #
# The order changes the size of the search and never a verdict.
# --------------------------------------------------------------------------- #

def _first_unresolved_disjunction(branch):
    """The choice without the forced-first clause: the first unresolved disjunction."""
    for node in branch.order:
        label = branch.label[node]
        for c in label:
            if isinstance(c, dl.Or) and c.left not in label and c.right not in label:
                return node, c
    return None


NAMES = ["A", "B", "C", "D", "E"]
ROLES = ["r", "s"]


def _random_concept(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        atom = dl.Atomic(rng.choice(NAMES))
        return dl.Not(atom) if rng.random() < 0.35 else atom
    kind = rng.choice(["and", "or", "or", "or", "some", "all", "not", "atleast", "atmost"])
    x, y = _random_concept(rng, depth - 1), _random_concept(rng, depth - 1)
    if kind == "and":
        return dl.And(x, y)
    if kind == "or":
        return dl.Or(x, y)
    if kind == "some":
        return dl.Exists(rng.choice(ROLES), x)
    if kind == "all":
        return dl.ForAll(rng.choice(ROLES), x)
    if kind == "atleast":
        return dl.AtLeast(rng.choice([1, 2]), rng.choice(ROLES), x)
    if kind == "atmost":
        return dl.AtMost(rng.choice([1, 2]), rng.choice(ROLES), x)
    return dl.Not(x)


def _random_problem(seed):
    rng = random.Random(seed)
    tbox = dl.TBox()
    for _ in range(rng.randint(1, 5)):
        tbox.add(_random_concept(rng, 2), _random_concept(rng, 2))
    if rng.random() < 0.3:
        tbox.add_role_inclusion("s", "r")
    return _random_concept(rng, 3), tbox


def _decide(goal, tbox, budget):
    """The verdict, or None when the step budget is exhausted."""
    saved = tableau.MAX_STEPS
    tableau.MAX_STEPS = budget
    try:
        return tableau.concept_satisfiable(goal, tbox)
    except RuntimeError:
        return None
    finally:
        tableau.MAX_STEPS = saved


def test_the_forced_first_order_decides_what_the_first_unresolved_order_decides_and_agrees_with_it(
        monkeypatch):
    budget = 1500
    both = forced_only = plain_only = disagreements = 0
    for seed in range(60):
        goal, tbox = _random_problem(seed)
        forced = _decide(goal, tbox, budget)
        with monkeypatch.context() as patch:
            patch.setattr(tableau, "_find_disjunction", _first_unresolved_disjunction)
            plain = _decide(goal, tbox, budget)
        if forced is not None and plain is not None:
            both += 1
            disagreements += forced != plain
        elif forced is not None:
            forced_only += 1
        elif plain is not None:
            plain_only += 1
    assert disagreements == 0
    assert plain_only == 0          # nothing the first-unresolved order decided is lost
    assert both >= 50               # the comparison has teeth

