"""The finite model finder and ``subsorts=`` on a theory that has no sorted node.

A subsort edge ``S < T`` is ``∀x (S(x) → T(x))`` whether or not the theory has a sorted node. For an
unsorted theory ``S`` and ``T`` are ordinary unary predicates, so the finder holds a structure to every
edge whose two ends the theory uses as unary predicates (through the transitive closure of the edges, as
for a sorted theory). An edge with an end the theory never mentions changes nothing: that end can always
be chosen to satisfy it. With no ``subsorts`` the search is the one there always was.

The expected answers are derived by hand from ``S ⊆ T``. The differential at the end compares the finder
against Z3 with ``subsort_axioms`` passed as premises: a different route to the same question.
"""

import itertools
import random

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Implies, Not, Or, subsort_axioms
from unicode_fol_kit.fol.signature import Signature
from unicode_fol_kit.semantics.modelfinder import (
    find_countermodel, find_model, is_satisfiable_finite, is_valid_finite,
)

CARL = Constant("carl")


def atom(name, constant=CARL):
    return Atom(name, [constant])


A_BELOW_B = {"A": frozenset({"B"})}


@pytest.mark.parametrize("symmetry_breaking", [True, False])
class TestUnsortedTheories:

    def test_an_edge_between_two_predicates_the_theory_uses_is_enforced(self, symmetry_breaking):
        # A ⊆ B, so A(carl) entails B(carl). Without the edge: U={0}, A={0}, B={}, carl=0.
        premises, goal = [atom("A")], atom("B")
        assert find_countermodel(premises, goal, max_size=3, symmetry_breaking=symmetry_breaking) is not None
        assert find_countermodel(premises, goal, max_size=3, symmetry_breaking=symmetry_breaking,
                                 subsorts=A_BELOW_B) is None

    def test_a_chain_bounds_its_ends_even_when_the_middle_is_not_used(self, symmetry_breaking):
        # S < T < U, the theory uses S and U only: S ⊆ T ⊆ U gives S ⊆ U.
        chain = {"S": frozenset({"T"}), "T": frozenset({"U"})}
        premises, goal = [atom("S")], atom("U")
        assert find_countermodel(premises, goal, max_size=3, symmetry_breaking=symmetry_breaking) is not None
        assert find_countermodel(premises, goal, max_size=3, symmetry_breaking=symmetry_breaking,
                                 subsorts=chain) is None

    def test_an_edge_with_an_end_the_theory_never_mentions_changes_nothing(self, symmetry_breaking):
        # B is not in the theory, so A < B can be satisfied by taking B to be everything.
        premises, goal = [atom("A")], atom("Q")
        with_edge = find_countermodel(premises, goal, max_size=3, symmetry_breaking=symmetry_breaking,
                                      subsorts=A_BELOW_B)
        assert with_edge is not None                      # U={0}, A={0}, Q={}, carl=0

    def test_the_edge_runs_one_way_only(self, symmetry_breaking):
        # B(carl) does not entail A(carl) however A < B is read: U={0}, B={0}, A={}.
        assert find_countermodel([atom("B")], atom("A"), max_size=3,
                                 symmetry_breaking=symmetry_breaking, subsorts=A_BELOW_B) is not None

    def test_a_model_found_under_the_edge_satisfies_it(self, symmetry_breaking):
        # A(carl) ∧ ¬B(dora). With carl = dora (one element) that is A={0}, B={} -- against A ⊆ B. The
        # smallest structure that respects the edge has two elements: A={0}, B={0}, carl=0, dora=1.
        theory = And(atom("A"), Not(atom("B", Constant("dora"))))
        free = find_model([theory], max_size=3, symmetry_breaking=symmetry_breaking)
        assert len(free.domain) == 1 and not free.predicates[("A", 1)] <= free.predicates[("B", 1)]
        model = find_model([theory], max_size=3, symmetry_breaking=symmetry_breaking, subsorts=A_BELOW_B)
        assert len(model.domain) == 2
        assert model.predicates[("A", 1)] <= model.predicates[("B", 1)]
        assert model.constants["carl"] != model.constants["dora"]

    def test_a_theory_the_edge_makes_unsatisfiable_has_no_model(self, symmetry_breaking):
        # A(carl) ∧ ¬B(carl) needs carl in A but not in B, against A ⊆ B.
        theory = And(atom("A"), Not(atom("B")))
        assert find_model([theory], max_size=3, symmetry_breaking=symmetry_breaking) is not None
        assert find_model([theory], max_size=3, symmetry_breaking=symmetry_breaking,
                          subsorts=A_BELOW_B) is None
        assert is_satisfiable_finite(theory, max_size=3, symmetry_breaking=symmetry_breaking) is True
        assert is_satisfiable_finite(theory, max_size=3, symmetry_breaking=symmetry_breaking,
                                     subsorts=A_BELOW_B) is False

    def test_validity_through_the_edge(self, symmetry_breaking):
        # A(carl) → B(carl) is valid exactly under A ⊆ B.
        implication = Implies(atom("A"), atom("B"))
        assert is_valid_finite(implication, max_size=3, symmetry_breaking=symmetry_breaking) is False
        assert is_valid_finite(implication, max_size=3, symmetry_breaking=symmetry_breaking,
                               subsorts=A_BELOW_B) is True


def test_with_no_subsorts_the_search_is_the_one_there_always_was():
    theory = [Atom("R", [CARL, Constant("dora")]), atom("A"), Or(atom("B"), atom("A"))]
    plain = find_model(theory, max_size=3)
    assert plain is not None
    # an empty mapping, and an edge among names the theory does not use, find the very same structure
    for subsorts in ({}, {"X": frozenset({"Y"})}, None):
        again = find_model(theory, max_size=3, subsorts=subsorts)
        assert (again.domain, again.constants, again.functions, again.predicates) == (
            plain.domain, plain.constants, plain.functions, plain.predicates)


def test_a_signatures_own_subsorts_attribute_is_accepted():
    signature = Signature.from_dict({"subsorts": {"A": ["B"]}})
    assert find_countermodel([atom("A")], atom("B"), max_size=2, subsorts=signature.subsorts) is None


def test_through_api_prove_the_model_finder_reads_the_edge_of_an_unsorted_theory():
    signature = Signature.from_dict({"subsorts": {"A": ["B"]}})
    verdict = api.prove(atom("B"), [atom("A")], backends=["modelfinder"], subsorts=signature.subsorts,
                        max_size=3)
    assert verdict.status == "unknown"                # no countermodel: nothing to refute with
    assert api.prove(atom("B"), [atom("A")], backends=["modelfinder"], max_size=3).status == "refuted"


# ---- the differential: the finder against Z3 with the edges asserted as premises --------------------

PREDICATES = ("A", "B", "C")
CONSTANTS = (Constant("carl"), Constant("dora"))


def random_ground_formula(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return Atom(rng.choice(PREDICATES), [rng.choice(CONSTANTS)])
    roll = rng.random()
    if roll < 0.25:
        return Not(random_ground_formula(rng, depth - 1))
    connective = rng.choice((And, Or, Implies))
    return connective(random_ground_formula(rng, depth - 1), random_ground_formula(rng, depth - 1))


def random_edges(rng):
    pairs = [("A", "B"), ("B", "C"), ("A", "C"), ("C", "A")]
    chosen = [p for p in pairs if rng.random() < 0.35]
    edges = {}
    for child, parent in chosen:
        edges.setdefault(child, set()).add(parent)
    return {child: frozenset(parents) for child, parents in edges.items()}


def acyclic(edges):
    try:
        Signature(subsorts=edges)
    except ValueError:
        return False
    return True


def test_the_finder_and_z3_with_the_edges_as_premises_agree_on_ground_problems():
    # Ground atoms over two constants: a countermodel, if there is one, has at most two elements
    # (each constant's atoms are read off its own element), so max_size=2 is complete here.
    compared = changed = 0
    for seed in range(300):
        rng = random.Random(seed)
        edges = random_edges(rng)
        if not acyclic(edges):
            continue
        premises = [random_ground_formula(rng, 2) for _ in range(rng.randrange(3))]
        goal = random_ground_formula(rng, 2)
        signature = Signature(subsorts=edges)
        z3_status = api.prove(goal, [*premises, *subsort_axioms(signature)], backends=["z3"]).status
        found = find_countermodel(premises, goal, max_size=2, subsorts=edges) is not None
        assert found == (z3_status == "refuted"), (seed, edges)
        if found != (find_countermodel(premises, goal, max_size=2) is not None):
            changed += 1
        compared += 1
    assert compared >= 200
    assert changed >= 10                      # the edges matter for some of the generated problems
