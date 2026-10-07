"""No public entry point of the classical tableau raises ``RecursionError`` for a deep formula.

The search is a loop over a branch, so a long BRANCH is no problem; but the helpers that walk
one FORMULA (the substitution of a witness for a bound variable, the collection of the ground
terms, the hashing of a node) recurse once per level of nesting. A formula nested deeper than
they can follow ends the search like a bound: "no closed tableau", never an exception and
never a claim of satisfiability.

The formula used throughout: ``∀x (P(x) ∧ (P(x) ∧ (… ∧ P(x))))``, the conjunction nested
``n`` deep. It is valid with the goal ``P(alpha)``: instantiate the premise at ``alpha`` and
take the first conjunct. So ``True`` (proved) is right, and ``False`` / ``unknown`` is the
bound; the opposite verdict never.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import tableau
from unicode_logic_kit.atp.protocol import get_backend
from unicode_logic_kit.atp.tableau import TableauProof
from unicode_logic_kit.atp.tableau_check import (
    TableauCheckError, check_entailment_tableau_detailed, check_tableau_proof,
)
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Implies, Not, Quantifier, Variable

x = Variable("x")
alpha = Constant("alpha")
GOAL = Atom("P", [alpha])
DEEP = 400            # deeper than the search can walk within the default recursion limit
VERY_DEEP = 5000
BEYOND = 9000         # deeper than api.prove takes on with a larger stack (about 8000 levels)


def nested(n, left=False):
    """``∀x`` over a conjunction of ``P(x)`` nested ``n`` deep, to the right or to the left."""
    body = Atom("P", [x])
    for _ in range(n):
        body = And(body, Atom("P", [x])) if left else And(Atom("P", [x]), body)
    return Quantifier("∀", x, body)


# --------------------------------------------------------------------------- #
# nesting_depth: measured with a stack of its own
# --------------------------------------------------------------------------- #

def test_nesting_depth_counts_the_nodes_of_the_longest_path():
    proposition = Atom("A", [])
    assert tableau.nesting_depth(proposition) == 1
    assert tableau.nesting_depth(Not(proposition)) == 2
    assert tableau.nesting_depth(Atom("P", [x])) == 2                 # the atom and its argument
    assert tableau.nesting_depth(And(proposition, Not(Not(proposition)))) == 4
    assert tableau.nesting_depth(proposition, Not(proposition)) == 2   # the deepest of several


@pytest.mark.parametrize("n", [10, 3000, 100000])
def test_nesting_depth_answers_for_any_depth(n):
    body = Atom("A", [])
    for _ in range(n):
        body = And(Atom("A", []), body)
    assert tableau.nesting_depth(body) == n + 1


# --------------------------------------------------------------------------- #
# every entry point of the search: a bound, never an exception
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("n", [DEEP, VERY_DEEP])
@pytest.mark.parametrize("left", [False, True], ids=["right", "left"])
def test_no_entry_point_raises_for_a_formula_nested_too_deep(n, left):
    premise = nested(n, left)
    assert tableau.prove_tableau([premise], GOAL, max_steps=100000) in (True, False)
    assert tableau.prove_tableau_detailed([premise], GOAL, max_steps=100000) is None \
        or isinstance(tableau.prove_tableau_detailed([premise], GOAL, max_steps=100000),
                      TableauProof)
    assert tableau.tableau_closed([premise, Not(GOAL)], max_steps=100000) in (True, False)
    assert tableau.is_valid_tableau(Implies(premise, GOAL), max_steps=100000) in (True, False)
    model = tableau.tableau_model([premise, Not(GOAL)], max_steps=100000)
    # a model of an unsatisfiable set would be a wrong claim of satisfiability
    assert model is None


def test_a_deep_formula_is_a_bound_not_a_claim_of_satisfiability():
    # the set {premise, ¬P(alpha)} is unsatisfiable, so no model may come back for it
    assert tableau.tableau_model([nested(VERY_DEEP), Not(GOAL)], max_steps=100000) is None
    # ... and the deep formula alone is satisfiable (P = everything), which the search may
    # either find or not, but it must not raise
    tableau.tableau_model([nested(VERY_DEEP)], max_steps=100000)


def test_a_moderately_deep_formula_is_still_proved():
    premise = nested(100)
    assert tableau.prove_tableau([premise], GOAL) is True
    proof = tableau.prove_tableau_detailed([premise], GOAL)
    assert proof is not None
    check_tableau_proof(proof, [premise], GOAL)


@pytest.mark.parametrize("n", [DEEP, VERY_DEEP])
def test_the_backend_answers_unknown_and_names_the_depth(n):
    verdict = get_backend("tableau").decide(GOAL, [nested(n)], timeout=20000)
    assert verdict.status == "unknown"
    assert verdict.reason == "bound_hit"
    assert f"nested {n + 3} levels deep" in verdict.detail, verdict.detail


def test_api_prove_reads_a_deep_formula_and_never_answers_error():
    # api.prove runs a deep problem where its backends can walk it: the valid problem is proved
    verdict = api.prove(GOAL, [nested(DEEP)], backends=["tableau"], timeout=20000)
    assert verdict.status == "proved"
    # past the depth api.prove takes on, the tableau's own bound is the answer
    verdict = api.prove(GOAL, [nested(BEYOND)], backends=["tableau"], timeout=20000)
    assert verdict.status == "unknown"                       # never "error", never "refuted"
    assert verdict.reason != "infra"
    assert f"nested {BEYOND + 3} levels deep" in verdict.detail
    assert api.prove(GOAL, [nested(DEEP)], timeout=20000).status == "proved"


def test_the_depth_in_the_message_is_the_depth_of_the_whole_problem():
    # the problem is the premise and the negated goal; the premise's quantifier, its n
    # conjunctions and the atom with its argument are n + 3 nodes on the longest path
    premise = nested(DEEP)
    assert tableau.nesting_depth(premise) == DEEP + 3
    assert tableau.nesting_depth(premise, Not(GOAL)) == DEEP + 3


# --------------------------------------------------------------------------- #
# the checker
# --------------------------------------------------------------------------- #

def test_the_checker_rejects_a_deep_proof_without_steps_for_what_is_wrong_with_it():
    # a proof that records no step leaves its one branch open, however deep its roots are
    premise = nested(VERY_DEEP)
    roots = (premise, Not(GOAL))
    proof = TableauProof(roots, (), ())
    with pytest.raises(TableauCheckError, match="open branch"):
        check_tableau_proof(proof, [premise], GOAL)


def test_the_checker_refuses_a_proof_it_cannot_walk_by_name_and_never_raises_recursion_error():
    # A genuine proof of the deep problem, found where the formula can be walked (the stack and
    # recursion limit api.prove gives a deep problem). Its second step puts the deep conjunction
    # with alpha for x on the branch, and that substitution recurses once per level.
    premise = nested(DEEP)
    depth = tableau.nesting_depth(premise, Not(GOAL))
    proof = api._call_deep(depth, lambda: tableau.prove_tableau_detailed([premise], GOAL))
    assert proof is not None
    # under the interpreter's own limit the checker cannot follow it, and says so
    with pytest.raises(TableauCheckError, match="nested deeper"):
        check_tableau_proof(proof, [premise], GOAL)
    # where it can be walked, the same proof is certified
    api._call_deep(depth, lambda: check_tableau_proof(proof, [premise], GOAL))


def test_check_entailment_reports_a_deep_search_as_not_proved():
    result = check_entailment_tableau_detailed([nested(VERY_DEEP)], GOAL, max_steps=100000)
    assert result["proved"] is False and result["proof"] is None
    assert result["check_passed"] is None
