"""The classical tableau searches a branch as long as its step budget allows: no recursion, no recursion limit.

The search is a loop over an explicit stack of pending branches. Every pass of the loop is one step of
the budget (``max_steps``): one rule application or one closure test. So a branch cannot be longer than
``max_steps``, and the interpreter's recursion limit, which bounded it before, plays no part.

Problem 33 of the OWL corpus is the case that showed it: its first branch is made of well over a
thousand productive rule applications (97 literals, 74 universals instantiated at six terms, 388
instantiation pairs; none repeats an earlier one), so a recursive search stopped at the recursion limit
at once, 0.02 seconds in, and reported a bound that was no bound of the search.

The workloads are two chains whose single branch is exactly as long as the chain.

``P0, P0 → P1, …, P(n-1) → Pn ⊢ Pn`` is valid. Its roots are ``P0``, the ``n`` implications and ``¬Pn``.
``P0`` is one step (a literal); each implication is three (the branching rule, the left alternative
``¬Pi``, which closes against ``Pi``, and the right alternative ``P(i+1)``, a literal); ``¬Pn`` is one
more (it closes against ``Pn``). So the tableau closes in ``3n + 2`` steps and in no fewer.

``Or(Pi, Qi)`` for ``i < n``, as ``n`` separate formulas, is satisfiable: the first branch takes the left
alternative of each, two steps apiece (the branching rule and the literal), and is saturated after
``2n + 1`` passes with ``P0 … P(n-1)`` true.
"""

import inspect
import sys
import time

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.protocol import PROVED, UNKNOWN, get_backend
from unicode_logic_kit.atp.tableau import (
    TableauClosure, TableauStep, is_valid_tableau, prove_tableau, prove_tableau_detailed,
    tableau_closed, tableau_model,
)
from unicode_logic_kit.atp.tableau_check import check_tableau_proof
from unicode_logic_kit.fol.nodes import Atom, Constant, Implies, Not, Or, Quantifier, Variable

SLACK = 5.0

P33_PREMISES = [
    "∀x (OwlThing(x) ∧ ∀y (S(x, y) → A(y)) → x ≠ x)",
    "∀x ∀y (R(x, y) → S(x, y))",
    "∀x ∀v ∀w (Z(x, v) ∧ Z(x, w) → v = w)",
    "∀x ∀v (Z(x, v) → Q(x))",
    "∀x ∀v (Z(x, v) → Int(v))",
    "∀t ¬(OwlThing(t) ∧ OwlData(t))",
    "∃t OwlThing(t)",
    "∃t OwlData(t)",
    "∀x ∀y (R(x, y) → OwlThing(x) ∧ OwlThing(y))",
    "∀x ∀y (S(x, y) → OwlThing(x) ∧ OwlThing(y))",
    "∀x ∀v (Z(x, v) → OwlThing(x) ∧ OwlData(v))",
    "∀v (Int(v) → OwlData(v))",
]
P33_GOAL = "∀x (OwlThing(x) ∧ x = x → x ≠ x ∧ x ≠ x)"


def _chain(length):
    """``P0, P0 → P1, …, P(n-1) → Pn ⊢ Pn``."""
    premises = [Atom("P0", [])]
    premises += [Implies(Atom(f"P{i}", []), Atom(f"P{i + 1}", [])) for i in range(length)]
    return premises, Atom(f"P{length}", [])


def _problem_33():
    return ([api.parse_any(text).formula for text in P33_PREMISES],
            api.parse_any(P33_GOAL).formula)


LONG = 1500                                  # more than the recursion limit of 1000 and its frames


def test_a_chain_has_the_exact_step_cost_of_the_derivation():
    for length in (1, 2, 5, 40):
        premises, conclusion = _chain(length)
        assert prove_tableau(premises, conclusion, max_steps=3 * length + 2) is True
        assert prove_tableau(premises, conclusion, max_steps=3 * length + 1) is False
        assert prove_tableau_detailed(premises, conclusion, max_steps=3 * length + 2) is not None
        assert prove_tableau_detailed(premises, conclusion, max_steps=3 * length + 1) is None


def test_a_valid_branch_longer_than_the_recursion_limit_is_searched_to_its_end():
    assert LONG > sys.getrecursionlimit()
    premises, conclusion = _chain(LONG)
    assert prove_tableau(premises, conclusion, max_steps=3 * LONG + 2) is True
    assert tableau_closed(list(premises) + [Not(conclusion)], max_steps=3 * LONG + 2) is True


def test_the_proof_of_a_branch_longer_than_the_recursion_limit_is_recorded_and_checked():
    premises, conclusion = _chain(LONG)
    proof = prove_tableau_detailed(premises, conclusion, max_steps=3 * LONG + 2)
    assert proof is not None
    # one branching formula per implication: two recorded steps each, one closure per left alternative,
    # and the closure of the last branch
    assert len(proof.steps) == 2 * LONG
    assert len(proof.closures) == LONG + 1
    check_tableau_proof(proof, premises, conclusion)


def test_the_step_budget_is_what_ends_a_branch_that_is_too_long():
    premises, conclusion = _chain(LONG)
    short = 3 * LONG + 1
    assert prove_tableau(premises, conclusion, max_steps=short) is False
    assert prove_tableau_detailed(premises, conclusion, max_steps=short) is None
    verdict = get_backend("tableau").decide(conclusion, premises, timeout=60_000, max_steps=short)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"
    verdict = get_backend("tableau").decide(conclusion, premises, timeout=60_000, max_steps=short + 1)
    assert verdict.status == PROVED
    assert len(verdict.proof["steps"]) == 2 * LONG and len(verdict.proof["closures"]) == LONG + 1


def test_the_search_does_not_depend_on_the_recursion_limit():
    premises, conclusion = _chain(300)               # about 900 steps on one branch
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(len(inspect.stack(0)) + 150)
    try:
        assert prove_tableau(premises, conclusion) is True
        assert prove_tableau_detailed(premises, conclusion) is not None
        assert tableau_model(list(premises) + [Not(conclusion)]) is None       # closed: no model
    finally:
        sys.setrecursionlimit(previous)


def test_an_open_branch_longer_than_the_recursion_limit_gives_its_model():
    formulas = [Or(Atom(f"P{i}", []), Atom(f"Q{i}", [])) for i in range(LONG)]
    assert tableau_model(formulas, max_steps=2 * LONG + 1) == {f"P{i}": True for i in range(LONG)}
    assert tableau_model(formulas, max_steps=2 * LONG) is None          # one pass short: no branch is saturated
    assert tableau_closed(formulas) is False


def test_the_deepest_branch_of_problem_33_is_searched_and_not_refused():
    premises, conclusion = _problem_33()
    start = time.perf_counter()
    # with no step bound only the limit of the call can end it, and it does: the search was going on
    verdict = get_backend("tableau").decide(conclusion, premises, timeout=300, max_steps=10 ** 9)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def test_problem_33_is_decided_by_its_bounds_alone():
    premises, conclusion = _problem_33()
    assert prove_tableau(premises, conclusion, max_steps=3000) is False
    assert prove_tableau_detailed(premises, conclusion, max_steps=3000) is None


# ---------------------------------------------------------------------------------------------
# the proof objects are the ones a recursive search recorded
# ---------------------------------------------------------------------------------------------
def test_the_proof_of_a_modus_ponens_branches_and_closes_both_alternatives():
    p, q = Atom("p", []), Atom("q", [])
    proof = prove_tableau_detailed([p, Implies(p, q)], q)
    assert proof.root_formulas == (p, Implies(p, q), Not(q))
    # the branching rule records both alternatives before either is searched: steps 1 and 2
    assert proof.steps == (
        TableauStep(1, 0, "beta", Implies(p, q), (Not(p),), branch_split=True),
        TableauStep(2, 0, "beta", Implies(p, q), (q,), branch_split=True),
    )
    # ¬p closes against the root p, ¬q (a root) against the q that step 2 added
    assert proof.closures == (
        TableauClosure(1, Not(p), 1, p, 0),
        TableauClosure(2, Not(q), 0, q, 2),
    )


def test_the_proof_of_an_instance_of_a_universal_instantiates_it_at_the_constant():
    x, a = Variable("x"), Constant("a")
    universal = Quantifier("∀", x, Atom("P", [x]))
    proof = prove_tableau_detailed([universal], Atom("P", [a]))
    assert proof.root_formulas == (universal, Not(Atom("P", [a])))
    assert proof.steps == (TableauStep(1, 0, "gamma", universal, (Atom("P", [a]),), terms=(a,)),)
    assert proof.closures == (TableauClosure(1, Not(Atom("P", [a])), 0, Atom("P", [a]), 1),)


def test_a_valid_implication_is_closed_through_is_valid_tableau():
    premises, conclusion = _chain(30)
    assert is_valid_tableau(_folded(premises, conclusion)) is True


def test_the_proof_of_an_existential_witnesses_it_and_then_instantiates_the_negation():
    x, y, c = Variable("x"), Variable("y"), Constant("_t0")
    witness = Quantifier("∃", x, Atom("P", [x]))
    goal = Quantifier("∃", y, Atom("P", [y]))
    proof = prove_tableau_detailed([witness], goal)
    assert proof.root_formulas == (witness, Not(goal))
    assert proof.steps == (
        TableauStep(1, 0, "delta", witness, (Atom("P", [c]),), fresh_constant=c),
        TableauStep(2, 1, "gamma", Not(goal), (Not(Atom("P", [c])),), terms=(c,)),
    )
    assert proof.closures == (TableauClosure(2, Not(Atom("P", [c])), 2, Atom("P", [c]), 1),)


def _folded(premises, conclusion):
    formula = conclusion
    for premise in reversed(premises):
        formula = Implies(premise, formula)
    return formula
