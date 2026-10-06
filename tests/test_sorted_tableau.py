"""The in-house tableau on many-sorted input, and the bounds that end its search.

The reading every many-sorted route of the kit shares: there is ONE universe; a sort ``S`` is the
non-empty extension of the unary predicate of its name; sorts may overlap; a sorted constant ``c:S``
denotes an element of ``S`` (and ``c:S`` here with a plain ``c`` there are one constant); an unsorted
constant, an unsorted variable and the value of a function may be any element of the universe.

The tableau reads ``∀x:S φ`` as ``∀x (S(x) → φ)`` (``to_fol``) and refutes that image together with the
background facts that reading needs, as roots of their own: every sort is non-empty and a sorted constant
lies in its sort (``sort_axioms``). The expectations below are derived by hand from the definition:

* ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is VALID: socrates is a Human, every Human is Mortal.
* ``∀x:Human Mortal(x) ⊢ Mortal(socrates)`` is NOT: universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1.
* ``P(carl:A), Q(carl:B) ⊢ ∃x:A Q(x)`` is VALID: carl is an A and Q(carl).
* ``⊢ Mortal(socrates:Human)`` is NOT: universe {0}, Human = {0}, Mortal = {}, socrates = 0.
* ``P(carl), Q(carl:A) ⊢ ∃x:A P(x)`` is VALID: it is ONE constant, and its sorted occurrence puts it in A.
* ``∀x:A P(x) ⊢ ∃x P(x)`` is VALID because A is not empty (the sort is not a free-floating guard).

The bounds: a step budget (which also bounds how long a branch can grow: the search is a loop, and the
interpreter's recursion limit plays no part) and a wall-clock ``timeout`` end the search with "not closed
within the bounds"; neither raises.
"""

import sys
import time

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.protocol import PROVED, UNKNOWN, get_backend
from unicode_fol_kit.atp.resolution import prove as resolution_prove
from unicode_fol_kit.atp.tableau import (
    TableauProof, is_valid_tableau, prove_tableau, prove_tableau_detailed, tableau_closed, tableau_model,
)
from unicode_fol_kit.atp.tableau_check import (
    TableauCheckError, check_entailment_tableau_detailed, check_tableau_proof,
)
from unicode_fol_kit.fol.nodes import (
    And, Atom, Implies, Not, Number, Or, SortedCardinality, Variable, sort_axioms, to_fol,
)


def F(text):
    parsed = api.parse_any(text)
    assert parsed.ok, (text, parsed)
    return parsed.formula


ALL_MORTAL = F("∀x:Human Mortal(x)")


def _implication(premises, goal):
    if not premises:
        return goal
    antecedent = premises[0]
    for p in premises[1:]:
        antecedent = And(antecedent, p)
    return Implies(antecedent, goal)


# (premises, conclusion, valid by hand)
PROBLEMS = {
    "V1 a sorted constant is in its sort": ([ALL_MORTAL], F("Mortal(socrates:Human)"), True),
    "I1 an unsorted constant is not": ([ALL_MORTAL], F("Mortal(socrates)"), False),
    "V2 one constant lies in both its sorts": ([F("P(carl:A)"), F("Q(carl:B)")], F("∃x:A Q(x)"), True),
    "I2 nothing follows about a sorted constant from nothing": ([], F("Mortal(socrates:Human)"), False),
    "V3 sorted here, plain there: one constant": ([F("P(carl)"), F("Q(carl:A)")], F("∃x:A P(x)"), True),
    "V4 a sort is not empty (sorted conclusion)": ([F("∀x:A P(x)")], F("∃x:A P(x)"), True),
    "V5 a sort is not empty (unsorted conclusion)": ([F("∀x:A P(x)")], F("∃x P(x)"), True),
    "V6 a sorted constant keeps its identity across formulas":
        ([F("P(carl:S)"), F("∀x (P(x) → Q(x))")], F("Q(carl:S)"), True),
}


@pytest.mark.parametrize("name", sorted(PROBLEMS))
def test_every_entry_point_of_the_tableau_answers_as_the_definition_says(name):
    premises, conclusion, valid = PROBLEMS[name]
    goal = _implication(premises, conclusion)
    assert prove_tableau(premises, conclusion) is valid
    assert tableau_closed(list(premises) + [Not(conclusion)]) is valid
    assert is_valid_tableau(goal) is valid
    assert (prove_tableau_detailed(premises, conclusion) is not None) is valid
    # tableau_model answers None exactly when the refuted set closed
    assert (tableau_model(list(premises) + [Not(conclusion)]) is None) is valid


@pytest.mark.parametrize("name", sorted(n for n in PROBLEMS if PROBLEMS[n][2]))
def test_a_proof_of_a_sorted_entailment_passes_the_independent_check(name):
    premises, conclusion, _ = PROBLEMS[name]
    result = check_entailment_tableau_detailed(premises, conclusion)
    assert result["proved"] is True
    assert result["check_passed"] is True, result["check_error"]


def test_the_backend_proves_instead_of_raising():
    # it used to raise ValueError "no rule for SortedQuantifier" through run_backend
    premises, conclusion, _ = PROBLEMS["V1 a sorted constant is in its sort"]
    assert api.prove(conclusion, premises, backends=["tableau"]).status == "proved"
    premises, conclusion, _ = PROBLEMS["V3 sorted here, plain there: one constant"]
    assert api.prove(conclusion, premises, backends=["tableau"]).status == "proved"


# ---------------------------------------------------------------------------------------------
# the open branch is the countermodel the definition describes
# ---------------------------------------------------------------------------------------------
def test_the_model_of_the_unsorted_constant_case_puts_it_outside_the_sort():
    # ∀x:Human Mortal(x) and ¬Mortal(socrates): the open branch says socrates is no Human and not
    # Mortal, and Human has some other member (a sort is not empty) which is Mortal.
    assignment = tableau_model([ALL_MORTAL, Not(F("Mortal(socrates)"))])
    assert assignment is not None
    assert assignment["Mortal(socrates)"] is False
    assert assignment["Human(socrates)"] is False
    witnesses = [atom for atom, value in assignment.items() if atom.startswith("Human(") and value]
    assert witnesses, assignment
    assert all(assignment["Mortal(" + w[len("Human("):]] for w in witnesses)


def test_the_model_of_a_sorted_constant_with_nothing_else_makes_it_a_member():
    # ¬Mortal(socrates:Human) alone: socrates is a Human (the membership fact), not Mortal.
    assignment = tableau_model([Not(F("Mortal(socrates:Human)"))])
    assert assignment is not None
    assert assignment["Human(socrates)"] is True
    assert assignment["Mortal(socrates)"] is False


# ---------------------------------------------------------------------------------------------
# the proof object and its checker see the same roots
# ---------------------------------------------------------------------------------------------
def test_the_roots_of_a_sorted_proof_are_the_guard_images_then_the_sort_axioms():
    premises, conclusion, _ = PROBLEMS["V1 a sorted constant is in its sort"]
    proof = prove_tableau_detailed(premises, conclusion)
    assert isinstance(proof, TableauProof)
    # by hand: the premise's image, the negated conclusion's image (the sorted constant is the plain
    # one), then "Human is not empty" and "socrates is a Human"
    assert [f.to_unicode_str() for f in proof.root_formulas] == [
        "∀x (Human(x) → Mortal(x))", "¬Mortal(socrates)", "∃x0 Human(x0)", "Human(socrates)"]
    assert proof.root_formulas == (
        to_fol(premises[0]), Not(to_fol(conclusion)), *sort_axioms(premises[0], Not(conclusion)))


def test_the_checker_rejects_a_sorted_proof_that_leaves_out_a_sort_axiom():
    premises, conclusion, _ = PROBLEMS["V1 a sorted constant is in its sort"]
    proof = prove_tableau_detailed(premises, conclusion)
    check_tableau_proof(proof, premises, conclusion)               # the real one passes
    trimmed = TableauProof(proof.root_formulas[:-1], proof.steps, proof.closures)
    with pytest.raises(TableauCheckError, match="root formulas"):
        check_tableau_proof(trimmed, premises, conclusion)


def test_the_checker_rejects_a_proof_offered_for_another_conclusion():
    premises, conclusion, _ = PROBLEMS["V1 a sorted constant is in its sort"]
    proof = prove_tableau_detailed(premises, conclusion)
    with pytest.raises(TableauCheckError, match="root formulas"):
        check_tableau_proof(proof, premises, F("Mortal(socrates)"))


def test_an_unsorted_problem_keeps_its_roots():
    premises, conclusion = [F("P → Q"), F("P")], F("Q")
    proof = prove_tableau_detailed(premises, conclusion)
    assert proof.root_formulas == (*premises, Not(conclusion))


def test_a_sorted_cardinality_is_refused_by_name():
    x = Variable("x")
    cardinality = Atom("=", [SortedCardinality(x, "S", Atom("P", [x])), Number(3)])
    with pytest.raises(NotImplementedError, match="SortedCardinality"):
        tableau_closed([cardinality])
    with pytest.raises(NotImplementedError, match="SortedCardinality"):
        prove_tableau([], cardinality)


# ---------------------------------------------------------------------------------------------
# the bounds
# ---------------------------------------------------------------------------------------------
def _chain(length):
    """``P0, P0 → P1, …, P(n-1) → Pn ⊢ Pn``: valid, and its one branch is as long as the chain."""
    premises = [Atom("P0", [])]
    premises += [Implies(Atom(f"P{i}", []), Atom(f"P{i + 1}", [])) for i in range(length)]
    return premises, Atom(f"P{length}", [])


def _pigeonhole(pigeons, holes):
    """Every pigeon sits in a hole and no hole holds two: unsatisfiable when pigeons > holes."""
    p = lambda i, j: Atom(f"P{i}x{j}", [])
    parts = []
    for i in range(pigeons):
        row = p(i, 0)
        for j in range(1, holes):
            row = Or(row, p(i, j))
        parts.append(row)
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i + 1, pigeons):
                parts.append(Not(And(p(i, j), p(k, j))))
    formula = parts[0]
    for part in parts[1:]:
        formula = And(formula, part)
    return formula


def test_a_branch_longer_than_the_recursion_limit_is_searched_to_its_end():
    # The chain is valid and its one branch is longer than the interpreter's recursion limit. It
    # used to be refused at that depth as if a bound of the search had been reached, although the
    # tableau closes (three steps per implication, 3n + 2 in all: see test_tableau_search_depth.py).
    # The search is a loop, so the branch is searched, and it is the step budget that bounds it.
    length = sys.getrecursionlimit() + 500
    premises, conclusion = _chain(length)
    assert prove_tableau(premises, conclusion, max_steps=10 ** 6) is True
    proof = prove_tableau_detailed(premises, conclusion, max_steps=10 ** 6)
    assert proof is not None
    check_tableau_proof(proof, premises, conclusion)
    assert tableau_model(list(premises) + [Not(conclusion)], max_steps=10 ** 6) is None   # closed: no model
    verdict = get_backend("tableau").decide(conclusion, premises, timeout=60000, max_steps=10 ** 6)
    assert verdict.status == PROVED
    assert api.prove(conclusion, premises, backends=["tableau"], max_steps=10 ** 6).status == PROVED


def test_a_branch_that_needs_more_steps_than_the_budget_is_a_bound_not_an_exception():
    premises, conclusion = _chain(sys.getrecursionlimit() + 500)
    budget = 3 * (sys.getrecursionlimit() + 500) + 1               # one step short of the 3n + 2 it needs
    assert prove_tableau(premises, conclusion, max_steps=budget) is False
    assert prove_tableau_detailed(premises, conclusion, max_steps=budget) is None
    verdict = get_backend("tableau").decide(conclusion, premises, timeout=60000, max_steps=budget)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"
    assert api.prove(conclusion, premises, backends=["tableau"], max_steps=budget).status == UNKNOWN


def test_a_chain_inside_the_limit_is_still_proved():
    premises, conclusion = _chain(50)
    assert prove_tableau(premises, conclusion) is True


def test_the_tableau_returns_at_its_deadline():
    # PHP(5,4), the pigeonhole principle: unsatisfiable, and far beyond what a tableau closes in a
    # moment. With no step bound only the deadline can end the search.
    formula = _pigeonhole(5, 4)
    start = time.perf_counter()
    assert tableau_closed([formula], max_steps=10 ** 9, timeout=100) is False
    assert time.perf_counter() - start < 5.0
    start = time.perf_counter()
    assert prove_tableau_detailed([], Not(formula), max_steps=10 ** 9, timeout=100) is None
    assert time.perf_counter() - start < 5.0


def test_the_tableau_backend_reports_a_used_up_limit_as_a_timeout():
    verdict_start = time.perf_counter()
    verdict = get_backend("tableau").decide(Not(_pigeonhole(5, 4)), [], timeout=100, max_steps=10 ** 9)
    assert time.perf_counter() - verdict_start < 5.0
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def test_a_small_pigeonhole_closes_within_its_limit():
    # the deadline is a bound, not a handicap: PHP(3,2) closes in a few dozen steps
    assert tableau_closed([_pigeonhole(3, 2)], timeout=60000) is True


# twelve premises and a goal for which a 2-element countermodel exists (so "proved" is wrong and "unknown" is the
# honest answer); the resolution prover used to run for 30 s on it whatever the limit
_SATURATING = [
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
_SATURATING_GOAL = "∀x (OwlThing(x) ∧ x = x → x ≠ x ∧ x ≠ x)"


def test_resolution_returns_at_its_deadline():
    premises = [F(text) for text in _SATURATING]
    goal = F(_SATURATING_GOAL)
    start = time.perf_counter()
    assert resolution_prove(premises, goal, timeout=500) is False
    assert time.perf_counter() - start < 5.0


def test_the_resolution_backend_reports_a_used_up_limit_as_a_timeout():
    premises = [F(text) for text in _SATURATING]
    goal = F(_SATURATING_GOAL)
    start = time.perf_counter()
    verdict = get_backend("resolution").decide(goal, premises, timeout=500)
    assert time.perf_counter() - start < 5.0
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def test_the_default_chain_answers_the_saturating_problem_within_its_limit():
    # 12 premises, a 2-element countermodel: the chain must come back inside the limit, with no error
    premises = [F(text) for text in _SATURATING]
    goal = F(_SATURATING_GOAL)
    start = time.perf_counter()
    verdict = api.prove(goal, premises, backends=["tableau", "resolution"], timeout=1500)
    assert time.perf_counter() - start < 8.0
    assert verdict.status == UNKNOWN          # never "proved", never an error
