"""A free variable is a parameter of the problem: one unknown element, the same everywhere.

The consequence relation is the assignment-wise one: ``Γ ⊨ φ`` iff every structure AND
assignment that satisfies ``Γ`` satisfies ``φ``. Every expectation below is derived by hand.

* ``P(x) ⊢ P(alpha)`` is NOT valid: universe ``{0, 1}``, ``x`` ↦ 1, ``alpha`` ↦ 0, ``P`` = ``{1}``
  makes the premise true and the conclusion false.
* ``P(x) ⊢ P(x)`` is valid, and so is ``P(x) ⊢ ∃y P(y)`` (take ``y`` := the element of ``x``).
* ``∀y P(y) ⊢ P(x)`` is valid: ``P`` holds of every element, ``x`` is one.
* ``⊢ P(x) → P(alpha)`` is NOT valid: the same structure, with no premise.
* ``P(x), Q(y) ⊢ ∀z (P(z) ∧ Q(z))`` is NOT valid: universe ``{0, 1}``, ``x`` = ``y`` = 0,
  ``P`` = ``Q`` = ``{0}`` makes both premises true and ``z`` = 1 falsifies the conclusion.

No route may close a PREMISE universally: ``∀x P(x)`` is a different premise from ``P(x)``.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import resolution, tableau
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Iff, Implies, Not, Quantifier, Variable, free_variables,
)
from unicode_logic_kit.semantics import modelfinder
from unicode_logic_kit.semantics.tarski import satisfies

x, y, z = Variable("x"), Variable("y"), Variable("z")
alpha = Constant("alpha")


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


# name, premises, conclusion, valid -- each one derived by hand in the module docstring
PROBLEMS = [
    ("P(x) |- P(alpha)", [P(x)], P(alpha), False),
    ("P(x) |- P(x)", [P(x)], P(x), True),
    ("P(x) |- exists y P(y)", [P(x)], exists(y, P(y)), True),
    ("forall y P(y) |- P(x)", [forall(y, P(y))], P(x), True),
    ("|- P(x) -> P(alpha)", [], Implies(P(x), P(alpha)), False),
    ("P(x), Q(y) |- forall z (P(z) & Q(z))", [P(x), Q(y)], forall(z, And(P(z), Q(z))), False),
]
IDS = [name for name, *_ in PROBLEMS]


def assignment_of(structure, *formulas):
    """The assignment the structure reports: each free variable under its own name."""
    names = {v.name for f in formulas for v in free_variables(f)}
    return {name: structure.constants[name] for name in names}


# --------------------------------------------------------------------------- #
# the six problems, route by route
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_resolution_reads_the_free_variable_as_a_parameter(name, premises, conclusion, valid):
    assert resolution.prove(premises, conclusion) is valid


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_the_tableau_reads_the_free_variable_as_a_parameter(name, premises, conclusion, valid):
    assert tableau.prove_tableau(premises, conclusion) is valid


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_the_model_finder_finds_a_countermodel_exactly_for_the_invalid_problems(
        name, premises, conclusion, valid):
    structure = modelfinder.find_countermodel(premises, conclusion, max_size=3)
    assert (structure is None) is valid
    if structure is not None:
        # the structure reports the parameter under the variable's own name, and the
        # premises hold and the conclusion fails under that ONE assignment
        assignment = assignment_of(structure, *premises, conclusion)
        assert all(satisfies(p, structure, assignment) for p in premises)
        assert not satisfies(conclusion, structure, assignment)


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
@pytest.mark.parametrize("chain", [["resolution", "z3"], ["z3", "resolution"]],
                         ids=["resolution-first", "z3-first"])
def test_api_prove_gives_the_same_answer_for_both_orders_of_a_chain(
        name, premises, conclusion, valid, chain):
    verdict = api.prove(conclusion, premises, backends=chain, timeout=8000)
    assert verdict.status == ("proved" if valid else "refuted")


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_no_route_answers_the_opposite_of_the_table(name, premises, conclusion, valid):
    for backend in ("resolution", "tableau", "modelfinder", "z3"):
        status = api.prove(conclusion, premises, backends=[backend], timeout=8000).status
        # a route may say "unknown" (every in-house prover is incomplete under its bound),
        # never the opposite
        assert status != ("refuted" if valid else "proved"), (backend, status)


def test_a_countermodel_through_the_api_reports_the_parameter_under_the_variables_name():
    result = api.countermodel(P(alpha), [P(x)], backends=["modelfinder"])
    assert result.found and result.backend == "modelfinder"
    assert "'x'" in result.model["repr"] and "'alpha'" in result.model["repr"]


# --------------------------------------------------------------------------- #
# the model finder: satisfiability and validity of formulas with free variables
# --------------------------------------------------------------------------- #

def test_two_free_variables_may_be_two_elements():
    # P(x) ∧ ¬P(y): satisfiable -- x and y are two unknown elements, one in P and one not
    theory = [P(x), Not(P(y))]
    structure = modelfinder.find_model(theory, max_size=2)
    assert structure is not None
    assignment = assignment_of(structure, *theory)
    assert assignment["x"] != assignment["y"]
    assert all(satisfies(f, structure, assignment) for f in theory)
    assert modelfinder.is_satisfiable_finite(And(P(x), Not(P(y))), max_size=2)


def test_the_same_variable_in_two_formulas_is_one_element():
    # P(x) and ¬P(x) cannot both hold of the one element x stands for
    assert modelfinder.find_model([P(x), Not(P(x))], max_size=3) is None


def test_validity_of_a_formula_with_free_variables_is_validity_of_its_closure():
    assert modelfinder.is_valid_finite(Implies(P(x), P(x)), max_size=2)
    assert not modelfinder.is_valid_finite(Implies(P(x), P(y)), max_size=2)
    assert not modelfinder.is_valid_finite(Implies(P(x), P(alpha)), max_size=2)


def test_a_search_over_two_elements_counts_the_parameters_as_constants():
    # R(x, y) over 2 elements: the binary predicate has 2^4 = 16 interpretations, and the two
    # parameters are two constants, whose assignments up to relabelling are 2 (x and y the
    # same element, or two elements): 2 * 16 = 32 structures. A closure would count 16.
    relation = Atom("R", [x, y])
    assert not modelfinder.is_size_exhaustive([relation], 2, max_candidates=31)
    assert modelfinder.is_size_exhaustive([relation], 2, max_candidates=32)


def test_a_variable_named_like_a_constant_is_refused_by_the_model_finder_by_name():
    clash = [Atom("R", [x, Constant("x")])]
    with pytest.raises(NotImplementedError, match="free variable 'x'"):
        modelfinder.find_model(clash)
    with pytest.raises(NotImplementedError, match="free variable 'x'"):
        modelfinder.find_countermodel([], Atom("R", [x, Constant("x")]))
    verdict = api.prove(Atom("R", [x, x]), clash, backends=["modelfinder"])
    assert verdict.status == "unknown"
    assert "free variable 'x'" in verdict.detail


# --------------------------------------------------------------------------- #
# resolution: a variable and a constant that are spelled alike are two symbols
# --------------------------------------------------------------------------- #

def test_a_free_variable_is_not_a_constant_of_the_same_name_in_resolution():
    # premises P(x) (x a variable) and ¬P(c) (c the constant spelled x); goal Z(zz).
    # Not valid: universe {0, 1}, P = {0}, the variable x ↦ 0, the constant c ↦ 1, Z = {}.
    # Closing P(x) universally would make it ∀x P(x), which contradicts ¬P(c).
    variable_premise = P(x)
    constant_premise = Not(P(Constant("x")))
    goal = Atom("Z", [Constant("zz")])
    assert resolution.prove([variable_premise, constant_premise], goal) is False
    assert tableau.prove_tableau([variable_premise, constant_premise], goal) is False


def test_a_premise_is_never_closed_universally():
    # ∀x P(x) ⊢ P(alpha) is valid, P(x) ⊢ P(alpha) is not: the two premises differ
    assert resolution.prove([forall(x, P(x))], P(alpha)) is True
    assert resolution.prove([P(x)], P(alpha)) is False
    assert resolution.is_valid_resolution(Implies(forall(x, P(x)), P(alpha))) is True
    assert resolution.is_valid_resolution(Implies(P(x), P(alpha))) is False
    assert resolution.is_valid_resolution(Implies(P(x), P(x))) is True


def test_a_free_variable_of_the_conclusion_stays_one_element_under_the_negation():
    # (P(x) → ∀y P(y)) is not valid: x is one element, P may hold of it and fail elsewhere
    assert resolution.is_valid_resolution(Implies(P(x), forall(y, P(y)))) is False
    # ... while (∀y P(y) → P(x)) is
    assert resolution.is_valid_resolution(Implies(forall(y, P(y)), P(x))) is True


def test_a_biconditional_of_one_parameter_is_valid_and_of_two_is_not():
    # P(x) ↔ P(x) is valid whatever x is; P(x) ↔ P(y) is not (x ≠ y is possible)
    assert resolution.is_valid_resolution(Iff(P(x), P(x))) is True
    assert resolution.is_valid_resolution(Iff(P(x), P(y))) is False


# --------------------------------------------------------------------------- #
# premises whose universal closure is inconsistent but whose parameter reading is not
# --------------------------------------------------------------------------- #

R = lambda a, b: Atom("R", [a, b])  # noqa: E731
ann, bob = Constant("ann"), Constant("bob")

CLOSURE_INCONSISTENT = [
    # ¬(Q(ann) → Q(x)) says Q(ann) ∧ ¬Q(x): true for x := an element outside Q, and
    # R(z, z) is not forced (R empty). ∀x of the premise fails at x := ann.
    ("not(Q(ann) -> Q(x)) |- R(z, z)",
     [Not(Implies(Q(ann), Q(x)))], R(z, z)),
    # Q(x) ∧ ¬Q(bob) ∧ ∀w R(w, x) holds with x ≠ bob; then R(ann, ann) ∧ ¬P(ann) fails for
    # P(ann) true. ∀x Q(x) contradicts ¬Q(bob).
    ("Q(x), not Q(bob) & forall w R(w, x) |- R(ann, ann) & not P(ann)",
     [Q(x), And(Not(Q(bob)), forall(Variable("w"), R(Variable("w"), x)))],
     And(R(ann, ann), Not(P(ann)))),
    # ¬(Q(x) ↔ Q(z)) puts x and z on different sides of Q (x ≠ z); with ¬Q(ann) the
    # conclusion ∀y ¬P(z) fails for P(z) true. ∀x of the premise fails at x := z.
    ("not(Q(x) <-> Q(z)), not Q(ann) |- forall y not P(z)",
     [Not(Iff(Q(x), Q(z))), Not(Q(ann))], forall(y, Not(P(z)))),
]


@pytest.mark.parametrize("name,premises,conclusion", CLOSURE_INCONSISTENT,
                         ids=[c[0] for c in CLOSURE_INCONSISTENT])
def test_a_premise_whose_closure_is_inconsistent_does_not_prove_everything(
        name, premises, conclusion):
    assert resolution.prove(premises, conclusion) is False
    assert tableau.prove_tableau(premises, conclusion) is False
    structure = modelfinder.find_countermodel(premises, conclusion, max_size=3)
    assert structure is not None
    assignment = assignment_of(structure, *premises, conclusion)
    assert all(satisfies(p, structure, assignment) for p in premises)
    assert not satisfies(conclusion, structure, assignment)
    assert api.prove(conclusion, premises, backends=["resolution"], timeout=8000).status != "proved"
