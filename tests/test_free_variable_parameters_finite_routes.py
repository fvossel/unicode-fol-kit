"""A free variable is a parameter on the finite-model routes of the nonclassical modules.

The consequence relation is the assignment-wise one: ``Γ ⊨ φ`` iff every structure AND
assignment that satisfies ``Γ`` satisfies ``φ``. A free variable names ONE unknown element, the
same in every premise and in the conclusion, and no premise is closed universally. Every
expectation is derived by hand.

* ``P(x) ⊢ P(alpha)`` is NOT valid: universe ``{0, 1}``, ``x`` ↦ 1, ``alpha`` ↦ 0, ``P`` = ``{1}``.
* ``P(x) ⊢ P(x)`` and ``P(x) ⊢ ∃y P(y)`` and ``∀y P(y) ⊢ P(x)`` are valid.
* ``⊢ P(x) → P(alpha)`` is NOT valid (the same structure, no premise).
* ``P(x), Q(y) ⊢ ∀z (P(z) ∧ Q(z))`` is NOT valid: universe ``{0, 1}``, ``x`` = ``y`` = 0,
  ``P`` = ``Q`` = ``{0}`` makes both premises true and ``z`` = 1 falsifies the conclusion.

Circumscribing ``P`` changes two rows of the table, and each is derived by hand below.
"""

import random

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.clingo_backend import ClingoBackend
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Implies, Not, Or, Quantifier, SecondOrderQuantifier, Variable,
    free_variables,
)
from unicode_logic_kit.semantics import (
    asp_models, free_logic, modelfinder, nonmonotonic, secondorder,
)
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


def implication(premises, conclusion):
    """The single formula ``(p1 ∧ … ∧ pn) → conclusion`` of a route that decides one formula."""
    if not premises:
        return conclusion
    body = premises[0]
    for premise in premises[1:]:
        body = And(body, premise)
    return Implies(body, conclusion)


def assignment_of(structure, *formulas):
    """The assignment a structure reports: each free variable under its own name."""
    names = {v.name for f in formulas for v in free_variables(f)}
    return {name: structure.constants[name] for name in names}


# --------------------------------------------------------------------------- #
# asp_models: a countermodel of Γ ⊢ φ is a model of Γ ∪ {¬φ} under ONE assignment
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_asp_find_model_finds_a_countermodel_exactly_for_the_invalid_problems(
        name, premises, conclusion, valid):
    pytest.importorskip("clingo")
    theory = list(premises) + [Not(conclusion)]
    structure = asp_models.asp_find_model(theory, size=2)
    assert (structure is None) is valid
    if structure is not None:
        assignment = assignment_of(structure, *theory)
        assert all(satisfies(f, structure, assignment) for f in theory)


def test_asp_find_model_reads_two_free_variables_as_two_elements():
    pytest.importorskip("clingo")
    # P(x) ∧ ¬P(y) holds when x and y are two elements, one in P and one not
    theory = [P(x), Not(P(y))]
    structure = asp_models.asp_find_model(theory, size=2)
    assert structure is not None
    assert structure.constants["x"] != structure.constants["y"]
    assert asp_models.asp_find_model([P(x), Not(P(x))], size=2) is None


def test_asp_find_model_keeps_a_variable_free_in_one_premise_apart_from_the_same_name_bound_in_another():
    pytest.importorskip("clingo")
    # P(x) with x free, and ∀x ¬P(x): the bound x is another symbol, so the premises
    # contradict each other (the parameter is an element of P and no element is)
    assert asp_models.asp_find_model([P(x), forall(x, Not(P(x)))], size=2) is None
    # while P(x) and ∀x Q(x) are satisfiable together
    assert asp_models.asp_find_model([P(x), forall(x, Q(x))], size=2) is not None


def _key(structure):
    return (structure.domain, tuple(sorted(structure.constants.items())),
            tuple(sorted((k, tuple(sorted(v))) for k, v in structure.predicates.items())))


@pytest.mark.parametrize("circumscribed", [None, {"P"}, set()], ids=["all", "P", "none"])
@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_asp_minimal_models_equal_the_brute_force_minimal_models(
        name, premises, conclusion, valid, circumscribed):
    pytest.importorskip("clingo")
    theory = list(premises) + [Not(conclusion)]
    for size in (1, 2):
        expected = [m for m in nonmonotonic.minimal_models(theory, circumscribed, max_size=size)
                    if len(m.domain) == size]
        found = asp_models.asp_minimal_models(theory, circumscribed, size=size)
        assert sorted(map(_key, found)) == sorted(map(_key, expected))


def test_asp_minimal_models_of_a_free_variable_circumscribing_its_predicate():
    pytest.importorskip("clingo")
    # P(x) with P minimised over {0, 1}: the minimal models make P true of x alone, and x is
    # either element, so there are exactly two of them
    found = asp_models.asp_minimal_models([P(x)], {"P"}, size=2)
    assert sorted((m.constants["x"], tuple(sorted(m.predicates[("P", 1)]))) for m in found) == [
        (0, ((0,),)), (1, ((1,),))]


# --------------------------------------------------------------------------- #
# nonmonotonic: the circumscribed entailment relation
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_minimal_entails_without_circumscription_is_the_classical_table(
        name, premises, conclusion, valid):
    assert nonmonotonic.minimal_entails(premises, conclusion, set(), max_size=3) is valid


# Circumscribing P: P(x) makes P true of x alone, so P(alpha) fails (alpha may be another
# element) and the fifth problem changes -- with no premise the minimal P is empty, so
# P(x) → P(alpha) holds in every minimal model. The sixth is still not entailed: x = y = 0,
# P = Q = {0}, and z = 1 falsifies the conclusion.
CIRCUMSCRIBED_P = [False, True, True, True, True, False]


@pytest.mark.parametrize("problem,expected", list(zip(PROBLEMS, CIRCUMSCRIBED_P)), ids=IDS)
def test_minimal_entails_circumscribing_P(problem, expected):
    name, premises, conclusion, _ = problem
    assert nonmonotonic.minimal_entails(premises, conclusion, {"P"}, max_size=3) is expected


def test_a_premise_with_a_free_variable_is_not_a_universal_premise():
    # ∀x P(x) circumscribing P entails P(alpha); P(x) does not
    assert nonmonotonic.minimal_entails([forall(x, P(x))], P(alpha), {"P"}, max_size=3)
    assert not nonmonotonic.minimal_entails([P(x)], P(alpha), {"P"}, max_size=3)


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_the_circumscription_axiom_decides_what_the_model_search_decides(
        name, premises, conclusion, valid):
    sentence = nonmonotonic.circumscription_entails_so(premises, {"P"}, conclusion)
    assert not free_variables(sentence)
    expected = CIRCUMSCRIBED_P[[p[0] for p in PROBLEMS].index(name)]
    assert secondorder.so_is_valid_finite(sentence, max_size=3) is expected


def test_the_circumscription_axiom_names_the_parameter_after_the_variable():
    axiom = nonmonotonic.circumscription_formula([P(x)], {"P"})
    assert not free_variables(axiom)
    assert any(isinstance(n, Constant) and n.name == "x" for n in axiom.walk())


# --------------------------------------------------------------------------- #
# secondorder: satisfiability reads a parameter, validity is validity under every assignment
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_so_validity_of_the_implication(name, premises, conclusion, valid):
    assert secondorder.so_is_valid_finite(implication(premises, conclusion), max_size=3) is valid


@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_so_satisfiability_of_premises_and_the_negated_conclusion(
        name, premises, conclusion, valid):
    theory = Not(conclusion)
    for premise in premises:
        theory = And(premise, theory)
    assert secondorder.so_is_satisfiable_finite(theory, max_size=2) is (not valid)


def test_so_find_model_reports_two_elements_for_two_free_variables():
    structure = secondorder.so_find_model(And(P(x), Not(P(y))), max_size=2)
    assert structure is not None
    assert structure.constants["x"] != structure.constants["y"]
    assert secondorder.so_find_model(And(P(x), Not(P(x))), max_size=2) is None


def test_so_countermodel_reports_the_falsifying_assignment():
    formula = Implies(P(x), P(alpha))
    structure = secondorder.so_find_countermodel(formula, max_size=2)
    assert structure is not None
    assert not satisfies(formula, structure, assignment_of(structure, formula))


def _so_validity_with_a_free_variable(fast):
    # ∀Q (Q(x) → Q(y)) says x and y are one element: it is valid exactly when they are.
    same = Atom("=", [x, y])
    block = SecondOrderQuantifier("∀", "Q", 1, Implies(Atom("Q", [x]), Atom("Q", [y])))
    assert secondorder.so_is_valid_finite(block, max_size=2, fast=fast) is False
    assert secondorder.so_is_valid_finite(Implies(same, block), max_size=2, fast=fast) is True


def test_so_validity_with_a_free_variable_by_enumeration():
    _so_validity_with_a_free_variable(fast=False)


def test_so_validity_checked_through_clingo_with_a_free_variable():
    # The second-order block has no free object variable once x and y are parameters, so the
    # clingo-grounded check applies, and agrees with the enumeration.
    pytest.importorskip("clingo")
    _so_validity_with_a_free_variable(fast=True)


# --------------------------------------------------------------------------- #
# free logic: a variable ranges over the EXISTING objects
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("policy", ["negative", "positive", "supervaluation"])
@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_free_entails_follows_the_table(name, premises, conclusion, valid, policy):
    assert free_logic.free_entails(premises, conclusion, max_size=3, policy=policy) is valid


def test_free_validity_of_a_formula_with_a_free_variable_is_validity_under_every_assignment():
    # the empty-existing model, in which ∀x ¬(P(x) → P(x)) holds vacuously, is no
    # countermodel: no assignment of x to an existing object is there
    assert free_logic.free_is_valid(Implies(P(x), P(x)))
    assert free_logic.free_countermodel(Implies(P(x), P(x))) is None


def test_a_free_variable_denotes_an_existing_object_and_a_constant_need_not():
    assert free_logic.free_is_valid(Atom("E!", [x]))
    assert not free_logic.free_is_valid(Atom("E!", [alpha]))


def test_a_model_with_no_existing_object_is_no_model_of_a_formula_with_a_free_variable():
    contradiction = And(P(x), Not(P(x)))
    assert free_logic.free_find_model(contradiction) is None


def test_free_find_model_reports_the_parameters_as_existing_elements():
    model = free_logic.free_find_model(And(P(x), Not(P(y))))
    assert model is not None
    assert {model.constants["x"], model.constants["y"]} <= model.existing
    assert model.constants["x"] != model.constants["y"]
    assignment = {"x": model.constants["x"], "y": model.constants["y"]}
    assert free_logic.free_satisfies(And(P(x), Not(P(y))), model, assignment)


# --------------------------------------------------------------------------- #
# clingo: a refutation-only route (never `proved`), complete on small counter-models
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name,premises,conclusion,valid", PROBLEMS, ids=IDS)
def test_clingo_refutes_exactly_the_invalid_problems(name, premises, conclusion, valid):
    pytest.importorskip("clingo")
    verdict = ClingoBackend().decide(conclusion, premises, max_size=3)
    if valid:
        assert verdict.status == "unknown" and verdict.reason == "bound_hit"
    else:
        from unicode_logic_kit.semantics import structure_from_dict
        assert verdict.status == "refuted"
        # every problem of the table has the free variable x, reported as a constant
        assert "x" in structure_from_dict(verdict.countermodel["data"]).constants


def test_clingo_countermodel_reports_the_parameter_under_the_variable_name():
    pytest.importorskip("clingo")
    from unicode_logic_kit.semantics import structure_from_dict
    verdict = ClingoBackend().decide(P(alpha), [P(x)], max_size=3)
    assert verdict.status == "refuted"
    structure = structure_from_dict(verdict.countermodel["data"])
    assert set(structure.constants) == {"alpha", "x"}
    assert structure.constants["x"] != structure.constants["alpha"]
    assert (structure.constants["x"],) in structure.extensions[("P", 1)]


def test_clingo_unique_names_concern_the_constants_never_a_variable():
    pytest.importorskip("clingo")
    # x = alpha ⊬ Q: one element, x and alpha the same one, Q false. A parameter that unique
    # names forced apart from alpha would make the premise unsatisfiable at every size.
    verdict = ClingoBackend().decide(Atom("Q", []), [Atom("=", [x, alpha])],
                                     max_size=3, all_different=True)
    assert verdict.status == "refuted"
    # two constants are still held apart
    beta = Constant("beta")
    verdict = ClingoBackend().decide(Atom("Q", []), [Atom("=", [alpha, beta])],
                                     max_size=3, all_different=True)
    assert verdict.status == "unknown"


def test_clingo_through_api_prove_agrees_in_both_chain_orders():
    pytest.importorskip("clingo")
    for chain in (["clingo", "z3"], ["z3", "clingo"]):
        for name, premises, conclusion, valid in PROBLEMS:
            status = api.prove(conclusion, premises, backends=chain, timeout=8000).status
            assert status == ("proved" if valid else "refuted"), (name, chain, status)


# --------------------------------------------------------------------------- #
# a variable and a constant that share a spelling cannot be told apart in a structure
# --------------------------------------------------------------------------- #

def test_the_asp_routes_refuse_a_free_variable_spelled_like_a_constant_by_name():
    pytest.importorskip("clingo")
    clash = [P(x), Q(Constant("x"))]
    with pytest.raises(NotImplementedError, match="'x'"):
        asp_models.asp_find_model(clash, size=2)
    with pytest.raises(NotImplementedError, match="'x'"):
        asp_models.asp_minimal_models(clash, size=2)


def test_a_free_variable_spelled_like_a_constant_is_refused_by_name():
    clash = [P(x), Q(Constant("x"))]
    with pytest.raises(NotImplementedError, match="'x'"):
        nonmonotonic.minimal_entails(clash, P(alpha), max_size=2)
    with pytest.raises(NotImplementedError, match="'x'"):
        nonmonotonic.circumscription_formula(clash, {"P"})
    with pytest.raises(NotImplementedError, match="'x'"):
        secondorder.so_find_model(And(*clash), max_size=2)
    with pytest.raises(NotImplementedError, match="'x'"):
        free_logic.free_entails(clash, P(alpha), max_size=2)
    with pytest.raises(NotImplementedError, match="'x'"):
        free_logic.free_find_model(And(*clash), max_size=2)


def test_clingo_refuses_a_free_variable_spelled_like_a_constant_by_name():
    pytest.importorskip("clingo")
    verdict = ClingoBackend().decide(P(alpha), [P(x), Q(Constant("x"))], max_size=2)
    assert verdict.status == "unknown" and verdict.reason == "unsupported"
    assert "'x'" in verdict.detail


# --------------------------------------------------------------------------- #
# the routes against an independent oracle: Z3 reads a free variable as a parameter too
# --------------------------------------------------------------------------- #

def _random_formula(rng, depth):
    terms = [x, y, alpha]
    if depth == 0 or rng.random() < 0.25:
        return Atom(rng.choice(["P", "Q"]), [rng.choice(terms)])
    kind = rng.choice(["not", "and", "or", "implies", "forall", "exists"])
    if kind == "not":
        return Not(_random_formula(rng, depth - 1))
    if kind in ("and", "or", "implies"):
        left, right = _random_formula(rng, depth - 1), _random_formula(rng, depth - 1)
        return {"and": And, "or": Or, "implies": Implies}[kind](left, right)
    var = rng.choice([x, y, z])
    body = _random_formula(rng, depth - 1)
    return Quantifier("∀" if kind == "forall" else "∃", var, body)


def _random_problems(count, seed):
    rng = random.Random(seed)
    problems = []
    while len(problems) < count:
        premises = [_random_formula(rng, 2) for _ in range(rng.choice([0, 1, 2]))]
        conclusion = _random_formula(rng, 2)
        if any(free_variables(f) for f in premises + [conclusion]):
            problems.append((premises, conclusion))
    return problems


GENERATED = _random_problems(60, seed=20261005)


def _z3_status(premises, conclusion):
    return api.prove(conclusion, premises, backends=["z3"], timeout=4000).status


def test_the_finite_routes_agree_with_each_other_and_never_contradict_z3_on_generated_problems():
    pytest.importorskip("clingo")
    clingo_backend = ClingoBackend()
    proved = refuted_by_a_route = 0
    for premises, conclusion in GENERATED:
        # the routes search the same structures (up to three elements, one signature), so
        # they agree exactly on whether a countermodel is there
        counter = modelfinder.find_countermodel(premises, conclusion, max_size=3) is not None
        votes = {
            "minimal_entails": not nonmonotonic.minimal_entails(premises, conclusion, set(), max_size=3),
            "asp_find_model": any(
                asp_models.asp_find_model(list(premises) + [Not(conclusion)], size=k) is not None
                for k in (1, 2, 3)),
            "so_is_valid_finite": not secondorder.so_is_valid_finite(
                implication(premises, conclusion), max_size=3),
            "clingo": ClingoBackend().decide(conclusion, premises, max_size=3).status == "refuted",
        }
        assert all(vote == counter for vote in votes.values()), (premises, conclusion, votes)
        # a countermodel is a real one, so Z3 has not proved the problem; a problem Z3 proved
        # has no countermodel to find. (Z3 may refute what no model of three elements does.)
        status = _z3_status(premises, conclusion)
        if counter:
            refuted_by_a_route += 1
            assert status != "proved", (premises, conclusion)
        if status == "proved":
            proved += 1
            assert not counter, (premises, conclusion)
    assert proved >= 5 and refuted_by_a_route >= 15
