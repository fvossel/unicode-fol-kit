r"""The tableau checker and the tableau search agree on an instance whose term is a variable.

A free variable of the problem is a parameter, so a universal may be instantiated at one. When
the parameter is spelled like a variable the matrix binds, the instance needs a renamed binder.
The search (``_subst_var``) and the checker (``substitute``) both rename, and the checker
compares the instance it recomputes with the one the proof records, formula for formula, so the
two have to give the same formula.

The checker used to recompute a WRONG instance there: ``substitute(∀x1 P(x1), x0 := x1)``
returned ``∀x0 P(x1)``, with a free ``x1`` the input does not have. That rejected a genuine proof
(``∀x0 ∀x1 P(x1) ⊢ P(x1)``) and accepted a proof of a non-consequence in which the gamma step
records that wrong formula (``∀x0 ∃x1 P(x1) ⊢ P(x1)``).
"""

import random

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.tableau import (
    TableauClosure, TableauProof, TableauStep, prove_tableau_detailed,
)
from unicode_fol_kit.atp.tableau_check import (
    TableauCheckError, check_entailment_tableau_detailed, check_tableau_proof,
)
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Implies, Not, Or, Quantifier, Variable,
)

x0, x1, x2 = Variable("x0"), Variable("x1"), Variable("x2")


def P(t):
    return Atom("P", (t,))


def parse(text):
    result = api.parse_any(text)
    assert result.ok, (text, result.errors)
    return result.formula


@pytest.mark.parametrize("premises, conclusion", [
    # ∀x0 ∀x1 P(x1) says P holds of every element, so P(x1) holds whatever the parameter x1
    # is: the outer ∀ is instantiated at x1 (the inner binder must be renamed away from the
    # incoming x1), then the inner one at x1.
    (["∀x0 ∀x1 P(x1)"], "P(x1)"),
    # ∀x0 ∀x P(beta) holds exactly when P(beta) does, so P(beta) follows from it; the free x of
    # Q(x) is a parameter the universals may be instantiated at, and the binder x of the
    # matrix has to be renamed when the outer ∀x0 is instantiated at it.
    (["Q(x)", "∀x0 ∀x P(beta)"], "P(beta)"),
    # ∀x0 ∀x1 R(x0, x1) gives R(x1, x1) at x0 := x1 and then x1 := x1.
    (["∀x0 ∀x1 R(x0, x1)"], "R(x1, x1)"),
    # an equality with a free variable on the left: ∀x0 ∀x y0 = x gives y0 = x by instantiating
    # the outer ∀ at x (the inner binder x captures it) and the inner one at x.
    (["∀x0 ∀x y0 = x"], "∀x0 y0 = x"),
])
def test_a_genuine_proof_with_a_variable_instance_is_found_and_certified(premises, conclusion):
    result = check_entailment_tableau_detailed([parse(p) for p in premises], parse(conclusion))
    assert result["proved"] is True
    assert result["check_error"] is None
    assert result["check_passed"] is True


def test_the_proof_the_api_returns_for_such_a_problem_is_certified():
    premise, conclusion = parse("∀x0 ∀x1 P(x1)"), parse("P(x1)")
    verdict = api.prove(conclusion, [premise], backends=["tableau"], timeout=5000)
    assert verdict.status == "proved"
    proof = prove_tableau_detailed([premise], conclusion)
    check_tableau_proof(proof, [premise], conclusion)     # raises when it does not check


def test_the_recorded_instance_has_no_free_variable_the_premise_lacks():
    # The first gamma step instantiates ∀x0 ∀x1 P(x1) at x1. The instance has a bound variable
    # and no free one: the matrix ∀x1 P(x1) has none, and nothing is free in the step.
    premise, conclusion = parse("∀x0 ∀x1 P(x1)"), parse("P(x1)")
    proof = prove_tableau_detailed([premise], conclusion)
    gamma = next(s for s in proof.steps if s.rule == "gamma")
    assert gamma.terms == (x1,)
    assert gamma.produced[0] == Quantifier("∀", x2, P(x2))


def _proof_of_a_non_consequence():
    """∀x0 ∃x1 P(x1) ⊢ P(x1) with a gamma step that records the wrong instance.

    The premise says some element has P. The conclusion P(x1) is about the parameter x1. A
    countermodel: domain {0, 1}, P = {0}, x1 ↦ 1; the premise holds (0 has P) and P(1) fails.
    So no proof exists. The proof below instantiates the outer ∀x0 at x1 and records
    ``∃x0 P(x1)`` for the result, which is what the wrong substitution returned; the true
    instance is ∃x2 P(x2). From ``∃x0 P(x1)`` a witness step gives P(x1), which closes against
    ¬P(x1) of the root -- a refutation of a satisfiable set.
    """
    premise = Quantifier("∀", x0, Quantifier("∃", x1, P(x1)))
    conclusion = P(x1)
    wrong = Quantifier("∃", x0, P(x1))
    proof = TableauProof(
        root_formulas=(premise, Not(conclusion)),
        steps=(
            TableauStep(1, 0, "gamma", premise, produced=(wrong,), terms=(x1,)),
            TableauStep(2, 1, "delta", wrong, produced=(P(x1),), fresh_constant=Constant("_t0")),
        ),
        closures=(TableauClosure(leaf_id=2, literal=P(x1), literal_step_id=2,
                                 complement=Not(P(x1)), complement_step_id=0),),
    )
    return proof, premise, conclusion


def test_a_proof_that_records_a_wrong_instance_is_rejected():
    proof, premise, conclusion = _proof_of_a_non_consequence()
    with pytest.raises(TableauCheckError, match="substitution does not check out"):
        check_tableau_proof(proof, [premise], conclusion)


def test_the_non_consequence_has_no_proof():
    # The search agrees: there is nothing to find (the countermodel above).
    _, premise, conclusion = _proof_of_a_non_consequence()
    assert prove_tableau_detailed([premise], conclusion, max_steps=400) is None


def _random_problem(rng):
    """A premise with nested universals over pool variables and a conclusion instantiating it."""
    pool = ["x", "x0", "x1", "y"]
    binders = [rng.choice(pool) for _ in range(rng.randrange(1, 4))]

    def atom(names):
        if rng.random() < 0.5:
            return Atom("P", (Variable(rng.choice(names)),))
        return Atom("R", (Variable(rng.choice(names)), Variable(rng.choice(names))))

    matrix = atom(binders)
    for _ in range(rng.randrange(0, 3)):
        extra = atom(binders + [rng.choice(pool)])
        matrix = rng.choice((And, Or))(matrix, extra) if rng.random() < 0.6 else matrix
    if rng.random() < 0.3:
        inner = Variable(rng.choice(pool))
        matrix = Quantifier(rng.choice("∀∃"), inner, And(matrix, atom(binders + [inner.name])))
    premise = matrix
    for name in reversed(binders):
        premise = Quantifier("∀", Variable(name), premise)
    # the conclusion: the matrix atom with every variable replaced by a pool variable
    conclusion = atom([rng.choice(pool) for _ in range(2)])
    if rng.random() < 0.4:
        conclusion = Implies(conclusion, conclusion)
    return premise, conclusion


def test_every_proof_the_search_finds_on_binder_heavy_problems_is_certified():
    rng = random.Random(1)
    proofs = 0
    for _ in range(3000):
        premise, conclusion = _random_problem(rng)
        result = check_entailment_tableau_detailed([premise], conclusion, max_steps=300,
                                                   max_terms=4)
        if result["proved"]:
            proofs += 1
            assert result["check_passed"] is True, (
                premise.to_unicode_str(), conclusion.to_unicode_str(), result["check_error"])
    assert proofs >= 1000      # the battery is not vacuous: most problems are provable
