"""Resolution refuses a cardinality term by name.

``|{x : P(x)}|`` is a natural number that is counted in a structure, not a term of first-order
logic, so it has no clause form. Read as an uninterpreted term it would answer another question:

    ∀x (P(x) ↔ Q(x))  ⊢  |{x : P(x)}| = |{x : Q(x)}|

is valid (``P`` and ``Q`` hold of the same elements, so the two sets are one set with one number
of elements), and it does not follow when the two cardinalities are two unrelated terms. The
route used to fail inside its clause renaming with a ``TypeError``, which the backend reported
as ``error`` / ``infra``: a failure of the machinery, where the input is simply outside the
fragment. It is ``unknown`` / ``unsupported`` with the cardinality named, as on the other routes.

A counting quantifier is first-order and is still read: from ``P(alpha)``, ``P(beta)`` and
``alpha ≠ beta`` there are two different elements with ``P``, so ``∃≥2 x P(x)`` follows; from
``P(alpha)`` alone it does not (universe ``{0}``, ``P = {0}``).
"""

import pytest

from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.atp import resolution
from unicode_fol_kit.atp.protocol import ResolutionBackend

PARSER = MSFLParser()
SORTED = MSFLParser(many_sorted=True)


def _problem(conclusion, *premises, parser=PARSER):
    return [parser.parse(premise) for premise in premises], parser.parse(conclusion)


CARDINALITY_PROBLEMS = {
    "an argument of a predicate": _problem("R(|{x : P(x)}|)", "∀y R(y)"),
    "compared with a number": _problem("|{x : P(x)}| ≥ 1", "P(alpha)"),
    "two cardinalities compared": _problem("|{x : P(x)}| = |{x : Q(x)}|", "∀x (P(x) ↔ Q(x))"),
    "in a premise the proof would not need": _problem("Q(alpha)", "R(|{x : P(x)}|)", "Q(alpha)"),
}


@pytest.mark.parametrize("label", sorted(CARDINALITY_PROBLEMS))
def test_the_prover_refuses_the_problem_and_names_the_cardinality(label):
    premises, conclusion = CARDINALITY_PROBLEMS[label]
    with pytest.raises(NotImplementedError, match=r"the cardinality \|\{x : P\(x\)\}\| has no clause form"):
        resolution.prove(premises, conclusion)


@pytest.mark.parametrize("label", sorted(CARDINALITY_PROBLEMS))
def test_the_backend_answers_unknown_unsupported_and_not_an_error(label):
    premises, conclusion = CARDINALITY_PROBLEMS[label]
    verdict = ResolutionBackend().decide(conclusion, premises)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "|{x : P(x)}|" in verdict.detail
    through_the_chain = api.prove(conclusion, premises, backends=["resolution"])
    assert through_the_chain.status == "unknown"
    assert "resolution:unknown/unsupported" in through_the_chain.detail


def test_a_sorted_cardinality_is_refused_too():
    premises, conclusion = _problem("|{x:Human : Tall(x)}| = 2", parser=SORTED)
    with pytest.raises(NotImplementedError, match=r"the cardinality \|\{x:Human : Tall\(x\)\}\|"):
        resolution.prove(premises, conclusion)


def test_a_counting_quantifier_is_still_read():
    premises, conclusion = _problem("∃≥2 x P(x)", "P(alpha)", "P(beta)", "alpha ≠ beta")
    assert resolution.prove(premises, conclusion) is True
    premises, conclusion = _problem("∃≥2 x P(x)", "P(alpha)")
    assert resolution.prove(premises, conclusion) is False


def test_a_problem_without_a_cardinality_is_decided_as_before():
    premises, conclusion = _problem("R(alpha)", "∀y R(y)")
    assert resolution.prove(premises, conclusion) is True
    assert ResolutionBackend().decide(conclusion, premises).status == "proved"
