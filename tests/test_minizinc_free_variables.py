"""A free variable on the MiniZinc route: a parameter in ``decide``, a refusal in ``to_minizinc``.

A free variable is ONE unknown element, shared by the premises and the conclusion. The six
problems below are decided by hand under that reading; the backend only ever refutes (it
searches for a countermodel up to a domain size), so a valid problem is ``unknown`` and an
invalid one is ``refuted`` with a countermodel that is checked here against the reading.

==========================================  =======  ==========================================
problem                                     valid?   why
==========================================  =======  ==========================================
``P(x) ⊢ P(alpha)``                         no       ``x`` and ``alpha`` may be two elements,
                                                     ``P`` holding of the first only
``P(x) ⊢ P(x)``                             yes      the same element on both sides
``P(x) ⊢ ∃y P(y)``                          yes      the element ``x`` is a witness
``∀y P(y) ⊢ P(x)``                          yes      whatever ``x`` is, ``P`` holds of it
``⊢ P(x) → P(alpha)``                       no       as the first row
``P(x), Q(y) ⊢ ∀z (P(z) ∧ Q(z))``           no       two elements, ``P`` of one, ``Q`` of the
                                                     other (or one element next to a third
                                                     with neither)
==========================================  =======  ==========================================

Closing every premise universally would call the first and the last row valid.
"""
import pytest

from unicode_fol_kit.atp.finite_domain import FiniteDomainProblem, free_variable_reason
from unicode_fol_kit.atp.minizinc_backend import MinizincBackend, minizinc_available, to_minizinc
from unicode_fol_kit.atp.protocol import REFUTED, UNKNOWN
from unicode_fol_kit.fol._free_parameters import free_parameter_names, parameterize
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Implies, Not, Quantifier, Variable
from unicode_fol_kit.semantics import evaluate_in_structure, structure_from_dict

live = pytest.mark.skipif(not minizinc_available(), reason="no minizinc binary reachable")

x, y, z = Variable("x"), Variable("y"), Variable("z")
alpha = Constant("alpha")


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


INVALID = [
    ("P(x) |- P(alpha)", [P(x)], P(alpha)),
    ("|- P(x) -> P(alpha)", [], Implies(P(x), P(alpha))),
    ("P(x), Q(y) |- forall z (P(z) & Q(z))", [P(x), Q(y)], Quantifier("forall", z, And(P(z), Q(z)))),
]
VALID = [
    ("P(x) |- P(x)", [P(x)], P(x)),
    ("P(x) |- exists y P(y)", [P(x)], Quantifier("exists", y, P(y))),
    ("forall y P(y) |- P(x)", [Quantifier("forall", y, P(y))], P(x)),
]


def _as_constants(formula):
    """``formula`` with the free variables ``x`` and ``y`` replaced by constants of their names."""
    return parameterize([formula], after_variables=True)[0][0]


@live
@pytest.mark.parametrize("name, premises, goal", INVALID, ids=[row[0] for row in INVALID])
def test_an_invalid_problem_is_refuted_with_a_countermodel_of_the_parameter_reading(name, premises, goal):
    verdict = MinizincBackend().decide(goal, premises, timeout=60000)
    assert verdict.status == REFUTED, verdict
    structure = structure_from_dict(verdict.countermodel["data"])
    # The free variables are reported under their own names, as elements of the domain.
    for variable in free_parameter_names([*premises, goal]):
        assert structure.constants[variable] in structure.domain, structure.constants
    # The structure makes every premise true and the conclusion false, with each free
    # variable denoting the one element reported for it.
    for premise in premises:
        assert evaluate_in_structure(_as_constants(premise), structure) is True
    assert evaluate_in_structure(_as_constants(goal), structure) is False


@live
@pytest.mark.parametrize("name, premises, goal", VALID, ids=[row[0] for row in VALID])
def test_a_valid_problem_has_no_countermodel(name, premises, goal):
    verdict = MinizincBackend().decide(goal, premises, timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict


@live
def test_a_closed_problem_is_decided_as_before():
    # P(alpha) |- P(beta): two constants, one of them in P.
    verdict = MinizincBackend().decide(P(Constant("beta")), [P(alpha)], timeout=60000)
    assert verdict.status == REFUTED
    # forall y P(y) |- P(alpha) is valid.
    verdict = MinizincBackend().decide(P(alpha), [Quantifier("forall", y, P(y))], timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit")


def test_distinct_constants_and_a_free_variable_are_refused_by_name():
    """Under ``all_different`` the constants are pairwise distinct; a parameter may equal any of
    them, and the model states distinctness over every constant it declares."""
    verdict = MinizincBackend().decide(P(alpha), [P(x)], timeout=60000, all_different=True,
                                       minizinc_path="unused: refused before a model is written")
    assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
    assert "all_different=True with the free variable 'x'" in verdict.detail


def test_a_free_variable_named_like_a_constant_is_refused_by_name():
    verdict = MinizincBackend().decide(P(Constant("x")), [P(x)], timeout=60000,
                                       minizinc_path="unused: refused before a model is written")
    assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
    assert "a free variable 'x' and a constant 'x'" in verdict.detail


def test_the_writer_refuses_an_open_sentence_by_name():
    problem = FiniteDomainProblem((P(x), Not(P(alpha))), size=2)
    with pytest.raises(NotImplementedError, match=r"to_minizinc: a sentence has the free variable 'x'"):
        to_minizinc(problem)


def test_the_writer_writes_the_same_problem_once_the_variable_is_a_constant():
    text = to_minizinc(FiniteDomainProblem((P(Constant("x")), Not(P(alpha))), size=2))
    assert "constraint" in text


def test_the_reason_names_every_free_variable_and_is_none_for_closed_sentences():
    assert free_variable_reason([Quantifier("forall", x, P(x)), P(alpha)]) is None
    reason = free_variable_reason([P(x), Quantifier("forall", x, Q(x)), Q(y)])
    assert reason.startswith("a sentence has the free variables 'x', 'y'.")
    # A name that is bound in one sentence and free in another is free in the problem.
    assert "'x'" in free_variable_reason([Quantifier("forall", x, P(x)), Q(x)])
