"""``equivalent`` says WHY it has no answer when the solver level refused the input.

The solver level answers ``True`` (equivalent), ``False`` (not, with a counterexample) or ``None``. ``None``
used to be the same for "undecided within the budget" and for "the input is one the solver level has no image
for" (a numeral and a constant that are one symbol, a family with no first-order translation), so a caller
could not tell a refusal from a time-out. ``EquivalenceResult.reason`` carries the refusal's own text, and is
``None`` in every other case.

Hand-derived inputs: ``P(1)`` and ``P('1')`` (``Number(1)`` and ``Constant('1')``) say the same only if a numeral
and a constant of one spelling were one symbol, which the translation refuses; ``P(a) ∧ Q(a)`` and
``Q(a) ∧ P(a)`` are equivalent, and ``P(a)`` and ``Q(a)`` are not.
"""
import pytest

from unicode_fol_kit import api
from unicode_fol_kit.eval.equivalence import EquivalenceResult, equivalent
from unicode_fol_kit.fol.nodes import And, Atom, Cardinality, Constant, Number, Variable

CLASH = (Atom("P", [Number(1)]), Atom("P", [Constant("1")]))


@pytest.mark.parametrize("method", ["solver", "auto"])
def test_a_numeral_and_a_constant_of_one_spelling_are_refused_and_the_result_says_so(method):
    result = equivalent(*CLASH, method=method)
    assert result.equivalent is None and result.counterexample is None
    assert result.method_used == "solver"
    assert "numeral 1" in result.reason and "constant named '1'" in result.reason


def test_the_reason_is_in_the_dict_form():
    data = equivalent(*CLASH, method="solver").to_dict()
    assert data["equivalent"] is None and "numeral 1" in data["reason"]


def test_a_family_the_solver_has_no_image_for_is_refused_by_name():
    # a set-cardinality term is second order: no first-order export
    x = Variable("x")
    left = Atom(">", [Cardinality(x, Atom("P", [x])), Number(1)])
    right = Atom(">", [Cardinality(x, Atom("Q", [x])), Number(1)])
    result = equivalent(left, right, method="solver")
    assert result.equivalent is None and "Cardinality" in result.reason


def test_a_decided_pair_has_no_reason():
    a = Constant("alpha")
    p, q = Atom("P", [a]), Atom("Q", [a])
    assert equivalent(And(p, q), And(q, p), method="solver").reason is None
    refuted = equivalent(p, q, method="solver")
    assert refuted.equivalent is False and refuted.reason is None


def test_a_call_that_never_reached_the_solver_has_no_reason():
    result = equivalent(Atom("P", [Constant("alpha")]), Atom("P", [Constant("alpha")]), method="exact")
    assert result.equivalent is True and result.reason is None
    assert EquivalenceResult(equivalent=None, method_used="exact").reason is None


def test_the_api_surface_carries_it():
    assert api.equivalent(*CLASH, method="solver").reason is not None
