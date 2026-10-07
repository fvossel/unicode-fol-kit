"""``$true`` / ``$false`` mean true and false on every route that evaluates a formula.

The TPTP reader produces TPTP's defined propositions as the nullary atoms
``Atom("$true")`` / ``Atom("$false")``. ``to_z3`` and the TPTP writers read them
as the truth constants; the finite model finder, the Tarski evaluator, the model
evaluator and the arithmetic route used to read them as free propositional
letters, so ``find_countermodel([P(a)], $true)`` returned a "countermodel" of a
formula that cannot be false. Two routes, one question, two answers.

Each expectation is the truth table of the constant, nothing more:
``$true`` holds in every structure, ``$false`` in none.
"""
import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.z3_arith import is_valid_arith
from unicode_logic_kit.fol.nodes import Atom, Constant, Implies, Not
from unicode_logic_kit.semantics import modelfinder
from unicode_logic_kit.semantics.model_eval import evaluate
from unicode_logic_kit.semantics.tarski import satisfies

TRUE, FALSE = Atom("$true", ()), Atom("$false", ())
P_A = Atom("P", (Constant("a"),))
RAIN = Atom("Rain", ())            # the control: an ordinary proposition


def _z3(goal, premises=()):
    status = api.prove(goal, list(premises), backends=["z3"], timeout=30000).status
    assert status in ("proved", "refuted"), status
    return status


def test_the_model_finder_cannot_falsify_true_or_satisfy_false():
    # $true holds everywhere, so nothing is a countermodel of  P(a) ⊢ $true.
    assert modelfinder.find_countermodel([P_A], TRUE, max_size=2) is None
    assert modelfinder.is_valid_finite(TRUE, max_size=2) is True
    # $false holds nowhere: it has no model, so  $false ⊢ P(a)  has no countermodel
    # either (ex falso), and $false is not valid.
    assert modelfinder.find_model([FALSE], max_size=2) is None
    assert modelfinder.find_countermodel([FALSE], P_A, max_size=2) is None
    assert modelfinder.is_valid_finite(FALSE, max_size=2) is False
    # P(a) ⊬ $false: any structure in which P(a) holds is a countermodel.
    assert modelfinder.find_countermodel([P_A], FALSE, max_size=2) is not None
    # The control. An ordinary proposition IS the structure's to choose:
    # P(a) ⊬ Rain, with the countermodel "P(a) and no rain".
    assert modelfinder.find_countermodel([P_A], RAIN, max_size=2) is not None


def test_the_two_evaluators_give_them_their_truth_value_in_any_structure():
    # A structure in which P(a) holds — any one will do, the constants do not
    # depend on it.
    structure = modelfinder.find_model([P_A], max_size=2)
    assert structure is not None
    assert satisfies(TRUE, structure) is True
    assert satisfies(FALSE, structure) is False
    assert satisfies(Implies(FALSE, Not(P_A)), structure) is True      # ex falso


def test_the_model_evaluator_agrees():
    from unicode_logic_kit.semantics.structures import FiniteStructure
    structure = FiniteStructure(domain=("a",), extensions={("P", 1): frozenset({("a",)})},
                                constants={"a": "a"})
    assert evaluate(P_A, structure) is True            # the structure is what it says
    assert evaluate(TRUE, structure) is True
    assert evaluate(FALSE, structure) is False


@pytest.mark.parametrize("formula, valid", [
    (TRUE, True),                       # the constant true
    (FALSE, False),                     # the constant false
    (Implies(FALSE, P_A), True),        # ex falso quodlibet
    (Implies(P_A, TRUE), True),         # anything implies true
    (Not(FALSE), True),
    (Implies(TRUE, P_A), False),        # P(a) is not valid
])
def test_the_arithmetic_route_and_z3_agree(formula, valid):
    assert is_valid_arith(formula) is valid
    assert _z3(formula) == ("proved" if valid else "refuted")


def test_the_finite_domain_route_does_not_invent_a_countermodel_of_true():
    # The clingo / MiniZinc encoding has no truth constant: it would ground
    # `$true` as a relation the solver may choose, and hand back a "countermodel"
    # in which true is false. It refuses the atom by name instead, so the verdict
    # is "unknown" (unsupported) — never "refuted" — and api.prove moves on.
    from unicode_logic_kit.atp.finite_domain import fragment_check
    for constant in (TRUE, FALSE):
        reason = fragment_check([constant])
        assert reason is not None and constant.predicate in reason
        assert fragment_check([Implies(P_A, constant)]) is not None      # found at any depth
    assert fragment_check([P_A]) is None                                 # the control
    assert fragment_check([RAIN]) is None                                # an ordinary proposition
    pytest.importorskip("clingo")
    assert api.prove(TRUE, [], backends=["clingo"]).status == "unknown"
    assert api.prove(P_A, [FALSE], backends=["clingo"]).status == "unknown"
    # and the public countermodel search agrees with the model finder above
    assert api.countermodel(TRUE).found is False
