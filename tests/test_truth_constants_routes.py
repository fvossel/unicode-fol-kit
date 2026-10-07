"""``$true`` and ``$false`` are the truth constants in every route that decides.

Six questions, each answered by hand from what the two constants mean (``$true``
holds in every interpretation, ``$false`` in none):

1. ``$false ⊢ P`` is valid: no interpretation makes the premise true, so every
   interpretation that does satisfies the conclusion, vacuously.
2. ``⊢ $true`` is valid: the goal holds everywhere.
3. ``⊢ $false`` is NOT valid: the goal holds nowhere, so any interpretation is a
   counterexample.
4. ``P ⊢ $true ∧ P`` is valid: ``$true ∧ P`` takes the value of ``P``.
5. ``⊢ ¬$false`` is valid: the negation of a constant that holds nowhere holds
   everywhere.
6. ``$true ⊢ P`` is NOT valid: ``P`` false and the premise (true everywhere) is a
   counterexample.

The same six answers are read in the classical routes, the intuitionistic ones
(falsity is forced nowhere, truth everywhere), the modal ones (the same at every
world), and the three-valued matrices (the top and the bottom value).
"""

import pytest

from unicode_logic_kit.fol.nodes import Atom, And, Not, Implies
from unicode_logic_kit.api import prove
from unicode_logic_kit.atp.protocol import _REGISTRY

TRUE = Atom("$true", ())
FALSE = Atom("$false", ())
P = Atom("P", ())

# (premises, goal, valid?)
PROBLEMS = {
    "false_entails_anything": ([FALSE], P, True),
    "true_is_valid": ([], TRUE, True),
    "false_is_not_valid": ([], FALSE, False),
    "conjoining_true": ([P], And(TRUE, P), True),
    "not_false_is_valid": ([], Not(FALSE), True),
    "true_does_not_entail": ([TRUE], P, False),
}
IDS = list(PROBLEMS)


def _implication(premises, goal):
    """``(⋀ premises) → goal``, or just ``goal`` without premises."""
    if not premises:
        return goal
    antecedent = premises[0]
    for extra in premises[1:]:
        antecedent = And(antecedent, extra)
    return Implies(antecedent, goal)


# ---------------------------------------------------------------------------
# Direct entry points that decide: answer True (valid) or False (not valid).
# ---------------------------------------------------------------------------

def _classical_truth_table(premises, goal):
    from unicode_logic_kit.semantics.truthtable import is_tautology
    return is_tautology(_implication(premises, goal), "classical")


def _z3(premises, goal):
    from unicode_logic_kit.atp.z3_models import is_valid
    return is_valid(_implication(premises, goal))


def _tableau(premises, goal):
    from unicode_logic_kit.atp.tableau import prove_tableau
    return prove_tableau(premises, goal)


def _resolution(premises, goal):
    from unicode_logic_kit.atp.resolution import prove as resolution_prove
    return resolution_prove(premises, goal)


def _fitch_search(premises, goal):
    from unicode_logic_kit.atp.fitch_search import fitch_prove
    return fitch_prove(premises, goal)


def _fitch_search_checked(premises, goal):
    """The proof the search finds must pass the independent Fitch checker."""
    from unicode_logic_kit.atp.fitch_search import find_fitch_proof
    from unicode_logic_kit.atp.fitch import verify_proof
    proof = find_fitch_proof(premises, goal)
    if proof is None:
        return False
    result = verify_proof(proof)
    assert result.ok, result.error
    return True


def _finite_model_search(premises, goal):
    from unicode_logic_kit.semantics.modelfinder import find_countermodel
    return find_countermodel(premises, goal) is None


def _second_order_finite(premises, goal):
    from unicode_logic_kit.semantics.secondorder import so_is_valid_finite
    return so_is_valid_finite(_implication(premises, goal))


def _lj_prove(premises, goal):
    from unicode_logic_kit.atp.lj import int_prove
    return int_prove(list(premises), goal)


def _lj_decide(premises, goal):
    from unicode_logic_kit.atp.lj import int_decide
    return int_decide(_implication(premises, goal))


def _kripke_intuitionistic(premises, goal):
    from unicode_logic_kit.semantics.intuitionistic import int_valid
    return int_valid(_implication(premises, goal))


def _free_logic(premises, goal):
    from unicode_logic_kit.semantics.free_logic import free_is_valid
    return free_is_valid(_implication(premises, goal))


def _conditional(premises, goal):
    from unicode_logic_kit.semantics.conditional import cf_valid
    return cf_valid(_implication(premises, goal))


def _modal_prove(premises, goal):
    from unicode_logic_kit.atp.modal_tableau import modal_prove
    return modal_prove(premises, goal)


def _modal_valid(premises, goal):
    from unicode_logic_kit.atp.modal_tableau import is_modal_valid
    return is_modal_valid(_implication(premises, goal))


def _ltl_valid(premises, goal):
    from unicode_logic_kit.atp.ltl_tableau import ltl_valid
    return ltl_valid(goal, premises)


def _k3_entails(premises, goal):
    from unicode_logic_kit.semantics.manyvalued import entails
    return entails(premises, goal, "K3")


def _lp_entails(premises, goal):
    from unicode_logic_kit.semantics.manyvalued import entails
    return entails(premises, goal, "LP")


def _k3_matrix(premises, goal):
    from unicode_logic_kit.semantics.matrix import matrix_entails, K3_MATRIX
    return matrix_entails(premises, goal, K3_MATRIX)


def _lp_matrix(premises, goal):
    from unicode_logic_kit.semantics.matrix import matrix_entails, LP_MATRIX
    return matrix_entails(premises, goal, LP_MATRIX)


def _fde_matrix(premises, goal):
    from unicode_logic_kit.semantics.matrix import matrix_entails, FDE_MATRIX
    return matrix_entails(premises, goal, FDE_MATRIX)


DIRECT_ROUTES = {
    "classical_truth_table": _classical_truth_table,
    "z3": _z3,
    "tableau": _tableau,
    "resolution": _resolution,
    "fitch_search": _fitch_search,
    "fitch_search_checked": _fitch_search_checked,
    "finite_model_search": _finite_model_search,
    "second_order_finite": _second_order_finite,
    "lj_prove": _lj_prove,
    "lj_decide": _lj_decide,
    "kripke_intuitionistic": _kripke_intuitionistic,
    "free_logic": _free_logic,
    "conditional": _conditional,
    "modal_prove": _modal_prove,
    "modal_valid": _modal_valid,
    "ltl_valid": _ltl_valid,
    "k3_entailment": _k3_entails,
    "lp_entailment": _lp_entails,
    "k3_matrix": _k3_matrix,
    "lp_matrix": _lp_matrix,
    "fde_matrix": _fde_matrix,
}


@pytest.mark.parametrize("problem", IDS)
@pytest.mark.parametrize("route", sorted(DIRECT_ROUTES))
def test_six_problems_in_every_direct_route(route, problem):
    premises, goal, valid = PROBLEMS[problem]
    assert bool(DIRECT_ROUTES[route](premises, goal)) is valid


# ---------------------------------------------------------------------------
# Routes through the backend registry. A prover that only proves must never say
# "proved" for an invalid question; a refuter that only refutes must never say
# "refuted" for a valid one; a route that decides says the right word either way.
# ---------------------------------------------------------------------------

#: backend name -> (logic, what it can say)
BACKENDS = {
    "z3": ("fol", "both"),
    "cvc5": ("fol", "both"),
    "eprover": ("fol", "both"),
    "vampire": ("fol", "both"),
    "tableau": ("fol", "proves"),
    "resolution": ("fol", "proves"),
    "prover9": ("fol", "proves"),
    "modelfinder": ("fol", "refutes"),
    "intuitionistic": ("intuitionistic", "both"),
    "modal-tableau": ("modal", "both"),
    "ltl-tableau": ("modal", "both"),
    "kripke-enum": ("modal", "refutes"),
    "qml": ("modal", "proves"),
    "hybrid": ("hybrid", "both"),
}


@pytest.mark.parametrize("problem", IDS)
@pytest.mark.parametrize("name", sorted(BACKENDS))
def test_six_problems_in_every_registered_backend(name, problem):
    backend = _REGISTRY[name]
    if not backend.available():
        pytest.skip(f"{name} is not installed here")
    logic, ability = BACKENDS[name]
    premises, goal, valid = PROBLEMS[problem]
    verdict = prove(goal, premises, backends=[name], logic=logic, timeout=20000)
    if valid:
        if ability == "refutes":
            assert verdict.status != "refuted"
        else:
            assert verdict.status == "proved"
    else:
        if ability == "proves":
            assert verdict.status != "proved"
        else:
            assert verdict.status == "refuted"
