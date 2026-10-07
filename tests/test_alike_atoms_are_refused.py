"""A route that names a letter by the text its atom prints as does not read two atoms as one.

``P(1)`` and ``P('1')`` (the TPTP reader makes the pair from ``p(1)`` and ``p('1')``) are two
atoms: the numeral ``1`` and a constant named ``1`` are two symbols, so ``P(1) ⊢ P('1')`` has
the countermodel "P is true of the numeral and false of the constant" and is NOT valid. In the
same way ``P(c) → P(x)`` with ``c = Constant('x')`` and a free variable ``x`` (a parameter, one
unknown element, which is not the constant of its name) is NOT valid: universe {0, 1}, the
constant ``x`` is 0, the parameter ``x`` is 1, P = {0}.

A route that keys a letter by text cannot hold the two apart: read as one letter ``p``,
``P(1) ⊢ P('1')`` would be 'proved' and ``is_tautology(P(1) → P('1'))`` True. Each such route
refuses the pair by name; none answers valid, proved or True.
"""

from fractions import Fraction

import pytest

from unicode_logic_kit import MSFLParser, api
from unicode_logic_kit.atp.lj import int_decide, int_prove
from unicode_logic_kit.atp.ltl_tableau import LTLTrace, ltl_decide, ltl_trace_satisfies
from unicode_logic_kit.atp.tableau import tableau_model
from unicode_logic_kit.atp.z3_fuzzy import fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid
from unicode_logic_kit.fol.nodes import (
    And, Always, Atom, Constant, Function, Implies, LukImplication, Not, Number, Variable)
from unicode_logic_kit.fol.tptp_input import parse_tptp
from unicode_logic_kit.hol.isabelle_conditional import to_isabelle_conditional, to_thf_conditional
from unicode_logic_kit.fol.nodes import Would
from unicode_logic_kit.hol.manyvalued import to_isabelle_k3lp, to_isabelle_matrix, to_thf_k3lp
from unicode_logic_kit.prob import ProbConstraint, ProbFact, ProbProgram, entailment_bounds, query
from unicode_logic_kit.semantics import manyvalued as mv
from unicode_logic_kit.semantics import matrix as mx
from unicode_logic_kit.semantics.conditional import cf_countermodel, cf_valid
from unicode_logic_kit.semantics.fuzzy import evaluate as fuzzy_evaluate
from unicode_logic_kit.semantics.intuitionistic import int_countermodel, int_valid
from unicode_logic_kit.semantics.truthtable import (
    is_contradiction, is_satisfiable_tt, is_tautology, truth_table)


def P(term):
    return Atom("P", [term])


#: Two terms that print alike, and one reading of what they are.
PAIRS = {
    "numeral and constant": (Number(1), Constant("1")),
    "free variable and constant": (Variable("x"), Constant("x")),
    "compound term and constant": (Function("f", [Constant("a")]), Constant("f(a)")),
}
pairs = pytest.mark.parametrize("left, right", list(PAIRS.values()), ids=list(PAIRS))


def refused(call):
    """The call ends in a refusal by name and the text of the refusal is returned.

    A route says what it refuses with the exception class its callers already handle:
    ``NotImplementedError`` for a decider, ``ValueError`` for the probabilistic routes, and
    ``TypeError`` for the free variable that the sphere semantics refuses on its own.
    """
    with pytest.raises((NotImplementedError, TypeError, ValueError)) as info:
        call()
    return str(info.value)


# One lambda per route and per question it answers. Each is handed the two terms.
ROUTES = {
    "truth_table": lambda a, b: truth_table(Implies(P(a), P(b))),
    "is_tautology": lambda a, b: is_tautology(Implies(P(a), P(b))),
    "is_contradiction": lambda a, b: is_contradiction(And(P(a), Not(P(b)))),
    "is_satisfiable_tt": lambda a, b: is_satisfiable_tt(And(P(a), Not(P(b)))),
    "manyvalued.is_valid": lambda a, b: mv.is_valid(Implies(P(a), P(b)), "LP"),
    "manyvalued.is_satisfiable": lambda a, b: mv.is_satisfiable(And(P(a), Not(P(b))), "K3"),
    "manyvalued.entails": lambda a, b: mv.entails([P(a)], P(b), "K3"),
    "manyvalued.kleene_value": lambda a, b: mv.kleene_value(Implies(P(a), P(b)), {"P(1)": 1.0, "P(x)": 1.0, "P(f(a))": 1.0}),
    "matrix_is_valid": lambda a, b: mx.matrix_is_valid(Implies(P(a), P(b)), mx.LP_MATRIX),
    "matrix_is_satisfiable": lambda a, b: mx.matrix_is_satisfiable(And(P(a), Not(P(b))), mx.FDE_MATRIX),
    "matrix_entails": lambda a, b: mx.matrix_entails([P(a)], P(b), mx.K3_MATRIX),
    "matrix_value": lambda a, b: mx.matrix_value(Implies(P(a), P(b)), {"P(1)": 1.0, "P(x)": 1.0, "P(f(a))": 1.0}, mx.K3_MATRIX),
    "fuzzy.evaluate": lambda a, b: fuzzy_evaluate(LukImplication(P(a), P(b)), {"P(1)": 1.0, "P(x)": 1.0, "P(f(a))": 1.0}),
    "fuzzy_is_valid": lambda a, b: fuzzy_is_valid(LukImplication(P(a), P(b))),
    "fuzzy_is_satisfiable": lambda a, b: fuzzy_is_satisfiable(LukImplication(P(a), P(b)), threshold=0.5),
    "fuzzy_get_model": lambda a, b: fuzzy_get_model(LukImplication(P(a), P(b))),
    "cf_valid": lambda a, b: cf_valid(Implies(P(a), P(b))),
    "cf_countermodel": lambda a, b: cf_countermodel(Implies(P(a), P(b))),
    "int_valid": lambda a, b: int_valid(Implies(P(a), P(b))),
    "int_countermodel": lambda a, b: int_countermodel(Implies(P(a), P(b))),
    "int_prove": lambda a, b: int_prove([P(a)], P(b)),
    "int_decide": lambda a, b: int_decide(Implies(P(a), P(b))),
    "ltl_trace_satisfies": lambda a, b: ltl_trace_satisfies(
        Implies(P(a), P(b)), LTLTrace((frozenset(),), (frozenset({"P(1)", "P(x)", "P(f(a))"}),))),
    # an open branch that holds P(a) and ¬P(b): one entry of the assignment for two atoms
    "tableau_model": lambda a, b: tableau_model([P(a), Not(P(b))]),
    "to_thf_k3lp": lambda a, b: to_thf_k3lp(Implies(P(a), P(b)), "LP"),
    "to_isabelle_k3lp": lambda a, b: to_isabelle_k3lp(Implies(P(a), P(b)), "LP"),
    "to_isabelle_matrix": lambda a, b: to_isabelle_matrix(Implies(P(a), P(b)), mx.FDE_MATRIX),
    "to_isabelle_conditional": lambda a, b: to_isabelle_conditional(Would(P(a), P(b))),
    "to_thf_conditional": lambda a, b: to_thf_conditional(Would(P(a), P(b))),
    "entailment_bounds": lambda a, b: entailment_bounds(
        [ProbConstraint.exact(P(a), Fraction(7, 10))], P(b)),
    "entailment_bounds, column generation": lambda a, b: entailment_bounds(
        [ProbConstraint.exact(P(a), Fraction(7, 10))], P(b), strategy="column_generation"),
    "prob query": lambda a, b: query(ProbProgram(facts=[ProbFact(P(Constant("n")), Fraction(1, 2))],
                                                 rules=[], hard_facts=[P(a)]), P(b)),
}


@pytest.mark.parametrize("route", list(ROUTES))
@pairs
def test_a_route_refuses_two_atoms_that_print_alike(route, left, right):
    # The probabilistic fact of a program is a ground atom: a variable is refused by the program itself.
    if route == "prob query" and isinstance(left, Variable):
        pytest.skip("a probabilistic program holds ground atoms only")
    message = refused(lambda: ROUTES[route](left, right))
    # either the atoms that print alike are named, or (the sphere semantics, which has always
    # refused an atom with a free variable) the free variable is
    assert "are both written" in message or "free variable" in message


@pytest.mark.parametrize("route", list(ROUTES))
def test_the_refusal_of_a_numeral_and_a_constant_names_both_and_says_why(route):
    message = refused(lambda: ROUTES[route](Number(1), Constant("1")))
    assert "numeral 1" in message and "constant named '1'" in message


# ---------------------------------------------------------------------------
# The documented pair, through the readers and through api.prove
# ---------------------------------------------------------------------------

def test_the_tptp_pair_is_not_proved_by_the_intuitionistic_backend():
    formulas = parse_tptp("fof(a, axiom, p(1)).\nfof(c, conjecture, p('1')).\n")
    premise, goal = formulas[0].formula, formulas[1].formula
    assert premise == Atom("P", [Number(1)]) and goal == Atom("P", [Constant("1")])
    verdict = api.prove(goal, [premise], backends=["intuitionistic"], logic="intuitionistic",
                        timeout=5000)
    assert verdict.status == "unknown"
    assert "numeral 1" in verdict.detail and "constant named '1'" in verdict.detail
    assert int_valid(Implies(Atom("P", [Number(1)]), Atom("P", [Number(1.0)])))


def test_a_constant_and_a_variable_of_one_name_are_not_proved_by_the_intuitionistic_backend():
    constant, variable = Constant("x"), Variable("x")
    verdict = api.prove(P(variable), [P(constant)], backends=["intuitionistic"],
                        logic="intuitionistic", timeout=5000)
    assert verdict.status == "unknown"
    assert "free variable is a parameter" in verdict.detail


def test_the_chain_for_the_intuitionistic_logic_does_not_prove_the_pair_either():
    verdict = api.prove(P(Constant("1")), [P(Number(1))], logic="intuitionistic", timeout=5000)
    assert verdict.status != "proved"


def test_a_modal_decider_that_keeps_atoms_as_nodes_never_calls_the_pair_valid():
    # □-free here: the linear-time tableau keeps the two atoms apart as nodes, finds the model
    # "P(1) true, P('1') false" and cannot write it down as a trace of keys: it says 'unknown',
    # never 'valid'.
    verdict = ltl_decide(Implies(Always(P(Number(1))), Always(P(Constant("1")))))
    assert verdict != "valid"


# ---------------------------------------------------------------------------
# Where a domain makes a constant of a quantified formula
# ---------------------------------------------------------------------------

def test_a_domain_element_named_like_a_numeral_meets_the_numeral():
    formula = MSFLParser().parse("∀x P(x) → P(1)")
    # over the single element '1' the quantifier's instance is P('1'), the constant: not the numeral
    with pytest.raises(NotImplementedError, match="numeral 1"):
        mv.is_valid(formula, "LP", domain={"1"})
    # over the element a, the instance is P(a); P(a) → P(1) fails when P(a) is true and P(1) false
    assert mv.is_valid(formula, "LP", domain={"a"}) is False


# ---------------------------------------------------------------------------
# Atoms that do not print alike are decided as before
# ---------------------------------------------------------------------------

def test_one_numeral_with_two_spellings_is_one_atom():
    assert is_tautology(Implies(P(Number(1)), P(Number(1.0))))
    assert int_prove([P(Number(1))], P(Number(1.0))) is True
    assert mv.entails([P(Number(1))], P(Number(1.0)), "K3") is True


def test_two_numerals_of_different_value_are_two_atoms():
    assert is_tautology(Implies(P(Number(1)), P(Number(2)))) is False
    assert int_prove([P(Number(1))], P(Number(2))) is False
    assert cf_valid(Implies(P(Number(1)), P(Number(2)))) is False


def test_a_numeral_next_to_a_constant_of_another_spelling_is_decided():
    assert int_prove([P(Number(1))], P(Constant("one"))) is False
    assert int_prove([P(Constant("one"))], P(Constant("one"))) is True


def test_a_free_variable_alone_is_one_parameter():
    # P(x) ⊢ P(x) is valid; P(x) ⊢ P(alpha) is not (universe {0, 1}, x = 1, alpha = 0, P = {1});
    # ⊢ P(x) → P(alpha) is not valid.
    x, alpha = Variable("x"), Constant("alpha")
    assert int_prove([P(x)], P(x)) is True
    assert int_prove([P(x)], P(alpha)) is False
    assert int_valid(Implies(P(x), P(alpha))) is False
    assert is_tautology(Implies(P(x), P(x))) is True
    assert is_tautology(Implies(P(x), P(alpha))) is False
    assert mx.matrix_is_valid(Implies(P(x), P(x)), mx.LP_MATRIX) is True


def test_the_probability_of_a_numeral_is_not_the_probability_of_a_constant_of_another_name():
    constraints = [ProbConstraint.exact(P(Number(1)), Fraction(7, 10))]
    # P(2) is independent of P(1): anything in [0, 1]
    bounds = entailment_bounds(constraints, P(Number(2)))
    assert (bounds.lower, bounds.upper) == (Fraction(0), Fraction(1))
    # P(1.0) is P(1)
    bounds = entailment_bounds(constraints, P(Number(1.0)))
    assert (bounds.lower, bounds.upper) == (Fraction(7, 10), Fraction(7, 10))


def test_a_probabilistic_program_with_a_numeral_fact_is_queried_per_atom():
    program = ProbProgram(facts=[ProbFact(P(Number(1)), Fraction(7, 10))], rules=[])
    assert query(program, P(Number(1))) == Fraction(7, 10)
    assert query(program, P(Number(1.0))) == Fraction(7, 10)
    assert query(program, P(Constant("two"))) == Fraction(0)
