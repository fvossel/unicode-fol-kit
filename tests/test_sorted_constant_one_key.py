"""A sorted constant ``c:S`` is the constant ``c``: one atom, one key, on the routes that name a letter by text.

The fuzzy route grounds ``∀x:Person Tall(x)`` over ``Person = {alice}`` to the atom ``Tall(alice)``;
``Tall(alice:Person)`` is that very atom, so
``(∀x:Person Tall(x)) → Tall(alice:Person)`` is ``Tall(alice) → Tall(alice)`` and has degree 1
under every valuation. The linear-time trace evaluator reads the trace of a countermodel, which
holds the plain key ``Mortal(carl)``, so ``Mortal(carl:Human)`` is true exactly where it is.
The many-valued routes (K3, LP, FDE, the truth table, the counterfactual search) have no
statement of what membership of a sort is worth in their truth values, and refuse the sorted
constant by name instead of reading ``Human(alice)`` as unrelated to ``alice:Human``.
"""

import pytest

from unicode_logic_kit import MSFLParser, fuzzy_evaluate, fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid
from unicode_logic_kit.atp.ltl_tableau import LTLTrace, ltl_countermodel, ltl_trace_satisfies
from unicode_logic_kit.fol._msfl_nodes import SortedConstant
from unicode_logic_kit.fol.nodes import Atom, Constant, Implies, LukNegation, StrongConjunction
from unicode_logic_kit.semantics import manyvalued as mv
from unicode_logic_kit.semantics import matrix as mx
from unicode_logic_kit.semantics.conditional import cf_countermodel, cf_valid
from unicode_logic_kit.semantics.truthtable import is_tautology, truth_table

PERSON = {"Person": {"alice"}}


def tall(term):
    return Atom("Tall", [term])


def alice_person():
    return SortedConstant("alice", "Person")


# ---------------------------------------------------------------------------
# Fuzzy
# ---------------------------------------------------------------------------

def test_a_quantifier_over_a_sort_and_a_sorted_constant_are_one_atom_in_the_decider():
    ms = MSFLParser(many_sorted=True, fuzzy=True)
    formula = ms.parse("(∀x:Person Tall(x)) → Tall(alice:Person)")
    assert fuzzy_is_valid(formula, sort_universes=PERSON) is True
    assert fuzzy_is_valid(formula, sort_universes=PERSON, tnorm="godel") is True


def test_the_model_of_a_fuzzy_formula_holds_one_key_for_the_atom():
    ms = MSFLParser(many_sorted=True, fuzzy=True)
    formula = ms.parse("(∀x:Person Tall(x)) → Tall(alice:Person)")
    model = fuzzy_get_model(formula, threshold=0.0, sort_universes=PERSON)
    assert sorted(model) == ["Tall(alice)", "degree"]


def test_the_fuzzy_evaluator_reads_a_sorted_constant_at_the_plain_key():
    ms = MSFLParser(many_sorted=True, fuzzy=True)
    formula = ms.parse("(∀x:Person Tall(x)) → Tall(alice:Person)")
    # the instance is Tall(alice) → Tall(alice): min(1, 1 - 0.2 + 0.2) = 1 whatever the degree is
    assert fuzzy_evaluate(formula, {"Tall(alice)": 0.2}, sort_universes=PERSON) == 1.0
    assert fuzzy_evaluate(formula, {"Tall(alice)": 0.9}, sort_universes=PERSON) == 1.0
    assert fuzzy_evaluate(ms.parse("Tall(alice:Person)"), {"Tall(alice)": 0.7}) == 0.7
    # the key with the sort is no key
    with pytest.raises(KeyError):
        fuzzy_evaluate(ms.parse("Tall(alice:Person)"), {"Tall(alice:Person)": 0.7})


def test_a_sorted_and_a_plain_occurrence_of_a_constant_are_one_variable_of_the_decider():
    # t ⊗ ¬t = max(0, t + (1 - t) - 1) = 0 for every degree t of the ONE atom, so no valuation
    # reaches 0.5. Read as two atoms (t1 ⊗ ¬t2) the degree 1 is reached at t1 = 1, t2 = 0.
    contradiction = StrongConjunction(tall(alice_person()), LukNegation(tall(Constant("alice"))))
    assert fuzzy_is_satisfiable(contradiction, threshold=0.5) is False
    other = StrongConjunction(tall(alice_person()), LukNegation(tall(Constant("bob"))))
    assert fuzzy_is_satisfiable(other, threshold=0.5) is True


# ---------------------------------------------------------------------------
# Linear time
# ---------------------------------------------------------------------------

def _trace(*keys):
    return LTLTrace((frozenset(keys),), (frozenset(keys),))


def test_a_sorted_constant_is_read_at_the_key_of_the_plain_constant_on_a_trace():
    sp = MSFLParser(modal=True, many_sorted=True)
    assert ltl_trace_satisfies(sp.parse("Mortal(carl:Human)"), _trace("Mortal(carl)")) is True
    assert ltl_trace_satisfies(sp.parse("Mortal(carl:Human)"), _trace("Human(carl)")) is False


def test_a_trace_that_refutes_a_sorted_formula_is_one_for_the_evaluator():
    # Human(carl) true and Mortal(carl) false: Human(carl:Human) → Mortal(carl:Human) fails there
    sp = MSFLParser(modal=True, many_sorted=True)
    formula = sp.parse("Human(carl:Human) → Mortal(carl:Human)")
    assert ltl_trace_satisfies(formula, _trace("Human(carl)")) is False
    assert ltl_trace_satisfies(formula, _trace("Human(carl)", "Mortal(carl)")) is True


def test_the_countermodel_of_a_sorted_formula_falsifies_it_under_the_evaluator():
    sp = MSFLParser(modal=True, many_sorted=True)
    formula = sp.parse("Human(carl:Human) → Mortal(carl:Human)")
    countermodel = ltl_countermodel(formula)
    assert countermodel is not None
    assert "Mortal(carl)" not in countermodel.at(0) and "Human(carl)" in countermodel.at(0)
    assert ltl_trace_satisfies(formula, countermodel) is False


# ---------------------------------------------------------------------------
# The many-valued routes refuse a sorted constant
# ---------------------------------------------------------------------------

def _sorted_atom():
    return Atom("P", [SortedConstant("alice", "Human")])


MANY_VALUED = {
    "kleene_value": lambda f: mv.kleene_value(f, {"P(alice)": 1.0, "P(alice:Human)": 1.0}),
    "is_valid": lambda f: mv.is_valid(f, "LP"),
    "is_satisfiable": lambda f: mv.is_satisfiable(f, "K3"),
    "entails": lambda f: mv.entails([f], f, "LP"),
    "matrix_value": lambda f: mx.matrix_value(f, {"P(alice)": 1.0, "P(alice:Human)": 1.0}, mx.K3_MATRIX),
    "matrix_is_valid": lambda f: mx.matrix_is_valid(f, mx.LP_MATRIX),
    "matrix_is_satisfiable": lambda f: mx.matrix_is_satisfiable(f, mx.FDE_MATRIX),
    "matrix_entails": lambda f: mx.matrix_entails([f], f, mx.K3_MATRIX),
    "truth_table": lambda f: truth_table(f),
    "is_tautology": lambda f: is_tautology(f),
    "cf_valid": lambda f: cf_valid(f),
    "cf_countermodel": lambda f: cf_countermodel(f),
}


@pytest.mark.parametrize("route", list(MANY_VALUED))
def test_a_many_valued_route_refuses_a_sorted_constant_by_name(route):
    # P(alice:Human) → Human(alice) is valid by the definition of a sorted constant (alice lies
    # in Human), but the three truth values have no statement of that, so no verdict is given:
    # an answer of False would read Human(alice) as unrelated to alice:Human.
    formula = Implies(_sorted_atom(), Atom("Human", [Constant("alice")]))
    with pytest.raises(NotImplementedError) as info:
        MANY_VALUED[route](formula)
    message = str(info.value)
    assert "alice:Human" in message and "no reading here" in message


def test_the_sorted_quantifier_is_still_refused_and_the_plain_atom_is_still_read():
    cl = MSFLParser(many_sorted=True)
    with pytest.raises(NotImplementedError):
        mv.is_valid(cl.parse("∀x:Human P(x)"), "LP", domain={"a"})
    plain = Implies(Atom("P", [Constant("alice")]), Atom("Human", [Constant("alice")]))
    assert mv.is_valid(plain, "LP") is False       # P(alice) true, Human(alice) false: not valid
    assert mv.is_valid(Implies(Atom("Human", [Constant("alice")]), Atom("Human", [Constant("alice")])), "LP") is True
