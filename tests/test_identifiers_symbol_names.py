"""``fol._identifiers.symbol_names``: every name a formula carries, of every kind.

A name minted for a target (a Skolem constant, a solver's tracking literal, a witness in
SMT-LIB or Prover9 text) can meet any symbol of the problem there, not only a variable, so its
avoid set has to hold all of them. The expected sets below are read off the formulas by hand.
"""

from unicode_logic_kit.fol._identifiers import symbol_names, variable_names
from unicode_logic_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Function, Not, Quantifier, Variable

X = Variable("x")


def test_predicates_functions_constants_and_variables_are_all_names():
    formula = Quantifier("∀", X, Atom("P", [X, Function("f", [Constant("carl")])]))
    assert {"P", "f", "carl", "x"} <= symbol_names(formula)


def test_a_proposition_and_a_constant_named_like_generated_names_are_seen():
    # the names a generator would otherwise mint without looking
    formula = And(Atom("goal", []), Atom("Q", [Constant("_sk0"), Constant("x0")]))
    assert {"goal", "Q", "_sk0", "x0"} <= symbol_names(formula)


def test_the_sort_of_a_sorted_node_is_a_name():
    formula = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X, SortedConstant("socrates", "Greek")]))
    assert {"Human", "Greek", "Mortal", "socrates", "x"} <= symbol_names(formula)


def test_names_are_collected_across_all_the_formulas_given():
    assert {"P", "alpha", "Q", "beta"} <= symbol_names(Atom("P", [Constant("alpha")]), Not(Atom("Q", [Constant("beta")])))
    assert symbol_names() == frozenset()


def test_fold_gives_the_form_a_case_folding_target_compares():
    formula = Atom("P", [Variable("X0"), Constant("Gaseous")])
    folded = symbol_names(formula, fold=str.casefold)
    assert {"p", "x0", "gaseous"} <= folded
    assert "X0" not in folded and "Gaseous" not in folded


def test_every_variable_name_is_among_the_symbol_names():
    formula = Quantifier("∃", Variable("y"), Atom("R", [X, Variable("y"), Constant("carl")]))
    assert variable_names(formula) <= symbol_names(formula)
    assert "carl" in symbol_names(formula) and "carl" not in variable_names(formula)
