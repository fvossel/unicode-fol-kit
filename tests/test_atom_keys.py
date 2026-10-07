"""The key of an atom on a route that names a letter by the text its atom prints as.

Hand-derived expectations: two atoms that are one atom (equal nodes, or equal once a sorted
constant ``c:S`` is read as the constant ``c``) have ONE key, and two atoms that are different
but print alike are refused by name, because a route that keyed them by text would read them
as one letter and answer about another problem.
"""

import pytest

from unicode_logic_kit.fol._atom_keys import (
    AtomKeys, agent_key, atom_key, plain_atom, refuse_alike_agents, refuse_sorted_constant)
from unicode_logic_kit.fol._msfl_nodes import SortedConstant
from unicode_logic_kit.fol.nodes import (
    Atom, Believes, CommonKnowledge, Constant, Function, Implies, Knows, Number, Variable)


def P(*terms):
    return Atom("P", list(terms))


# ---------------------------------------------------------------------------
# One atom, one key
# ---------------------------------------------------------------------------

def test_a_plain_atom_is_keyed_by_the_text_it_prints_as():
    assert atom_key(P(Constant("a"), Number(2))) == "P(a, 2)"
    assert atom_key(Atom("Q", [])) == "Q"


def test_a_sorted_constant_has_the_key_of_the_plain_constant():
    # c:S is the constant c, so Mortal(carl:Human) and Mortal(carl) are one letter.
    sorted_atom = Atom("Mortal", [SortedConstant("carl", "Human")])
    plain = Atom("Mortal", [Constant("carl")])
    assert atom_key(sorted_atom) == atom_key(plain) == "Mortal(carl)"
    assert plain_atom(sorted_atom) == plain


def test_a_sorted_constant_inside_a_function_term_is_read_as_the_plain_constant():
    nested = P(Function("f", [SortedConstant("a", "S")]))
    assert atom_key(nested) == "P(f(a))"


def test_numerals_of_one_value_are_one_atom():
    keys = AtomKeys("route")
    assert keys.key(P(Number(1))) == keys.key(P(Number(1.0))) == "P(1)"


def test_the_same_atom_may_be_keyed_again():
    keys = AtomKeys("route")
    assert keys.key(P(Constant("a"))) == keys.key(P(Constant("a")))


def test_a_sorted_and_a_plain_constant_are_one_atom_for_the_registry():
    keys = AtomKeys("route")
    assert keys.key(P(SortedConstant("c", "S"))) == keys.key(P(Constant("c"))) == "P(c)"


def test_letters_lists_each_key_once_in_first_seen_order_and_skips_the_truth_constants():
    formula = Implies(P(Constant("b")), Implies(Atom("$true", ()), Implies(P(Constant("a")), P(Constant("b")))))
    assert AtomKeys("route").letters([formula]) == ["P(b)", "P(a)"]


# ---------------------------------------------------------------------------
# Two atoms that print alike
# ---------------------------------------------------------------------------

def test_the_numeral_one_and_a_constant_named_one_are_refused():
    # Countermodel of P(1) |- P('1') if they were two symbols: P true of the numeral, false of the constant.
    keys = AtomKeys("the route")
    keys.key(P(Number(1)))
    with pytest.raises(NotImplementedError) as info:
        keys.key(P(Constant("1")))
    message = str(info.value)
    assert message.startswith("the route:")
    assert "'P(1)'" in message and "numeral 1" in message and "constant named '1'" in message


def test_a_free_variable_and_a_constant_of_one_name_are_refused():
    keys = AtomKeys("the route")
    keys.key(P(Constant("x")))
    with pytest.raises(NotImplementedError, match="free variable is a parameter"):
        keys.key(P(Variable("x")))


def test_a_constant_that_is_written_like_a_compound_term_is_refused():
    keys = AtomKeys("the route")
    keys.key(P(Function("f", [Constant("a")])))
    with pytest.raises(NotImplementedError, match="different terms with one written form"):
        keys.key(P(Constant("f(a)")))


def test_the_difference_is_found_inside_nested_terms():
    keys = AtomKeys("the route")
    keys.key(P(Function("g", [Number(2)])))
    with pytest.raises(NotImplementedError) as info:
        keys.key(P(Function("g", [Constant("2")])))
    # the refusal names the terms that differ, not the whole atoms
    assert "Number(value=2)" in str(info.value) and "Constant(name='2')" in str(info.value)


def test_atoms_that_print_differently_never_clash():
    keys = AtomKeys("the route")
    for term in (Number(1), Constant("a"), Variable("x"), Number(2), Constant("two")):
        keys.key(P(term))
    assert keys.letters([P(Number(1)), P(Number(2))]) == ["P(1)", "P(2)"]


def test_the_exception_class_of_a_refusal_is_the_callers():
    keys = AtomKeys("the route", "read", ValueError)
    keys.key(P(Number(1)))
    with pytest.raises(ValueError, match="numeral 1"):
        keys.key(P(Constant("1")))


# ---------------------------------------------------------------------------
# A route that has no reading of a sorted constant
# ---------------------------------------------------------------------------

def test_a_route_that_refuses_sorted_constants_names_the_constant_and_its_sort():
    keys = AtomKeys("the route", sorted_constants="refuse")
    with pytest.raises(NotImplementedError) as info:
        keys.key(Atom("Mortal", [SortedConstant("carl", "Human")]))
    message = str(info.value)
    assert "carl:Human" in message and "the route:" in message and "Human(carl)" in message
    # an atom without a sorted constant is unaffected
    assert keys.key(Atom("Mortal", [Constant("carl")])) == "Mortal(carl)"


def test_refuse_sorted_constant_finds_a_constant_in_a_nested_term():
    with pytest.raises(NotImplementedError, match="c:S"):
        refuse_sorted_constant(P(Function("f", [SortedConstant("c", "S")])), "the route")
    refuse_sorted_constant(P(Function("f", [Constant("c")])), "the route")


def test_an_unknown_reading_of_sorted_constants_is_refused():
    with pytest.raises(ValueError):
        AtomKeys("route", sorted_constants="guess")


# ---------------------------------------------------------------------------
# The relation an agent's operator reads
# ---------------------------------------------------------------------------

def test_the_key_of_an_agent_is_its_name_or_its_written_form():
    assert agent_key(Constant("alice")) == "alice"
    assert agent_key(Variable("x")) == "x"
    assert agent_key(Number(1)) == "1"


def test_one_agent_met_twice_and_a_sorted_agent_are_not_a_pair():
    p = Atom("P", [])
    refuse_alike_agents([Implies(Knows(Constant("a"), p), Believes(Constant("a"), p))], "route")
    refuse_alike_agents([Knows(SortedConstant("a", "S"), p), Knows(Constant("a"), p)], "route")


def test_a_group_operator_names_every_member_and_a_clash_with_a_member_is_refused():
    p = Atom("P", [])
    group = CommonKnowledge([Constant("a"), Number(1)], p)
    with pytest.raises(NotImplementedError, match="two different agents are both named '1'"):
        refuse_alike_agents([group, Knows(Constant("1"), p)], "route")
    refuse_alike_agents([group, Knows(Constant("a"), p)], "route")


def test_the_refusal_of_two_agents_names_the_route_and_both_terms():
    p = Atom("P", [])
    with pytest.raises(NotImplementedError) as info:
        refuse_alike_agents([Knows(Variable("x"), p), Knows(Constant("x"), p)], "the route")
    message = str(info.value)
    assert message.startswith("the route:") and "Variable(name='x')" in message
    assert "Constant(name='x')" in message and "free variable is a parameter" in message
