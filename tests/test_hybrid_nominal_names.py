"""A nominal's world constant ``nom_<name>`` is never the constant of a user symbol.

The standard translation turns a nominal ``i`` into the world constant ``nom_i``. A user symbol
that carries that name would be the same constant in the first-order image, whatever kind of
node it is, so the translation refuses the clash by name (the parser cannot build such a name,
so only hand-built syntax trees reach it).

``@a b → (Q(nom_a:S) ↔ Q(nom_b:S))`` is NOT valid. Countermodel (hybrid semantics, where a
ground atom is an independent proposition): one world 0; the nominals ``a`` and ``b`` both
name it, so ``@a b`` holds; ``Q(nom_a:S)`` is true and ``Q(nom_b:S)`` false there; ``S(nom_a)``
and ``S(nom_b)`` are true at 0. The antecedent holds and the consequent fails. The image would
make the user constants ``nom_a`` and ``nom_b`` the world constants of the nominals, so ``@a b``
would force ``nom_a = nom_b`` and the equivalence would follow: a wrong ``valid``.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.fol.modal_translation import hybrid_is_valid, standard_translation
from unicode_logic_kit.fol.nodes import (
    At, Atom, Constant, Function, Iff, Implies, Nominal, SortedConstant,
)


def Q(term):
    return Atom("Q", [term])


def antecedent():
    return At("a", Nominal("b"))


def sorted_clash():
    return Implies(antecedent(), Iff(Q(SortedConstant("nom_a", "S")),
                                     Q(SortedConstant("nom_b", "S"))))


def plain_clash():
    return Implies(antecedent(), Iff(Q(Constant("nom_a")), Q(Constant("nom_b"))))


@pytest.mark.parametrize("make", [sorted_clash, plain_clash],
                         ids=["sorted-constant", "plain-constant"])
def test_a_user_constant_named_like_a_world_constant_is_refused_by_name(make):
    with pytest.raises(ValueError, match="collide with the reserved world constant"):
        standard_translation(make())
    with pytest.raises(ValueError, match="collide with the reserved world constant"):
        hybrid_is_valid(make())


def test_the_refusal_names_the_symbols_and_the_nominals():
    with pytest.raises(ValueError) as caught:
        standard_translation(sorted_clash())
    message = str(caught.value)
    assert "nom_a" in message and "nom_b" in message


def test_api_prove_does_not_prove_the_non_valid_formula():
    verdict = api.prove(sorted_clash(), [], backends=["hybrid"], logic="hybrid", timeout=8000)
    assert verdict.status == "unknown"
    assert "collide" in verdict.detail


def test_a_function_symbol_of_that_name_is_refused_too():
    clash = Implies(antecedent(), Iff(Q(Function("nom_a", [])), Q(Function("nom_b", []))))
    with pytest.raises(ValueError, match="collide with the reserved world constant"):
        standard_translation(clash)


def test_a_sorted_constant_that_does_not_clash_gives_the_hand_derived_answer():
    # the same formula with sorted constants alpha and beta: not valid, the countermodel above
    free = Implies(antecedent(), Iff(Q(SortedConstant("alpha", "S")),
                                     Q(SortedConstant("beta", "S"))))
    assert hybrid_is_valid(free) is False
    # nom_a is no clash when the only nominals are b and c: their world constants are nom_b, nom_c
    standard_translation(Implies(At("b", Nominal("c")), Q(SortedConstant("nom_a", "S"))))


def test_a_nominal_alone_is_no_clash_with_a_constant_of_its_own_name():
    # the nominal a has the world constant nom_a; a constant spelled a is a different symbol
    standard_translation(Implies(At("a", Nominal("b")), Q(Constant("a"))))
    standard_translation(Implies(At("a", Nominal("b")), Q(SortedConstant("a", "S"))))
