"""``signature_axioms``: what a ``Signature`` declares, written as plain first-order sentences.

THE DEFINITION. There is ONE universe. A sort ``S`` is the non-empty extension of the unary
predicate ``S``; sorts may overlap. A constant declared with sort ``S`` is an element of ``S``,
a function declared with result sort ``S`` maps elements of its argument sorts into ``S``, and
a subsort edge ``S < T`` is ``S ⊆ T``. A predicate may hold of anything, whatever argument
sorts it was declared with.

Every expected sentence below is written down from that definition (the family it belongs to,
the variables it binds), not read off the function's output.
"""

import pytest

import unicode_logic_kit
from unicode_logic_kit import api
from unicode_logic_kit import fol as fol_package
from unicode_logic_kit.fol import _msfl_nodes, nodes as fol_nodes
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Quantifier, Variable, signature_axioms, subsort_axioms,
)
from unicode_logic_kit.fol.signature import ConstantDecl, FunctionDecl, PredicateDecl, Signature


def var(name):
    return Variable(name)


def exists(name, sort):
    """``∃x S(x)``: the sort ``S`` is not empty."""
    return Quantifier("∃", var(name), Atom(sort, [var(name)]))


def forall(names, body):
    for name in reversed(names):
        body = Quantifier("∀", var(name), body)
    return body


# ---- the four families, in order --------------------------------------------------------------

SIGNATURE = Signature.from_dict({
    "functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}},
    "constants": {"carl": "A"},
    "subsorts": {"B": ["C"]},
    "predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}},
})


def test_the_four_families_in_their_order_for_a_signature_that_has_all_of_them():
    # sorts named by the signature: A (constant, argument, predicate), B (result, subsort edge),
    # C (subsort edge): three non-emptiness sentences, sorted by name.
    # then the one subsort edge B < C; then A(carl); then the closure of f: A -> B.
    assert signature_axioms(SIGNATURE) == (
        exists("x", "A"), exists("x", "B"), exists("x", "C"),
        forall(["x"], Implies(Atom("B", [var("x")]), Atom("C", [var("x")]))),
        Atom("A", [Constant("carl")]),
        forall(["x1"], Implies(Atom("A", [var("x1")]),
                               Atom("B", [Function("f", [var("x1")])]))),
    )


def test_the_second_family_is_exactly_subsort_axioms():
    sentences = signature_axioms(SIGNATURE)
    assert sentences[3:4] == subsort_axioms(SIGNATURE)


def test_a_predicates_declared_argument_sorts_give_no_sentence():
    # P: A means P is a relation over the universe whose first argument the signature calls an A;
    # it does NOT say that whatever P holds of is an A. A signature with only that predicate
    # declares the sort A (non-empty) and nothing else.
    only_predicate = Signature.from_dict({"predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}}})
    assert signature_axioms(only_predicate) == (exists("x", "A"),)
    for sentence in signature_axioms(only_predicate):
        assert "P" not in {n.predicate for n in sentence.walk() if isinstance(n, Atom)}


def test_a_signature_without_declarations_gives_no_sentence():
    assert signature_axioms(Signature()) == ()


def test_a_declared_sort_that_nothing_uses_is_still_non_empty():
    assert signature_axioms(Signature(sorts=frozenset({"Lonely"}))) == (exists("x", "Lonely"),)


# ---- functions ---------------------------------------------------------------------------------

def test_a_function_closure_guards_exactly_the_positions_that_have_a_sort():
    # g: (A, -, B) -> C. Position 2 has no sort and contributes no guard.
    signature = Signature.from_dict({"functions": {
        "g": {"arity": 3, "arg_sorts": ["A", None, "B"], "result_sort": "C"}}})
    closure = signature_axioms(signature)[-1]
    assert closure == forall(
        ["x1", "x2", "x3"],
        Implies(And(Atom("A", [var("x1")]), Atom("B", [var("x3")])),
                Atom("C", [Function("g", [var("x1"), var("x2"), var("x3")])])))


def test_a_function_without_argument_sorts_is_closed_without_a_guard():
    signature = Signature.from_dict({"functions": {
        "m": {"arity": 2, "arg_sorts": None, "result_sort": "A"}}})
    assert signature_axioms(signature)[-1] == forall(
        ["x1", "x2"], Atom("A", [Function("m", [var("x1"), var("x2")])]))


def test_a_function_without_a_result_sort_gives_no_sentence():
    signature = Signature.from_dict({"functions": {
        "k": {"arity": 1, "arg_sorts": ["A"], "result_sort": None}}})
    # only the non-emptiness of A, which the argument sort names
    assert signature_axioms(signature) == (exists("x", "A"),)


def test_a_nullary_function_gives_the_membership_of_its_name():
    signature = Signature.from_dict({"functions": {
        "zero": {"arity": 0, "arg_sorts": None, "result_sort": "N"}}})
    assert signature_axioms(signature) == (exists("x", "N"), Atom("N", [Constant("zero")]))


def test_a_constant_declared_without_a_sort_gives_no_sentence():
    signature = Signature.from_dict({"constants": {"dora": None}})
    assert signature_axioms(signature) == ()


def test_a_sentence_that_two_declarations_both_give_is_given_once():
    # the constant `one` in A and the nullary function `one` into A say the same thing.
    signature = Signature(
        constants={"one": ConstantDecl("one", "A")},
        functions={"one": FunctionDecl("one", 0, None, "A")})
    assert signature_axioms(signature).count(Atom("A", [Constant("one")])) == 1


def test_a_hand_built_signature_whose_sorts_field_is_incomplete_still_names_every_sort():
    # `sorts` lists nothing, but the declarations name A (argument), B (result), C (constant),
    # D and E (an edge). Every named sort is non-empty.
    signature = Signature(
        functions={"f": FunctionDecl("f", 1, ("A",), "B")},
        constants={"carl": ConstantDecl("carl", "C")},
        subsorts={"D": frozenset({"E"})})
    sentences = signature_axioms(signature)
    assert sentences[:5] == tuple(exists("x", s) for s in "ABCDE")


# ---- determinism and form -----------------------------------------------------------------------

def test_the_order_does_not_depend_on_the_order_of_the_declarations():
    forward = Signature.from_dict({
        "constants": {"alpha": "A", "beta": "B"},
        "functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"},
                      "g": {"arity": 1, "arg_sorts": ["B"], "result_sort": "A"}}})
    backward = Signature.from_dict({
        "functions": {"g": {"arity": 1, "arg_sorts": ["B"], "result_sort": "A"},
                      "f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}},
        "constants": {"beta": "B", "alpha": "A"}})
    assert signature_axioms(forward) == signature_axioms(backward)
    assert signature_axioms(forward)[2:4] == (Atom("A", [Constant("alpha")]),
                                              Atom("B", [Constant("beta")]))


def test_every_sentence_is_closed_and_reads_back_from_its_text():
    signature = Signature.from_dict({
        "functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"},
                      "g": {"arity": 3, "arg_sorts": ["A", None, "B"], "result_sort": "C"},
                      "zero": {"arity": 0, "arg_sorts": None, "result_sort": "B"}},
        "constants": {"carl": "A"}, "subsorts": {"B": ["C"]}})
    for sentence in signature_axioms(signature):
        assert api.check(sentence).is_closed
        parsed = api.parse_any(sentence.to_unicode_str())
        assert parsed.ok and parsed.formula == sentence, sentence.to_unicode_str()


def test_the_function_works_on_anything_that_has_the_five_attributes():
    class Declarations:
        sorts = frozenset({"A"})
        predicates = {}
        functions = {}
        constants = {"carl": ConstantDecl("carl", "A")}
        subsorts = {}

    assert signature_axioms(Declarations()) == (exists("x", "A"), Atom("A", [Constant("carl")]))


# ---- the export lists ---------------------------------------------------------------------------

@pytest.mark.parametrize("module", [unicode_logic_kit, fol_package, fol_nodes])
def test_the_function_is_exported_next_to_subsort_axioms(module):
    assert module.signature_axioms is _msfl_nodes.signature_axioms
    assert "signature_axioms" in module.__all__ and "subsort_axioms" in module.__all__
