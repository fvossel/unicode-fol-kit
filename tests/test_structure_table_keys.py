"""The keys of the tables of a ``Structure`` are checked when it is built.

The evaluator reads a predicate or function table under ``(name, arity)``, a constant and a
sort under their name. ``Structure(domain, predicates={"Q": {(0,)}})`` used to be accepted
and never read: ``Q`` denoted the empty relation, ``satisfies_so(Q(x), ..., {"x": 0})`` was
False, and a sort ``S`` given only under the bare name next to a table of the same name was
not noticed. A table under a key the evaluator never reads is now refused when the structure
is built, by an ``IllegalStructureError`` that names the key and the key to write instead.
"""
import pytest

from unicode_logic_kit import MSFLParser, Structure, holds, satisfies_so
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Iff, Quantifier, Variable
from unicode_logic_kit.semantics.tarski import IllegalStructureError
from unicode_logic_kit.semantics.modelfinder import find_model

_P = MSFLParser(second_order=True).parse
_PS = MSFLParser(second_order=True, many_sorted=True).parse


def test_a_predicate_table_under_a_bare_name_is_refused_with_the_key_to_write():
    """Every tuple of the table has length 1, so the key meant is ``("Q", 1)``."""
    with pytest.raises(IllegalStructureError) as caught:
        Structure(domain={0, 1}, predicates={"Q": {(0,)}})
    message = str(caught.value)
    assert "predicates['Q']" in message and "('Q', 1)" in message
    assert "empty relation" in message


def test_the_refusal_is_a_value_error():
    with pytest.raises(ValueError):
        Structure(domain={0}, predicates={"Q": {(0,)}})


def test_the_arity_in_the_hint_follows_the_tuples_of_the_table():
    """A binary table (tuples of length 2) is meant as ``("R", 2)``, a nullary predicate's
    truth value (a bool) as ``("R", 0)``; a table that does not say (empty) names
    ``arity``."""
    with pytest.raises(IllegalStructureError, match=r"\('R', 2\)"):
        Structure(domain={0, 1}, predicates={"R": {(0, 1)}})
    with pytest.raises(IllegalStructureError, match=r"\('Rain', 0\)"):
        Structure(domain={0}, predicates={"Rain": True})
    with pytest.raises(IllegalStructureError, match=r"\('E', arity\)"):
        Structure(domain={0}, predicates={"E": set()})


def test_a_function_table_under_a_bare_name_is_refused():
    with pytest.raises(IllegalStructureError) as caught:
        Structure(domain={0, 1}, functions={"s": {(0,): 1, (1,): 0}})
    message = str(caught.value)
    assert "functions['s']" in message and "('s', 1)" in message
    assert "no value" in message


@pytest.mark.parametrize("key", [
    ("Q",), ("Q", 1, 2), ("Q", "1"), (1, 1), ("Q", -1), ("Q", True), 7, None, frozenset({"Q"}),
])
def test_a_key_of_any_other_shape_is_refused_for_predicates_and_functions(key):
    with pytest.raises(IllegalStructureError, match="not keyed by"):
        Structure(domain={0}, predicates={key: {(0,)}})
    with pytest.raises(IllegalStructureError, match="not keyed by"):
        Structure(domain={0}, functions={key: {(0,): 0}})


@pytest.mark.parametrize("table", ["constants", "sorts"])
def test_a_constant_or_sort_table_must_be_keyed_by_a_name(table):
    """The evaluator reads a constant under its name and a sort under its name."""
    key = ("c", 0)
    with pytest.raises(IllegalStructureError, match=table):
        Structure(domain={0}, **{table: {key: 0 if table == "constants" else (0,)}})


def test_every_offending_key_is_named_at_once():
    with pytest.raises(IllegalStructureError) as caught:
        Structure(domain={0, 1}, predicates={"Q": {(0,)}, "R": {(0, 1)}},
                  functions={"f": {(0,): 1}})
    message = str(caught.value)
    assert "predicates['Q']" in message and "predicates['R']" in message
    assert "functions['f']" in message


def test_the_documented_keys_are_accepted_and_read():
    """``(name, arity)`` for predicates and functions, names for constants and sorts,
    ``(name, 0)`` for a proposition: the structure is built and the tables are read
    (hand-checked: Q = {0} on {0, 1}, f swaps, the constant c is 1, S = {0})."""
    s = Structure(
        domain={0, 1},
        constants={"c": 1},
        functions={("f", 1): {(0,): 1, (1,): 0}},
        predicates={("Q", 1): {(0,)}, ("Rain", 0): True},
        sorts={"S": {0}},
    )
    x = Variable("x")
    assert satisfies_so(_P("Q(x)"), s, {"x": 0}) is True
    assert satisfies_so(_P("Q(x)"), s, {"x": 1}) is False
    assert satisfies_so(Atom("Rain", []), s) is True
    # ∀x (Q(x) ↔ x = f(c)): f(c) = f(1) = 0 and Q = {0}
    assert holds(Quantifier("∀", x, Iff(Atom("Q", [x]), Atom(
        "=", [x, Function("f", [Constant("c")])]))), s) is True
    assert holds(_PS("∀x:S Q(x)"), s) is True                   # S = {0} and Q = {0}


def test_the_silent_drop_that_made_a_formula_false_is_no_longer_possible():
    """The same table under the bare name gave ``False`` for ``Q(x)`` at ``x = 0``; under
    the documented key it is True. The bare name is refused instead of answering."""
    keyed = Structure(domain={0, 1}, predicates={("Q", 1): {(0,)}})
    assert satisfies_so(_P("Q(x)"), keyed, {"x": 0}) is True
    with pytest.raises(IllegalStructureError):
        Structure(domain={0, 1}, predicates={"Q": {(0,)}})


def test_a_sort_beside_a_bare_table_of_the_same_name_is_no_longer_accepted():
    """``sorts={"S": {0, 1}}`` and ``predicates={"S": {(0,)}}`` is a sort and a table of
    its own name with two different extensions: not a structure. Under the bare key it
    was not even looked at, and ``∀x:S S(x)`` was evaluated as if the table were not
    there; under the documented key the existing law refuses it when the sort is read."""
    with pytest.raises(IllegalStructureError, match="bare name"):
        Structure(domain={0, 1, 2}, sorts={"S": {0, 1}}, predicates={"S": {(0,)}})
    both = Structure(domain={0, 1, 2}, sorts={"S": {0, 1}}, predicates={("S", 1): {(0,)}})
    with pytest.raises(IllegalStructureError, match="both a sort and a unary predicate"):
        holds(_PS("∀x:S S(x)"), both)


def test_the_structures_the_package_builds_keep_their_keys():
    """A model found by the model finder is a ``Structure`` built by the package itself;
    it carries ``(name, arity)`` keys, so it is accepted and read back."""
    found = find_model([_P("∃x Q(x) ∧ ∃y ¬Q(y)")], max_size=2)
    assert found is not None
    assert all(isinstance(key, tuple) and len(key) == 2 for key in found.predicates)
    assert holds(_P("∃x Q(x) ∧ ∃y ¬Q(y)"), found) is True
