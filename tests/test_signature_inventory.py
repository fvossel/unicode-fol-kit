"""Tests for :func:`unicode_logic_kit.fol.signature.inventory_of` — the LENIENT,
never-raising symbol-inventory walk factored out of
:mod:`unicode_logic_kit.eval.predicate_match` (roadmap item C5).

No snapshot tests: every expected value below is derived BY HAND against the
function's documented contract (see ``unicode_logic_kit/fol/signature.py``'s
module docstring and :func:`inventory_of`'s own docstring), mirroring
``tests/test_signature.py``'s own convention. Formulas are built directly
from the AST node constructors for full control over exactly which
conflicting/ambiguous shapes are exercised.
"""

import pytest

from unicode_logic_kit.fol.nodes import (
    Variable, Constant, SortedConstant, Function, Atom, Not, And,
    Implies, Quantifier, SortedQuantifier, Number,
)
from unicode_logic_kit.fol.signature import Signature, PredicateDecl, FunctionDecl, inventory_of
from unicode_logic_kit.fol.msflparser import MSFLParser

_MODAL = MSFLParser(modal=True)


# =============================================================================
# The clean / conformant case: inventory_of agrees with Signature.from_formulas
# =============================================================================

def test_inventory_of_matches_from_formulas_predicates_and_functions_on_clean_input():
    """On a batch with NO vocabulary conflicts, inventory_of's (name, arity)
    sets must exactly match the arities Signature.from_formulas declares —
    the two are independently-triggered classifications of the SAME
    underlying facts, and must agree whenever there is nothing to refuse.

    Hand-derivation (same fixture as
    test_signature.py::test_from_formulas_hand_derived_msfol_example):
      f1 = forall x:Human (Mortal(x) -> Loves(x, fatherOf(x)))
      f2 = Human(alice:Human)
      f3 = Rain()
      f4 = forall y (P(y) v not P(y))
    predicates: Mortal/1, Loves/2, Human/1, Rain/0, P/1.
    functions: fatherOf/1.
    constants: alice.
    """
    x = Variable("x")
    y = Variable("y")
    f1 = SortedQuantifier(
        "∀", x, "Human",
        Implies(Atom("Mortal", [x]),
                Atom("Loves", [x, Function("fatherOf", [x])])))
    f2 = Atom("Human", [SortedConstant("alice", "Human")])
    f3 = Atom("Rain", [])
    f4 = Quantifier("∀", y, Not(Atom("P", [y])))

    sig = Signature.from_formulas([f1, f2, f3, f4])
    combined = And(And(f1, f2), And(f3, f4))
    preds, funcs, consts = inventory_of(combined)

    assert preds == {(name, decl.arity) for name, decl in sig.predicates.items()}
    assert funcs == {(name, decl.arity) for name, decl in sig.functions.items()}
    assert consts == set(sig.constants)


def test_inventory_of_excludes_builtin_operators():
    """'=' and '+' are the kit's built-in operators, never user vocabulary —
    the exact same classification Signature.validate uses (see the two
    modules' _BUILTIN_PREDS / _BUILTIN_FUNCS)."""
    n = Atom("=", [Function("+", [Constant("a"), Number(1)]), Constant("b")])
    preds, funcs, consts = inventory_of(n)
    assert preds == set()
    assert funcs == set()
    assert consts == {"a", "b"}


def test_inventory_of_reaches_atoms_nested_under_modal_operators():
    """The generic node.walk() reach: an Atom nested under a modal box/
    diamond is still found, exactly like validate()'s own walk documents.

    ('alice'/'bob', not 'a'/'b': the grammar's VARIABLE production is a
    single lowercase letter optionally followed by digits, so a bare 'a'
    parses as a Variable, not a Constant — a two-letter-plus NAME is
    needed to get an actual constant here.)
    """
    f = _MODAL.parse("□Winner(alice) → ◇Loser(bob)")
    preds, funcs, consts = inventory_of(f)
    assert preds == {("Winner", 1), ("Loser", 1)}
    assert consts == {"alice", "bob"}


# =============================================================================
# The adversarial cases: exactly what Signature.from_formulas refuses
# =============================================================================

def test_inventory_of_tolerates_arity_inconsistent_predicate():
    """P used at arity 1 and arity 2 in ONE tree: Signature.from_formulas
    refuses this outright (see test_signature.py's own conflict tests);
    inventory_of keeps BOTH (name, arity) entries side by side and never
    raises — the property predicate_match's whole purpose depends on."""
    n = And(Atom("P", [Constant("a")]),
            Atom("P", [Constant("a"), Constant("b")]))
    with pytest.raises(ValueError, match="conflicting arities"):
        Signature.from_formulas([n])

    preds, funcs, consts = inventory_of(n)
    assert preds == {("P", 1), ("P", 2)}
    assert funcs == set()
    assert consts == {"a", "b"}


def test_inventory_of_tolerates_name_used_as_constant_and_as_function():
    """'alice' as a bare constant in one atom and as an applied function in
    another, in ONE tree: Signature.from_formulas refuses this; inventory_of
    records 'alice' in BOTH the constants set and the functions set."""
    x = Variable("x")
    n = And(Atom("S", [Constant("alice")]),
            Atom("T", [Function("alice", [x])]))
    with pytest.raises(ValueError, match="used both as a constant and as a function"):
        Signature.from_formulas([n])

    preds, funcs, consts = inventory_of(n)
    assert preds == {("S", 1), ("T", 1)}
    assert funcs == {("alice", 1)}
    assert consts == {"alice"}


def test_inventory_of_allows_a_predicate_and_a_function_sharing_a_name():
    """'Foo' as a predicate (Foo(x)) AND as a function (Q(Foo(x))) is NOT a
    conflict for either implementation (predicates and functions are
    separate namespaces; only constant-vs-function is a clash — see the
    module docstring). Signature.from_formulas accepts this batch cleanly,
    and inventory_of records the name in both namespace sets, agreeing."""
    x = Variable("x")
    p1 = Atom("Foo", [x])
    p2 = Atom("Q", [Function("Foo", [x])])
    n = And(p1, p2)

    sig = Signature.from_formulas([p1, p2])
    assert dict(sig.predicates) == {
        "Foo": PredicateDecl("Foo", 1), "Q": PredicateDecl("Q", 1),
    }
    assert dict(sig.functions) == {"Foo": FunctionDecl("Foo", 1)}

    preds, funcs, consts = inventory_of(n)
    assert preds == {("Foo", 1), ("Q", 1)}
    assert funcs == {("Foo", 1)}


def test_inventory_of_tolerates_all_three_conflicts_at_once():
    """A single tree combining every adversarial shape at once: arity
    inconsistency, constant-vs-function clash, AND a predicate/function
    name overlap — inventory_of must still return a complete, non-raising
    classification (this is the property align_symbols's own robustness
    depends on for arbitrary, possibly-malformed model output)."""
    x = Variable("x")
    n = And(
        And(Atom("P", [Constant("a")]),
            Atom("P", [Constant("a"), Constant("b")])),
        And(Atom("S", [Constant("alice")]),
            Atom("T", [Function("alice", [x])])),
    )
    preds, funcs, consts = inventory_of(n)
    assert preds == {("P", 1), ("P", 2), ("S", 1), ("T", 1)}
    assert funcs == {("alice", 1)}
    assert consts == {"a", "b", "alice"}


# =============================================================================
# Determinism (a formatting/inventory layer must be repeatable)
# =============================================================================

def test_inventory_of_is_deterministic():
    n = And(Atom("P", [Constant("a")]), Atom("Q", [Function("f", [Constant("b")])]))
    first = inventory_of(n)
    second = inventory_of(n)
    assert first == second
