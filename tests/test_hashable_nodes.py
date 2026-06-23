"""Regression tests for frozen / hashable AST nodes (args stored as a tuple).

All node dataclasses are ``frozen=True`` and therefore hashable, so they can be
used in sets, as dict keys, and deduplicated. ``Function``/``Atom`` coerce their
``args`` to a tuple in ``__post_init__`` so construction stays lenient (a list is
accepted) while the stored value is hashable.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit import (
    Variable, Constant, Number, Function, Atom,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

_X = Variable("x")
_P = Atom("P", [_X])
_Q = Atom("Q", [])

ALL_NODES = [
    Variable("x"), Constant("a"), Number(3), Number(3.5),
    Function("f", [_X]), Atom("P", [_X]), Atom("R", []),
    Not(_P), And(_P, _Q), Or(_P, _Q), Xor(_P, _Q), Implies(_P, _Q), Iff(_P, _Q),
    Quantifier("∀", _X, _P),
    SortedQuantifier("∀", _X, "Human", _P), SortedConstant("alice", "Human"),
    WeakConjunction(_P, _Q), WeakDisjunction(_P, _Q),
    StrongConjunction(_P, _Q), StrongDisjunction(_P, _Q),
    LukNegation(_P), LukImplication(_P, _Q), LukEquivalence(_P, _Q),
    LambdaVar("p"), Lambda(LambdaVar("p"), Atom("P", [LambdaVar("p")])),
    Application(LambdaVar("p"), _X),
]


class TestHashable:
    @pytest.mark.parametrize("node", ALL_NODES, ids=lambda n: type(n).__name__)
    def test_every_node_is_hashable(self, node):
        assert isinstance(hash(node), int)

    def test_nodes_usable_in_set_and_dict(self):
        s = set(ALL_NODES)
        assert len(s) == len(ALL_NODES)  # all distinct
        d = {n: i for i, n in enumerate(ALL_NODES)}
        assert d[ALL_NODES[0]] == 0

    def test_equal_nodes_dedupe(self):
        f1 = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
        f2 = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
        assert f1 == f2 and hash(f1) == hash(f2)
        assert len({f1, f2}) == 1


class TestArgsTuple:
    def test_args_coerced_to_tuple(self):
        assert isinstance(Atom("P", [_X]).args, tuple)
        assert isinstance(Function("f", [_X]).args, tuple)

    def test_list_and_tuple_construction_are_equal(self):
        a_list = Atom("P", [_X, Constant("a")])
        a_tuple = Atom("P", (_X, Constant("a")))
        assert a_list == a_tuple
        assert hash(a_list) == hash(a_tuple)

    def test_empty_args(self):
        assert Atom("R", []).args == ()

    def test_frozen_cannot_mutate(self):
        with pytest.raises(Exception):  # FrozenInstanceError
            Atom("P", [_X]).predicate = "Q"

    def test_atoms_dedup_via_set(self):
        f = MSFLParser().parse("P(x) ∧ P(x)")
        assert len(set(f.atoms())) == 1
