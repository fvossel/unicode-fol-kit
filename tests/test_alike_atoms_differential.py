"""Random propositional formulas over terms that print alike, against an oracle that keys by node.

The terms are drawn from a pool in which two pairs print alike: the numeral ``1`` and the
constant named ``1``, and the free variable ``x`` and the constant named ``x``. A route that
names a letter by text refuses a formula that holds both atoms ``P(1)`` and ``P('1')`` (or
``P(x)`` and ``P(x)`` with a variable and a constant of one name), and decides every other
formula as an oracle does that keys each letter by the atom NODE: 3**n valuations for the
three-valued logics, 2**n for the classical one, with the connectives evaluated by hand
(``¬v = 1 - v``, ``∧ = min``, ``∨ = max``, ``a → b = max(1 - a, b)``).
"""

import itertools
import random

import pytest

from unicode_fol_kit.atp.lj import int_prove
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Implies, Not, Number, Or, Variable
from unicode_fol_kit.semantics import manyvalued as mv
from unicode_fol_kit.semantics import matrix as mx
from unicode_fol_kit.semantics.intuitionistic import int_valid
from unicode_fol_kit.semantics.truthtable import is_tautology

POOL = [Number(1), Constant("1"), Constant("a"), Variable("x"), Constant("x"), Number(1.0)]
#: the two pairs of the pool that print alike, by position in POOL (Number(1.0) is Number(1))
ALIKE_PAIRS = [(0, 1), (3, 4), (5, 1)]


def _formula(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return Atom(rng.choice("PQ"), [rng.choice(POOL)])
    kind = rng.choice(["not", "and", "or", "implies"])
    if kind == "not":
        return Not(_formula(rng, depth - 1))
    cls = {"and": And, "or": Or, "implies": Implies}[kind]
    return cls(_formula(rng, depth - 1), _formula(rng, depth - 1))


def _atoms(formula):
    return [n for n in formula.walk() if isinstance(n, Atom)]


def _is_alike(formula):
    """Whether two atoms of the formula are different nodes that print alike (by the pool's pairs)."""
    atoms = _atoms(formula)
    for left in atoms:
        for right in atoms:
            if left.predicate != right.predicate or left == right:
                continue
            a, b = left.args[0], right.args[0]
            if any({a, b} == {POOL[i], POOL[j]} for i, j in ALIKE_PAIRS):
                return True
    return False


def _value(formula, valuation):
    if isinstance(formula, Atom):
        return valuation[repr(formula)]
    if isinstance(formula, Not):
        return 1.0 - _value(formula.formula, valuation)
    left, right = _value(formula.left, valuation), _value(formula.right, valuation)
    if isinstance(formula, And):
        return min(left, right)
    if isinstance(formula, Or):
        return max(left, right)
    return max(1.0 - left, right)


def _oracle_valid(formula, values, designated):
    keys = sorted({repr(a) for a in _atoms(formula)})
    return all(_value(formula, dict(zip(keys, row))) in designated
               for row in itertools.product(values, repeat=len(keys)))


@pytest.mark.parametrize("seed", range(12))
def test_a_route_refuses_exactly_the_formulas_with_a_pair_that_prints_alike(seed):
    rng = random.Random(seed)
    refused = decided = 0
    for _ in range(40):
        formula = _formula(rng, 3)
        if len({repr(a) for a in _atoms(formula)}) > 5:
            continue
        routes = {
            "is_tautology": lambda: is_tautology(formula),
            "K3": lambda: mv.is_valid(formula, "K3"),
            "LP": lambda: mv.is_valid(formula, "LP"),
            "FDE": lambda: mx.matrix_is_valid(formula, mx.FDE_MATRIX),
            "int_valid": lambda: int_valid(formula),
            "int_prove": lambda: int_prove([], formula),
        }
        if _is_alike(formula):
            for name, call in routes.items():
                with pytest.raises(NotImplementedError):
                    call()
            refused += 1
            continue
        classical = _oracle_valid(formula, (0.0, 1.0), {1.0})
        assert is_tautology(formula) is classical
        assert mv.is_valid(formula, "K3") is _oracle_valid(formula, (0.0, 0.5, 1.0), {1.0})
        assert mv.is_valid(formula, "LP") is _oracle_valid(formula, (0.0, 0.5, 1.0), {0.5, 1.0})
        # an intuitionistic theorem is classically valid, and holds in every bounded Kripke model
        # (the bounded search may still call a non-theorem valid, so only this direction is pinned)
        if int_prove([], formula):
            assert classical
            assert int_valid(formula) is True
        decided += 1
    assert refused + decided > 0
