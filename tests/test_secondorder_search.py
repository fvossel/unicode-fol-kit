"""Bounded second-order validity / (counter)model search (semantics.secondorder).

Second-order validity is not even semi-decidable, so this is a *bounded* finite-model
search: it interprets the formula's FREE symbols over small domains while the
satisfies_so evaluator ranges the SO-quantified predicates over all relations. A found
(counter)model is genuine; "none up to size N" is bounded evidence. Verdicts are
hand-checked against standard second-order (in)validities, and counter-models are
re-checked to actually refute the formula.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant,
)
from unicode_fol_kit.fol._so_nodes import SecondOrderQuantifier
from unicode_fol_kit.semantics.secondorder import (
    holds, so_find_model, so_find_countermodel,
    so_is_satisfiable_finite, so_is_valid_finite,
)

x, y = Variable("x"), Variable("y")
a, b = Constant("a"), Constant("b")
P = lambda t: Atom("P", [t])
Q = lambda t: Atom("Q", [t])
fa = lambda v, body: Quantifier("∀", v, body)
ex = lambda v, body: Quantifier("∃", v, body)
faP = lambda body: SecondOrderQuantifier("∀", "P", 1, body)
exP = lambda body: SecondOrderQuantifier("∃", "P", 1, body)


@pytest.mark.parametrize("formula", [
    exP(fa(x, Iff(P(x), Not(Q(x))))),            # the complement of Q is always definable
    exP(fa(x, P(x))),                            # the total relation exists
    faP(Implies(P(a), P(a))),                    # ∀P (P(a) → P(a))
    # Leibniz's definition of equality is second-order valid.
    fa(x, fa(y, Iff(Atom("=", [x, y]),
                    SecondOrderQuantifier("∀", "P", 1, Iff(P(x), P(y)))))),
], ids=["complement-definable", "total-relation", "p-implies-p", "leibniz-equality"])
def test_second_order_validities(formula):
    assert so_is_valid_finite(formula, max_size=3) is True


@pytest.mark.parametrize("formula", [
    faP(ex(x, P(x))),                            # not every relation is non-empty (∅)
    exP(And(P(a), Not(P(b)))),                   # a, b need not be distinguishable (a=b)
], ids=["every-relation-nonempty", "constants-distinguishable"])
def test_second_order_invalidities_have_verified_countermodels(formula):
    assert so_is_valid_finite(formula, max_size=3) is False
    cm = so_find_countermodel(formula, max_size=3)
    assert cm is not None
    assert holds(formula, cm) is False


def test_second_order_satisfiability():
    assert so_is_satisfiable_finite(exP(fa(x, P(x))), max_size=2) is True
    # An unsatisfiable SO sentence: ∃P (∀x P(x) ∧ ∃x ¬P(x)) is contradictory.
    contradiction = exP(And(fa(x, P(x)), ex(x, Not(P(x)))))
    assert so_is_satisfiable_finite(contradiction, max_size=3) is False


def test_so_find_model_returns_structure_that_holds():
    f = exP(fa(x, Iff(P(x), Q(x))))             # P can copy Q
    m = so_find_model(f, max_size=2)
    assert m is not None and holds(f, m) is True
