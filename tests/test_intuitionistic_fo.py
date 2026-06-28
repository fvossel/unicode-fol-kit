"""First-order intuitionistic Kripke search (increasing domains).

Propositional intuitionistic validity stays a decision procedure; the first-order
extension is a *bounded* counter-model search over increasing-domain Kripke models.
A found counter-model genuinely refutes validity; a clean search does not prove it
(first-order intuitionistic logic is undecidable). Verdicts are hand-checked against
the standard intuitionistic (in)validities, and every reported counter-model is
re-checked to actually falsify the formula.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Constant,
)
from unicode_fol_kit.semantics.intuitionistic import (
    IntKripkeModel, int_valid, int_countermodel,
)

x = Variable("x")
P = lambda t: Atom("P", [t])
Q = Atom("Q", ())
Px = P(x)
fa = lambda body: Quantifier("∀", x, body)
ex = lambda body: Quantifier("∃", x, body)


# --------------------------------------------------------------------------- #
# First-order intuitionistic validities (no finite counter-model).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("formula", [
    Implies(fa(Px), ex(Px)),                          # ∀x P → ∃x P (non-empty domains)
    Implies(ex(Px), Not(fa(Not(Px)))),               # ∃x P → ¬∀x ¬P
    Implies(ex(Not(Px)), Not(fa(Px))),               # ∃x ¬P → ¬∀x P
    Implies(fa(And(Px, Q)), And(fa(Px), Q)),         # ∀ distributes over ∧
    Implies(Or(fa(Px), Q), fa(Or(Px, Q))),           # (∀x P ∨ Q) → ∀x(P ∨ Q)  [converse CD, valid]
], ids=["forall-to-exists", "ex-to-not-all-not", "ex-not-to-not-all",
        "forall-and", "converse-cd"])
def test_first_order_validities(formula):
    assert int_valid(formula, max_worlds=2) is True


# --------------------------------------------------------------------------- #
# First-order invalidities with small finite counter-models.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("formula", [
    Implies(Not(fa(Px)), ex(Not(Px))),               # ¬∀x P → ∃x ¬P (constructively fails)
    fa(Or(Px, Not(Px))),                             # universal excluded middle
    Implies(fa(Or(Px, Q)), Or(fa(Px), Q)),           # constant-domain shift CD (the invalid dir.)
], ids=["not-all-to-ex-not", "universal-lem", "constant-domain-shift"])
def test_first_order_invalidities_have_verified_countermodels(formula):
    assert int_valid(formula, max_worlds=2) is False
    result = int_countermodel(formula, max_worlds=2)
    assert result is not None
    model, world = result
    # The reported model genuinely fails to force the formula at that world.
    assert model.forces(world, formula) is False


def test_double_negation_shift_is_finitely_valid():
    # DNS ∀x¬¬P → ¬¬∀x P is intuitionistically INVALID but valid in every FINITE
    # model (terminal worlds are classical), so the finite-model search reports
    # 'no counter-model' — the documented incompleteness of the bounded FO search.
    dns = Implies(fa(Not(Not(Px))), Not(Not(fa(Px))))
    assert int_valid(dns, max_worlds=2) is True


# --------------------------------------------------------------------------- #
# Direct forcing on a hand-built increasing-domain model.
# --------------------------------------------------------------------------- #

def test_forcing_increasing_domain_model():
    # Two worlds 0 ≤ 1. Domain grows: D0={a}, D1={a,b}. P forced only of a (at both).
    upset = {0: frozenset({0, 1}), 1: frozenset({1})}
    domains = {0: frozenset({"a"}), 1: frozenset({"a", "b"})}
    valuation = {"P(a)": frozenset({0, 1})}           # P(a) up-closed; P(b) never
    m = IntKripkeModel(upset, valuation, domains)
    # ∀x P(x) fails at 0: world 1 has b with ¬P(b).
    assert m.forces(0, fa(Px)) is False
    # ∃x P(x) holds at 0: a witnesses it.
    assert m.forces(0, ex(Px)) is True
    # ¬∀x P(x) holds at 0 (no later world forces ∀x P).
    assert m.forces(0, Not(fa(Px))) is True


def test_quantifier_forcing_needs_domains():
    m = IntKripkeModel({0: frozenset({0})}, {})
    with pytest.raises(ValueError, match="per-world domains"):
        m.forces(0, fa(Px))


# --------------------------------------------------------------------------- #
# Propositional fragment unchanged (still a decision procedure).
# --------------------------------------------------------------------------- #

def test_propositional_still_decided():
    p, q = Atom("p", ()), Atom("q", ())
    assert int_valid(Or(p, Not(p))) is False          # LEM fails
    assert int_valid(Implies(p, p)) is True
    assert int_valid(Implies(Not(Not(p)), p)) is False  # DNE fails
    assert int_valid(Implies(Implies(Implies(p, q), p), p)) is False  # Peirce fails
