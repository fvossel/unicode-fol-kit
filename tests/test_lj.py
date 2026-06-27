"""Tests for the intuitionistic sequent calculus LJ checker (atp.lj).

Soundness oracle: an accepted LJ derivation's end-sequent ``Γ ⊢ A`` must be
intuitionistically valid — cross-checked with the Kripke-model decision procedure
``int_valid`` (propositional) and with classical ``is_valid`` (LJ ⊆ LK). The
defining intuitionistic restriction — at most one succedent formula — is exercised by
rejecting the multi-succedent route to excluded middle.
"""

from functools import reduce

import pytest

from unicode_fol_kit import int_valid, is_valid
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant,
)
from unicode_fol_kit.atp.sequent import sequent, derive, axiom
from unicode_fol_kit.atp.lj import check_lj_proof, verify_lj_proof

P, Q = Atom("P", ()), Atom("Q", ())
NP, NNP = Not(P), Not(Not(P))
x, c = Variable("x"), Constant("c")


def Px(t):
    return Atom("P", [t])


def _d_imp_refl():
    return derive(sequent([], [Implies(P, P)]), "→R", axiom(sequent([P], [P])))


def _d_p_to_nnp():
    return derive(sequent([], [Implies(P, NNP)]), "→R",
              derive(sequent([P], [NNP]), "¬R",
                  derive(sequent([P, NP], []), "¬L",
                      axiom(sequent([P], [P])))))


def _d_non_contradiction():
    return derive(sequent([], [Not(And(P, NP))]), "¬R",
              derive(sequent([And(P, NP)], []), "∧L",
                  derive(sequent([P, NP], []), "¬L",
                      axiom(sequent([P], [P])))))


def _d_modus_ponens():
    return derive(sequent([P, Implies(P, Q)], [Q]), "→L",
                  axiom(sequent([P], [P])), axiom(sequent([P, Q], [Q])))


def _d_and_comm():
    return derive(sequent([And(P, Q)], [And(Q, P)]), "∧L",
              derive(sequent([P, Q], [And(Q, P)]), "∧R",
                  axiom(sequent([P, Q], [Q])), axiom(sequent([P, Q], [P]))))


def _d_disjunction_intro():
    # P ⊢ P ∨ Q  via ∨R1
    return derive(sequent([P], [Or(P, Q)]), "∨R1", axiom(sequent([P], [P])))


def _d_forall_inst():
    return derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
                  axiom(sequent([Px(c)], [Px(c)])), extra=[c])


_PROP = [
    (_d_imp_refl, Implies(P, P)),
    (_d_p_to_nnp, Implies(P, NNP)),
    (_d_non_contradiction, Not(And(P, NP))),
    (_d_modus_ponens, Implies(And(P, Implies(P, Q)), Q)),
    (_d_and_comm, Implies(And(P, Q), And(Q, P))),
    (_d_disjunction_intro, Implies(P, Or(P, Q))),
]


@pytest.mark.parametrize("builder,goal", _PROP, ids=[b.__name__ for b, _ in _PROP])
def test_curated_lj_accepted_and_intuitionistically_sound(builder, goal):
    result = verify_lj_proof(builder())
    assert result.ok, result.error
    # The end-sequent's formula must be intuitionistically valid (Kripke search) ...
    assert int_valid(goal, max_worlds=3), goal.to_unicode_str()
    # ... and therefore classically valid too.
    assert is_valid(goal)


def test_forall_instantiation_accepted():
    d = _d_forall_inst()
    assert check_lj_proof(d)
    assert is_valid(Implies(Quantifier("∀", x, Px(x)), Px(c)))


def test_reject_multi_succedent():
    # The classical route to excluded middle needs a two-formula succedent (⊢ P, ¬P);
    # LJ forbids it.
    bad = derive(sequent([], [P, NP]), "¬R", axiom(sequent([P], [P])))
    result = verify_lj_proof(bad)
    assert result.ok is False
    assert "at most one succedent" in result.error


def test_reject_bogus_excluded_middle():
    # ∨R1 from an underivable premise ⊢ P (no axiom: empty antecedent) must fail.
    bad = derive(sequent([], [Or(P, NP)]), "∨R1", derive(sequent([], [P]), "Ax"))
    assert check_lj_proof(bad) is False


def test_reject_bad_axiom():
    assert check_lj_proof(axiom(sequent([P], [Q]))) is False


def test_lj_exports():
    import unicode_fol_kit as u
    for name in ("check_lj_proof", "verify_lj_proof"):
        assert hasattr(u, name) and name in u.__all__, name
