"""Tests for the ALC description-logic reasoner (unicode_fol_kit.dl).

Hand-checked against standard ALC reasoning (concept (un)satisfiability, subsumption,
TBox entailment, cyclic-TBox termination via blocking, ABox consistency), and
differentially against the labelled modal tableau — ALC is exactly multi-modal K, so a
single-role concept is satisfiable iff its modal translation (∃r↦◇, ∀r↦□) is
satisfiable, which the (independently brute-force-validated) modal tableau decides.
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.fol.nodes import (
    Atom, Not as FNot, And as FAnd, Or as FOr, Box, Diamond,
)
from unicode_fol_kit.atp.modal_tableau import is_modal_valid

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
r = "r"


# --------------------------------------------------------------------------- #
# Concept (un)satisfiability and subsumption (empty TBox).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, sat", [
    (A, True),
    (dl.And(A, dl.Not(A)), False),
    (dl.Bottom(), False),
    (dl.Top(), True),
    (dl.And(dl.Exists(r, A), dl.ForAll(r, dl.Not(A))), False),   # ∃r.A ⊓ ∀r.¬A clashes
    (dl.And(dl.Exists(r, A), dl.Exists(r, dl.Not(A))), True),    # two different successors
])
def test_concept_satisfiability(concept, sat):
    assert dl.concept_satisfiable(concept) is sat
    assert dl.concept_unsatisfiable(concept) is (not sat)


@pytest.mark.parametrize("sub, sup, holds", [
    (dl.And(A, B), A, True),
    (A, dl.Or(A, B), True),
    (A, B, False),
    (dl.Exists(r, A), dl.Exists(r, dl.Top()), True),
    (dl.And(dl.ForAll(r, A), dl.Exists(r, dl.Top())), dl.Exists(r, A), True),
    (dl.Exists(r, A), dl.ForAll(r, A), False),
    (dl.ForAll(r, A), dl.ForAll(r, dl.Or(A, B)), True),
])
def test_subsumption(sub, sup, holds):
    assert dl.subsumes(sub, sup) is holds


def test_equivalence_de_morgan():
    # ¬(A ⊓ B) ≡ ¬A ⊔ ¬B and ¬∃r.A ≡ ∀r.¬A.
    assert dl.equivalent(dl.Not(dl.And(A, B)), dl.Or(dl.Not(A), dl.Not(B))) is True
    assert dl.equivalent(dl.Not(dl.Exists(r, A)), dl.ForAll(r, dl.Not(A))) is True
    assert dl.equivalent(A, dl.Or(A, B)) is False


# --------------------------------------------------------------------------- #
# General TBoxes (internalisation + blocking).
# --------------------------------------------------------------------------- #

def test_tbox_subsumption_transitivity():
    t = dl.TBox().add(A, B).add(B, C)
    assert dl.subsumes(A, C, t) is True
    assert dl.subsumes(A, dl.Not(C), t) is False


def test_cyclic_tbox_terminates_via_blocking():
    # A ⊑ ∃r.A has only infinite models, but blocking yields a finite witness.
    t = dl.TBox().add(A, dl.Exists(r, A))
    assert dl.concept_satisfiable(A, t) is True


def test_tbox_can_force_unsatisfiability():
    t = dl.TBox().add(A, dl.Bottom())
    assert dl.concept_satisfiable(A, t) is False
    assert dl.concept_satisfiable(B, t) is True            # B is unconstrained


def test_tbox_equivalence_axiom():
    # With A ≡ B ⊓ C, A subsumes nothing new but A ⊑ B and A ⊑ C hold.
    t = dl.TBox().add_equivalence(A, dl.And(B, C))
    assert dl.subsumes(A, B, t) is True
    assert dl.subsumes(A, C, t) is True
    assert dl.subsumes(dl.And(B, C), A, t) is True


# --------------------------------------------------------------------------- #
# ABox consistency.
# --------------------------------------------------------------------------- #

def test_abox_clash():
    ab = dl.ABox().assert_concept("alice", A).assert_concept("alice", dl.Not(A))
    assert dl.abox_consistent(ab) is False


def test_abox_value_restriction_propagates():
    ab = (dl.ABox().assert_concept("alice", dl.ForAll(r, A))
          .assert_role("alice", "bob", r).assert_concept("bob", dl.Not(A)))
    assert dl.abox_consistent(ab) is False                  # ∀r.A forces bob:A, clashes


def test_abox_consistent_with_existential():
    assert dl.abox_consistent(dl.ABox().assert_concept("alice", dl.Exists(r, A))) is True


def test_abox_with_tbox():
    t = dl.TBox().add(A, dl.Bottom())
    assert dl.abox_consistent(dl.ABox().assert_concept("alice", A), t) is False
    assert dl.abox_consistent(dl.ABox().assert_concept("alice", B), t) is True


# --------------------------------------------------------------------------- #
# Rendering + NNF.
# --------------------------------------------------------------------------- #

def test_render_and_nnf():
    assert dl.Exists(r, dl.And(A, dl.Not(B))).to_unicode() == "∃r.(A ⊓ ¬B)"
    assert dl.nnf(dl.Not(dl.Exists(r, A))) == dl.ForAll(r, dl.Not(A))
    assert dl.nnf(dl.Not(dl.Not(A))) == A


# --------------------------------------------------------------------------- #
# Differential vs the modal tableau (ALC ≅ multi-modal K, single role).
# --------------------------------------------------------------------------- #

_ATOMS = [dl.Atomic("A"), dl.Atomic("B")]


def _rand_concept(depth, rng):
    if depth <= 0 or rng.random() < 0.35:
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.16:
        return dl.Not(_rand_concept(depth - 1, rng))
    if k < 0.36:
        return dl.And(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k < 0.56:
        return dl.Or(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k < 0.78:
        return dl.Exists(r, _rand_concept(depth - 1, rng))
    return dl.ForAll(r, _rand_concept(depth - 1, rng))


def _to_modal(concept):
    """Translate a single-role ALC concept to a propositional modal formula (K)."""
    if isinstance(concept, dl.Atomic):
        return Atom(concept.name, ())
    if isinstance(concept, dl.Top):
        return FOr(Atom("T", ()), FNot(Atom("T", ())))
    if isinstance(concept, dl.Bottom):
        return FAnd(Atom("T", ()), FNot(Atom("T", ())))
    if isinstance(concept, dl.Not):
        return FNot(_to_modal(concept.concept))
    if isinstance(concept, dl.And):
        return FAnd(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, dl.Or):
        return FOr(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, dl.Exists):
        return Diamond(_to_modal(concept.concept))
    if isinstance(concept, dl.ForAll):
        return Box(_to_modal(concept.concept))
    raise TypeError(concept)


def test_differential_vs_modal_tableau():
    rng = random.Random(2718)
    checked = 0
    for _ in range(150):
        concept = _rand_concept(3, rng)
        alc_sat = dl.concept_satisfiable(concept)
        # C satisfiable iff its modal translation is satisfiable iff ¬translation is
        # NOT valid in K.
        modal_sat = not is_modal_valid(FNot(_to_modal(concept)), frame="K")
        assert alc_sat == modal_sat, concept.to_unicode()
        checked += 1
    assert checked == 150
