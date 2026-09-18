"""Tests for the ALC description-logic reasoner (unicode_fol_kit.dl).

Hand-checked against standard ALC reasoning (concept (un)satisfiability, subsumption,
TBox entailment, cyclic-TBox termination via blocking, ABox consistency), and
differentially against the labelled modal tableau — ALC is exactly multi-modal K, so a
single-role concept is satisfiable iff its modal translation (∃r↦◇, ∀r↦□) is
satisfiable, which the (independently brute-force-validated) modal tableau decides.

Also covers the boundary this kit draws for **I**/**O** (inverse roles, nominals):
``dl.tableau``'s in-house ALCHQ tableau refuses both by name (see
``dl.tableau.UnsupportedConceptError`` / its "Inverse roles and nominals (I, O)"
docstring section), while ``dl.translate`` DOES translate them faithfully to FOL —
checked here differentially against the kit's Z3 backend, in both directions
(entailed / not-entailed). The external, HermiT-backed reasoner that actually
DECIDES this fragment lives in ``dl.owl_reasoner`` (see ``tests/test_owl_reasoner.py``).
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.fol.nodes import (
    Atom, Not as FNot, And as FAnd, Or as FOr, Box, Diamond, Constant, Variable,
)
from unicode_fol_kit.atp.modal_tableau import is_modal_valid
from unicode_fol_kit.atp.z3_models import is_satisfiable
from unicode_fol_kit.dl.translate import _translate, _fresh_var_factory

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


# --------------------------------------------------------------------------- #
# instance_check / instance_retrieval / realize / realize_all: pure reductions
# to abox_consistent, mirroring subsumes's reduction to concept_satisfiable one
# level up at the ABox layer.
# --------------------------------------------------------------------------- #

def test_instance_check_textbook():
    # Human ⊑ Mortal, socrates : Human ⊢ socrates : Mortal. Open-world: the absence
    # of entailment for an unrelated concept is False, not "entailed to be false".
    Human, Mortal, Unrelated = dl.Atomic("Human"), dl.Atomic("Mortal"), dl.Atomic("Unrelated")
    t = dl.TBox().add(Human, Mortal)
    ab = dl.ABox().assert_concept("socrates", Human)
    assert dl.instance_check(ab, "socrates", Mortal, t) is True
    assert dl.instance_check(ab, "socrates", dl.Bottom(), t) is False
    assert dl.instance_check(ab, "socrates", Unrelated, t) is False


def test_instance_check_differential_reduction():
    # Independent second route: re-derive the abox_consistent reduction inline
    # (rather than trusting instance_check's own implementation of it) for every
    # (individual, concept) pair over a small generated ABox/TBox.
    Human, Mortal, Dog = dl.Atomic("Human"), dl.Atomic("Mortal"), dl.Atomic("Dog")
    t = dl.TBox().add(Human, Mortal)
    ab = (dl.ABox().assert_concept("socrates", Human)
          .assert_concept("rex", Dog)
          .assert_role("socrates", "rex", "owns"))
    checked = 0
    for individual in ("socrates", "rex", "ghost"):
        for concept in (Human, Mortal, Dog, dl.Not(Mortal), dl.Top(), dl.Bottom()):
            abox2 = dl.ABox(
                concept_assertions=ab.concept_assertions + [(individual, dl.Not(concept))],
                role_assertions=list(ab.role_assertions),
            )
            expected = not dl.abox_consistent(abox2, t)
            assert dl.instance_check(ab, individual, concept, t) == expected
            checked += 1
    assert checked == 18


def test_instance_retrieval_chain():
    # Dog ⊑ Mammal ⊑ Animal; rex : Dog, plus a role-only individual ("leash1", never
    # in a concept assertion) that must still be part of the retrieval universe but
    # is not entailed to be any of Dog/Mammal/Animal.
    Dog, Mammal, Animal = dl.Atomic("Dog"), dl.Atomic("Mammal"), dl.Atomic("Animal")
    t = dl.TBox().add(Dog, Mammal).add(Mammal, Animal)
    ab = dl.ABox().assert_concept("rex", Dog).assert_role("rex", "leash1", "hasAccessory")
    assert dl.instance_retrieval(ab, Dog, t) == {"rex"}
    assert dl.instance_retrieval(ab, Mammal, t) == {"rex"}
    assert dl.instance_retrieval(ab, Animal, t) == {"rex"}
    assert dl.instance_retrieval(ab, dl.Atomic("Cat"), t) == set()


def test_realize_single_most_specific():
    # Dog ⊑ Mammal ⊑ Animal, rex : Dog only -> realize drops Mammal/Animal/Top as
    # strictly subsumed-by Dog, keeping exactly [Dog].
    Dog, Mammal, Animal = dl.Atomic("Dog"), dl.Atomic("Mammal"), dl.Atomic("Animal")
    t = dl.TBox().add(Dog, Mammal).add(Mammal, Animal)
    ab = dl.ABox().assert_concept("rex", Dog)
    assert dl.realize(ab, "rex", [Animal, Mammal, Dog, dl.Top()], t) == [Dog]


def test_realize_incomparable_antichain():
    # Dog ⊑ Pet, Dog ⊑ Mammal, Pet and Mammal themselves incomparable -> both survive
    # as most-specific types; the antichain logic must not over-filter.
    Dog, Pet, Mammal = dl.Atomic("Dog"), dl.Atomic("Pet"), dl.Atomic("Mammal")
    t = dl.TBox().add(Dog, Pet).add(Dog, Mammal)
    ab = dl.ABox().assert_concept("rex", Dog)
    assert set(dl.realize(ab, "rex", [Pet, Mammal], t)) == {Pet, Mammal}


def test_realize_all_over_abox():
    Dog, Mammal = dl.Atomic("Dog"), dl.Atomic("Mammal")
    t = dl.TBox().add(Dog, Mammal)
    ab = dl.ABox().assert_concept("rex", Dog).assert_concept("felix", Mammal)
    result = dl.realize_all(ab, [Dog, Mammal], t)
    assert result == {"rex": [Dog], "felix": [Mammal]}


def test_instance_and_realize_edge_cases():
    A = dl.Atomic("A")
    empty = dl.ABox()
    # Empty ABox, TBox=None: nothing forces the anonymous "a" (abox_consistent's own
    # default-individual fallback) into A.
    assert dl.instance_check(empty, "a", A) is False
    assert dl.instance_retrieval(empty, A) == set()
    assert dl.realize_all(empty, [A, dl.Top()]) == {"a": [dl.Top()]}

    # An individual mentioned only via a role assertion is still a valid target.
    ab = dl.ABox().assert_role("alice", "bob", "hasChild")
    assert dl.instance_retrieval(ab, dl.Top()) == {"alice", "bob"}
    assert dl.instance_check(ab, "bob", dl.Top()) is True


# --------------------------------------------------------------------------- #
# Inverse roles and nominals (I, O): the in-house tableau refuses both by name
# (dl.tableau.UnsupportedConceptError), never silently approximates them.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("build", [
    lambda: dl.concept_satisfiable(dl.Nominal("a")),
    lambda: dl.concept_satisfiable(dl.Exists(dl.InverseRole("r"), dl.Top())),
    # Nested inside a TBox inclusion, not just the query concept.
    lambda: dl.concept_satisfiable(
        dl.Atomic("X"), dl.TBox().add(dl.Atomic("Y"), dl.Nominal("a"))),
    lambda: dl.concept_satisfiable(
        dl.Atomic("X"), dl.TBox().add(dl.Atomic("Y"), dl.Exists(dl.InverseRole("r"), dl.Top()))),
    # abox_consistent: concept assertion and TBox inclusion, each.
    lambda: dl.abox_consistent(dl.ABox().assert_concept("x", dl.Nominal("a"))),
    lambda: dl.abox_consistent(
        dl.ABox().assert_concept("x", dl.Atomic("A")),
        dl.TBox().add(dl.Atomic("B"), dl.Exists(dl.InverseRole("r"), dl.Top()))),
    # Pure reductions (subsumes/equivalent/instance_check/classify) inherit the
    # guard "for free" through concept_satisfiable/abox_consistent — no separate
    # guard call of their own exists, so this also checks the reduction wiring.
    lambda: dl.subsumes(dl.Nominal("a"), dl.Top()),
    lambda: dl.equivalent(dl.Atomic("A"), dl.Nominal("a")),
    lambda: dl.instance_check(dl.ABox(), "x", dl.Nominal("a")),
])
def test_inverse_role_and_nominal_refused_by_tableau(build):
    from unicode_fol_kit.dl.tableau import UnsupportedConceptError
    with pytest.raises(UnsupportedConceptError):
        build()


@pytest.mark.parametrize("build", [
    # classify() reduces to subsumes(), but collects its OWN vocabulary first
    # (dl.classification._atomic_names) — a TBox axiom using ONLY InverseRole/
    # Nominal contributes no names there, so it must raise on its own rather
    # than rely on tableau's guard ever being reached (see classification.py's
    # _atomic_names docstring for the exact gap this closes).
    lambda: dl.classify(dl.TBox().add(dl.Atomic("A"), dl.Nominal("a"))),
    lambda: dl.classify(dl.TBox().add(dl.Atomic("A"), dl.Exists(dl.InverseRole("r"), dl.Top()))),
])
def test_classify_refuses_inverse_role_and_nominal(build):
    with pytest.raises(TypeError):
        build()


def test_nnf_still_refuses_nominal_when_called_directly():
    # Regression test for the soundness fix this task shipped: nnf's top-level
    # (Top, Bottom, Atomic) pass-through tuple deliberately does NOT include
    # Nominal, even though it is "atomic-shaped", precisely so that a caller who
    # bypasses dl.tableau._reject_beyond_alc (simulated here by calling nnf
    # directly, as a hypothetical future call site might) still gets a loud
    # TypeError naming the construct instead of a silently too-permissive
    # pass-through. See dl.concepts.nnf's own docstring for the full argument.
    with pytest.raises(TypeError, match="Nominal"):
        dl.nnf(dl.Nominal("a"))
    # Nested under Not/And too — nnf's catch-all still fires (naming the
    # immediately-enclosing unsupported node, since Nominal itself is never
    # reached by any isinstance branch along the way).
    with pytest.raises(TypeError):
        dl.nnf(dl.Not(dl.Nominal("a")))
    with pytest.raises(TypeError):
        dl.nnf(dl.And(dl.Nominal("a"), dl.Atomic("B")))


# --------------------------------------------------------------------------- #
# dl.translate DOES translate InverseRole/Nominal to FOL (unlike the tableau) —
# checked differentially, in BOTH directions, against the kit's Z3 backend.
# --------------------------------------------------------------------------- #

def test_translate_inverse_role_entailment_both_directions():
    # Corrected textbook case (see this task's roadmap entry): a role assertion
    # (a, b):hasChild, queried via the concept-level InverseRole wrapper, not a
    # named-inverse-role RBox declaration (which this kit's AST does not have).
    #
    # Entailed direction: (a,b):hasChild |= b : ∃hasChild⁻.⊤ — b IS a
    # hasChild-predecessor's... no, b has an INCOMING hasChild edge from a, so b
    # has an hasChild-inverse successor (a) in ⊤. Hand-checked: TRUE.
    kb_entailed = dl.abox_to_fol(dl.ABox().assert_role("a", "b", "hasChild"))
    query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
    not_query_at_b = FNot(_translate(query, Constant("b"), _fresh_var_factory("b")))
    # KB ∧ ¬(b : query) unsatisfiable  <=>  KB |= b : query.
    assert is_satisfiable(FAnd(kb_entailed, not_query_at_b)) is False

    # Countermodel direction: only (a,c):hasChild — b has NO incoming hasChild
    # edge at all, so b : ∃hasChild⁻.⊤ is NOT entailed. Hand-checked: FALSE
    # (not entailed), i.e. KB ∧ ¬query IS satisfiable (b can simply have no
    # hasChild-predecessor in the countermodel).
    kb_not_entailed = dl.abox_to_fol(dl.ABox().assert_role("a", "c", "hasChild"))
    not_query_at_b_2 = FNot(_translate(query, Constant("b"), _fresh_var_factory("b")))
    assert is_satisfiable(FAnd(kb_not_entailed, not_query_at_b_2)) is True


def test_translate_nominal_no_unique_name_assumption_both_directions():
    # {a} ⊓ {b}: satisfiable absent an explicit DifferentIndividuals-style
    # assertion (no UNA — OWL 2's own semantics, and this kit's ABox mirrors
    # it: see dl.tableau's "no unique name assumption" note). Hand-checked:
    # SATISFIABLE (a and b may simply denote the same domain element).
    nominal_and = dl.And(dl.Nominal("a"), dl.Nominal("b"))
    formula = _translate(nominal_and, Constant("_probe"), _fresh_var_factory("_probe"))
    assert is_satisfiable(formula) is True

    # Forcing distinctness (the FOL image of ABox.assert_distinct) makes the
    # SAME formula unsatisfiable: {a} ⊓ {b} ⊓ (a ≠ b) has no model. Hand-checked:
    # UNSATISFIABLE.
    distinct = Atom("≠", (Constant("a"), Constant("b")))
    assert is_satisfiable(FAnd(formula, distinct)) is False


def test_translate_nominal_as_equality():
    # π({a}, x) is exactly "x = a" — checked structurally, not just by running
    # a solver on it, since this is the one branch of _translate that is
    # genuinely new (not a reuse of an existing case like Top/Bottom's equality
    # trick — see dl.translate's module docstring).
    assert dl.concept_to_fol(dl.Nominal("a"), "x") == Atom("=", (Variable("x"), Constant("a")))


def test_concept_to_modal_refuses_inverse_role_and_nominal():
    # Propositional K has no converse modality and no naming/nominal construct
    # (that is hybrid logic, a different formalism this kit does not
    # implement) — concept_to_modal must refuse rather than silently drop or
    # misencode either, pointing callers at concept_to_fol instead.
    with pytest.raises(NotImplementedError, match="concept_to_modal"):
        dl.concept_to_modal(dl.Exists(dl.InverseRole("r"), dl.Atomic("A")))
    with pytest.raises(NotImplementedError, match="concept_to_modal"):
        dl.concept_to_modal(dl.Nominal("a"))
