"""Tests for the ALC -> FOL standard translation (unicode_fol_kit.dl.translate).

Two kinds of check:

1. Hand-checked structural assertions on `concept_to_fol` / `subsumption_to_fol`
   / `tbox_to_fol` / `abox_to_fol` / `concept_to_modal` — the exact FOL shape
   expected is derived by hand in a comment wherever it isn't obvious.
2. Differential tests against the dl tableau (`unicode_fol_kit.dl.tableau`):
   for concept satisfiability, subsumption, and ABox consistency, the FOL
   image (checked via the kit's Z3 route, `unicode_fol_kit.is_satisfiable` /
   `is_valid`) must agree with the tableau's own verdict on both hand-picked
   and randomly seeded concepts (including multi-role, deep nesting, and
   Top/Bottom leaves).
"""

import random

import pytest

import unicode_fol_kit as k
import unicode_fol_kit.dl as dl
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Atom,
    Not as FNot, And as FAnd, Or as FOr, Implies, Quantifier,
    Box, Diamond,
)
from unicode_fol_kit.atp.modal_tableau import is_modal_valid

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")


def _fol_satisfiable(concept: dl.Concept, var: str = "x") -> bool:
    """The FOL-side reading of concept satisfiability: is `exists x. pi(C, x)` SAT?"""
    formula = Quantifier("∃", Variable(var), dl.concept_to_fol(concept, var))
    return k.is_satisfiable(formula)


# --------------------------------------------------------------------------- #
# concept_to_fol: hand-checked structural shape.
# --------------------------------------------------------------------------- #

def test_atomic_translates_to_unary_predicate():
    assert dl.concept_to_fol(A, "x") == Atom("A", (Variable("x"),))


def test_top_translates_to_reflexive_equality():
    # x = x: valid in every model, matching the tableau's treatment of Top
    # (never a clash, imposes no constraint).
    assert dl.concept_to_fol(dl.Top(), "x") == Atom("=", (Variable("x"), Variable("x")))


def test_bottom_translates_to_irreflexive_disequality():
    # x != x: unsatisfiable in every model, matching x:Bottom being itself a
    # clash condition in the tableau's _clash check.
    assert dl.concept_to_fol(dl.Bottom(), "x") == Atom("≠", (Variable("x"), Variable("x")))


def test_negation_and_boolean_connectives_are_structural():
    assert dl.concept_to_fol(dl.Not(A), "x") == FNot(Atom("A", (Variable("x"),)))
    assert dl.concept_to_fol(dl.And(A, B), "x") == FAnd(
        Atom("A", (Variable("x"),)), Atom("B", (Variable("x"),)))
    assert dl.concept_to_fol(dl.Or(A, B), "x") == FOr(
        Atom("A", (Variable("x"),)), Atom("B", (Variable("x"),)))


def test_exists_translates_to_guarded_existential():
    # exists r.A |-> exists y (r(x,y) & A(y)); the fresh var is named "x_1"
    # (concept_to_fol's var argument as prefix, see translate.py's freshness scheme).
    got = dl.concept_to_fol(dl.Exists("r", A), "x")
    y = Variable("x_1")
    expected = Quantifier("∃", y, FAnd(Atom("r", (Variable("x"), y)), Atom("A", (y,))))
    assert got == expected


def test_forall_translates_to_guarded_universal():
    got = dl.concept_to_fol(dl.ForAll("r", A), "x")
    y = Variable("x_1")
    expected = Quantifier("∀", y, Implies(Atom("r", (Variable("x"), y)), Atom("A", (y,))))
    assert got == expected


def test_nested_restrictions_use_distinct_fresh_variables_no_capture():
    # exists r.(forall s.A): outer fresh var x_1 (for r), inner fresh var x_2
    # (for s) -- structurally distinct Variable nodes, so no accidental capture.
    got = dl.concept_to_fol(dl.Exists("r", dl.ForAll("s", A)), "x")
    y1, y2 = Variable("x_1"), Variable("x_2")
    expected = Quantifier("∃", y1, FAnd(
        Atom("r", (Variable("x"), y1)),
        Quantifier("∀", y2, Implies(Atom("s", (y1, y2)), Atom("A", (y2,))))))
    assert got == expected
    # The two bound variables really are distinct names.
    assert y1 != y2


def test_sibling_restrictions_within_one_call_get_distinct_fresh_names():
    # exists r.A ⊓ exists r.B: ONE concept_to_fol call shares a single counter
    # across its whole recursive walk, so the two Exists (siblings under And)
    # get pairwise-distinct names x_1, x_2 -- not reused.
    got = dl.concept_to_fol(dl.And(dl.Exists("r", A), dl.Exists("r", B)), "x")
    y1, y2 = Variable("x_1"), Variable("x_2")
    left = Quantifier("∃", y1, FAnd(Atom("r", (Variable("x"), y1)), Atom("A", (y1,))))
    right = Quantifier("∃", y2, FAnd(Atom("r", (Variable("x"), y2)), Atom("B", (y2,))))
    assert got == FAnd(left, right)


def test_independent_top_level_calls_may_reuse_fresh_names_without_capture():
    # subsumption_to_fol translates its antecedent and consequent with TWO
    # independent top-level calls, each starting its own counter back at 1 --
    # so both may mint "x_1" for their own restriction. Safe: the two scopes
    # are siblings under ->, neither nested inside the other.
    got = dl.subsumption_to_fol(dl.Exists("r", A), dl.Exists("r", B), "x")
    x, y = Variable("x"), Variable("x_1")
    antecedent = Quantifier("∃", y, FAnd(Atom("r", (x, y)), Atom("A", (y,))))
    consequent = Quantifier("∃", y, FAnd(Atom("r", (x, y)), Atom("B", (y,))))
    assert got == Quantifier("∀", x, Implies(antecedent, consequent))


def test_translate_rejects_unsupported_input():
    with pytest.raises(TypeError):
        dl.concept_to_fol("not a concept")


# --------------------------------------------------------------------------- #
# subsumption_to_fol / tbox_to_fol / abox_to_fol: hand-checked shape.
# --------------------------------------------------------------------------- #

def test_subsumption_to_fol_is_universally_closed_implication():
    got = dl.subsumption_to_fol(dl.And(A, B), A, "x")
    x = Variable("x")
    expected = Quantifier("∀", x, Implies(
        FAnd(Atom("A", (x,)), Atom("B", (x,))), Atom("A", (x,))))
    assert got == expected


def test_tbox_to_fol_conjoins_one_closure_per_gci():
    t = dl.TBox().add(A, B).add(B, C)
    got = dl.tbox_to_fol(t, "x")
    expected = FAnd(dl.subsumption_to_fol(A, B, "x"), dl.subsumption_to_fol(B, C, "x"))
    assert got == expected


def test_tbox_to_fol_empty_is_a_tautology():
    # Vacuous TBox: no axioms => a formula that is satisfiable AND valid (a
    # tautology), so it never constrains anything it's conjoined with.
    formula = dl.tbox_to_fol(dl.TBox())
    assert k.is_satisfiable(formula) is True
    assert k.is_valid(formula) is True


def test_abox_to_fol_uses_constants_not_variables_for_individuals():
    ab = dl.ABox().assert_concept("alice", A).assert_role("alice", "bob", "r")
    got = dl.abox_to_fol(ab)
    expected = FAnd(Atom("A", (Constant("alice"),)), Atom("r", (Constant("alice"), Constant("bob"))))
    assert got == expected
    # Individuals must be Constants: Prover9/TPTP export uppercases Variable
    # names into their variable syntax, which would silently turn "alice"
    # into a universally/existentially-scoped variable instead of an
    # individual -- to_prover9 on a Constant leaves the name alone.
    assert got.to_prover9() == "(A(alice) & r(alice, bob))"


def test_abox_to_fol_empty_is_a_tautology():
    formula = dl.abox_to_fol(dl.ABox())
    assert k.is_satisfiable(formula) is True
    assert k.is_valid(formula) is True


def test_abox_to_fol_with_nested_restriction_translates_correctly():
    ab = dl.ABox().assert_concept("alice", dl.Exists("r", A))
    got = dl.abox_to_fol(ab)
    y = Variable("alice_1")
    expected = Quantifier("∃", y, FAnd(Atom("r", (Constant("alice"), y)), Atom("A", (y,))))
    assert got == expected


# --------------------------------------------------------------------------- #
# concept_to_modal: single-role -> Box/Diamond; multi-role -> NotImplementedError.
# --------------------------------------------------------------------------- #

def test_concept_to_modal_single_role_maps_exists_forall_to_diamond_box():
    assert dl.concept_to_modal(dl.Exists("r", A)) == Diamond(Atom("A", ()))
    assert dl.concept_to_modal(dl.ForAll("r", A)) == Box(Atom("A", ()))


def test_concept_to_modal_top_bottom_are_propositional_tautology_contradiction():
    top_formula = dl.concept_to_modal(dl.Top())
    bottom_formula = dl.concept_to_modal(dl.Bottom())
    assert not is_modal_valid(FNot(top_formula), frame="K")   # top's negation is unsat
    assert is_modal_valid(FNot(bottom_formula), frame="K")    # bottom's negation is valid


def test_concept_to_modal_same_role_used_twice_is_still_single_role():
    # Two DIFFERENT restrictions over the SAME role name "r" is still exactly
    # one accessibility relation -- must NOT raise.
    c = dl.And(dl.Exists("r", A), dl.ForAll("r", B))
    got = dl.concept_to_modal(c)
    assert got == FAnd(Diamond(Atom("A", ())), Box(Atom("B", ())))


def test_concept_to_modal_multi_role_raises_pointing_at_concept_to_fol():
    c = dl.Exists("r", dl.ForAll("s", A))
    with pytest.raises(NotImplementedError, match="concept_to_fol"):
        dl.concept_to_modal(c)


def test_concept_to_modal_zero_role_concept_is_fine():
    # A pure Boolean concept mentions no role at all -- 0 <= 1 roles, no raise.
    assert dl.concept_to_modal(dl.And(A, dl.Not(B))) == FAnd(Atom("A", ()), FNot(Atom("B", ())))


# --------------------------------------------------------------------------- #
# Differential: dl tableau vs. FOL image, hand-picked concepts (>= 20 cases).
# --------------------------------------------------------------------------- #

r = "r"

_HAND_PICKED = [
    A,
    dl.Not(A),
    dl.Top(),
    dl.Bottom(),
    dl.Not(dl.Top()),
    dl.Not(dl.Bottom()),
    dl.And(A, dl.Not(A)),                                   # clash
    dl.Or(A, dl.Not(A)),                                    # tautology
    dl.And(A, B),
    dl.Or(A, B),
    dl.And(dl.Top(), A),
    dl.Or(dl.Bottom(), A),
    dl.And(dl.Bottom(), A),                                 # unsat regardless of A
    dl.Exists(r, A),
    dl.ForAll(r, A),
    dl.Exists(r, dl.Bottom()),                               # needs an r-successor in Bottom: unsat
    dl.ForAll(r, dl.Bottom()),                                # satisfiable: just have no r-successors
    dl.Exists(r, dl.Top()),                                   # needs some r-successor at all
    dl.And(dl.Exists(r, A), dl.ForAll(r, dl.Not(A))),         # clash: witness both in A and not-A
    dl.And(dl.Exists(r, A), dl.Exists(r, dl.Not(A))),         # fine: two DIFFERENT successors
    dl.Exists(r, dl.ForAll("s", A)),                          # nested, two roles
    dl.ForAll(r, dl.Exists("s", A)),
    dl.And(dl.ForAll(r, A), dl.Exists(r, dl.Top())),
    dl.Not(dl.And(A, B)),
    dl.Not(dl.Exists(r, A)),                                  # == forall r. not A
    dl.And(dl.Exists(r, dl.And(A, B)), dl.ForAll(r, dl.Or(A, B))),
    dl.Or(dl.Exists(r, A), dl.ForAll(r, dl.Not(A))),          # tautology-ish shape, but check satisfiability
    dl.And(dl.Exists("r1", A), dl.Exists("r2", B)),           # genuinely multi-role
    dl.ForAll("r1", dl.ForAll("r2", dl.And(A, dl.Not(A)))),   # every r1r2-successor pair is impossible;
                                                               # satisfiable by having no such successors
    dl.Exists("r1", dl.Exists("r2", dl.And(A, dl.Not(A)))),   # needs an actual witness in a contradiction: unsat
]

assert len(_HAND_PICKED) >= 20


@pytest.mark.parametrize("concept", _HAND_PICKED, ids=lambda c: c.to_unicode())
def test_differential_satisfiability_hand_picked(concept):
    assert dl.concept_satisfiable(concept) == _fol_satisfiable(concept)


def test_hand_verified_satisfiability_values():
    """A handful of cases with an INDEPENDENTLY hand-derived expected value
    (not just tableau-vs-FOL agreement), so a bug shared by both implementations
    would still be caught.
    """
    cases = [
        (dl.And(A, dl.Not(A)), False),        # a direct contradiction
        (dl.Or(A, dl.Not(A)), True),          # excluded middle: A=true works
        (dl.Bottom(), False),                 # unsatisfiable by definition
        (dl.Top(), True),                     # every individual satisfies it
        (dl.And(dl.Bottom(), A), False),      # conjunct with Bottom is always false
        (dl.Exists(r, dl.Bottom()), False),   # needs an r-successor in Bottom: impossible
        (dl.ForAll(r, dl.Bottom()), True),    # vacuous: satisfied by having NO r-successors
        (dl.Exists(r, dl.Top()), True),       # needs some r-successor at all: any r-edge does
        (dl.And(dl.Exists(r, A), dl.ForAll(r, dl.Not(A))), False),
            # the ∃-witness is ALSO an r-successor, so ∀r.¬A forces it into ¬A: clash with A
        (dl.And(dl.Exists(r, A), dl.Exists(r, dl.Not(A))), True),
            # two DIFFERENT r-successors (one in A, one in ¬A) avoid the clash above
        (dl.Exists("r1", dl.Exists("r2", dl.And(A, dl.Not(A)))), False),
            # the innermost concept is a bare contradiction, however deep the nesting
        (dl.ForAll("r1", dl.ForAll("r2", dl.And(A, dl.Not(A)))), True),
            # vacuous again: satisfied by having no r1-successors at all
    ]
    for concept, expected in cases:
        assert dl.concept_satisfiable(concept) is expected, concept.to_unicode()
        assert _fol_satisfiable(concept) is expected, concept.to_unicode()


_HAND_PICKED_SUBSUMPTIONS = [
    (dl.And(A, B), A),
    (A, dl.Or(A, B)),
    (A, B),
    (dl.Exists(r, A), dl.Exists(r, dl.Top())),
    (dl.And(dl.ForAll(r, A), dl.Exists(r, dl.Top())), dl.Exists(r, A)),
    (dl.Exists(r, A), dl.ForAll(r, A)),
    (dl.ForAll(r, A), dl.ForAll(r, dl.Or(A, B))),
    (dl.Bottom(), A),                                          # Bottom subsumes everything
    (A, dl.Top()),                                              # everything is subsumed by Top
    (dl.Exists(r, dl.Bottom()), dl.Bottom()),                   # unsatisfiable antecedent: subsumption holds vacuously
]


@pytest.mark.parametrize("sub, sup", _HAND_PICKED_SUBSUMPTIONS,
                          ids=lambda c: c.to_unicode())
def test_differential_subsumption_hand_picked(sub, sup):
    assert dl.subsumes(sub, sup) == k.is_valid(dl.subsumption_to_fol(sub, sup))


# --------------------------------------------------------------------------- #
# Differential: ~50 seeded random concepts (multi-role, nested, Top/Bottom).
# --------------------------------------------------------------------------- #

_ATOMS = [A, B, C]
_ROLES = ["r", "s", "t"]


def _rand_concept(depth, rng):
    if depth <= 0 or rng.random() < 0.25:
        choice = rng.random()
        if choice < 0.1:
            return dl.Top()
        if choice < 0.2:
            return dl.Bottom()
        return rng.choice(_ATOMS)
    k_ = rng.random()
    if k_ < 0.14:
        return dl.Not(_rand_concept(depth - 1, rng))
    if k_ < 0.34:
        return dl.And(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k_ < 0.54:
        return dl.Or(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k_ < 0.77:
        return dl.Exists(rng.choice(_ROLES), _rand_concept(depth - 1, rng))
    return dl.ForAll(rng.choice(_ROLES), _rand_concept(depth - 1, rng))


def test_differential_satisfiability_random_multi_role():
    rng = random.Random(90210)
    checked = 0
    for _ in range(60):
        concept = _rand_concept(4, rng)
        tableau_sat = dl.concept_satisfiable(concept)
        fol_sat = _fol_satisfiable(concept)
        assert tableau_sat == fol_sat, concept.to_unicode()
        checked += 1
    assert checked == 60


def test_differential_subsumption_random_multi_role():
    rng = random.Random(314159)
    checked = 0
    for _ in range(40):
        sub = _rand_concept(3, rng)
        sup = _rand_concept(3, rng)
        tableau_holds = dl.subsumes(sub, sup)
        fol_valid = k.is_valid(dl.subsumption_to_fol(sub, sup))
        assert tableau_holds == fol_valid, (sub.to_unicode(), sup.to_unicode())
        checked += 1
    assert checked == 40


# --------------------------------------------------------------------------- #
# Differential: concept_to_modal vs. the modal tableau (single-role, extends
# the private _to_modal helper in tests/test_dl_alc.py to the public API).
# --------------------------------------------------------------------------- #

def _rand_single_role_concept(depth, rng):
    if depth <= 0 or rng.random() < 0.3:
        choice = rng.random()
        if choice < 0.1:
            return dl.Top()
        if choice < 0.2:
            return dl.Bottom()
        return rng.choice([A, B])
    k_ = rng.random()
    if k_ < 0.16:
        return dl.Not(_rand_single_role_concept(depth - 1, rng))
    if k_ < 0.36:
        return dl.And(_rand_single_role_concept(depth - 1, rng),
                      _rand_single_role_concept(depth - 1, rng))
    if k_ < 0.56:
        return dl.Or(_rand_single_role_concept(depth - 1, rng),
                     _rand_single_role_concept(depth - 1, rng))
    if k_ < 0.78:
        return dl.Exists(r, _rand_single_role_concept(depth - 1, rng))
    return dl.ForAll(r, _rand_single_role_concept(depth - 1, rng))


def test_differential_concept_to_modal_random_single_role():
    rng = random.Random(271828)
    checked = 0
    for _ in range(50):
        concept = _rand_single_role_concept(3, rng)
        tableau_sat = dl.concept_satisfiable(concept)
        modal_sat = not is_modal_valid(FNot(dl.concept_to_modal(concept)), frame="K")
        assert tableau_sat == modal_sat, concept.to_unicode()
        checked += 1
    assert checked == 50


# --------------------------------------------------------------------------- #
# Differential: abox_consistent vs. the joint (tbox_to_fol & abox_to_fol) image.
# --------------------------------------------------------------------------- #

def test_differential_abox_consistency_with_tbox():
    t = dl.TBox().add(A, dl.Exists(r, B))
    ab = dl.ABox().assert_concept("alice", A).assert_role("alice", "bob", r)
    formula = FAnd(dl.tbox_to_fol(t), dl.abox_to_fol(ab))
    assert dl.abox_consistent(ab, t) == k.is_satisfiable(formula) is True


def test_differential_abox_consistency_clash():
    ab = dl.ABox().assert_concept("alice", A).assert_concept("alice", dl.Not(A))
    formula = FAnd(dl.tbox_to_fol(dl.TBox()), dl.abox_to_fol(ab))
    assert dl.abox_consistent(ab) == k.is_satisfiable(formula) is False


def test_differential_abox_consistency_forced_by_tbox():
    t = dl.TBox().add(A, dl.Bottom())
    ab = dl.ABox().assert_concept("alice", A)
    formula = FAnd(dl.tbox_to_fol(t), dl.abox_to_fol(ab))
    assert dl.abox_consistent(ab, t) == k.is_satisfiable(formula) is False
