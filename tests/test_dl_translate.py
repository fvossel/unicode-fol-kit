"""Tests for the ALC -> FOL standard translation (unicode_logic_kit.dl.translate).

Three kinds of check:

1. Hand-checked structural assertions on `concept_to_fol` / `subsumption_to_fol`
   / `tbox_to_fol` / `abox_to_fol` / `concept_to_modal` — the exact FOL shape
   expected is derived by hand in a comment wherever it isn't obvious.
2. Differential tests against the dl tableau (`unicode_logic_kit.dl.tableau`):
   for concept satisfiability, subsumption, and ABox consistency, the FOL
   image (checked via the kit's Z3 route, `unicode_logic_kit.is_satisfiable` /
   `is_valid`) must agree with the tableau's own verdict on both hand-picked
   and randomly seeded concepts (including multi-role, deep nesting, and
   Top/Bottom leaves).
3. The knowledge-base entry point, at the end of the file: `tbox_to_fol` refuses to
   drop a TBox's role box silently, and `kb_to_fol` returns the knowledge base and
   the role-box side axioms separately; subsumption, concept satisfiability,
   instance checking and consistency relative to the KB are each decided through
   `api.prove` over that bundle and compared with the tableau (the seeded random
   differentials live in `test_dl_rbox.py` and `test_dl_alcq.py`).
"""

import functools
import random

import pytest

import unicode_logic_kit as k
import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.translate import RoleBoxOmittedError
from unicode_logic_kit.fol.nodes import (
    Variable, Constant, Atom,
    Not as FNot, And as FAnd, Or as FOr, Implies, Quantifier,
    Box, Diamond,
)
from unicode_logic_kit.atp.modal_tableau import is_modal_valid

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
Doctor = dl.Atomic("Doctor")


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
    # exists r.A |-> exists y (r(x,y) & A(y)); the fresh var is named "x0"
    # (the var argument picks the LETTER, fresh_variables adds the digits, see
    # translate.py's freshness scheme). It used to be "x_1", which the kit's own
    # VARIABLE terminal rejects, so the output could not be parsed back.
    got = dl.concept_to_fol(dl.Exists("r", A), "x")
    y = Variable("x0")
    expected = Quantifier("∃", y, FAnd(Atom("r", (Variable("x"), y)), Atom("A", (y,))))
    assert got == expected


def test_forall_translates_to_guarded_universal():
    got = dl.concept_to_fol(dl.ForAll("r", A), "x")
    y = Variable("x0")
    expected = Quantifier("∀", y, Implies(Atom("r", (Variable("x"), y)), Atom("A", (y,))))
    assert got == expected


def test_nested_restrictions_use_distinct_fresh_variables_no_capture():
    # exists r.(forall s.A): outer fresh var x0 (for r), inner fresh var x1
    # (for s) -- structurally distinct Variable nodes, so no accidental capture.
    got = dl.concept_to_fol(dl.Exists("r", dl.ForAll("s", A)), "x")
    y1, y2 = Variable("x0"), Variable("x1")
    expected = Quantifier("∃", y1, FAnd(
        Atom("r", (Variable("x"), y1)),
        Quantifier("∀", y2, Implies(Atom("s", (y1, y2)), Atom("A", (y2,))))))
    assert got == expected
    # The two bound variables really are distinct names.
    assert y1 != y2


def test_sibling_restrictions_within_one_call_get_distinct_fresh_names():
    # exists r.A ⊓ exists r.B: ONE concept_to_fol call shares a single counter
    # across its whole recursive walk, so the two Exists (siblings under And)
    # get pairwise-distinct names x0, x1 -- not reused.
    got = dl.concept_to_fol(dl.And(dl.Exists("r", A), dl.Exists("r", B)), "x")
    y1, y2 = Variable("x0"), Variable("x1")
    left = Quantifier("∃", y1, FAnd(Atom("r", (Variable("x"), y1)), Atom("A", (y1,))))
    right = Quantifier("∃", y2, FAnd(Atom("r", (Variable("x"), y2)), Atom("B", (y2,))))
    assert got == FAnd(left, right)


def test_independent_top_level_calls_may_reuse_fresh_names_without_capture():
    # subsumption_to_fol translates its antecedent and consequent with TWO
    # independent top-level calls, each starting its own minter back at x0 --
    # so both may mint "x0" for their own restriction. Safe: the two scopes
    # are siblings under ->, neither nested inside the other.
    got = dl.subsumption_to_fol(dl.Exists("r", A), dl.Exists("r", B), "x")
    x, y = Variable("x"), Variable("x0")
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
    # The seed is the INDIVIDUAL's name, which is no legal variable name at all,
    # so it contributes only its first letter: "a0", not "alice_1".
    ab = dl.ABox().assert_concept("alice", dl.Exists("r", A))
    got = dl.abox_to_fol(ab)
    y = Variable("a0")
    expected = Quantifier("∃", y, FAnd(Atom("r", (Constant("alice"), y)), Atom("A", (y,))))
    assert got == expected
    # and the individual stays a Constant: the bound variable is a different node
    assert Constant("alice") != y


def test_a_nominal_named_like_a_minted_variable_is_not_captured():
    # A Nominal becomes a Constant, and Variable("x0") and Constant("x0") print
    # the same and are the SAME Z3 expression, so a bound variable that reused
    # the name would capture the nominal: the concept would stop saying "related
    # to the individual x0" and start saying "related to something".
    concept = dl.Exists("r", dl.And(dl.Nominal("x0"), A))
    got = dl.concept_to_fol(concept, "x")
    assert got.variable == Variable("x1")
    assert "x0" in {t.name for t in got.formula.walk() if isinstance(t, Constant)}
    # the nominal still says WHICH individual
    assert got.to_unicode_str() == "∃x1 (r(x, x1) ∧ (x1 = x0 ∧ A(x1)))"


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


# --------------------------------------------------------------------------- #
# tbox_to_fol must not silently drop the role box; kb_to_fol is the entry point
# that renders the knowledge base and the role box (as SEPARATE side axioms).
# --------------------------------------------------------------------------- #

def _role_box_tbox() -> dl.TBox:
    return dl.TBox().add(A, B).add_role_inclusion("r", "s").add_transitive_role("s")


@pytest.mark.parametrize("tbox", [
    dl.TBox().add(A, B).add_role_inclusion("r", "s"),          # a role inclusion
    dl.TBox().add(A, B).add_transitive_role("r"),              # a transitive role
    dl.TBox().add_role_inclusion("r", "s"),                    # a role box and nothing else
], ids=["role-inclusion", "transitive-role", "role-box-only"])
def test_tbox_to_fol_refuses_to_drop_the_role_box_silently(tbox):
    with pytest.raises(RoleBoxOmittedError) as info:
        dl.tbox_to_fol(tbox)
    message = str(info.value)
    # the error says what to use instead, and how to opt out
    assert "kb_to_fol" in message and "rbox_to_fol" in message
    assert "concept_inclusions_only" in message
    assert isinstance(info.value, ValueError)
    assert dl.RoleBoxOmittedError is RoleBoxOmittedError       # exported from the package


def test_tbox_to_fol_concept_inclusions_only_is_the_explicit_opt_out():
    t = _role_box_tbox()
    got = dl.tbox_to_fol(t, concept_inclusions_only=True)
    assert got == dl.subsumption_to_fol(A, B, "x")              # the GCI, and nothing of the role box
    # the opt-out is keyword-only: it cannot be passed by accident as the `var` neighbour
    with pytest.raises(TypeError):
        dl.tbox_to_fol(t, "x", True)
    # a role box with an empty GCI list: the image is the tautology, not an error
    only_rbox = dl.TBox().add_role_inclusion("r", "s")
    assert dl.tbox_to_fol(only_rbox, concept_inclusions_only=True) == dl.tbox_to_fol(dl.TBox())


def test_tbox_to_fol_without_a_role_box_needs_no_keyword():
    # the pre-existing call shape keeps working for every plain (GCI-only) TBox
    t = dl.TBox().add(A, B).add_equivalence(B, C)
    assert dl.tbox_to_fol(t) == dl.tbox_to_fol(t, concept_inclusions_only=True)


def test_kb_to_fol_renders_the_pieces_and_keeps_the_role_box_separate():
    t = _role_box_tbox()
    ab = dl.ABox().assert_concept("alice", A).assert_role("alice", "bob", "r")
    kb = dl.kb_to_fol(t, ab)
    assert isinstance(kb, dl.KnowledgeBaseFOL)

    # the halves are exactly the existing renderers' output
    assert kb.tbox == dl.tbox_to_fol(t, concept_inclusions_only=True)
    assert kb.abox == dl.abox_to_fol(ab)
    # the knowledge base is their conjunction ...
    assert kb.formula == FAnd(kb.tbox, kb.abox)
    # ... and the role box is the SEPARATE side axioms, hand-checked: one per role
    # inclusion, then one per transitive role
    assert [a.to_unicode_str() for a in kb.axioms] == [
        "∀x ∀y (r(x, y) → s(x, y))",
        "∀x ∀y ∀z (s(x, y) ∧ s(y, z) → s(x, z))",
    ]
    assert dl.rbox_to_fol(t) == FAnd(kb.axioms[0], kb.axioms[1])    # same content as rbox_to_fol
    # never conjoined into the main formula: no axiom occurs anywhere inside it
    inside = list(kb.formula.walk())
    assert all(axiom not in inside for axiom in kb.axioms)
    assert kb.individuals == ("alice", "bob")
    # the two ready-made premise lists
    assert kb.premises == (kb.formula, *kb.axioms)
    assert kb.tbox_premises == (kb.tbox, *kb.axioms)


def test_kb_to_fol_halves_that_are_empty_are_left_out_of_the_formula():
    t = dl.TBox().add(A, B)
    ab = dl.ABox().assert_concept("alice", A)
    only_tbox = dl.kb_to_fol(t)
    assert only_tbox.formula == dl.tbox_to_fol(t) and only_tbox.axioms == ()
    assert only_tbox.individuals == ()
    only_abox = dl.kb_to_fol(None, ab)
    assert only_abox.formula == dl.abox_to_fol(ab) and only_abox.axioms == ()
    assert only_abox.individuals == ("alice",)
    # an ABox given as an empty ABox is the same as none
    assert dl.kb_to_fol(t, dl.ABox()).formula == only_tbox.formula
    # nothing at all: the usual equality tautology, no side axioms, no individuals
    nothing = dl.kb_to_fol()
    assert nothing.axioms == () and nothing.individuals == ()
    assert nothing.formula == nothing.tbox == nothing.abox == dl.tbox_to_fol(dl.TBox())
    assert k.is_valid(nothing.formula) is True
    # a TBox that is ONLY a role box: the formula is the tautology, the role box is all axioms
    rbox_only = dl.kb_to_fol(dl.TBox().add_role_inclusion("r", "s"))
    assert rbox_only.formula == rbox_only.tbox and len(rbox_only.axioms) == 1


def test_kb_to_fol_collects_every_individual_the_abox_names():
    ab = (dl.ABox().assert_concept("c", A).assert_role("a", "b", "r")
          .assert_distinct("d", "a"))
    assert dl.kb_to_fol(None, ab).individuals == ("a", "b", "c", "d")     # sorted, deduplicated


def test_kb_to_fol_var_reaches_the_gci_closures():
    t = dl.TBox().add(A, B)
    assert dl.kb_to_fol(t, var="z").tbox == dl.subsumption_to_fol(A, B, "z")


def test_kb_to_fol_is_a_frozen_value_and_serialises():
    import dataclasses
    import json
    kb = dl.kb_to_fol(_role_box_tbox(), dl.ABox().assert_concept("alice", A))
    with pytest.raises(dataclasses.FrozenInstanceError):
        kb.formula = kb.tbox
    as_dict = kb.to_dict()
    assert set(as_dict) == {"formula", "axioms", "tbox", "abox", "individuals"}
    assert len(as_dict["axioms"]) == 2 and as_dict["individuals"] == ["alice"]
    json.dumps(as_dict)                                   # JSON-able


# --- the three questions, exactly as kb_to_fol's docstring spells them -------------------

def test_kb_to_fol_subsumption_relative_to_the_kb():
    # (a) api.prove(subsumption_to_fol(sub, sup), kb.tbox_premises)  <=>  dl.subsumes(..., tbox)
    t = dl.TBox().add(A, dl.Exists("hasChild", B)).add_role_inclusion("hasChild", "hasDescendant")
    kb = dl.kb_to_fol(t)
    entailed = (A, dl.Exists("hasDescendant", B))      # needs the GCI AND the role inclusion
    not_entailed = (A, dl.Exists("hasDescendant", C))  # B and C are unrelated
    assert dl.subsumes(*entailed, t) is True
    assert api.prove(dl.subsumption_to_fol(*entailed), kb.tbox_premises).status == "proved"
    assert dl.subsumes(*not_entailed, t) is False
    assert api.prove(dl.subsumption_to_fol(*not_entailed), kb.tbox_premises).status == "refuted"


def test_kb_to_fol_concept_satisfiability_relative_to_the_kb():
    # (a)'s sibling: prove(Not(∃x π(C, x)), kb.tbox_premises) proved <=> C unsatisfiable w.r.t. tbox
    t = dl.TBox().add_role_inclusion("r", "s")
    kb = dl.kb_to_fol(t)
    # ∃r.A ⊓ ∀s.¬A is satisfiable on its own, unsatisfiable once r ⊑ s makes the r-witness an s-successor
    clash = dl.And(dl.Exists("r", A), dl.ForAll("s", dl.Not(A)))
    fine = dl.And(dl.Exists("r", A), dl.ForAll("s", A))
    for concept, satisfiable in ((clash, False), (fine, True)):
        assert dl.concept_satisfiable(concept, t) is satisfiable
        exists = Quantifier("∃", Variable("x"), dl.concept_to_fol(concept))
        status = api.prove(FNot(exists), kb.tbox_premises).status
        assert status == ("refuted" if satisfiable else "proved")
    assert dl.concept_satisfiable(clash) is True       # no role box: the clash needs r ⊑ s


def test_kb_to_fol_instance_checking():
    # (b) api.prove(abox_to_fol(ABox().assert_concept(a, C)), kb.premises)
    #       <=>  dl.instance_check(abox, a, C, tbox)
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
    ab = dl.ABox().assert_concept("alice", dl.Exists("hasChild", Doctor))
    kb = dl.kb_to_fol(t, ab)

    def entailed(individual, concept):
        goal = dl.abox_to_fol(dl.ABox().assert_concept(individual, concept))
        return api.prove(goal, kb.premises).status

    # by hand: alice has a hasChild-successor in Doctor; hasChild ⊑ hasDescendant makes it a
    # hasDescendant-successor too, so alice : ∃hasDescendant.Doctor
    descendant = dl.Exists("hasDescendant", Doctor)
    assert dl.instance_check(ab, "alice", descendant, t) is True
    assert entailed("alice", descendant) == "proved"
    # nothing forces alice herself to be a Doctor (open world)
    assert dl.instance_check(ab, "alice", Doctor, t) is False
    assert entailed("alice", Doctor) == "refuted"
    # and without the role box in the premises the entailed instance would be lost
    goal = dl.abox_to_fol(dl.ABox().assert_concept("alice", descendant))
    assert api.prove(goal, [kb.formula]).status == "refuted"


def test_kb_to_fol_consistency():
    # (c) api.prove(Not(kb.formula), kb.axioms): proved <=> inconsistent
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
    consistent = dl.ABox().assert_concept("alice", dl.Exists("hasChild", Doctor))
    # alice's ∀hasDescendant.¬Doctor clashes with her hasChild-successor in Doctor — only
    # through the role inclusion
    clash = (dl.ABox().assert_role("alice", "bob", "hasChild").assert_concept("bob", Doctor)
             .assert_concept("alice", dl.ForAll("hasDescendant", dl.Not(Doctor))))
    kb_ok, kb_clash = dl.kb_to_fol(t, consistent), dl.kb_to_fol(t, clash)
    assert dl.abox_consistent(consistent, t) is True
    assert api.prove(FNot(kb_ok.formula), kb_ok.axioms).status == "refuted"
    assert dl.abox_consistent(clash, t) is False
    assert api.prove(FNot(kb_clash.formula), kb_clash.axioms).status == "proved"
    # the same clash is invisible without the role box (consistent there)
    no_rbox = dl.kb_to_fol(dl.TBox(), clash)
    assert dl.abox_consistent(clash) is True
    assert api.prove(FNot(no_rbox.formula), no_rbox.axioms).status == "refuted"
    # the equivalent satisfiability spelling
    assert k.is_satisfiable(functools.reduce(FAnd, [kb_clash.formula, *kb_clash.axioms])) is False


def test_docstrings_point_every_knowledge_base_question_at_kb_to_fol():
    # The neighbouring renderers take no TBox, so they cannot silently drop one — but each
    # is an answer about the EMPTY knowledge base, and its docstring has to say so.
    for fn in (dl.concept_to_fol, dl.subsumption_to_fol, dl.abox_to_fol, dl.tbox_to_fol, dl.rbox_to_fol):
        assert "kb_to_fol" in fn.__doc__, fn.__name__
    for recipe in ("kb.tbox_premises", "kb.premises", "kb.axioms"):
        assert recipe in dl.kb_to_fol.__doc__


# --------------------------------------------------------------------------- #
# A knowledge base the size of a real ontology. `_conjoin` used to fold LEFT,
# so the conjunction's depth was the number of axioms and the kit's recursive
# node operations fell over on anything ontology-sized: binary-searched on the
# pre-0.30.0 tree, a TBox of 495 concept inclusions printed and 496 raised
# RecursionError, and at 1000 conjuncts EVERY operation below failed -- the
# last two generated by @dataclass, so no printer fix could have helped.
# --------------------------------------------------------------------------- #

def test_a_knowledge_base_of_a_thousand_inclusions_prints_and_exports():
    t = dl.TBox()
    for i in range(1000):
        t.add(dl.Atomic(f"A{i}"), dl.Atomic(f"B{i}"))
    kb = dl.kb_to_fol(t)
    assert len(kb.formulas) == 1                       # one TBox half, no ABox
    node = kb.formula
    assert len(node.to_unicode_str()) > 10000          # it prints, in full
    for export in (node.to_dict, node.to_tptp, node.to_prover9, node.to_z3):
        export()                                       # and every exporter runs
    assert node == kb.formula                          # __eq__ (dataclass-generated)
    assert isinstance(hash(node), int)                 # __hash__ likewise
    # A balanced fold is the SAME formula up to associativity, so the conjuncts
    # are still exactly the 1000 GCIs, each rendered once.
    assert node.to_unicode_str().count("→") == 1000


def test_the_fold_is_associativity_only_for_two_conjuncts():
    # 0, 1 and 2 conjuncts print IDENTICALLY under either fold -- which is why
    # the change churned no pinned string in the suite. Three is where the
    # parenthesisation moves, and the hand-derived shape is the balanced one.
    t2 = dl.TBox().add(A, B).add(B, C)
    assert dl.tbox_to_fol(t2).to_unicode_str() == (
        "∀x (A(x) → B(x)) ∧ ∀x (B(x) → C(x))")
    t3 = dl.TBox().add(A, B).add(B, C).add(C, A)
    assert dl.tbox_to_fol(t3).to_unicode_str() == (
        "∀x (A(x) → B(x)) ∧ ∀x (B(x) → C(x)) ∧ ∀x (C(x) → A(x))")


def test_the_empty_knowledge_bases_tautology_reads_back():
    # The FOL image of "no constraint". Until 0.30.0 it was built from
    # Constant("_") and printed `_ = _`, which api.parse_any rejects outright
    # ("Unexpected character '_'") -- so an RBox-only or empty knowledge base
    # printed text the kit could not read. Measured on the OEO fragment: 150 of
    # the 3636 accepted axioms, every one of them an RBox-only knowledge base.
    for kb in (dl.kb_to_fol(),
               dl.kb_to_fol(dl.TBox().add_role_inclusion("HasPart", "Overlaps")),
               dl.kb_to_fol(dl.TBox(), dl.ABox())):
        for part in (kb.formula, kb.tbox, kb.abox):
            text = part.to_unicode_str()
            parsed = api.parse_any(text)
            assert parsed.ok, f"the kit printed text it cannot parse: {text!r}"
            assert parsed.formula == part                 # and the SAME formula


def test_side_axioms_carry_the_owl_kind_they_came_from():
    # kb.axioms is the bare-formula VIEW of the one stored field, so the two can
    # never drift; the kind is what lets a caller census an ontology's image.
    t = dl.TBox().add_role_inclusion("r", "s").add_transitive_role("s")
    kb = dl.kb_to_fol(t)
    assert [(a.kind, a.group) for a in kb.side_axioms] == [
        ("SubObjectPropertyOf", "rbox"), ("TransitiveObjectProperty", "rbox")]
    assert kb.axioms == tuple(a.formula for a in kb.side_axioms)
    assert kb.rbox_axioms == kb.axioms and kb.data_axioms == ()
    assert kb.axioms_of_kind("TransitiveObjectProperty") == (kb.axioms[1],)
    assert kb.axioms_of_kind("DataPropertyRange") == ()       # unknown kind: none
