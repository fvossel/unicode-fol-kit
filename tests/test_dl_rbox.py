"""Tests for RBox support in the ALC tableau (unicode_fol_kit.dl): role hierarchies
``r ⊑ s`` and transitive roles ``Trans(r)``, giving ALCH plus transitive roles (the
non-inverse fragment of SH — see the "Role hierarchies and transitive roles (RBox)"
section of ``unicode_fol_kit.dl.tableau``'s module docstring for the algorithm and its
soundness/termination argument).

Three independent lines, per the item's test oracle:

1. Hand-checked textbook cases (role hierarchy alone, transitivity alone, combined,
   the classic ``∃r.∃r.C ⊓ ∀r.¬C`` example, and a role-hierarchy+transitivity chain
   propagation case) run through the public API, each with the derivation spelled
   out in a comment.
2. A differential oracle against the kit's OWN independent route: Z3 deciding
   ``Implies(And(tbox_to_fol(tbox), rbox_to_fol(tbox)), subsumption_to_fol(C, D))`` —
   a structurally unrelated FOL-validity check — must agree with
   ``dl.subsumes(C, D, tbox)`` on every hand-picked AND randomly generated case.
3. A termination/soundness regression: an unbounded transitive-role chain must still
   terminate within budget via subset blocking and report satisfiable, confirming the
   ∀+-rule does not break blocking.

``instance_check``/``classify`` are checked too, but only to confirm they inherit RBox
support for free (as the module docstrings promise) — no new reduction is tested there
beyond what ``tests/test_dl_alc.py``/``tests/test_dl_classify.py`` already cover.
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.translate import tbox_to_fol, rbox_to_fol, subsumption_to_fol
from unicode_fol_kit.fol.nodes import Implies, And as FAnd
from unicode_fol_kit.atp.z3_models import is_valid

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
Engine = dl.Atomic("Engine")
Happy = dl.Atomic("Happy")


# --------------------------------------------------------------------------- #
# TBox/RBox API basics.
# --------------------------------------------------------------------------- #

def test_tbox_role_axiom_fields_and_chaining():
    t = dl.TBox()
    assert t.role_inclusions == []
    assert t.transitive_roles == set()
    ret1 = t.add_role_inclusion("hasSon", "hasChild")
    ret2 = t.add_transitive_role("partOf")
    assert ret1 is t and ret2 is t              # chainable, like add/add_equivalence
    assert t.role_inclusions == [("hasSon", "hasChild")]
    assert t.transitive_roles == {"partOf"}


def test_internalized_unaffected_by_rbox():
    # RBox axioms are role constraints, not concepts forced on every individual —
    # internalized() must stay exactly the GCI list, empty here.
    t = dl.TBox().add_role_inclusion("r", "s").add_transitive_role("s")
    assert t.internalized() == []
    t.add(A, B)
    assert len(t.internalized()) == 1


# --------------------------------------------------------------------------- #
# Hand-checked textbook cases (test_oracle item 1 / 3).
# --------------------------------------------------------------------------- #

def test_role_hierarchy_alone_flips_subsumption():
    # hasSon ⊑ hasChild: an ∃hasSon-witness is also an ∃hasChild-witness, but only
    # once the inclusion is declared.
    sub, sup = dl.Exists("hasSon", dl.Top()), dl.Exists("hasChild", dl.Top())
    assert dl.subsumes(sub, sup, dl.TBox()) is False          # no RBox: unrelated roles
    t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
    assert dl.subsumes(sub, sup, t) is True                   # RBox rule H fires


def test_transitivity_alone_flips_subsumption():
    # Trans(partOf): a 2-hop partOf-chain to an Engine is itself a partOf-Engine.
    # By hand: ∃partOf.∃partOf.Engine ⊓ ¬∃partOf.Engine, negated to NNF, is
    # ∃partOf.∃partOf.Engine ⊓ ∀partOf.¬Engine. Without Trans(partOf) the witness
    # chain a→y1→y2 only forces y1:¬Engine (a's own ∀-successor), not y2 — y2 gets
    # Engine from the ∃-rule and nothing contradicts it, so SAT (subsumption False).
    # With Trans(partOf), the ∀+-rule copies ∀partOf.¬Engine onto y1 too, so y1's own
    # partOf-edge to y2 then forces y2:¬Engine as well — clashing with y2:Engine, so
    # UNSAT (subsumption True).
    sub = dl.Exists("partOf", dl.Exists("partOf", Engine))
    sup = dl.Exists("partOf", Engine)
    assert dl.subsumes(sub, sup, dl.TBox()) is False
    t = dl.TBox().add_transitive_role("partOf")
    assert dl.subsumes(sub, sup, t) is True


def test_role_hierarchy_and_transitivity_combined():
    # hasChild ⊑ hasDescendant, Trans(hasDescendant):
    # ∃hasChild.∃hasChild.⊤ ⊑ ∃hasDescendant.⊤. By hand: negate to
    # ∃hasChild.∃hasChild.⊤ ⊓ ∀hasDescendant.⊥. The ∃-rule builds a hasChild-edge to
    # y1; rule H alone (hasChild ⊑ hasDescendant, no transitivity needed for THIS
    # step) already forces y1 : ⊥ directly — an immediate clash, so UNSAT, so the
    # subsumption holds.
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    sub = dl.Exists("hasChild", dl.Exists("hasChild", dl.Top()))
    sup = dl.Exists("hasDescendant", dl.Top())
    assert dl.subsumes(sub, sup, t) is True
    # without either RBox axiom, unrelated roles: no entailment
    assert dl.subsumes(sub, sup, dl.TBox()) is False


def test_role_inclusion_cycle_collapses_into_equivalence_class():
    # r ⊑ s and s ⊑ r: a ⊑-cycle. Both the TBox and _RBox docstrings call this out
    # as a deliberate, sound degenerate case ("a cycle just collapses those roles
    # into a semantic equivalence class") rather than something to reject, so lock
    # it in with a regression test on both the internal closure and the public API.
    from unicode_fol_kit.dl.tableau import _RBox

    rbox = _RBox([("r", "s"), ("s", "r")], set())
    assert rbox.ancestors("r") == rbox.ancestors("s") == frozenset({"r", "s"})

    # Semantically, rule H then treats an r-edge and an s-edge as interchangeable
    # in both directions: ∃r.⊤ ⊑ ∃s.⊤ *and* ∃s.⊤ ⊑ ∃r.⊤, neither of which holds
    # without the cycle (r and s are otherwise unrelated role names).
    sub, sup = dl.Exists("r", dl.Top()), dl.Exists("s", dl.Top())
    assert dl.subsumes(sub, sup, dl.TBox()) is False
    assert dl.subsumes(sup, sub, dl.TBox()) is False
    t = dl.TBox().add_role_inclusion("r", "s").add_role_inclusion("s", "r")
    assert dl.subsumes(sub, sup, t) is True
    assert dl.subsumes(sup, sub, t) is True

    # Cross-checked against the independent Z3 route (test_oracle item 2), the same
    # differential this file uses throughout.
    formula = Implies(FAnd(tbox_to_fol(t), rbox_to_fol(t)), subsumption_to_fol(sub, sup))
    assert is_valid(formula) is True


def test_classic_transitivity_makes_nested_exists_forall_clash():
    # The textbook example: ∃r.∃r.C ⊓ ∀r.¬C is satisfiable in plain ALC (the two
    # r-successors of the ∃-chain are distinct individuals from the ∀'s immediate
    # r-successor's perspective), but UNsatisfiable once Trans(r) is declared,
    # because the ∀+-rule then forces ¬C two hops out, clashing with the ∃-chain's
    # forced C at the same node.
    concept = dl.And(dl.Exists("r", dl.Exists("r", C)), dl.ForAll("r", dl.Not(C)))
    assert dl.concept_satisfiable(concept) is True
    t = dl.TBox().add_transitive_role("r")
    assert dl.concept_satisfiable(concept, t) is False


def test_forall_propagates_along_role_hierarchy_chain():
    # hasChild ⊑ hasDescendant, Trans(hasDescendant), and a chain of THREE hasChild
    # edges a-b-c-d. By hand: a : ∀hasDescendant.Happy forces b:Happy directly (rule
    # H, first hop). For c and d — reached only via further hasChild edges, never
    # directly from a — soundness requires the ∀+-rule to have copied
    # ∀hasDescendant.Happy onto b (and then c) so it keeps firing: hasChild(a,b) ∧
    # hasChild(b,c) ∧ hasChild(c,d), each ⊑ hasDescendant, compose under
    # Trans(hasDescendant) into hasDescendant(a,d), so a's restriction forces d:Happy
    # too. Asserting d : ¬Happy must therefore be inconsistent.
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    kb = (dl.ABox()
          .assert_concept("a", dl.ForAll("hasDescendant", Happy))
          .assert_role("a", "b", "hasChild")
          .assert_role("b", "c", "hasChild")
          .assert_role("c", "d", "hasChild")
          .assert_concept("d", dl.Not(Happy)))
    assert dl.abox_consistent(kb, t) is False
    # Sanity: the same KB minus the RBox (plain ALC, unrelated roles) is consistent —
    # the clash genuinely depends on the RBox, not on some unrelated bug.
    assert dl.abox_consistent(kb) is True
    # And with only the role hierarchy (no Trans) it is consistent too — this
    # specific 3-hop clash genuinely needs transitivity, not hierarchy alone.
    t_no_trans = dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
    assert dl.abox_consistent(kb, t_no_trans) is True


# --------------------------------------------------------------------------- #
# Termination (test_oracle item 3): an unbounded transitive-role chain must still
# terminate via subset blocking, mirroring test_dl_alc.py's cyclic-TBox pattern.
# --------------------------------------------------------------------------- #

def test_transitive_cyclic_tbox_terminates_via_blocking():
    # A ⊑ ∃partOf.A with Trans(partOf) naively generates an infinite partOf-chain,
    # each node also carrying a copy of ∀+-propagated restrictions from its
    # ancestors. Subset blocking must still cap the branch (see the module
    # docstring's termination argument) and report satisfiable.
    t = dl.TBox().add(A, dl.Exists("partOf", A)).add_transitive_role("partOf")
    assert dl.concept_satisfiable(A, t) is True


def test_transitive_cyclic_tbox_with_hierarchy_terminates():
    # Same shape, but through a role-hierarchy edge (hasChild ⊑ hasDescendant,
    # Trans(hasDescendant)) so both RBox rules (H and the ∀+-rule S) are exercised
    # together along the cyclic chain.
    t = (dl.TBox()
         .add(A, dl.Exists("hasChild", A))
         .add_role_inclusion("hasChild", "hasDescendant")
         .add_transitive_role("hasDescendant"))
    assert dl.concept_satisfiable(A, t) is True
    # A genuine clash along the cycle must still be found (blocking only suppresses
    # redundant re-expansion, not real contradictions).
    t2 = (dl.TBox()
          .add(A, dl.And(dl.Exists("hasChild", A), dl.ForAll("hasDescendant", dl.Bottom())))
          .add_role_inclusion("hasChild", "hasDescendant")
          .add_transitive_role("hasDescendant"))
    assert dl.concept_satisfiable(A, t2) is False


# --------------------------------------------------------------------------- #
# instance_check / classify inherit RBox support automatically (pure reductions).
# --------------------------------------------------------------------------- #

def test_instance_check_respects_role_hierarchy():
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
    ab = dl.ABox().assert_concept("alice", dl.Exists("hasChild", dl.Top()))
    assert dl.instance_check(ab, "alice", dl.Exists("hasDescendant", dl.Top()), t) is True
    assert dl.instance_check(ab, "alice", dl.Exists("hasDescendant", dl.Top()), dl.TBox()) is False


def test_classify_respects_role_hierarchy_via_named_equivalences():
    # classify()'s vocabulary is Atomic names only (see classification.py's
    # _atomic_names), so give HasSon/HasChild definitions that route through the
    # RBox-related roles, then check the RBox alone (no other GCI) is what makes
    # HasSon a direct child of HasChild in the Hasse diagram.
    HasSon, HasChild = dl.Atomic("HasSon"), dl.Atomic("HasChild")
    t = (dl.TBox()
         .add_equivalence(HasSon, dl.Exists("hasSon", dl.Top()))
         .add_equivalence(HasChild, dl.Exists("hasChild", dl.Top()))
         .add_role_inclusion("hasSon", "hasChild"))
    cl = dl.classify(t)
    assert sorted(cl.parents["HasSon"]) == ["HasChild"]
    assert sorted(cl.children["HasChild"]) == ["HasSon"]
    assert sorted(cl.ancestors["HasSon"]) == ["HasChild"]

    # Drop the RBox: the same two named concepts become unrelated leaves, so the
    # edge above really did come from the role inclusion, not from anything else.
    t_no_rbox = (dl.TBox()
                 .add_equivalence(HasSon, dl.Exists("hasSon", dl.Top()))
                 .add_equivalence(HasChild, dl.Exists("hasChild", dl.Top())))
    cl_no_rbox = dl.classify(t_no_rbox)
    assert cl_no_rbox.parents["HasSon"] == frozenset()
    assert cl_no_rbox.parents["HasChild"] == frozenset()


# --------------------------------------------------------------------------- #
# rbox_to_fol: hand-checked FOL rendering.
# --------------------------------------------------------------------------- #

def test_rbox_to_fol_hand_checked():
    t = dl.TBox().add_role_inclusion("r", "s").add_transitive_role("s")
    formula = rbox_to_fol(t)
    assert formula.to_unicode_str() == (
        "∀x ∀y (r(x, y) → s(x, y)) ∧ ∀x ∀y ∀z (s(x, y) ∧ s(y, z) → s(x, z))"
    )


def test_rbox_to_fol_empty_is_tautology():
    # An empty RBox renders as the same equality tautology tbox_to_fol/abox_to_fol
    # use for "no axioms" — vacuously true.
    formula = rbox_to_fol(dl.TBox())
    assert is_valid(formula) is True


def test_rbox_to_fol_sorts_transitive_roles_deterministically():
    t1 = dl.TBox()
    t1.transitive_roles = {"z", "a", "m"}
    t2 = dl.TBox()
    t2.transitive_roles = {"m", "z", "a"}
    assert rbox_to_fol(t1).to_unicode_str() == rbox_to_fol(t2).to_unicode_str()


# --------------------------------------------------------------------------- #
# Differential oracle vs Z3 (test_oracle item 2): tableau vs an independent FOL
# validity check over the SAME axioms, translated by a structurally unrelated code
# path (dl.translate, not dl.tableau).
# --------------------------------------------------------------------------- #

def _z3_subsumes(sub, sup, tbox: dl.TBox) -> bool:
    formula = Implies(FAnd(tbox_to_fol(tbox), rbox_to_fol(tbox)), subsumption_to_fol(sub, sup))
    return is_valid(formula, timeout=5000)


@pytest.mark.parametrize("tbox, sub, sup", [
    (dl.TBox().add_role_inclusion("hasSon", "hasChild"),
     dl.Exists("hasSon", dl.Top()), dl.Exists("hasChild", dl.Top())),
    (dl.TBox().add_transitive_role("partOf"),
     dl.Exists("partOf", dl.Exists("partOf", Engine)), dl.Exists("partOf", Engine)),
    (dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant"),
     dl.Exists("hasChild", dl.Exists("hasChild", dl.Top())), dl.Exists("hasDescendant", dl.Top())),
    (dl.TBox().add_transitive_role("r"),
     dl.And(dl.Exists("r", dl.Exists("r", C)), dl.ForAll("r", dl.Not(C))), dl.Bottom()),
    (dl.TBox(), dl.Exists("hasSon", dl.Top()), dl.Exists("hasChild", dl.Top())),  # no RBox: not entailed
])
def test_differential_vs_z3_hand_picked(tbox, sub, sup):
    assert dl.subsumes(sub, sup, tbox) == _z3_subsumes(sub, sup, tbox)


_ROLES = ["r1", "r2", "r3"]
_RBOX_ATOMS = [A, B]


def _rand_concept(depth, rng):
    if depth <= 0 or rng.random() < 0.35:
        return rng.choice(_RBOX_ATOMS)
    k = rng.random()
    role = rng.choice(_ROLES)
    if k < 0.16:
        return dl.Not(_rand_concept(depth - 1, rng))
    if k < 0.36:
        return dl.And(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k < 0.56:
        return dl.Or(_rand_concept(depth - 1, rng), _rand_concept(depth - 1, rng))
    if k < 0.78:
        return dl.Exists(role, _rand_concept(depth - 1, rng))
    return dl.ForAll(role, _rand_concept(depth - 1, rng))


def _rand_rbox(rng) -> dl.TBox:
    t = dl.TBox()
    pairs = [(a, b) for a in _ROLES for b in _ROLES if a != b]
    rng.shuffle(pairs)
    for a, b in pairs[:rng.randint(0, 2)]:
        t.add_role_inclusion(a, b)
    for role in rng.sample(_ROLES, rng.randint(0, 2)):
        t.add_transitive_role(role)
    return t


def test_differential_vs_z3_randomized_small_rboxes():
    # "A handful of randomized small RBoxes over 2-3 roles" per the test oracle —
    # every one of the 40 cases below must have the tableau and Z3 agree.
    rng = random.Random(20260916)          # fixed seed: reproducible, not flaky
    checked = 0
    for _ in range(40):
        tbox = _rand_rbox(rng)
        sub = _rand_concept(2, rng)
        sup = _rand_concept(2, rng)
        tableau_result = dl.subsumes(sub, sup, tbox)
        z3_result = _z3_subsumes(sub, sup, tbox)
        assert tableau_result == z3_result, (
            f"disagreement: incl={tbox.role_inclusions} trans={tbox.transitive_roles} "
            f"sub={sub.to_unicode()} sup={sup.to_unicode()} "
            f"tableau={tableau_result} z3={z3_result}"
        )
        checked += 1
    assert checked == 40


# --------------------------------------------------------------------------- #
# Manchester syntax: SubPropertyOf / Characteristics: Transitive.
# --------------------------------------------------------------------------- #

def test_manchester_role_axiom_subproperty():
    assert dl.parse_manchester_role_axiom("hasChild SubPropertyOf hasDescendant") == (
        "subproperty", "hasChild", "hasDescendant")
    assert dl.parse_manchester_role_axiom("hasChild SubPropertyOf: hasDescendant") == (
        "subproperty", "hasChild", "hasDescendant")


def test_manchester_role_axiom_transitive():
    assert dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive") == (
        "transitive", "hasDescendant")


def test_manchester_role_axiom_round_trip():
    for axiom in (("subproperty", "hasChild", "hasDescendant"), ("transitive", "partOf")):
        text = dl.role_axiom_to_manchester(*axiom)
        assert dl.parse_manchester_role_axiom(text) == axiom


@pytest.mark.parametrize("characteristic", [
    "Functional", "InverseFunctional", "Symmetric", "Asymmetric", "Reflexive", "Irreflexive",
])
def test_manchester_role_axiom_rejects_other_characteristics_by_name(characteristic):
    with pytest.raises(dl.ManchesterSyntaxError, match=characteristic):
        dl.parse_manchester_role_axiom(f"r Characteristics: {characteristic}")


def test_manchester_role_axiom_rejects_malformed_input():
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_role_axiom("hasChild SubPropertyOf")
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_role_axiom("not a role axiom at all")


def test_manchester_role_axiom_feeds_the_tbox():
    # End-to-end: parse both axiom shapes and build the exact TBox the hand-checked
    # test_role_hierarchy_and_transitivity_combined above uses.
    kind1, sub_role, super_role = dl.parse_manchester_role_axiom(
        "hasChild SubPropertyOf hasDescendant")
    kind2, role = dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive")
    assert kind1 == "subproperty" and kind2 == "transitive"
    t = dl.TBox().add_role_inclusion(sub_role, super_role).add_transitive_role(role)
    sub = dl.Exists("hasChild", dl.Exists("hasChild", dl.Top()))
    sup = dl.Exists("hasDescendant", dl.Top())
    assert dl.subsumes(sub, sup, t) is True
