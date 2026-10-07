"""Tests for RBox support in the ALC tableau (unicode_logic_kit.dl): role hierarchies
``r ⊑ s`` and transitive roles ``Trans(r)``, giving ALCH plus transitive roles (the
non-inverse fragment of SH — see the "Role hierarchies and transitive roles (RBox)"
section of ``unicode_logic_kit.dl.tableau``'s module docstring for the algorithm and its
soundness/termination argument).

Three independent lines, per the item's test oracle:

1. Hand-checked textbook cases (role hierarchy alone, transitivity alone, combined,
   the classic ``∃r.∃r.C ⊓ ∀r.¬C`` example, and a role-hierarchy+transitivity chain
   propagation case) run through the public API, each with the derivation spelled
   out in a comment.
2. A differential oracle against the kit's OWN independent route: Z3 deciding
   ``Implies(And(tbox_to_fol(tbox, concept_inclusions_only=True), rbox_to_fol(tbox)),
   subsumption_to_fol(C, D))`` — a structurally unrelated FOL-validity check — must
   agree with ``dl.subsumes(C, D, tbox)`` on every hand-picked AND randomly generated
   case. The same agreement is checked, at the end of this file, through the
   knowledge-base entry point ``kb_to_fol`` and ``api.prove`` (subsumption, instance
   checking, consistency) — including the regression for the trap that entry point
   closes: the concept-inclusion image alone silently drops the role box and yields
   false counterexamples.
3. A termination/soundness regression: an unbounded transitive-role chain must still
   terminate within budget via subset blocking and report satisfiable, confirming the
   ∀+-rule does not break blocking.

``instance_check``/``classify`` are checked too, but only to confirm they inherit RBox
support for free (as the module docstrings promise) — no new reduction is tested there
beyond what ``tests/test_dl_alc.py``/``tests/test_dl_classify.py`` already cover.
"""

import random

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.translate import (
    tbox_to_fol, rbox_to_fol, subsumption_to_fol, abox_to_fol, kb_to_fol,
)
from unicode_logic_kit.dl.tableau import _holder_fields, _is_simple_role, _RBox
from unicode_logic_kit.fol.nodes import Implies, And as FAnd, Not as FNot
from unicode_logic_kit.atp.z3_models import is_valid

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
Engine = dl.Atomic("Engine")
Happy = dl.Atomic("Happy")

# Z3-backed calls take their timeout in MILLISECONDS, and the budget is never
# shrunk to make a test fast: "unknown" is not a verdict. The three differential
# helpers below used 5000/3000 here; a budget that small turns a slow machine's
# "unknown" into a silent False (`is_valid`) or an "undecided" nobody reads.
TIMEOUT_MS = 30000


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


def test_internalized_unaffected_by_a_functional_role_either():
    # Func(P) IS the GCI ⊤ ⊑ ≤1 P.⊤, and the tableau decides it by adding
    # exactly that concept — but in _new_branch, NOT here: internalized() is
    # documented as the image of `inclusions` and callers read it that way.
    from unicode_logic_kit.dl.tableau import _new_branch

    t = dl.TBox().add_functional_role("r")
    assert t.internalized() == []
    _branch, tbox_concepts, _rbox = _new_branch(t)
    assert tbox_concepts == [dl.AtMost(1, "r", dl.Top())]
    # and a second functional role is added in SORTED order, so the list is
    # deterministic despite functional_roles being a set
    t2 = dl.TBox().add_functional_role("z").add_functional_role("a")
    assert _new_branch(t2)[1] == [dl.AtMost(1, "a", dl.Top()),
                                  dl.AtMost(1, "z", dl.Top())]


# --------------------------------------------------------------------------- #
# The rest of the OWL 2 role box: builders, fields and their normalisation.
# --------------------------------------------------------------------------- #

def test_every_role_box_builder_is_chainable_and_stores_its_axiom():
    t = dl.TBox()
    calls = [
        ("add_inverse_roles", ("p", "q"), "inverse_role_pairs", [("p", "q")]),
        ("add_role_chain", (("c1", "c2"), "c3"), "role_chains",
         [(("c1", "c2"), "c3")]),
        ("add_disjoint_roles", ("d1", "d2"), "disjoint_role_pairs",
         [("d1", "d2")]),
        ("add_symmetric_role", ("y",), "symmetric_roles", {"y"}),
        ("add_asymmetric_role", ("a",), "asymmetric_roles", {"a"}),
        ("add_reflexive_role", ("x",), "reflexive_roles", {"x"}),
        ("add_irreflexive_role", ("i",), "irreflexive_roles", {"i"}),
        ("add_functional_role", ("f",), "functional_roles", {"f"}),
        ("add_inverse_functional_role", ("g",), "inverse_functional_roles",
         {"g"}),
    ]
    for builder, args, field, expected in calls:
        assert getattr(t, builder)(*args) is t, f"{builder} is not chainable"
        assert getattr(t, field) == expected, builder


def test_disjoint_roles_is_all_pairs_sorted_and_deduplicated():
    # OWL 2 direct semantics: Pi^I ∩ Pj^I = ∅ for every i < j, i.e. ALL C(k,2)
    # pairs. Three roles therefore give THREE axioms, not two: disjointness has
    # no transitive closure, so a consecutive chain is strictly weaker.
    t = dl.TBox().add_disjoint_roles("r", "s", "t")
    assert t.disjoint_role_pairs == [("r", "s"), ("r", "t"), ("s", "t")]
    # Each pair stored SORTED, so the spelling order does not change the TBox
    # and TBox equality is spelling-independent.
    assert (dl.TBox().add_disjoint_roles("s", "r")
            == dl.TBox().add_disjoint_roles("r", "s"))
    # Repeating a pair across calls adds nothing; repeating a NAME within one
    # call is the degenerate (P, P) — "P is empty" — and IS kept.
    assert (dl.TBox().add_disjoint_roles("r", "s").add_disjoint_roles("s", "r")
            .disjoint_role_pairs == [("r", "s")])
    assert dl.TBox().add_disjoint_roles("r", "r").disjoint_role_pairs == [("r", "r")]
    assert dl.concept_satisfiable(dl.Exists("r", dl.Top()),
                                  dl.TBox().add_disjoint_roles("r", "r")) is False


def test_equivalent_roles_is_consecutive_mutual_inclusions():
    # The CONTRAST with disjointness: ⊑ is transitive, so P1 ≡ P2 ≡ P3 already
    # entails P1 ≡ P3 and the consecutive pairs suffice — no new field at all.
    t = dl.TBox().add_equivalent_roles("r", "s", "t")
    assert t.role_inclusions == [("r", "s"), ("s", "r"), ("s", "t"), ("t", "s")]
    assert t.internalized() == []


def test_role_box_argument_validation():
    # B1: every one of these used to be ACCEPTED, and rbox_to_fol then printed
    # an atom that looks like an axiom and is not (measured before 0.30.0:
    # `∀x ∀y (('r', 's')(x, y) → t(x, y))`).
    with pytest.raises(dl.RoleExpressionError, match="add_role_chain"):
        dl.TBox().add_role_inclusion(("r", "s"), "t")
    with pytest.raises(dl.RoleExpressionError, match="add_role_chain"):
        dl.TBox().add_role_inclusion("t", ["r", "s"])
    # Trans(r⁻) IS Trans(r) — transitivity is preserved by taking the converse —
    # so the contorted image would be an obfuscated spelling of an axiom the
    # caller can write properly; the message names that spelling.
    with pytest.raises(dl.RoleExpressionError, match="'r' instead"):
        dl.TBox().add_transitive_role(dl.InverseRole("r"))
    for builder in ("add_symmetric_role", "add_asymmetric_role",
                    "add_reflexive_role", "add_irreflexive_role",
                    "add_functional_role", "add_inverse_functional_role"):
        with pytest.raises(dl.RoleExpressionError, match="InverseRole"):
            getattr(dl.TBox(), builder)(dl.InverseRole("r"))
    with pytest.raises(dl.RoleExpressionError, match="InverseRole"):
        dl.TBox().add_role_chain((dl.InverseRole("r"), "s"), "t")
    # ... but an InverseRole on either side of an INCLUSION is accepted: r ⊑ s⁻
    # is a genuinely different axiom from r ⊑ s, and it has a correct image.
    dl.TBox().add_role_inclusion("r", dl.InverseRole("s"))
    dl.TBox().add_role_inclusion(dl.InverseRole("r"), "s")
    # arity
    with pytest.raises(dl.RoleExpressionError, match="add_role_inclusion"):
        dl.TBox().add_role_chain(("r",), "t")
    with pytest.raises(dl.RoleExpressionError, match="at least 2"):
        dl.TBox().add_disjoint_roles("r")
    with pytest.raises(dl.RoleExpressionError, match="at least 2"):
        dl.TBox().add_equivalent_roles("r")
    # a value that is no kind of role at all
    with pytest.raises(dl.RoleExpressionError, match="int"):
        dl.TBox().add_transitive_role(3)


def test_rbox_to_fol_is_the_second_line_of_defence():
    # The convention nnf and _reject_beyond_alc already follow: a TBox whose
    # role-box list was assembled or mutated BY HAND must fail loudly rather
    # than print a nonsense atom. This is the exact pre-0.30.0 symptom.
    t = dl.TBox()
    t.role_inclusions.append((("r", "s"), "t"))
    with pytest.raises(dl.RoleExpressionError, match="add_role_chain"):
        rbox_to_fol(t)
    t2 = dl.TBox()
    t2.transitive_roles.add(dl.InverseRole("r"))
    with pytest.raises(dl.RoleExpressionError, match="InverseRole"):
        rbox_to_fol(t2)
    t3 = dl.TBox()
    t3.symmetric_roles.add("owl:topObjectProperty")
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        rbox_to_fol(t3)


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
    from unicode_logic_kit.dl.tableau import _RBox

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
    formula = Implies(FAnd(tbox_to_fol(t, concept_inclusions_only=True), rbox_to_fol(t)),
                      subsumption_to_fol(sub, sup))
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

# --------------------------------------------------------------------------- #
# The three clash conditions, hand-derived. Each case was measured before 0.30.0
# first: the kit could not express the axiom at all, and with the hierarchy
# alone (or no role box) the verdict is the OPPOSITE of the one asserted here.
# --------------------------------------------------------------------------- #

def test_disjoint_roles_with_hierarchy_makes_exists_unsatisfiable():
    # By hand: r ⊑ s makes every r-pair an s-pair, so an r-pair is in BOTH r
    # and s — which Disj(r, s) forbids. Hence r denotes the empty relation and
    # ∃r.⊤ has no instance. The tableau sees it as an edge pattern: the
    # ∃-rule's generated edge (a, r, _x1) entails both r and s between the
    # same source and destination, and the disjoint pair closes the branch.
    t = dl.TBox().add_role_inclusion("r", "s").add_disjoint_roles("r", "s")
    assert dl.concept_satisfiable(dl.Exists("r", dl.Top()), t) is False
    assert dl.subsumes(dl.Exists("r", dl.Top()), dl.Bottom(), t) is True
    # With the hierarchy ALONE it is satisfiable — the role box is doing the work.
    assert dl.concept_satisfiable(dl.Exists("r", dl.Top()),
                                  dl.TBox().add_role_inclusion("r", "s")) is True
    # Cross-checked against the independent Z3 route over the same axioms.
    assert _z3_subsumes(dl.Exists("r", dl.Top()), dl.Bottom(), t) is True


def test_asymmetric_role_two_cycle_abox_is_inconsistent():
    # Asym(r) is ∀x ∀y (r(x,y) → ¬r(y,x)); instantiated at (a, b) it refutes
    # the second assertion. [measured before 0.30.0: True — nothing looked at the
    # edge pattern, because the axiom could not be written.]
    ab = dl.ABox().assert_role("a", "b", "r").assert_role("b", "a", "r")
    assert dl.abox_consistent(ab, dl.TBox().add_asymmetric_role("r")) is False
    assert dl.abox_consistent(ab, dl.TBox()) is True
    # The same, through the role HIERARCHY: the pattern must be closed under
    # ⊑*, so two different sub-roles of an asymmetric r still clash.
    t = (dl.TBox().add_role_inclusion("r1", "r").add_role_inclusion("r2", "r")
         .add_asymmetric_role("r"))
    ab2 = dl.ABox().assert_role("a", "b", "r1").assert_role("b", "a", "r2")
    assert dl.abox_consistent(ab2, t) is False


def test_asymmetric_role_forbids_a_self_loop():
    # The ENTAILED irreflexivity: instantiate ∀x ∀y (r(x,y) → ¬r(y,x)) at
    # y := x to get r(x,x) → ¬r(x,x), hence ¬r(x,x). So the degenerate x = y
    # case of the clash condition is not an optional extra.
    ab = dl.ABox().assert_role("a", "a", "r")
    assert dl.abox_consistent(ab, dl.TBox().add_asymmetric_role("r")) is False


def test_irreflexive_role_self_loop_abox_is_inconsistent():
    # Irr(r) is ∀x ¬r(x,x) — one variable. [measured before 0.30.0: True.]
    ab = dl.ABox().assert_role("a", "a", "r")
    assert dl.abox_consistent(ab, dl.TBox().add_irreflexive_role("r")) is False
    assert dl.abox_consistent(ab, dl.TBox()) is True
    # ... and an edge between two NAMES stays consistent, with or without a
    # unique name assumption: a model may read the two names apart.
    assert dl.abox_consistent(dl.ABox().assert_role("a", "b", "r"),
                              dl.TBox().add_irreflexive_role("r")) is True


def test_irreflexive_role_catches_a_self_loop_created_by_the_at_most_merge():
    # THE case that proves the clash condition is consulted AFTER a merge
    # rather than only at branch setup. By hand: a : ≤1 r.⊤ with r-neighbours
    # b and c, which are not forced distinct, so the ≤-rule merges them; the
    # survivor then carries r(b, b) from the asserted edge b —r→ c, and
    # irreflexivity closes the branch. Every candidate merge is tried and all
    # fail, so the knowledge base is INCONSISTENT.
    # [measured before 0.30.0: True — the merge created a self-loop nothing read.]
    ab = (dl.ABox().assert_role("a", "b", "r").assert_role("a", "c", "r")
          .assert_role("b", "c", "r")
          .assert_concept("a", dl.AtMost(1, "r", dl.Top())))
    assert dl.abox_consistent(ab, dl.TBox()) is True
    assert dl.abox_consistent(ab, dl.TBox().add_irreflexive_role("r")) is False


def test_asymmetric_role_still_terminates_under_an_unbounded_chain():
    # The blocking/unravelling regression. ⊤ ⊑ ∃r.⊤ forces an infinite
    # r-chain, and the LOOPED finite model subset blocking usually reads off
    # (the blocked node's edge bent back to its blocker) contains r(a, _x1) AND
    # r(_x1, a), so it violates asymmetry — while the infinite UNRAVELLED tree
    # model does not. The tableau's boolean must be the latter's: satisfiable.
    # An implementer who checks the rule against the looped model concludes it
    # is unsound and weakens it; this is what stops that.
    t = dl.TBox().add(dl.Top(), dl.Exists("r", dl.Top())).add_asymmetric_role("r")
    assert dl.concept_satisfiable(dl.Top(), t) is True
    assert dl.concept_satisfiable(A, t) is True
    # the same for irreflexivity, whose looped model has the self-loop
    t2 = dl.TBox().add(dl.Top(), dl.Exists("r", dl.Top())).add_irreflexive_role("r")
    assert dl.concept_satisfiable(dl.Top(), t2) is True


def test_functional_role_merges_two_successors():
    # Func(r) IS the GCI ⊤ ⊑ ≤1 r.⊤. By hand: x has an r-successor in A and one
    # in B; at most one r-successor exists, so they are the SAME individual,
    # which is therefore in A ⊓ B. [measured before 0.30.0: True with the GCI
    # written out by hand, False with no role box — so the internalisation is
    # what carries it.]
    t = dl.TBox().add_functional_role("r")
    sub = dl.And(dl.Exists("r", A), dl.Exists("r", B))
    sup = dl.Exists("r", dl.And(A, B))
    assert dl.subsumes(sub, sup, t) is True
    assert dl.subsumes(sub, sup, dl.TBox()) is False
    assert _z3_subsumes(sub, sup, t) is True
    # and it reaches GENERATED individuals too, not only the root: the ∃-rule
    # copies the internalised list onto every fresh node, so the same
    # subsumption holds one step down.
    nested_sub = dl.Exists("s", sub)
    nested_sup = dl.Exists("s", sup)
    assert dl.subsumes(nested_sub, nested_sup, t) is True


def test_functional_role_with_distinct_successors_is_inconsistent():
    # ... and the ABox mirror: two r-successors FORCED distinct contradict
    # functionality, while without the distinctness they simply merge (there is
    # no unique name assumption).
    t = dl.TBox().add_functional_role("r")
    ab = dl.ABox().assert_role("a", "b", "r").assert_role("a", "c", "r")
    assert dl.abox_consistent(ab, t) is True
    assert dl.abox_consistent(ab.assert_distinct("b", "c"), t) is False


def test_equivalent_roles_subsume_both_ways():
    # Two mutual inclusions, so _RBox's reflexive-transitive closure makes the
    # two roles share one ancestor set — the ⊑-cycle case
    # test_role_inclusion_cycle_collapses_into_equivalence_class already covers.
    t = dl.TBox().add_equivalent_roles("r", "s")
    assert dl.subsumes(dl.Exists("r", A), dl.Exists("s", A), t) is True
    assert dl.subsumes(dl.Exists("s", A), dl.Exists("r", A), t) is True
    assert dl.subsumes(dl.Exists("r", A), dl.Exists("s", A), dl.TBox()) is False
    # non-consecutive pair of a three-role equivalence, which is what makes the
    # consecutive-chain decomposition sound
    t3 = dl.TBox().add_equivalent_roles("r", "s", "t")
    assert dl.subsumes(dl.Exists("r", A), dl.Exists("t", A), t3) is True


# --------------------------------------------------------------------------- #
# The six refused role-box kinds: refused BY NAME, from every entry point, and
# still answered by the FOL route. This is rule 2 made checkable for the half
# of the role box the tableau does not decide.
# --------------------------------------------------------------------------- #

_REFUSED_ROLE_BOXES = [
    ("inverse-pair", lambda: dl.TBox().add_inverse_roles("p", "q"),
     "InverseObjectProperties"),
    ("chain", lambda: dl.TBox().add_role_chain(("p", "q"), "t"),
     "ObjectPropertyChain"),
    ("symmetric", lambda: dl.TBox().add_symmetric_role("p"),
     "SymmetricObjectProperty"),
    ("reflexive", lambda: dl.TBox().add_reflexive_role("p"),
     "ReflexiveObjectProperty"),
    ("inverse-functional", lambda: dl.TBox().add_inverse_functional_role("p"),
     "InverseFunctionalObjectProperty"),
]


@pytest.mark.parametrize("label, build, kind", _REFUSED_ROLE_BOXES,
                         ids=[c[0] for c in _REFUSED_ROLE_BOXES])
def test_tableau_refuses_each_unsupported_role_box_axiom_by_name(label, build, kind):
    # Every reasoning entry point must refuse. Counted from the code
    # (`_reject_role_box(` and `_reject_inputs(`): _reject_role_box is the first
    # statement of concept_satisfiable, abox_consistent and classify, and
    # _reject_inputs -- which calls it -- opens instance_retrieval, realize,
    # realize_all and classify. concept_unsatisfiable, subsumes, equivalent and
    # instance_check hold no guard and inherit it, which is the claim
    # test_dl_alc.py already makes for _reject_beyond_alc. The others carry
    # their own because inheriting is no guard when there is nothing to reduce
    # (an empty vocabulary or ABox); classify asks about PAIRS of named
    # concepts and so reaches subsumes only when the TBox names at least two --
    # it calls the guard itself, up front (tests/test_dl_data.py pins the
    # one-name case).
    t = build()
    ab = dl.ABox().assert_concept("a", A)
    calls = [
        lambda: dl.concept_satisfiable(A, t),
        lambda: dl.concept_unsatisfiable(A, t),
        lambda: dl.subsumes(A, B, t),
        lambda: dl.equivalent(A, B, t),
        lambda: dl.abox_consistent(ab, t),
        lambda: dl.instance_check(ab, "a", B, t),
        lambda: dl.instance_retrieval(ab, B, t),
        lambda: dl.realize(ab, "a", [A, B], t),
        lambda: dl.realize_all(ab, [A, B], t),
        # classify refuses with the TBox as it stands -- no second named concept
        # is needed to reach `subsumes`, because the guard runs first.
        lambda: dl.classify(t),
        lambda: dl.classify(t.add_equivalence(A, dl.Exists("p", B))),
    ]
    for call in calls:
        with pytest.raises(dl.UnsupportedAxiomError) as info:
            call()
        message = str(info.value)
        assert kind in message, f"the refusal must NAME the kind; got {message!r}"
        assert "Why" in message, (
            "the refusal must carry the construct's own reason and remedy, not "
            f"only its name; got {message!r}")
        for pointer in ("dl.owl_reasoner", "dl.kb_to_fol", "api.prove"):
            assert pointer in message


def test_an_inverse_role_in_a_role_inclusion_is_refused_by_name_too():
    # r ⊑ s⁻ is the I of SHIQ exactly as InverseObjectProperties is, but
    # SubObjectPropertyOf as a KIND is decided — so this is a condition on the
    # stored VALUE, not a table row, and it needs its own guard.
    t = dl.TBox().add_role_inclusion("r", dl.InverseRole("s"))
    for call in (lambda: dl.concept_satisfiable(A, t),
                 lambda: dl.subsumes(A, B, t),
                 lambda: dl.abox_consistent(dl.ABox(), t),
                 lambda: dl.instance_check(dl.ABox().assert_concept("a", A),
                                            "a", B, t)):
        with pytest.raises(dl.UnsupportedAxiomError) as info:
            call()
        message = str(info.value)
        assert "INVERSE role" in message and "s⁻" in message
        assert "subset blocking" in message
        for pointer in ("dl.rbox_to_fol", "dl.kb_to_fol", "dl.owl_reasoner"):
            assert pointer in message
    # ... and the FOL route renders it correctly, so the question has an answer
    assert rbox_to_fol(t).to_unicode_str() == "∀x ∀y (r(x, y) → s(y, x))"


def test_a_refused_role_box_is_still_answered_by_the_fol_route():
    # THE rule-2 divergence this package closes, in its original form. On
    # the pre-0.30.0 tree the caller's workaround for a property chain —
    # add_role_inclusion(('r','s'), 't') — was accepted silently and the
    # tableau returned False for a subsumption z3 PROVES. Now the tableau
    # refuses by name and the FOL route gives the right answer.
    t = dl.TBox().add_role_chain(("r", "s"), "t")
    sub = dl.Exists("r", dl.Exists("s", dl.Top()))
    sup = dl.Exists("t", dl.Top())
    with pytest.raises(dl.UnsupportedAxiomError, match="ObjectPropertyChain"):
        dl.subsumes(sub, sup, t)
    kb = kb_to_fol(t)
    assert _prove(subsumption_to_fol(sub, sup), kb.tbox_premises) == "proved"
    # and the workaround itself is now refused on the call that is wrong
    with pytest.raises(dl.RoleExpressionError, match="add_role_chain"):
        dl.TBox().add_role_inclusion(("r", "s"), "t")


# --------------------------------------------------------------------------- #
# OWL 2's own SIMPLE-role restriction (Structural Specification §11), which is
# what makes the three clash conditions EXACT rather than merely sound.
# --------------------------------------------------------------------------- #

# The four OWL 2 (§11) restricts to simple roles AND the tableau decides, so
# the public entry points reach the simple-role check. InverseFunctional is
# §11-restricted too, but it is a REFUSED kind, so `_reject_unsupported` fires
# first with the more specific message -- checked at the function level below.
_SIMPLE_RESTRICTED = [
    ("asymmetric", "add_asymmetric_role", ("r",), "AsymmetricObjectProperty"),
    ("irreflexive", "add_irreflexive_role", ("r",), "IrreflexiveObjectProperty"),
    ("functional", "add_functional_role", ("r",), "FunctionalObjectProperty"),
    ("disjoint", "add_disjoint_roles", ("r", "s"), "DisjointObjectProperties"),
]


@pytest.mark.parametrize("label, builder, args, kind", _SIMPLE_RESTRICTED,
                         ids=[c[0] for c in _SIMPLE_RESTRICTED])
def test_a_characteristic_on_a_transitive_role_is_refused_by_name(label, builder,
                                                                   args, kind):
    t = dl.TBox().add_transitive_role("r")
    getattr(t, builder)(*args)
    with pytest.raises(dl.NonSimpleRoleError) as info:
        dl.concept_satisfiable(A, t)
    message = str(info.value)
    assert kind in message, f"the refusal must name the OWL axiom; got {message!r}"
    assert "'r'" in message, "the refusal must name the offending ROLE"
    assert "NON-SIMPLE" in message


_SIMPLE_ROLE_ENTRY_POINTS = [
    ("concept_satisfiable", lambda t: dl.concept_satisfiable(A, t)),
    ("abox_consistent, empty ABox", lambda t: dl.abox_consistent(dl.ABox(), t)),
    ("abox_consistent, edges on the role",
     lambda t: dl.abox_consistent(dl.ABox().assert_role("a", "b", "t")
                                  .assert_role("b", "a", "t"), t)),
    ("instance_check", lambda t: dl.instance_check(dl.ABox(), "a", A, t)),
    ("instance_retrieval",
     lambda t: dl.instance_retrieval(dl.ABox().assert_concept("a", A), A, t)),
    ("subsumes", lambda t: dl.subsumes(A, B, t)),
]


@pytest.mark.parametrize("label, call", _SIMPLE_ROLE_ENTRY_POINTS,
                         ids=[c[0] for c in _SIMPLE_ROLE_ENTRY_POINTS])
def test_every_entry_point_reaches_the_simple_role_check(label, call):
    # The simple-role check is called from BOTH deciding entry points, and only
    # concept_satisfiable's call was covered: removing abox_consistent's left the
    # suite green and made it answer, silently, about a non-simple role.
    #
    # Trans(t) with Irr(t): Irreflexive on a role that is composite. The witness
    # below is t(a, b), t(b, a): by transitivity t(a, a), which Irr(t) forbids,
    # so the knowledge base has NO model -- the right verdict is "inconsistent",
    # and the tableau (which never materialises the derived edge) would say
    # CONSISTENT. Refusing by name is the only honest answer.
    tbox = dl.TBox().add_transitive_role("t").add_irreflexive_role("t")
    with pytest.raises(dl.NonSimpleRoleError, match="IrreflexiveObjectProperty"):
        call(tbox)


def test_the_witness_of_the_simple_role_check_really_is_inconsistent():
    # The hand-derivation above, checked by the other route: the FOL image
    # proves the knowledge base inconsistent, so a silent "consistent" from the
    # tableau would have been a WRONG answer and not merely an unproved one.
    tbox = dl.TBox().add_transitive_role("t").add_irreflexive_role("t")
    abox = dl.ABox().assert_role("a", "b", "t").assert_role("b", "a", "t")
    kb = kb_to_fol(tbox, abox)
    assert api.prove(FNot(kb.formula), list(kb.axioms),
                     timeout=TIMEOUT_MS).status == "proved"


def test_inverse_functional_is_simple_role_restricted_too():
    # The refusal ORDER is deliberate: a refused KIND is refused by name before
    # anything else is checked, because that message is the more specific one
    # (the caller never wrote a number restriction). The simple-role check
    # still covers it, which is what this asserts at the function level.
    from unicode_logic_kit.dl.tableau import _check_simple_role_box

    t = dl.TBox().add_transitive_role("r").add_inverse_functional_role("r")
    with pytest.raises(dl.UnsupportedAxiomError,
                       match="InverseFunctionalObjectProperty"):
        dl.concept_satisfiable(A, t)
    with pytest.raises(dl.NonSimpleRoleError,
                       match="InverseFunctionalObjectProperty"):
        _check_simple_role_box(t, _RBox.from_tbox(t))


def test_the_non_simple_direction_is_the_right_way_round():
    # A COMPOSITE SUB-role is what makes the super-role non-simple: Trans(r)
    # with r ⊑ P makes P non-simple, while P ⊑ r does NOT. Getting this ⊑*
    # direction backwards silently permits a combination that is undecidable
    # (Horrocks, Sattler & Tobies 1999).
    bad = dl.TBox().add_transitive_role("r").add_role_inclusion("r", "P")
    bad.add_asymmetric_role("P")
    with pytest.raises(dl.NonSimpleRoleError, match="'P'"):
        dl.concept_satisfiable(A, bad)
    ok = dl.TBox().add_transitive_role("r").add_role_inclusion("P", "r")
    ok.add_asymmetric_role("P")
    assert dl.concept_satisfiable(A, ok) is True


def test_a_chain_super_role_is_composite_for_the_simple_role_check():
    # OWL 2 §11's "composite" is transitive OR a chain super-role, and
    # _is_simple_role reads both from one place. Checked at the _RBox level
    # because the tableau's CHAIN refusal fires first at the public entry
    # points — a more specific message for the same TBox, and the right one.
    t = dl.TBox().add_role_chain(("p", "q"), "t")
    rbox = _RBox.from_tbox(t)
    assert _is_simple_role("t", rbox) is False
    assert _is_simple_role("p", rbox) is True
    # ... and through the hierarchy: t ⊑ P makes P non-simple as well.
    t2 = dl.TBox().add_role_chain(("p", "q"), "t").add_role_inclusion("t", "P")
    rbox2 = _RBox.from_tbox(t2)
    assert _is_simple_role("P", rbox2) is False
    # The existing number-restriction guard widens with it, which is correct:
    # a chain super-role may carry no qualified number restriction either.
    from unicode_logic_kit.dl.tableau import _check_simple_roles
    with pytest.raises(dl.NonSimpleRoleError, match="number restriction"):
        _check_simple_roles([dl.AtMost(1, "t", dl.Top())], rbox)


def test_the_simple_role_check_runs_on_the_external_route_too():
    # The kit's OWN error, with the kit's OWN message, on every route — rather
    # than surfacing as a HermiT error here and a tableau error there.
    t = dl.TBox().add_transitive_role("r").add_functional_role("r")
    with pytest.raises(dl.NonSimpleRoleError, match="FunctionalObjectProperty"):
        dl.external_subsumes(A, B, t)


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


# Every role-box axiom kind, with the FOL image DERIVED BY HAND from the OWL 2
# direct semantics (Structural Specification / Direct Semantics §2.3.2) in the
# comment, never read off what the code printed. Role names are UPPER-case
# because the kit's PREDICATE terminal is: that is a property of the
# vocabulary, not of the image (see tests/test_printed_text_reads_back.py), and
# it lets every string below be checked for reading back as well.
_RBOX_IMAGES = [
    # P^I ⊆ Q^I as sets of PAIRS, so the closure is over two variables.
    ("inclusion", lambda t: t.add_role_inclusion("R", "S"),
     "∀x ∀y (R(x, y) → S(x, y))"),
    # P^I transitive. Three variables; this IS the chain R ∘ R ⊑ R, which is
    # why the chain image below reuses exactly these three names.
    ("transitive", lambda t: t.add_transitive_role("R"),
     "∀x ∀y ∀z (R(x, y) ∧ R(y, z) → R(x, z))"),
    # P^I ∩ Q^I = ∅: no pair is in both.
    ("disjoint", lambda t: t.add_disjoint_roles("P", "Q"),
     "∀x ∀y ¬(P(x, y) ∧ Q(x, y))"),
    # <x,y> ∈ P^I implies <y,x> ∉ P^I. Entails irreflexivity (y := x).
    ("asymmetric", lambda t: t.add_asymmetric_role("R"),
     "∀x ∀y (R(x, y) → ¬R(y, x))"),
    # <x,x> ∉ P^I. ONE variable and no second quantifier — the only role-box
    # image here that is not a two- or three-variable sentence, which is
    # exactly how an implementer copying the asymmetry case gets it wrong.
    ("irreflexive", lambda t: t.add_irreflexive_role("R"), "∀x ¬R(x, x)"),
    # P^I is functional. The direct-semantics equality sentence, not the Count
    # image of ≤1 R.⊤; the two are interderivable and the tableau uses the
    # latter, so the cross-check is unaffected.
    ("functional", lambda t: t.add_functional_role("R"),
     "∀x ∀y ∀z (R(x, y) ∧ R(x, z) → y = z)"),
    # (P)^OP = ((Q)^OP)^-, i.e. <x,y> ∈ P^I iff <y,x> ∈ Q^I. ONE biconditional,
    # because the axiom is an EQUALITY of relations, not two inclusions.
    ("inverse-pair", lambda t: t.add_inverse_roles("P", "Q"),
     "∀x ∀y (P(x, y) ↔ Q(y, x))"),
    # <x,y> ∈ P^I implies <y,x> ∈ P^I. The implication, not a biconditional:
    # the converse implication is the same sentence with x and y renamed.
    ("symmetric", lambda t: t.add_symmetric_role("R"),
     "∀x ∀y (R(x, y) → R(y, x))"),
    # <x,x> ∈ P^I for every x of the (never empty) domain. FORCES an edge
    # rather than forbidding one, which is why it is the expensive one.
    ("reflexive", lambda t: t.add_reflexive_role("R"), "∀x R(x, x)"),
    # ((P)^OP)^- is functional, i.e. ≤1 P⁻.⊤. The argument ORDER of the two
    # body atoms is the only difference from functionality, and the whole
    # content of the axiom.
    ("inverse-functional", lambda t: t.add_inverse_functional_role("R"),
     "∀x ∀y ∀z (R(y, x) ∧ R(z, x) → y = z)"),
    # For every y0, y1, y2 with <y0,y1> ∈ P1^I and <y1,y2> ∈ P2^I we have
    # <y0,y2> ∈ Q^I.
    ("chain", lambda t: t.add_role_chain(("P1", "P2"), "Q"),
     "∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z))"),
]


@pytest.mark.parametrize("label, build, expected", _RBOX_IMAGES,
                         ids=[c[0] for c in _RBOX_IMAGES])
def test_rbox_to_fol_hand_checked_per_axiom_kind(label, build, expected):
    t = dl.TBox()
    build(t)
    formula = rbox_to_fol(t)
    assert formula.to_unicode_str() == expected
    # Everything the kit PRINTS must read back, and the re-parse must be the
    # same formula (these images bind only x, y, z — all legal VARIABLE
    # terminals — so there is no generated-variable shape involved at all).
    parsed = api.parse_any(expected)
    assert parsed.ok, f"{label}: the kit printed text it cannot parse"
    assert parsed.formula == formula


def test_rbox_to_fol_renders_an_inverse_role_inclusion_correctly():
    # B1. The standard translation of r⁻ swaps the atom's argument order and
    # nothing else — translate._role_atom has done exactly that for every
    # concept restriction since 0.26, and _rbox_axioms simply did not call it.
    # Measured before 0.30.0, both sides printed `InverseRole(role='s')(x, y)`.
    for build, expected in [
        (lambda: dl.TBox().add_role_inclusion("R", dl.InverseRole("S")),
         "∀x ∀y (R(x, y) → S(y, x))"),
        (lambda: dl.TBox().add_role_inclusion(dl.InverseRole("R"), "S"),
         "∀x ∀y (R(y, x) → S(x, y))"),
    ]:
        formula = rbox_to_fol(build())
        assert formula.to_unicode_str() == expected
        assert api.parse_any(expected).ok
        assert api.parse_any(expected).formula == formula


def test_chain_axiom_variable_shape():
    # n = 2 uses exactly x, y, z — the same three transitivity uses, because
    # transitivity IS the chain r ∘ r ⊑ r. Beyond three positions the kit has
    # no fourth canonical name, so the rest are MINTED through
    # fol._identifiers.fresh_variables (x0, x1, …), the only shape the kit's
    # VARIABLE terminal accepts — never a hand-rolled "base_n".
    two = rbox_to_fol(dl.TBox().add_role_chain(("P1", "P2"), "Q")).to_unicode_str()
    assert two == "∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z))"
    three = rbox_to_fol(
        dl.TBox().add_role_chain(("P1", "P2", "P3"), "Q")).to_unicode_str()
    assert three == "∀x ∀y ∀z ∀x0 (P1(x, y) ∧ P2(y, z) ∧ P3(z, x0) → Q(x, x0))"
    four = rbox_to_fol(
        dl.TBox().add_role_chain(("P1", "P2", "P3", "P4"), "Q")).to_unicode_str()
    assert four == ("∀x ∀y ∀z ∀x0 ∀x1 "
                    "(P1(x, y) ∧ P2(y, z) ∧ (P3(z, x0) ∧ P4(x0, x1)) → Q(x, x1))")
    for text in (two, three, four):
        assert "_" not in text
        assert api.parse_any(text).ok, text


# The role box's fields, read off the axiom-kind table rather than listed here:
# the two tests below then go red automatically when a tenth field is added and
# a consumer is not updated, which is the one silent-weakening bug this package
# can introduce (forgetting a field in ONE of the ten consumers).
_ROLE_BOX_FIELDS = _holder_fields("tbox", part="side", layer="object")

_ROLE_BOX_SAMPLES = {
    "role_inclusions": lambda t: t.add_role_inclusion("R", "S"),
    "transitive_roles": lambda t: t.add_transitive_role("R"),
    "disjoint_role_pairs": lambda t: t.add_disjoint_roles("P", "Q"),
    "asymmetric_roles": lambda t: t.add_asymmetric_role("R"),
    "irreflexive_roles": lambda t: t.add_irreflexive_role("R"),
    "functional_roles": lambda t: t.add_functional_role("R"),
    "inverse_role_pairs": lambda t: t.add_inverse_roles("P", "Q"),
    "symmetric_roles": lambda t: t.add_symmetric_role("R"),
    "reflexive_roles": lambda t: t.add_reflexive_role("R"),
    "inverse_functional_roles": lambda t: t.add_inverse_functional_role("R"),
    "role_chains": lambda t: t.add_role_chain(("P1", "P2"), "Q"),
    # The two role-box kinds whose axiom carries a CLASS EXPRESSION; an atomic
    # filler keeps the sample one axiom with no accidental interaction, and the
    # complex-filler cases live in tests/test_dl_role_domain_range.py.
    "role_domains": lambda t: t.add_role_domain("R", dl.Atomic("C")),
    "role_ranges": lambda t: t.add_role_range("R", dl.Atomic("C")),
}


def test_every_role_box_field_has_a_sample_here():
    assert set(_ROLE_BOX_FIELDS) == set(_ROLE_BOX_SAMPLES), (
        "this file and dl.tableau._AXIOM_KINDS disagree about which TBox "
        f"fields are side axioms: {sorted(set(_ROLE_BOX_FIELDS) ^ set(_ROLE_BOX_SAMPLES))}")


@pytest.mark.parametrize("field", _ROLE_BOX_FIELDS)
def test_rbox_to_fol_reaches_every_role_box_field(field):
    # A field rbox_to_fol does not know about renders as the "no constraint"
    # tautology — a SILENT weakening, not an error. So: a TBox carrying only
    # that field must render something that is NOT the tautology.
    t = dl.TBox()
    _ROLE_BOX_SAMPLES[field](t)
    formula = rbox_to_fol(t)
    assert is_valid(formula, timeout=TIMEOUT_MS) is False, (
        f"rbox_to_fol dropped {field}: it rendered a tautology for a TBox that "
        f"carries an axiom, so the role box is silently missing from "
        f"kb_to_fol(...).axioms as well")
    assert len(kb_to_fol(t).side_axioms) == 1


@pytest.mark.parametrize("field", _ROLE_BOX_FIELDS)
def test_tbox_to_fol_refuses_every_role_box_field(field):
    # The other half: tbox_to_fol renders the CONCEPT inclusions only, so a
    # TBox carrying a side axiom must raise rather than hand back a weaker
    # theory. The condition is derived from the table (TBox.has_side_axioms),
    # which is what lets this be parametrised over it.
    t = dl.TBox()
    _ROLE_BOX_SAMPLES[field](t)
    assert t.has_side_axioms() is True
    with pytest.raises(dl.RoleBoxOmittedError, match="kb_to_fol"):
        tbox_to_fol(t)
    tbox_to_fol(t, concept_inclusions_only=True)      # the explicit opt-out


# --------------------------------------------------------------------------- #
# Differential oracle vs Z3 (test_oracle item 2): tableau vs an independent FOL
# validity check over the SAME axioms, translated by a structurally unrelated code
# path (dl.translate, not dl.tableau).
# --------------------------------------------------------------------------- #

def _z3_subsumes(sub, sup, tbox: dl.TBox) -> bool:
    # The role box is conjoined on purpose here, and the opt-out says so: this is the
    # single-formula spelling of "the GCIs and the role box entail the subsumption".
    # (The kit's convention for a KNOWLEDGE BASE is the premise list of
    # kb_to_fol — see the kb_to_fol differentials further down.)
    formula = Implies(FAnd(tbox_to_fol(tbox, concept_inclusions_only=True), rbox_to_fol(tbox)),
                      subsumption_to_fol(sub, sup))
    return is_valid(formula, timeout=TIMEOUT_MS)


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
    """A random role box over 2-3 roles, carrying only the kinds the tableau
    DECIDES — role inclusions, transitivity, equivalence, and the four axioms
    OWL 2 restricts to simple roles.

    The four simple-role-restricted axioms are added only where that
    restriction actually holds: a characteristic on a non-simple role is
    refused by name (``NonSimpleRoleError``), and the differential would then
    measure the refusal rather than the two routes' verdicts. Equivalence goes
    in BEFORE the simple roles are computed, because an equivalence is two role
    inclusions and can make a previously-simple role non-simple.
    """
    t = dl.TBox()
    pairs = [(a, b) for a in _ROLES for b in _ROLES if a != b]
    rng.shuffle(pairs)
    for a, b in pairs[:rng.randint(0, 2)]:
        t.add_role_inclusion(a, b)
    for role in rng.sample(_ROLES, rng.randint(0, 2)):
        t.add_transitive_role(role)
    if rng.random() < 0.2:
        a, b = rng.sample(_ROLES, 2)
        t.add_equivalent_roles(a, b)
    rbox = _RBox.from_tbox(t)
    simple = [role for role in _ROLES if _is_simple_role(role, rbox)]
    if simple and rng.random() < 0.45:
        getattr(t, rng.choice(["add_asymmetric_role", "add_irreflexive_role",
                                "add_functional_role"]))(rng.choice(simple))
    if len(simple) >= 2 and rng.random() < 0.3:
        a, b = rng.sample(simple, 2)
        t.add_disjoint_roles(a, b)
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
# Manchester syntax: the one-line role-box frames.
# --------------------------------------------------------------------------- #

def test_manchester_role_axiom_subproperty():
    assert dl.parse_manchester_role_axiom("hasChild SubPropertyOf hasDescendant") == (
        "subproperty", "hasChild", "hasDescendant")
    assert dl.parse_manchester_role_axiom("hasChild SubPropertyOf: hasDescendant") == (
        "subproperty", "hasChild", "hasDescendant")


def test_manchester_role_axiom_transitive():
    assert dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive") == (
        "transitive", "hasDescendant")


@pytest.mark.parametrize("keyword, tag", [
    ("SubPropertyOf", "subproperty"),
    ("EquivalentTo", "equivalentproperty"),
    ("InverseOf", "inverse"),
    ("DisjointWith", "disjoint"),
])
def test_manchester_role_axiom_every_binary_frame(keyword, tag):
    # Each of the four binary frames, with and without the W3C grammar's
    # trailing colon, exactly like SubClassOf/SubClassOf:.
    assert dl.parse_manchester_role_axiom(f"p {keyword} q") == (tag, "p", "q")
    assert dl.parse_manchester_role_axiom(f"p {keyword}: q") == (tag, "p", "q")


@pytest.mark.parametrize("characteristic, tag", [
    ("Transitive", "transitive"),
    ("Symmetric", "symmetric"),
    ("Asymmetric", "asymmetric"),
    ("Reflexive", "reflexive"),
    ("Irreflexive", "irreflexive"),
    ("Functional", "functional"),
    ("InverseFunctional", "inversefunctional"),
])
def test_manchester_role_axiom_every_characteristic(characteristic, tag):
    # All SEVEN of OWL 2's object-property characteristics are READ: a parser
    # never refuses an axiom KIND (see "The axiom-kind table" in
    # dl/tableau.py). Three of them then make the TABLEAU refuse the knowledge
    # base by name -- tests/test_dl_route_agreement.py is where that is checked.
    assert dl.parse_manchester_role_axiom(
        f"r Characteristics: {characteristic}") == (tag, "r")


@pytest.mark.parametrize("axiom", [
    ("subproperty", "hasChild", "hasDescendant"),
    ("equivalentproperty", "hasSink", "hasOutput"),
    ("inverse", "partOf", "hasPart"),
    ("disjoint", "hasSink", "hasSource"),
    ("transitive", "partOf"),
    ("symmetric", "isConnectedTo"),
    ("asymmetric", "hasPhysicalInput"),
    ("reflexive", "overlapsWith"),
    ("irreflexive", "hasPhysicalInput"),
    ("functional", "hasState"),
    ("inversefunctional", "hasState"),
], ids=lambda a: a[0])
def test_manchester_role_axiom_round_trip(axiom):
    text = dl.role_axiom_to_manchester(*axiom)
    assert dl.parse_manchester_role_axiom(text) == axiom


def test_manchester_role_axiom_rejects_malformed_input():
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_role_axiom("hasChild SubPropertyOf")
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_role_axiom("not a role axiom at all")
    # An unknown characteristic word is still a syntax error naming itself --
    # the refusal that remains once all seven real ones are read.
    with pytest.raises(dl.ManchesterSyntaxError, match="Bogus"):
        dl.parse_manchester_role_axiom("r Characteristics: Bogus")
    with pytest.raises(dl.ManchesterSyntaxError, match="seven"):
        dl.parse_manchester_role_axiom("r Characteristics: Bogus")


def test_manchester_role_axiom_still_refuses_a_chain_by_name():
    # A property chain is read by parse_owl_functional, and the refusal says
    # so. The bare name 'o' is deliberately NOT promoted to a keyword here ...
    with pytest.raises(dl.ManchesterSyntaxError) as exc:
        dl.parse_manchester_role_axiom("r o s SubPropertyOf t")
    assert "PROPERTY CHAIN" in str(exc.value)
    assert "parse_owl_functional" in str(exc.value)
    assert "add_role_chain" in str(exc.value)


def test_bare_name_o_is_still_usable_in_a_class_expression():
    # ... and this is that decision's regression: a class literally named 'o'
    # keeps working, which promoting 'o' to a chain keyword would have broken.
    assert dl.parse_manchester("o and A") == dl.And(dl.Atomic("o"), A)
    assert dl.parse_manchester("o some B") == dl.Exists("o", B)


def test_manchester_role_axiom_refuses_the_n_ary_frame_slot_by_name():
    # DisjointWith needs ALL pairs, and a one-axiom parser returning one pair
    # would quietly produce a weaker theory -- so the n-ary comma-separated
    # frame slot is refused, naming the entry point that expands it correctly.
    with pytest.raises(dl.ManchesterSyntaxError) as exc:
        dl.parse_manchester_role_axiom("p DisjointWith q, r")
    assert "parse_owl_functional" in str(exc.value)
    assert "add_disjoint_roles" in str(exc.value)
    with pytest.raises(dl.ManchesterSyntaxError, match="add_equivalent_roles"):
        dl.parse_manchester_role_axiom("p EquivalentTo q, r")


@pytest.mark.parametrize("text", [
    "r SubPropertyOf owl:topObjectProperty",
    "owl:topObjectProperty SubPropertyOf r",
    "r Characteristics: Transitive".replace("r ", "owl:topObjectProperty "),
    "r DisjointWith owl:bottomObjectProperty",
])
def test_manchester_role_axiom_refuses_a_built_in_role_name_by_name(text):
    # The deliberate ASYMMETRY with parse_owl_functional, documented in both:
    # even the TAUTOLOGICAL super-role case is refused here, because a
    # single-axiom parser has no return shape for "this axiom is nothing".
    with pytest.raises(dl.ManchesterSyntaxError) as exc:
        dl.parse_manchester_role_axiom(text)
    message = str(exc.value)
    assert "BUILT-IN" in message
    if "topObjectProperty SubPropertyOf" not in text and "owl:top" in text:
        assert "parse_owl_functional" in message


def test_manchester_role_axioms_feed_every_tbox_builder():
    # End-to-end: every return shape names a builder that exists, and the
    # tag-to-builder mapping is the one the docstring promises.
    builders = {
        "subproperty": "add_role_inclusion", "equivalentproperty": "add_equivalent_roles",
        "inverse": "add_inverse_roles", "disjoint": "add_disjoint_roles",
        "transitive": "add_transitive_role", "symmetric": "add_symmetric_role",
        "asymmetric": "add_asymmetric_role", "reflexive": "add_reflexive_role",
        "irreflexive": "add_irreflexive_role", "functional": "add_functional_role",
        "inversefunctional": "add_inverse_functional_role",
    }
    for text in ("p SubPropertyOf q", "p EquivalentTo q", "p InverseOf q",
                 "p DisjointWith q", "p Characteristics: Transitive",
                 "p Characteristics: Symmetric", "p Characteristics: Asymmetric",
                 "p Characteristics: Reflexive", "p Characteristics: Irreflexive",
                 "p Characteristics: Functional",
                 "p Characteristics: InverseFunctional"):
        tag, *roles = dl.parse_manchester_role_axiom(text)
        tbox = getattr(dl.TBox(), builders[tag])(*roles)
        assert tbox != dl.TBox(), f"{text!r} built nothing"


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


# --------------------------------------------------------------------------- #
# The trap kb_to_fol closes: a TBox holds the concept inclusions AND the role
# box, tbox_to_fol renders ONLY the former, and a question asked against its
# output alone answers a weaker theory. Regression + the knowledge-base
# differentials (tableau vs api.prove over the kb_to_fol bundle).
# --------------------------------------------------------------------------- #

# A deliberately BOUNDED chain: z3 decides almost everything at once, the finite model
# finder supplies the countermodels z3 cannot (a FOL refutation can need a model that
# the SMT solver's quantifier handling does not produce). The default chain would
# continue into the resolution prover, which can spend a minute on one undecided query.
_PROVE_BACKENDS = ["z3", "modelfinder"]


def _prove(goal, premises) -> str:
    return api.prove(goal, list(premises), backends=_PROVE_BACKENDS,
                     timeout=TIMEOUT_MS).status


def _agreement(tableau_says: bool, status: str) -> str:
    """Compare a boolean tableau answer with a ``prove`` status, where ``proved`` means
    "the tableau answer is True"; ``refuted`` means False; anything else is undecided."""
    if status == "proved":
        return "agree" if tableau_says else "disagree"
    if status == "refuted":
        return "disagree" if tableau_says else "agree"
    return "undecided"


# Each case: the TBox, and a subsumption the tableau accepts only BECAUSE of the role box.
_TRAP_CASES = [
    # the minimal instance: a pure role hierarchy, no GCI at all (tbox_to_fol is a tautology)
    (dl.TBox().add_role_inclusion("hasChild", "hasDescendant"),
     dl.Exists("hasChild", dl.Top()), dl.Exists("hasDescendant", dl.Top())),
    # transitivity alone
    (dl.TBox().add_transitive_role("partOf"),
     dl.Exists("partOf", dl.Exists("partOf", Engine)), dl.Exists("partOf", Engine)),
    # a real GCI, whose conclusion then needs the hierarchy:  A ⊑ ∃hasChild.B  gives
    # A ⊑ ∃hasDescendant.B only through  hasChild ⊑ hasDescendant
    (dl.TBox().add(A, dl.Exists("hasChild", B)).add_role_inclusion("hasChild", "hasDescendant"),
     A, dl.Exists("hasDescendant", B)),
    # hierarchy and transitivity together
    (dl.TBox().add(A, dl.Exists("hasChild", dl.Exists("hasChild", B)))
              .add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant"),
     dl.And(A, dl.ForAll("hasDescendant", dl.Not(B))), dl.Bottom()),
]


@pytest.mark.parametrize("tbox, sub, sup", _TRAP_CASES,
                         ids=["hierarchy", "transitive", "gci+hierarchy", "all"])
def test_trap_concept_inclusions_alone_give_a_false_counterexample(tbox, sub, sup):
    # The recorded instance. The kit's own tableau accepts the subsumption ...
    assert dl.subsumes(sub, sup, tbox) is True
    goal = subsumption_to_fol(sub, sup)
    # ... and the looks-complete spelling "the TBox's FOL image entails it" REFUTES it:
    # tbox_to_fol never rendered the role box, so Z3 finds a model of the GCIs in which
    # the roles are unrelated. (The opt-out keyword is what lets this old spelling run.)
    gcis_only = tbox_to_fol(tbox, concept_inclusions_only=True)
    assert api.prove(Implies(gcis_only, goal), backends=["z3"]).status == "refuted"
    # The knowledge-base bundle carries the role box as premises and gets it right.
    assert _prove(goal, kb_to_fol(tbox).tbox_premises) == "proved"
    # ... and the silent spelling is gone: tbox_to_fol refuses to drop the role box unasked.
    with pytest.raises(dl.RoleBoxOmittedError, match="kb_to_fol"):
        tbox_to_fol(tbox)


def test_trap_same_hole_for_instance_checking_and_consistency():
    # KB-relative questions need the role box as much as subsumption does: dropping it
    # flips an entailed instance to "not entailed" (instance checking) and a clashing
    # knowledge base to "consistent" (consistency).
    t = (dl.TBox().add_role_inclusion("hasChild", "hasDescendant")
         .add_transitive_role("hasDescendant"))
    clash = (dl.ABox()
             .assert_concept("a", dl.ForAll("hasDescendant", Happy))
             .assert_role("a", "b", "hasChild").assert_role("b", "c", "hasChild")
             .assert_concept("c", dl.Not(Happy)))
    kb = kb_to_fol(t, clash)
    assert dl.abox_consistent(clash, t) is False
    assert _prove(FNot(kb.formula), kb.axioms) == "proved"            # inconsistent
    assert _prove(FNot(kb.formula), []) == "refuted"                  # role box dropped: "consistent"

    ab = dl.ABox().assert_concept("a", dl.ForAll("hasDescendant", Happy)).assert_role("a", "b", "hasChild")
    assert dl.instance_check(ab, "b", Happy, t) is True               # b is a hasDescendant of a
    kb2 = kb_to_fol(t, ab)
    goal = abox_to_fol(dl.ABox().assert_concept("b", Happy))          # π(Happy, b), b a constant
    assert _prove(goal, kb2.premises) == "proved"
    assert _prove(goal, [kb2.formula]) == "refuted"                   # role box dropped


# --- random knowledge bases --------------------------------------------------------------

_INDIVIDUALS = ["a", "b", "c"]


def _rand_kb_tbox(rng, max_gcis=3) -> dl.TBox:
    """A random TBox that ALWAYS carries a role hierarchy or transitivity (>= 1
    role inclusion or transitive role — the case the trap is about) plus
    0..max_gcis random GCIs.

    The fallback adds a role INCLUSION rather than a transitivity declaration:
    ``_rand_rbox`` may already have put a simple-role-restricted characteristic
    on a role, and declaring that role transitive would make it non-simple, so
    the query would be refused by name instead of answered. An inclusion is
    always safe here — with no composite role in the box, nothing can become
    non-simple.
    """
    t = _rand_rbox(rng)
    if not t.role_inclusions and not t.transitive_roles:
        a, b = rng.sample(_ROLES, 2)
        t.add_role_inclusion(a, b)
    for _ in range(rng.randint(0, max_gcis)):
        t.add(_rand_concept(1, rng), _rand_concept(1, rng))
    return t


def _role_ups(tbox: dl.TBox) -> dict:
    """``ups[r]`` = every role ``s`` with ``r ⊑* s`` under ``tbox``'s role inclusions
    (reflexive-transitive closure, computed here independently of the tableau's own)."""
    ups = {role: {role} for role in _ROLES}
    changed = True
    while changed:
        changed = False
        for lo, hi in tbox.role_inclusions:
            for role in _ROLES:
                if lo in ups[role] and hi not in ups[role]:
                    ups[role].add(hi)
                    changed = True
    return ups


def _rand_nnf_concept(depth, rng):
    """Like ``_rand_concept`` but negation only on atoms (so ``_weaken`` is monotone)."""
    if depth <= 0 or rng.random() < 0.3:
        atom = rng.choice(_RBOX_ATOMS)
        return atom if rng.random() < 0.7 else dl.Not(atom)
    k = rng.random()
    role = rng.choice(_ROLES)
    if k < 0.2:
        return dl.And(_rand_nnf_concept(depth - 1, rng), _rand_nnf_concept(depth - 1, rng))
    if k < 0.35:
        return dl.Or(_rand_nnf_concept(depth - 1, rng), _rand_nnf_concept(depth - 1, rng))
    if k < 0.75:
        return dl.Exists(role, _rand_nnf_concept(depth - 1, rng))
    return dl.ForAll(role, _rand_nnf_concept(depth - 1, rng))


def _weaken(concept, tbox: dl.TBox, ups: dict, rng):
    """A concept the role box makes (at least often) subsume ``concept``: ``∃r`` becomes
    ``∃s`` for a super-role ``s``, ``∀r`` becomes ``∀s`` for a SUB-role ``s``, a conjunct
    may be dropped, a disjunct added, and ``∃r.∃r.C`` collapses to ``∃r.C`` for a
    transitive ``r``. This aims random subsumption questions at the cases that HINGE on
    the role box — plain random pairs almost never do — and is only a generator: the
    verdict still comes from the tableau and the FOL route, never from this construction.
    """
    if isinstance(concept, dl.And):
        if rng.random() < 0.25:
            return _weaken(rng.choice([concept.left, concept.right]), tbox, ups, rng)
        return dl.And(_weaken(concept.left, tbox, ups, rng), _weaken(concept.right, tbox, ups, rng))
    if isinstance(concept, dl.Or):
        return dl.Or(_weaken(concept.left, tbox, ups, rng), _weaken(concept.right, tbox, ups, rng))
    if isinstance(concept, dl.Exists):
        inner = concept.concept
        if (concept.role in tbox.transitive_roles and isinstance(inner, dl.Exists)
                and inner.role == concept.role and rng.random() < 0.6):
            return dl.Exists(concept.role, _weaken(inner.concept, tbox, ups, rng))
        return dl.Exists(rng.choice(sorted(ups[concept.role])), _weaken(inner, tbox, ups, rng))
    if isinstance(concept, dl.ForAll):
        subs = sorted(role for role in _ROLES if concept.role in ups[role])
        return dl.ForAll(rng.choice(subs), _weaken(concept.concept, tbox, ups, rng))
    return concept


def _rand_kb_abox(rng, tbox: dl.TBox):
    """A random ABox, and (or ``None``) a query concept aimed at the same role-box axiom.

    Plain random ABoxes almost never hinge on the role box, so with probability 1/2 one
    pattern that does is added on top: a clash that exists only through ``lo ⊑ hi``
    (``a : ∃lo.A ⊓ ∀hi.¬A``), a transitive chain (``a : ∀tr.A``, an ``tr``-chain a→b→c,
    ``c : ¬A``), or a lone ``a : ∃lo.A`` whose aimed query is ``∃hi.A``. The tableau and the
    FOL route still decide every question independently — this only aims the generator.
    """
    ab = dl.ABox()
    for ind in _INDIVIDUALS:
        for _ in range(rng.randint(0, 2)):
            ab.assert_concept(ind, _rand_concept(2, rng))
    for x in _INDIVIDUALS:
        for y in _INDIVIDUALS:
            if x != y and rng.random() < 0.45:
                ab.assert_role(x, y, rng.choice(_ROLES))
    aimed_query = None
    if rng.random() < 0.5:
        patterns = []
        if tbox.role_inclusions:
            patterns += ["clash", "lone"]
        if tbox.transitive_roles:
            patterns += ["chain"]
        pattern = rng.choice(patterns)
        if pattern == "chain":
            tr = rng.choice(sorted(tbox.transitive_roles))
            ab.assert_concept("a", dl.ForAll(tr, A))
            ab.assert_role("a", "b", tr).assert_role("b", "c", tr)
            ab.assert_concept("c", dl.Not(A) if rng.random() < 0.5 else A)
            aimed_query = A
        else:
            lo, hi = rng.choice(tbox.role_inclusions)
            if pattern == "clash":
                ab.assert_concept("a", dl.And(dl.Exists(lo, A), dl.ForAll(hi, dl.Not(A))))
            else:
                ab.assert_concept("a", dl.Exists(lo, A))
                aimed_query = dl.Exists(hi, A)
    return ab, aimed_query


def run_kb_subsumption_differential(seed: int, n: int) -> dict:
    """``n`` random (TBox with role box, sub, sup) triples: ``dl.subsumes`` against
    ``api.prove(subsumption_to_fol, kb_to_fol(t).tbox_premises)``. Returns the tallies.

    Also counts the *trap*: cases the tableau accepts but the premises WITHOUT the role
    box (``[kb.tbox]`` alone) refute — the false counterexamples ``tbox_to_fol`` used to
    produce silently. A generator that never reaches the trap would prove nothing.
    """
    rng = random.Random(seed)
    stats = {"seed": seed, "cases": n, "agree": 0, "disagree": 0, "undecided": 0,
             "tableau_true": 0, "trap_false_counterexamples": 0}
    for _ in range(n):
        t = _rand_kb_tbox(rng)
        if rng.random() < 0.6:                    # aimed at the role box
            sub = _rand_nnf_concept(3, rng)
            sup = _weaken(sub, t, _role_ups(t), rng)
        else:                                     # plain random pair
            sub, sup = _rand_concept(2, rng), _rand_concept(2, rng)
        expected = dl.subsumes(sub, sup, t)
        kb, goal = kb_to_fol(t), subsumption_to_fol(sub, sup)
        outcome = _agreement(expected, _prove(goal, kb.tbox_premises))
        stats[outcome] += 1
        if outcome == "disagree":
            stats.setdefault("failures", []).append(
                f"incl={t.role_inclusions} trans={sorted(t.transitive_roles)} "
                f"gcis={[(a.to_unicode(), b.to_unicode()) for a, b in t.inclusions]} "
                f"sub={sub.to_unicode()} sup={sup.to_unicode()} tableau={expected}")
        if expected:
            stats["tableau_true"] += 1
            if _prove(goal, [kb.tbox]) == "refuted":
                stats["trap_false_counterexamples"] += 1
    return stats


def run_kb_abox_differential(seed: int, n: int) -> dict:
    """``n`` random (TBox with role box, ABox) pairs, each asked two questions:
    consistency (``dl.abox_consistent`` vs ``prove(Not(kb.formula), kb.axioms)``) and one
    instance check (``dl.instance_check`` vs ``prove(π(C, a), kb.premises)``).

    Counts the trap here too: clashes the premises WITHOUT the role box miss
    (``trap_missed_clashes``) and entailments they lose (``trap_lost_entailments``).
    """
    rng = random.Random(seed)
    stats = {"seed": seed, "kbs": n, "agree": 0, "disagree": 0, "undecided": 0,
             "inconsistent": 0, "consistent": 0, "entailed": 0, "not_entailed": 0,
             "trap_missed_clashes": 0, "trap_lost_entailments": 0}
    for _ in range(n):
        t = _rand_kb_tbox(rng, max_gcis=2)
        ab, aimed = _rand_kb_abox(rng, t)
        ind, query = rng.choice(_INDIVIDUALS), _rand_concept(1, rng)
        if aimed is not None:
            ind, query = ("c" if rng.random() < 0.3 else "a"), aimed
        kb = kb_to_fol(t, ab)

        consistent = dl.abox_consistent(ab, t)
        stats["consistent" if consistent else "inconsistent"] += 1
        outcome = _agreement(not consistent, _prove(FNot(kb.formula), kb.axioms))
        stats[outcome] += 1
        if outcome == "disagree":
            stats.setdefault("failures", []).append(f"consistency: tableau={consistent} {ab} {t}")
        if not consistent and _prove(FNot(kb.formula), []) == "refuted":
            stats["trap_missed_clashes"] += 1

        entailed = dl.instance_check(ab, ind, query, t)
        stats["entailed" if entailed else "not_entailed"] += 1
        goal = abox_to_fol(dl.ABox().assert_concept(ind, query))
        outcome = _agreement(entailed, _prove(goal, kb.premises))
        stats[outcome] += 1
        if outcome == "disagree":
            stats.setdefault("failures", []).append(
                f"instance {ind}:{query.to_unicode()} tableau={entailed} {ab} {t}")
        if entailed and consistent and _prove(goal, [kb.formula]) == "refuted":
            stats["trap_lost_entailments"] += 1
    return stats


def test_the_random_role_box_actually_reaches_the_new_fields():
    """The extension's own guard. ``_rand_rbox`` only adds a
    simple-role-restricted characteristic WHERE the restriction holds, so a
    bug in that condition could silently stop it adding any — and the two
    differentials below would then cover the same fragment they covered before,
    while looking as if they covered more.
    """
    rng = random.Random(20261005)
    seen = {field: 0 for field in _ROLE_BOX_SAMPLES}
    for _ in range(400):
        t = _rand_rbox(rng)
        for field in seen:
            if getattr(t, field):
                seen[field] += 1
    decided = ["role_inclusions", "transitive_roles", "disjoint_role_pairs",
               "asymmetric_roles", "irreflexive_roles", "functional_roles"]
    for field in decided:
        assert seen[field] >= 10, (seen, field)
    # ... and never a kind the tableau refuses: the differential compares
    # VERDICTS, and a refused role box has no tableau verdict to compare.
    for field in ("inverse_role_pairs", "symmetric_roles", "reflexive_roles",
                  "inverse_functional_roles", "role_chains"):
        assert seen[field] == 0, (seen, field)


def test_randomized_refused_role_boxes_refuse_and_the_fol_route_answers():
    """The refusal path, randomised. For 60 random knowledge bases, one REFUSED
    role-box axiom is added on top: the tableau must raise by name, and the FOL
    route must still produce a verdict for the same question.

    Without this the randomised battery would exercise only the half of the
    role box the tableau decides, and a refusal that stopped firing — or a FOL
    image that stopped being rendered — would go unnoticed.
    """
    rng = random.Random(20261006)
    refusals, answered = 0, 0
    for _ in range(60):
        t = _rand_kb_tbox(rng, max_gcis=1)
        label, build, kind = rng.choice(_REFUSED_ROLE_BOXES)
        refused = build()
        for field in _ROLE_BOX_SAMPLES:
            value = getattr(refused, field)
            if value and field not in ("role_inclusions", "transitive_roles"):
                getattr(t, field).extend(value) if isinstance(value, list) \
                    else getattr(t, field).update(value)
        sub, sup = _rand_concept(2, rng), _rand_concept(2, rng)
        with pytest.raises(dl.UnsupportedAxiomError, match=kind):
            dl.subsumes(sub, sup, t)
        refusals += 1
        # The FOL route renders the refused axiom and answers the question.
        kb = kb_to_fol(t)
        assert kind in {a.kind for a in kb.side_axioms}, label
        if _prove(subsumption_to_fol(sub, sup), kb.tbox_premises) in ("proved", "refuted"):
            answered += 1
    assert refusals == 60
    assert answered >= 55, answered


def test_differential_kb_to_fol_subsumption_vs_tableau():
    # Role hierarchies AND transitive roles AND GCIs, every case; fixed seed.
    stats = run_kb_subsumption_differential(seed=20261003, n=150)
    assert not stats.get("failures"), stats
    assert stats["disagree"] == 0
    # FOL entailment is only semi-decidable, so an undecided query is possible in principle
    # — it is neither agreement nor disagreement, and it must not quietly hollow the test out.
    assert stats["agree"] >= 0.95 * stats["cases"], stats
    # The battery must actually reach the trap, or it would not have caught it.
    assert stats["tableau_true"] >= 10, stats
    assert stats["trap_false_counterexamples"] >= 1, stats


def test_differential_kb_to_fol_consistency_and_instance_checking_vs_tableau():
    stats = run_kb_abox_differential(seed=20261004, n=120)
    assert not stats.get("failures"), stats
    assert stats["disagree"] == 0
    assert stats["agree"] >= 0.95 * (2 * stats["kbs"]), stats
    # all four outcomes occurred: the oracle is not trivially constant
    assert min(stats["inconsistent"], stats["consistent"],
               stats["entailed"], stats["not_entailed"]) >= 5, stats
    # ... and the battery reaches the trap for both questions
    assert stats["trap_missed_clashes"] >= 1 and stats["trap_lost_entailments"] >= 1, stats
