"""Tests for **ALCQ** (qualified number restrictions on top of ALC(H+S)):
``dl.AtLeast``/``dl.AtMost`` and the tableau's ≥/≤/choose completion rules — see
the "Qualified number restrictions" section of ``unicode_logic_kit.dl.tableau``'s
module docstring for the algorithm and its soundness/termination argument.

Four independent lines, matching the item's test oracle:

1. Hand-checked textbook cases (pigeonhole unsatisfiability, the ≥/≤/∀ interplay
   example, forced-merge and forced-clash-after-merge ABox scenarios, the "no
   unique name assumption" pair, role-hierarchy-aware neighbour counting, and the
   "simple roles" refusal), each with the derivation spelled out in a comment.
2. A differential oracle against the kit's OWN independent route: the NEW
   ``concept_to_fol``/``abox_to_fol`` translation, which routes AtLeast/AtMost
   through the already-tested ``fol.nodes.Count`` node and is decided by Z3
   (``unicode_logic_kit.atp.z3_models.is_satisfiable``) — a genuinely independent
   algorithm (SMT solving on the distinct-witnesses expansion) checking the
   hand-written tableau, exactly the pattern the project already uses for plain
   ALC and for the RBox extension. Both a random battery of small concepts
   (``dl.concept_satisfiable``) and a random battery of small ABoxes
   (``dl.abox_consistent``, exercising the merge/choose rules against named
   individuals and distinctness assertions) are checked.
3. Round-trip parse/render tests, both for the glyph syntax
   (``unicode_logic_kit.dl.parser``) and for OWL Manchester Syntax's ``min``/
   ``max``/``exactly`` (``unicode_logic_kit.dl.owl_manchester``), following the
   existing ``tests/test_dl_parser.py``/``tests/test_owl_manchester.py`` pattern.
4. Regression: ``instance_check``/``classify`` (pure reductions to
   ``abox_consistent``/``subsumes``) correctly inherit ALCQ support with no
   change to their own code, mirroring how ``tests/test_dl_rbox.py`` checks the
   same inheritance for the RBox extension.

``tests/test_dl_alc.py`` and ``tests/test_dl_rbox.py`` are left untouched by this
item (pure-ALC/ALCH+S inputs never mention AtLeast/AtMost, so every new tableau
rule here is a no-op for them — see the regression note in the module docstring).
"""

import functools
import random
import time

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.parser import parse_concept, ConceptSyntaxError
from unicode_logic_kit.dl.owl_manchester import parse_manchester, to_manchester, ManchesterSyntaxError
from unicode_logic_kit.dl.translate import (
    concept_to_fol, abox_to_fol, subsumption_to_fol, kb_to_fol,
)
from unicode_logic_kit.fol.nodes import (
    Quantifier, Variable, Constant, Count, Number, Atom, And as FAnd, Not as FNot,
)
from unicode_logic_kit.atp.z3_models import is_satisfiable

A, B, C, D = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C"), dl.Atomic("D")
r, s = "r", "s"

# Z3-backed calls take their timeout in MILLISECONDS. 30 s is the budget most of
# the other dl and owl test files give a Z3 call (the rest use 20 s or 60 s), and it
# is never shrunk to make a test fast: ``is_satisfiable`` turns a Z3 "unknown" into
# False, so a budget a loaded machine can exceed makes a differential here report a
# disagreement with the tableau that is only a timeout.
TIMEOUT_MS = 30000

# The three differential batteries below also guard the TABLEAU against a
# catastrophic slowdown (the merge-pair search degenerating to something
# exponential, say), and only the tableau: the seconds counted against this
# ceiling are the ones spent inside the in-house calls. A Z3 call that uses its
# whole TIMEOUT_MS budget would otherwise trip it, and report "too slow" for a
# solver timeout that has nothing to do with the tableau (and that
# ``is_satisfiable`` turns into False, which the assertion on the verdicts names
# on its own). Measured: each battery takes 0.01 to 0.02 s in the tableau, so the
# ceiling is a margin of three orders of magnitude, not a benchmark.
TABLEAU_BATTERY_CEILING_S = 10.0


# --------------------------------------------------------------------------- #
# Concept-level: constructor validation, rendering, NNF.
# --------------------------------------------------------------------------- #

def test_constructors_validate_n():
    dl.AtLeast(0, r, A)                      # n = 0 is allowed (a tautology, see nnf)
    dl.AtMost(0, r, A)
    for bad in (-1, -100):
        with pytest.raises(ValueError):
            dl.AtLeast(bad, r, A)
        with pytest.raises(ValueError):
            dl.AtMost(bad, r, A)


def test_render():
    assert dl.AtLeast(2, r, A).to_unicode() == "≥2 r.A"
    assert dl.AtMost(3, r, A).to_unicode() == "≤3 r.A"
    # the filler parenthesises exactly like Exists/ForAll's (same _PREC slot, 3)
    assert dl.AtLeast(1, r, dl.And(A, B)).to_unicode() == "≥1 r.(A ⊓ B)"
    assert dl.Not(dl.AtLeast(1, r, A)).to_unicode() == "¬≥1 r.A"


def test_nnf_duals():
    # ¬(≥n r.C) = ≤(n-1) r.C for n >= 1; ¬(≥0 r.C) = ⊥ (≥0 is a tautology).
    assert dl.nnf(dl.Not(dl.AtLeast(3, r, A))) == dl.AtMost(2, r, A)
    assert dl.nnf(dl.Not(dl.AtLeast(1, r, A))) == dl.AtMost(0, r, A)
    assert dl.nnf(dl.Not(dl.AtLeast(0, r, A))) == dl.Bottom()
    # ¬(≤n r.C) = ≥(n+1) r.C, always (≤ has no n=0 special case: ¬(≤0 r.C) = ≥1 r.C).
    assert dl.nnf(dl.Not(dl.AtMost(2, r, A))) == dl.AtLeast(3, r, A)
    assert dl.nnf(dl.Not(dl.AtMost(0, r, A))) == dl.AtLeast(1, r, A)
    # nnf recurses into the filler, but the duality does NOT negate the filler --
    # only the quantifier flips (≥n <-> ≤(n-1)/(n+1)); the filler concept C stays
    # exactly the same set of individuals on both sides, just nnf'd internally.
    assert dl.nnf(dl.AtLeast(2, r, dl.Not(dl.Not(A)))) == dl.AtLeast(2, r, A)
    assert dl.nnf(dl.Not(dl.AtLeast(2, r, dl.And(A, B)))) == dl.AtMost(1, r, dl.And(A, B))
    # double negation is idempotent through nnf, same as every other constructor
    assert dl.nnf(dl.nnf(dl.Not(dl.AtLeast(2, r, A)))) == dl.nnf(dl.Not(dl.AtLeast(2, r, A)))


# --------------------------------------------------------------------------- #
# Round-trip: glyph syntax (unicode_logic_kit.dl.parser).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.AtLeast(0, r, A),
    dl.AtLeast(2, r, A),
    dl.AtMost(0, r, A),
    dl.AtMost(3, r, A),
    dl.AtLeast(2, r, dl.And(A, dl.Not(B))),
    dl.AtMost(1, r, dl.Exists(s, A)),
    dl.And(dl.AtLeast(2, r, A), dl.AtMost(1, r, dl.Top())),
    dl.Not(dl.AtLeast(2, r, A)),
    dl.ForAll(r, dl.AtLeast(1, s, A)),
    dl.AtLeast(10, "hasChild", dl.Atomic("Doctor")),
], ids=lambda c: c.to_unicode())
def test_glyph_round_trip(concept):
    rendered = concept.to_unicode()
    assert parse_concept(rendered) == concept, rendered


def test_glyph_parser_requires_a_number_after_the_glyph():
    with pytest.raises(ConceptSyntaxError):
        parse_concept("≥r.A")           # missing the bound n
    with pytest.raises(ConceptSyntaxError):
        parse_concept("≥two r.A")       # not a digit run


def test_glyph_round_trip_random():
    # Same shape of generator as test_dl_parser.py's own fuzz test, extended with
    # AtLeast/AtMost; checks render-idempotence (see that file's own note on why
    # exact structural equality is not the right property for a fuzzed ⊓/⊔ chain).
    atoms = [A, B, C]
    roles = [r, s, "hasChild"]

    def rand(depth, rng):
        if depth <= 0 or rng.random() < 0.3:
            return rng.choice(atoms)
        k = rng.random()
        role = rng.choice(roles)
        if k < 0.15:
            return dl.Not(rand(depth - 1, rng))
        if k < 0.35:
            return dl.And(rand(depth - 1, rng), rand(depth - 1, rng))
        if k < 0.55:
            return dl.Or(rand(depth - 1, rng), rand(depth - 1, rng))
        if k < 0.65:
            return dl.Exists(role, rand(depth - 1, rng))
        if k < 0.75:
            return dl.ForAll(role, rand(depth - 1, rng))
        if k < 0.88:
            return dl.AtLeast(rng.randint(0, 5), role, rand(depth - 1, rng))
        return dl.AtMost(rng.randint(0, 5), role, rand(depth - 1, rng))

    rng = random.Random(271828)
    checked = 0
    for _ in range(60):
        concept = rand(4, rng)
        rendered = concept.to_unicode()
        reparsed = parse_concept(rendered)
        assert reparsed.to_unicode() == rendered, rendered
        checked += 1
    assert checked == 60


# --------------------------------------------------------------------------- #
# Round-trip: OWL Manchester Syntax (min / max / exactly).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.AtLeast(2, "hasChild", dl.Atomic("Doctor")),
    dl.AtMost(3, "hasChild", dl.Atomic("Doctor")),
    dl.AtLeast(0, "hasChild", dl.Top()),          # unqualified: renders as "hasChild min 0"
    dl.AtMost(1, "hasChild", dl.Top()),
    dl.AtLeast(2, "hasChild", dl.And(dl.Atomic("Doctor"), dl.Not(dl.Atomic("Rich")))),
    dl.And(dl.AtLeast(1, "hasChild", dl.Top()), dl.AtMost(1, "hasChild", dl.Top())),
], ids=lambda c: c.to_unicode())
def test_manchester_round_trip(concept):
    rendered = to_manchester(concept)
    assert parse_manchester(rendered) == concept


def test_manchester_min_max_exactly_parse():
    assert parse_manchester("hasChild min 2 Doctor") == dl.AtLeast(2, "hasChild", dl.Atomic("Doctor"))
    assert parse_manchester("hasChild max 3 Doctor") == dl.AtMost(3, "hasChild", dl.Atomic("Doctor"))
    # 'exactly n C' desugars to AtLeast(n) ⊓ AtMost(n) at parse time (no separate AST node).
    assert parse_manchester("hasChild exactly 1 Doctor") == dl.And(
        dl.AtLeast(1, "hasChild", dl.Atomic("Doctor")),
        dl.AtMost(1, "hasChild", dl.Atomic("Doctor")))


def test_manchester_qualifying_class_is_optional_and_defaults_to_thing():
    # W3C grammar: 'min n primary?' -- the qualifying class may be omitted.
    assert parse_manchester("hasChild min 2") == dl.AtLeast(2, "hasChild", dl.Top())
    assert parse_manchester("hasChild min 2 owl:Thing") == dl.AtLeast(2, "hasChild", dl.Top())
    # both spellings render the same (the unqualified shorthand) and reparse identically
    assert to_manchester(dl.AtLeast(2, "hasChild", dl.Top())) == "hasChild min 2"


def test_manchester_number_restriction_omitted_class_does_not_swallow_the_conjunction():
    # 'hasChild min 2 and Rich': since 'and' cannot start a primary, the qualifying
    # class is omitted (defaults to owl:Thing), and 'and Rich' is parsed at the
    # OUTER conjunction level -- this must NOT parse as 'hasChild min 2 (and Rich)'.
    got = parse_manchester("hasChild min 2 and Rich")
    assert got == dl.And(dl.AtLeast(2, "hasChild", dl.Top()), dl.Atomic("Rich"))


def test_manchester_malformed_number_restrictions_are_rejected():
    with pytest.raises(ManchesterSyntaxError, match="non-negative integer"):
        parse_manchester("hasChild min")
    with pytest.raises(ManchesterSyntaxError, match="non-negative integer"):
        parse_manchester("hasChild min two Doctor")


@pytest.mark.parametrize("text, needle", [
    # `r value a` is READ since 0.30.0 (dl.HasValue) -- see
    # tests/test_dl_has_value.py. `r some {a}`, its sibling, is still refused
    # by the `{a, b}` row below.
    ("r Self", "Self"),
    ("inverse r some A", "inverse"),
    ("{a, b}", "nominal"),
])
def test_manchester_still_rejects_other_out_of_fragment_constructs(text, needle):
    # min/max/exactly are no longer rejected, but the REST of the "outside ALCHQ"
    # fragment boundary is unchanged -- this is the regression half of item 3.
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester(text)
    assert needle in str(exc.value)


@pytest.mark.parametrize("characteristic, tag", [
    ("Functional", "functional"),
    ("InverseFunctional", "inversefunctional"),
    ("Symmetric", "symmetric"),
])
def test_manchester_role_characteristics_are_read_and_the_refusal_moved(characteristic,
                                                                        tag):
    # These were refused BY THE PARSER until the role box landed. They are now
    # READ -- a parser never refuses an axiom KIND, because a TBox is what a
    # parser fills from a file -- and the refusal, where there still is one,
    # moved to QUERY time where a verdict is actually at stake. Functional IS
    # decided (it is the GCI ⊤ ⊑ ≤1 r.⊤, so the ALCQ machinery of this very
    # file covers it); Symmetric and InverseFunctional need inverse roles and
    # are refused by name from concept_satisfiable/abox_consistent.
    assert dl.parse_manchester_role_axiom(
        f"r Characteristics: {characteristic}") == (tag, "r")
    builder = {"functional": "add_functional_role",
               "inversefunctional": "add_inverse_functional_role",
               "symmetric": "add_symmetric_role"}[tag]
    t = getattr(dl.TBox(), builder)("r")
    if tag == "functional":
        assert dl.concept_satisfiable(dl.Atomic("A"), t) is True
    else:
        with pytest.raises(dl.UnsupportedAxiomError, match=characteristic):
            dl.concept_satisfiable(dl.Atomic("A"), t)


def test_a_functional_role_is_decided_by_this_files_own_machinery():
    # The claim above, made concrete: Func(r) internalises ⊤ ⊑ ≤1 r.⊤, and the
    # ≤-rule + choose-rule this file tests are what then merge the two
    # successors. No new tableau rule was added for it.
    A, B = dl.Atomic("A"), dl.Atomic("B")
    t = dl.TBox().add_functional_role("r")
    sub = dl.And(dl.Exists("r", A), dl.Exists("r", B))
    sup = dl.Exists("r", dl.And(A, B))
    assert dl.subsumes(sub, sup, t) is True
    # identical to writing the GCI out by hand, which is the point
    by_hand = dl.TBox().add(dl.Top(), dl.AtMost(1, "r", dl.Top()))
    assert dl.subsumes(sub, sup, by_hand) is True
    assert dl.subsumes(sub, sup, dl.TBox()) is False


# --------------------------------------------------------------------------- #
# Hand-checked textbook cases (test_oracle item 1).
# --------------------------------------------------------------------------- #

def test_pigeonhole_unsatisfiable_with_unqualified_bound():
    # (≤1 r.⊤) ⊓ (≥2 r.C) ⊓ (≥2 r.¬C): forces two PROVABLY-DISTINCT r-successors
    # (one pairwise-distinct pair from each ≥-rule application), while allowing only
    # one r-successor total -- classic pigeonhole, UNSAT.
    concept = dl.And(dl.And(dl.AtMost(1, r, dl.Top()), dl.AtLeast(2, r, A)),
                      dl.AtLeast(2, r, dl.Not(A)))
    assert dl.concept_satisfiable(concept) is False


def test_atleast_atmost_top_unsatisfiable():
    # ≥2 r.C ⊓ ≤1 r.⊤: at least 2 (pairwise-distinct, by the ≥-rule's own generation)
    # r-successors in C, but at most 1 r-successor AT ALL -- immediately UNSAT, no
    # merge can rescue it (the two witnesses are FORCED distinct by construction).
    concept = dl.And(dl.AtLeast(2, r, A), dl.AtMost(1, r, dl.Top()))
    assert dl.concept_satisfiable(concept) is False


def test_atleast_atmost_forall_interplay_satisfiable():
    # ≥2 r.C ⊓ ≤2 r.D ⊓ ∀r.(C ⊔ D): the ≥-rule's two witnesses are already labelled
    # C, so ∀r.(C⊔D)'s disjunction is trivially resolved (C is already present) --
    # no D-successor is ever needed, so ≤2 r.D (0 ≤ 2) is vacuously satisfied. SAT.
    concept = dl.And(dl.And(dl.AtLeast(2, r, A), dl.AtMost(2, r, B)), dl.ForAll(r, dl.Or(A, B)))
    assert dl.concept_satisfiable(concept) is True


def test_atleast_one_equals_exists():
    # ≥1 r.C is semantically Exists(r, C) -- same satisfiability/subsumption
    # behaviour despite being a syntactically different constructor with its own
    # (simpler) tableau rule.
    assert dl.equivalent(dl.AtLeast(1, r, A), dl.Exists(r, A)) is True
    assert dl.subsumes(dl.AtLeast(2, r, A), dl.AtLeast(1, r, A)) is True   # "at least 2" implies "at least 1"
    assert dl.subsumes(dl.AtLeast(1, r, A), dl.AtLeast(2, r, A)) is False


def test_atmost_zero_forbids_any_successor():
    # ≤0 r.C forbids ANY r-successor in C at all; a single asserted witness clashes.
    ab = dl.ABox().assert_role("x", "y", r).assert_concept("y", A).assert_concept("x", dl.AtMost(0, r, A))
    assert dl.abox_consistent(ab) is False
    # ...but an r-successor NOT in C is fine.
    ab2 = dl.ABox().assert_role("x", "y", r).assert_concept("y", dl.Not(A)).assert_concept("x", dl.AtMost(0, r, A))
    assert dl.abox_consistent(ab2) is True


def test_abox_merge_no_unique_name_assumption_is_satisfiable():
    # Two named r-successors of x, NOT asserted distinct, with x forced (via a
    # global TBox axiom, ⊤ ⊑ ≤1 r.⊤) to have at most one r-successor total. With no
    # unique name assumption, y1 and y2 may denote the SAME domain element, so this
    # is SATISFIABLE (the ≤-rule merges them).
    ab = dl.ABox().assert_role("x", "y1", r).assert_role("x", "y2", r)
    tbox = dl.TBox().add(dl.Top(), dl.AtMost(1, r, dl.Top()))
    assert dl.abox_consistent(ab, tbox) is True


def test_abox_merge_blocked_by_explicit_distinctness_is_unsatisfiable():
    # Same ABox, but now y1 ≠ y2 is asserted explicitly (ABox.assert_distinct) --
    # merging is no longer available, so x genuinely has 2 pairwise-distinct
    # r-successors against a ≤1 bound: UNSATISFIABLE.
    ab = dl.ABox().assert_role("x", "y1", r).assert_role("x", "y2", r).assert_distinct("y1", "y2")
    tbox = dl.TBox().add(dl.Top(), dl.AtMost(1, r, dl.Top()))
    assert dl.abox_consistent(ab, tbox) is False


def test_abox_merge_reveals_a_clash_between_the_merged_labels():
    # x : ≤1 r.⊤, with two named r-successors y1 : A, y2 : ¬A, NOT asserted
    # distinct. Since (x, y1) : r and (x, y2) : r are hard facts, the ONLY way to
    # keep x's r-successor count at ≤1 is for y1 and y2 to be the SAME individual
    # in every model -- but merging them unions their labels into {A, ¬A, ...}, an
    # immediate clash. Every candidate merge (the only pair, (y1, y2)) fails, so
    # this KB is genuinely UNSATISFIABLE -- a case the ≤-rule can only discover by
    # actually attempting the merge.
    ab = (dl.ABox().assert_role("x", "y1", r).assert_role("x", "y2", r)
          .assert_concept("y1", A).assert_concept("y2", dl.Not(A))
          .assert_concept("x", dl.AtMost(1, r, dl.Top())))
    assert dl.abox_consistent(ab) is False


def test_abox_merge_unrelated_concepts_no_clash_is_satisfiable():
    # Same shape, but y1 : A and y2 : B (unrelated atoms) -- merging unions their
    # labels into {A, B, ...}, which is perfectly consistent, so this IS satisfiable
    # (x has exactly one r-successor that happens to be both A and B).
    ab = (dl.ABox().assert_role("x", "y1", r).assert_role("x", "y2", r)
          .assert_concept("y1", A).assert_concept("y2", B)
          .assert_concept("x", dl.AtMost(1, r, dl.Top())))
    assert dl.abox_consistent(ab) is True


def test_choose_rule_reuses_an_undetermined_neighbour_instead_of_over_generating():
    # x : ≤2 r.⊤ ⊓ ≥1 r.¬A, with TWO named r-successors y1, y2 already at the ≤2
    # cap, neither with A/¬A decided. The choose-rule lets the ≥-rule recognise
    # y1 (say) as a reusable ¬A-witness rather than generating a brand-new node
    # that would (without a merge) push the total past 2 -- SAT either way, but
    # this exercises the choose/reuse path directly rather than falling back on
    # generate-then-merge.
    ab = (dl.ABox().assert_role("x", "y1", r).assert_role("x", "y2", r)
          .assert_concept("x", dl.And(dl.AtMost(2, r, dl.Top()), dl.AtLeast(1, r, dl.Not(A)))))
    assert dl.abox_consistent(ab) is True


# --------------------------------------------------------------------------- #
# Role-hierarchy-aware neighbour counting (mandatory soundness point 2).
# --------------------------------------------------------------------------- #

def test_atmost_counts_neighbours_through_the_role_hierarchy():
    # hasSon ⊑ hasChild: an r-successor via hasSon is ALSO a hasChild-neighbour, so
    # ≤1 hasChild.⊤ must count BOTH hasSon-edges, not just literal hasChild-edges.
    t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
    ab = (dl.ABox().assert_role("x", "y1", "hasSon").assert_role("x", "y2", "hasSon")
          .assert_distinct("y1", "y2")
          .assert_concept("x", dl.AtMost(1, "hasChild", dl.Top())))
    assert dl.abox_consistent(ab, t) is False
    # Sanity: without the role inclusion, hasSon and hasChild are unrelated roles,
    # so the same two hasSon-edges do not count against hasChild's bound at all.
    assert dl.abox_consistent(ab, dl.TBox()) is True


def test_atleast_satisfied_by_a_hierarchy_neighbour():
    # ≥1 hasChild.⊤ is satisfied by an EXISTING hasSon-successor once hasSon ⊑
    # hasChild is declared -- no new witness needs generating.
    t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
    ab = dl.ABox().assert_role("x", "y", "hasSon").assert_concept("x", dl.AtLeast(1, "hasChild", dl.Top()))
    assert dl.abox_consistent(ab, t) is True


def test_atmost_dedups_a_neighbour_reached_by_two_entailing_roles():
    # Regression for a crash this item's adversarial review caught: x has BOTH
    # an r-edge AND an s-edge to the SAME y (s ⊑ r), so y is x's r-neighbour via
    # TWO different edges -- it must still count ONCE against ≤1 r.A, not corrupt
    # the branch by looking like two DIFFERENT neighbours eligible to be merged
    # into each other (_role_neighbours used to return y twice; _find_mergeable
    # then treated the degenerate pair (y, y) as mergeable, and _merge deleted y
    # from the branch while edges/labels still referenced it -- see
    # _role_neighbours's docstring in tableau.py). x genuinely has exactly ONE
    # r-neighbour (y), so this is SATISFIABLE, not a crash.
    ab = (dl.ABox().assert_role("x", "y", r).assert_role("x", "y", s)
          .assert_concept("y", A).assert_concept("x", dl.AtMost(1, r, A)))
    t = dl.TBox().add_role_inclusion(s, r)
    assert dl.abox_consistent(ab, t) is True


def test_atmost_dedup_still_clashes_when_the_bound_is_genuinely_exceeded():
    # Same convergent-edge shape as above, but ≤0 r.A: x's ONE (deduplicated)
    # r-neighbour y is still in A, which already exceeds a bound of 0 --
    # UNSATISFIABLE. Guards against a dedup fix that accidentally undercounts
    # (e.g. by dropping y instead of counting it exactly once).
    ab = (dl.ABox().assert_role("x", "y", r).assert_role("x", "y", s)
          .assert_concept("y", A).assert_concept("x", dl.AtMost(0, r, A)))
    t = dl.TBox().add_role_inclusion(s, r)
    assert dl.abox_consistent(ab, t) is False


def test_atmost_merge_between_witnesses_reached_by_different_entailing_roles():
    # Concept-level regression for the same root cause, the tableau's second
    # crash shape: a fresh ∃r.A-witness and a fresh ∃s.A-witness (s ⊑ r) are TWO
    # DIFFERENT nodes that both count as r-neighbours of x (via _role_neighbours'
    # role-hierarchy awareness), so ≤1 r.⊤ forces the ≤-rule to merge them --
    # they were never marked pairwise distinct (that only happens between
    # witnesses generated TOGETHER by one ≥-rule application, not by two
    # independent ∃-rule applications). SATISFIABLE (the merge succeeds; nothing
    # in either witness's label clashes with the other's).
    concept = dl.And(dl.And(dl.Exists(r, A), dl.Exists(s, A)), dl.AtMost(1, r, dl.Top()))
    t = dl.TBox().add_role_inclusion(s, r)
    assert dl.concept_satisfiable(concept, t) is True


# --------------------------------------------------------------------------- #
# Simple roles only (mandatory soundness point 1): refuse non-simple roles by name.
# --------------------------------------------------------------------------- #

def test_number_restriction_on_transitive_role_is_refused():
    t = dl.TBox().add_transitive_role(r)
    with pytest.raises(dl.NonSimpleRoleError, match=r"'r'"):
        dl.concept_satisfiable(dl.AtLeast(2, r, A), t)
    with pytest.raises(dl.NonSimpleRoleError):
        dl.concept_satisfiable(dl.AtMost(1, r, A), t)


def test_number_restriction_on_role_with_transitive_subrole_is_refused():
    # s ⊑ r, Trans(s): r itself is not declared transitive, but it has a
    # transitive SUB-role, which is exactly the SHQ/SHIQ non-simple case.
    t = dl.TBox().add_role_inclusion(s, r).add_transitive_role(s)
    with pytest.raises(dl.NonSimpleRoleError, match=f"'{r}'"):
        dl.concept_satisfiable(dl.AtLeast(1, r, A), t)


def test_number_restriction_on_unrelated_role_is_unaffected_by_an_unrelated_transitive_role():
    t = dl.TBox().add_transitive_role("other")
    assert dl.concept_satisfiable(dl.AtLeast(1, r, A), t) is True


def test_simple_role_check_reaches_into_tbox_gcis_and_abox_assertions():
    # The refusal must fire even when the AtLeast/AtMost is buried inside a TBox
    # GCI (internalised onto every individual) or an ABox concept assertion, not
    # just when it is the top-level query concept.
    t = dl.TBox().add_transitive_role(r).add(A, dl.AtLeast(1, r, B))
    with pytest.raises(dl.NonSimpleRoleError):
        dl.concept_satisfiable(A, t)

    t2 = dl.TBox().add_transitive_role(r)
    ab = dl.ABox().assert_concept("x", dl.AtMost(2, r, A))
    with pytest.raises(dl.NonSimpleRoleError):
        dl.abox_consistent(ab, t2)


def test_transitive_role_without_any_number_restriction_is_unaffected():
    # Regression: plain ∃/∀ over a transitive role is untouched (that's the whole
    # point of restricting the check to AtLeast/AtMost specifically).
    t = dl.TBox().add_transitive_role(r)
    assert dl.concept_satisfiable(dl.Exists(r, dl.Exists(r, A)), t) is True


# --------------------------------------------------------------------------- #
# instance_check / classify inherit ALCQ support automatically (test_oracle item 4).
# --------------------------------------------------------------------------- #

def test_instance_check_with_number_restriction():
    # alice has (at least) two named, distinct hasChild-successors -> entails
    # ≥2 hasChild.⊤.
    ab = (dl.ABox().assert_role("alice", "bob", "hasChild")
          .assert_role("alice", "carol", "hasChild").assert_distinct("bob", "carol"))
    assert dl.instance_check(ab, "alice", dl.AtLeast(2, "hasChild", dl.Top())) is True
    # without the distinctness assertion, it is NOT entailed (open-world: bob and
    # carol might be the same individual).
    ab2 = dl.ABox().assert_role("alice", "bob", "hasChild").assert_role("alice", "carol", "hasChild")
    assert dl.instance_check(ab2, "alice", dl.AtLeast(2, "hasChild", dl.Top())) is False


def test_classify_with_number_restrictions_in_gcis():
    # HasManyChildren ≡ ≥3 hasChild.⊤ ⊑ HasChildren ≡ ≥1 hasChild.⊤: classify must
    # place HasManyChildren strictly below HasChildren in the Hasse diagram.
    HasChildren = dl.Atomic("HasChildren")
    HasManyChildren = dl.Atomic("HasManyChildren")
    t = (dl.TBox()
         .add_equivalence(HasChildren, dl.AtLeast(1, "hasChild", dl.Top()))
         .add_equivalence(HasManyChildren, dl.AtLeast(3, "hasChild", dl.Top())))
    cl = dl.classify(t)
    assert cl.parents["HasManyChildren"] == frozenset({"HasChildren"})
    assert cl.children["HasChildren"] == frozenset({"HasManyChildren"})


# --------------------------------------------------------------------------- #
# ABox.assert_distinct: API basics.
# --------------------------------------------------------------------------- #

def test_assert_distinct_is_chainable_and_recorded():
    ab = dl.ABox()
    ret = ab.assert_distinct("a", "b")
    assert ret is ab
    assert ab.distinct_assertions == [("a", "b")]
    ab.assert_role("a", "c", r).assert_distinct("b", "c")
    assert ab.distinct_assertions == [("a", "b"), ("b", "c")]


# --------------------------------------------------------------------------- #
# concept_to_fol / abox_to_fol: hand-checked Count-based translation shape
# (test_oracle item 2's translation side).
# --------------------------------------------------------------------------- #

def test_concept_to_fol_atleast_hand_checked():
    got = concept_to_fol(dl.AtLeast(2, r, A), "x")
    x, w = Variable("x"), Variable("x0")
    expected = Count("ge", Number(2), w, FAnd(Atom(r, (x, w)), Atom("A", (w,))))
    assert got == expected


def test_concept_to_fol_atmost_hand_checked():
    got = concept_to_fol(dl.AtMost(1, r, dl.Top()), "x")
    x, w = Variable("x"), Variable("x0")
    expected = Count("le", Number(1), w, FAnd(Atom(r, (x, w)), Atom("=", (w, w))))
    assert got == expected


def test_abox_to_fol_renders_distinct_assertions_as_disequality():
    ab = dl.ABox().assert_role("a", "b", r).assert_distinct("a", "b")
    got = abox_to_fol(ab)
    ca, cb = Constant("a"), Constant("b")
    expected = FAnd(Atom(r, (ca, cb)), Atom("≠", (ca, cb)))
    assert got == expected


def test_an_individual_asserted_distinct_from_itself_is_inconsistent():
    """``a ≠ a`` has no model, and both routes have to say so.

    Hand-derived: a model of this ABox would need an interpretation under which
    the one element denoted by ``a`` is not the element denoted by ``a``. There is
    none, for the same reason ``¬(a = a)`` is unsatisfiable in FOL, and
    ``DifferentIndividuals(a a)`` is inconsistent in OWL for exactly this reason.

    Until 0.30.0 ``_Branch.mark_distinct`` dropped the pair when both names were
    the same node (nothing to add to a set of UNORDERED pairs), so the tableau
    reported the ABox consistent while ``abox_to_fol`` rendered ``a ≠ a``, which
    ``api.prove`` refutes — the two routes answered differently about the same
    knowledge base.
    """
    ab = dl.ABox().assert_distinct("a", "a")
    assert dl.abox_consistent(ab) is False
    # the FOL cross-check, independently: proving the negation means inconsistent
    assert api.prove(FNot(abox_to_fol(ab))).status == "proved"
    # and it survives being buried under other assertions
    buried = (dl.ABox().assert_concept("b", dl.Atomic("A"))
              .assert_role("b", "c", r)
              .assert_distinct("a", "a"))
    assert dl.abox_consistent(buried) is False


def test_distinctness_between_two_individuals_is_still_consistent():
    """The control: the clash is about ONE individual, not about distinctness.

    Without a unique name assumption ``a`` and ``b`` may denote the same element,
    and asserting that they do not is satisfiable in any domain with two elements.
    """
    ab = dl.ABox().assert_distinct("a", "b")
    assert dl.abox_consistent(ab) is True
    assert api.prove(FNot(abox_to_fol(ab))).status != "proved"


def test_the_number_restriction_rule_still_reads_the_distinctness_it_needs():
    """The second control: the ≥/≤-rules are what distinctness exists for here.

    Hand-derived with ``A ⊑ ≤1 r.⊤`` and an ``A``-individual ``x`` with two named
    ``r``-successors: consistent while the successors may be merged, inconsistent
    once they are asserted distinct — two distinct successors of an individual
    that may have at most one. A self-distinctness clash that fired too eagerly
    (on any pair, say) would make the first of these inconsistent too.
    """
    tbox = dl.TBox().add(dl.Atomic("A"), dl.AtMost(1, r, dl.Top()))
    mergeable = (dl.ABox().assert_concept("x", dl.Atomic("A"))
                 .assert_role("x", "a", r).assert_role("x", "b", r))
    assert dl.abox_consistent(mergeable, tbox) is True
    assert dl.abox_consistent(mergeable.assert_distinct("a", "b"), tbox) is False


# --------------------------------------------------------------------------- #
# Differential vs Z3 (test_oracle item 2): hand-picked cases.
# --------------------------------------------------------------------------- #

def _z3_concept_sat(concept, var="x") -> bool:
    formula = Quantifier("∃", Variable(var), concept_to_fol(concept, var))
    return is_satisfiable(formula, timeout=TIMEOUT_MS)


@pytest.mark.parametrize("concept", [
    dl.And(dl.AtLeast(2, r, A), dl.AtMost(1, r, dl.Top())),                       # UNSAT
    dl.And(dl.And(dl.AtMost(1, r, dl.Top()), dl.AtLeast(2, r, A)),
           dl.AtLeast(2, r, dl.Not(A))),                                         # UNSAT (pigeonhole)
    dl.And(dl.And(dl.AtLeast(2, r, A), dl.AtMost(2, r, B)), dl.ForAll(r, dl.Or(A, B))),  # SAT
    dl.AtLeast(0, r, dl.Bottom()),                                               # SAT (≥0 is a tautology)
    dl.AtMost(0, r, dl.Top()),                                                   # SAT (no r-successor at all)
    dl.And(dl.AtLeast(3, r, A), dl.AtMost(2, r, A)),                             # UNSAT (n bounds clash directly)
    dl.Or(dl.AtLeast(5, r, A), dl.Not(dl.AtLeast(5, r, A))),                      # SAT (tautology)
])
def test_differential_vs_z3_hand_picked(concept):
    assert dl.concept_satisfiable(concept) == _z3_concept_sat(concept)


# --------------------------------------------------------------------------- #
# Differential vs Z3 (test_oracle item 2): randomized batteries.
# --------------------------------------------------------------------------- #

_ATOMS = [A, B]
_ROLES = [r, s]


def _rand_concept(depth, rng, max_n=4):
    if depth <= 0 or rng.random() < 0.32:
        return rng.choice(_ATOMS)
    k = rng.random()
    role = rng.choice(_ROLES)
    if k < 0.15:
        return dl.Not(_rand_concept(depth - 1, rng, max_n))
    if k < 0.34:
        return dl.And(_rand_concept(depth - 1, rng, max_n), _rand_concept(depth - 1, rng, max_n))
    if k < 0.53:
        return dl.Or(_rand_concept(depth - 1, rng, max_n), _rand_concept(depth - 1, rng, max_n))
    if k < 0.65:
        return dl.Exists(role, _rand_concept(depth - 1, rng, max_n))
    if k < 0.77:
        return dl.ForAll(role, _rand_concept(depth - 1, rng, max_n))
    if k < 0.89:
        return dl.AtLeast(rng.randint(0, max_n), role, _rand_concept(depth - 1, rng, max_n))
    return dl.AtMost(rng.randint(0, max_n), role, _rand_concept(depth - 1, rng, max_n))


def test_differential_vs_z3_randomized_concepts():
    # Small bounded n (<=4) and a small vocabulary, per the test oracle: 150
    # generated ALCQ concepts, decided both by the tableau and by Z3 through the
    # Count-based FOL translation; every one must agree. Also times the battery
    # (see the item's "report the performance" instruction).
    rng = random.Random(20260916)
    checked = 0
    tableau_seconds = 0.0
    for _ in range(150):
        concept = _rand_concept(3, rng)
        start = time.perf_counter()
        tableau_result = dl.concept_satisfiable(concept)
        tableau_seconds += time.perf_counter() - start
        z3_result = _z3_concept_sat(concept)
        assert tableau_result == z3_result, (
            f"disagreement: concept={concept.to_unicode()} "
            f"tableau={tableau_result} z3={z3_result}")
        checked += 1
    assert checked == 150
    assert tableau_seconds < TABLEAU_BATTERY_CEILING_S


def _rand_abox(rng, individuals=("a", "b", "c")):
    ab = dl.ABox()
    for ind in individuals:
        if rng.random() < 0.8:
            ab.assert_concept(ind, _rand_concept(2, rng, max_n=2))
    for x in individuals:
        for y in individuals:
            if x != y and rng.random() < 0.35:
                ab.assert_role(x, y, rng.choice(_ROLES))
    for i, x in enumerate(individuals):
        for y in individuals[i + 1:]:
            if rng.random() < 0.25:
                ab.assert_distinct(x, y)
    return ab


def _z3_abox_sat(abox: dl.ABox) -> bool:
    return is_satisfiable(abox_to_fol(abox), timeout=TIMEOUT_MS)


def test_differential_vs_z3_randomized_aboxes():
    # ABox-level battery: named individuals, role edges, and randomized
    # distinctness assertions specifically exercise the ≤-rule's merge search and
    # the choose-rule (undetermined neighbours of named individuals), which the
    # pure-concept battery above rarely reaches (its witnesses are almost always
    # freshly generated, hence already pairwise-distinct-or-not by construction).
    rng = random.Random(424242)
    checked = 0
    tableau_seconds = 0.0
    for _ in range(100):
        abox = _rand_abox(rng)
        start = time.perf_counter()
        tableau_result = dl.abox_consistent(abox)
        tableau_seconds += time.perf_counter() - start
        z3_result = _z3_abox_sat(abox)
        assert tableau_result == z3_result, (
            f"disagreement: concepts={abox.concept_assertions} roles={abox.role_assertions} "
            f"distinct={abox.distinct_assertions} tableau={tableau_result} z3={z3_result}")
        checked += 1
    assert checked == 100
    assert tableau_seconds < TABLEAU_BATTERY_CEILING_S


# --------------------------------------------------------------------------- #
# Differential vs Z3 (mandatory soundness point 2): randomized ABoxes WITH a
# role hierarchy. Neither battery above ever attaches a TBox with role
# inclusions, so the merge/choose machinery was never differentially fuzzed
# TOGETHER with role-hierarchy-aware neighbour counting -- exactly the gap an
# adversarial review of this item found, via a node reached by two DIFFERENT
# entailing roles converging on the same destination (see
# _role_neighbours's docstring in tableau.py, and the hand-checked
# test_atmost_dedups_a_neighbour_reached_by_two_entailing_roles above).
# --------------------------------------------------------------------------- #

_SUB_ROLES = ["r1", "r2"]      # both declared ⊑ r in every TBox _rand_rbox_abox returns


def _rand_rbox_abox(rng, individuals=("a", "b", "c")):
    """Like ``_rand_abox``, but every role assertion uses one of ``_SUB_ROLES``
    (both ``⊑ r``) instead of a literal ``_ROLES`` member, and -- unlike
    ``_rand_abox``, which tries each unordered role independently per pair --
    EVERY ordered pair of distinct individuals gets a separate coin flip for
    EACH sub-role, so ``x —r1→ y`` and ``x —r2→ y`` (two different entailing
    roles, same source AND destination) both landing on one branch is common
    rather than left to chance.

    On top of that, EVERY ordered pair also gets its own chance to be
    deliberately forced into exactly the shape that used to crash the reasoner
    (see ``_role_neighbours``'s docstring in tableau.py): both ``r1`` and
    ``r2`` from ``x`` to the SAME ``y``, plus a small (random 0-or-1)
    ``≤n r.⊤`` bound asserted on ``x`` -- so ``_find_mergeable`` actually has
    to process a witness list containing a node reached by two different
    entailing edges, not just have the opportunity to by chance.
    """
    tbox = dl.TBox().add_role_inclusion("r1", r).add_role_inclusion("r2", r)
    ab = dl.ABox()
    for ind in individuals:
        if rng.random() < 0.8:
            ab.assert_concept(ind, _rand_concept(2, rng, max_n=2))
    for x in individuals:
        for y in individuals:
            if x == y:
                continue
            for sub_role in _SUB_ROLES:
                if rng.random() < 0.3:
                    ab.assert_role(x, y, sub_role)
            if rng.random() < 0.4:
                ab.assert_role(x, y, "r1")
                ab.assert_role(x, y, "r2")
                filler = rng.choice(_ATOMS)
                ab.assert_concept(y, filler)         # a QUALIFYING (non-⊤) filler,
                ab.assert_concept(x, dl.AtMost(rng.randint(0, 1), r, filler))  # not ⊤ --
                # see the docstring: ⊤ short-circuits _in_concept's label lookup and
                # would mask exactly the bug this injection targets.
    for i, x in enumerate(individuals):
        for y in individuals[i + 1:]:
            if rng.random() < 0.25:
                ab.assert_distinct(x, y)
    return ab, tbox


def _z3_abox_sat_with_rbox(abox: dl.ABox, tbox: dl.TBox) -> bool:
    # The knowledge base and the role box travel as kb_to_fol's formula + side axioms;
    # satisfiability of the knowledge base is satisfiability of their conjunction.
    kb = kb_to_fol(tbox, abox)
    return is_satisfiable(functools.reduce(FAnd, [kb.formula, *kb.axioms]), timeout=TIMEOUT_MS)


def test_differential_vs_z3_randomized_aboxes_with_role_hierarchy():
    # 100 random ABoxes, each under a TBox declaring TWO sub-roles of r, decided
    # independently by the tableau (dl.abox_consistent(abox, tbox)) and by Z3
    # through the RBox-aware FOL translation (kb_to_fol: ABox formula ∧ role-box axioms). This
    # is the battery that would have caught the review's blocker before it
    # shipped: with two sub-roles both entailing the number-restricted role r,
    # a shared destination individual is reached by two DIFFERENT edges often
    # enough to exercise _role_neighbours' dedup on nearly every run.
    rng = random.Random(90210)
    checked = 0
    tableau_seconds = 0.0
    for _ in range(100):
        abox, tbox = _rand_rbox_abox(rng)
        start = time.perf_counter()
        tableau_result = dl.abox_consistent(abox, tbox)
        tableau_seconds += time.perf_counter() - start
        z3_result = _z3_abox_sat_with_rbox(abox, tbox)
        assert tableau_result == z3_result, (
            f"disagreement: concepts={abox.concept_assertions} roles={abox.role_assertions} "
            f"distinct={abox.distinct_assertions} tableau={tableau_result} z3={z3_result}")
        checked += 1
    assert checked == 100
    assert tableau_seconds < TABLEAU_BATTERY_CEILING_S


def test_the_battery_ceiling_counts_tableau_seconds_and_not_solver_seconds(monkeypatch):
    # A Z3 call that is slow (it may use all of TIMEOUT_MS) must not make a
    # tableau battery fail with "too slow". Here the solver side is replaced by a
    # stand-in that answers correctly after 20 ms, so each battery spends
    # 150 x 20 ms = 3 s waiting for it, and the ceiling is lowered to 1 s: a ceiling
    # that counted the whole battery would fail, one that counts the tableau
    # calls (about 10 ms for the whole battery) does not.
    def slow_solver(concept, var="x"):
        time.sleep(0.02)
        return dl.concept_satisfiable(concept)

    monkeypatch.setitem(globals(), "_z3_concept_sat", slow_solver)
    monkeypatch.setitem(globals(), "TABLEAU_BATTERY_CEILING_S", 1.0)
    start = time.perf_counter()
    test_differential_vs_z3_randomized_concepts()
    assert time.perf_counter() - start > 1.0       # the battery really was slow: 150 x 20 ms


# --------------------------------------------------------------------------- #
# Differential vs api.prove over the kb_to_fol bundle: ALCHQ knowledge bases —
# GCIs with number restrictions on a SIMPLE role, plus a role box (hierarchy +
# a transitive role) — the one place where Count nodes and the role-box side
# axioms meet in the same premise list. The tableau (dl.subsumes /
# dl.abox_consistent) and the FOL route must agree on every case.
# --------------------------------------------------------------------------- #

_QKB_ROLES = ["r1", "r2", "q"]       # q carries the number restrictions: never transitive,
                                     # and never has a transitive sub-role (so it is simple)


def _rand_qkb_concept(depth, rng):
    if depth <= 0 or rng.random() < 0.3:
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.12:
        return dl.Not(_rand_qkb_concept(depth - 1, rng))
    if k < 0.28:
        return dl.And(_rand_qkb_concept(depth - 1, rng), _rand_qkb_concept(depth - 1, rng))
    if k < 0.42:
        return dl.Or(_rand_qkb_concept(depth - 1, rng), _rand_qkb_concept(depth - 1, rng))
    if k < 0.60:
        return dl.Exists(rng.choice(_QKB_ROLES), _rand_qkb_concept(depth - 1, rng))
    if k < 0.72:
        return dl.ForAll(rng.choice(_QKB_ROLES), _rand_qkb_concept(depth - 1, rng))
    if k < 0.86:
        return dl.AtLeast(rng.randint(1, 2), "q", _rand_qkb_concept(depth - 1, rng))
    return dl.AtMost(rng.randint(0, 2), "q", _rand_qkb_concept(depth - 1, rng))


def _rand_qkb_tbox(rng):
    """Always has a role box: some of r1 ⊑ r2, q ⊑ r2, Trans(r2) (at least one), plus 0..2 GCIs."""
    t = dl.TBox()
    axioms = rng.sample(["r1<r2", "q<r2", "trans r2"], rng.randint(1, 3))
    if "r1<r2" in axioms:
        t.add_role_inclusion("r1", "r2")
    if "q<r2" in axioms:
        t.add_role_inclusion("q", "r2")
    if "trans r2" in axioms:
        t.add_transitive_role("r2")
    for _ in range(rng.randint(0, 2)):
        t.add(_rand_qkb_concept(1, rng), _rand_qkb_concept(1, rng))
    return t


# ``api.prove`` asks its backends in order and gives each the whole limit, so the limit is what
# a problem costs on which the first backend finds nothing. One of the hundred knowledge bases
# below is such a problem: its consistency question is
#     ¬(∀x (A(x) → ∃≥2 y (q(x, y) ∧ A(y))) ∧ A(b) ∧ q(a, b)),
# refuted by a model of two elements that the model finder returns in a tenth of a second,
# while Z3 instantiates the counting axiom without end. Unlike ``is_satisfiable`` above,
# ``api.prove`` keeps "no answer" apart from both verdicts (it is counted as undecided, never
# as a disagreement), so this limit may be short. Measured: every other call of the battery
# is answered by Z3 in under a second.
QKB_TIMEOUT_MS = 5000


def _qkb_status(goal, premises) -> str:
    return api.prove(goal, list(premises), backends=["z3", "modelfinder"],
                     timeout=QKB_TIMEOUT_MS).status


def run_qkb_differential(seed: int, n: int) -> dict:
    """``n`` random ALCHQ knowledge bases, each asked a subsumption question and a
    consistency question; tableau against ``api.prove`` over :func:`kb_to_fol`."""
    rng = random.Random(seed)
    stats = {"seed": seed, "kbs": n, "agree": 0, "disagree": 0, "undecided": 0,
             "subsumed": 0, "not_subsumed": 0, "inconsistent": 0, "consistent": 0,
             "with_number_restriction": 0}
    for _ in range(n):
        t = _rand_qkb_tbox(rng)
        sub, sup = _rand_qkb_concept(2, rng), _rand_qkb_concept(2, rng)
        ab = dl.ABox()
        for ind in ("a", "b"):
            if rng.random() < 0.8:
                ab.assert_concept(ind, _rand_qkb_concept(2, rng))
        if rng.random() < 0.6:
            ab.assert_role("a", "b", rng.choice(_QKB_ROLES))
        if rng.random() < 0.3:
            ab.assert_distinct("a", "b")
        shape = rng.random()
        if shape < 0.15:           # a counting clash: at least 2 q-successors in A, at most 1 in all
            ab.assert_concept("a", dl.And(dl.AtLeast(2, "q", A), dl.AtMost(1, "q", dl.Top())))
        elif shape < 0.30:         # a clash that exists only if the role box relates r1 to r2
            ab.assert_concept("a", dl.And(dl.Exists("r1", A), dl.ForAll("r2", dl.Not(A))))
        elif shape < 0.40:         # a counting clash only via q ⊑ r2: at most 0 r2-successors, yet a q-edge
            ab.assert_concept("a", dl.ForAll("r2", dl.Bottom()))
            ab.assert_role("a", "b", "q")
        kb = kb_to_fol(t, ab)
        if any(isinstance(node, Count) for f in (*kb.premises, subsumption_to_fol(sub, sup))
               for node in f.walk()):
            stats["with_number_restriction"] += 1

        holds = dl.subsumes(sub, sup, t)
        stats["subsumed" if holds else "not_subsumed"] += 1
        status = _qkb_status(subsumption_to_fol(sub, sup), kb.tbox_premises)
        verdict = {"proved": holds, "refuted": not holds}.get(status)
        outcome = "undecided" if verdict is None else ("agree" if verdict else "disagree")
        stats[outcome] += 1
        if outcome == "disagree":
            stats.setdefault("failures", []).append(
                f"subsumption {sub.to_unicode()} ⊑ {sup.to_unicode()}: tableau={holds} fol={status} "
                f"incl={t.role_inclusions} trans={sorted(t.transitive_roles)} "
                f"gcis={[(x.to_unicode(), y.to_unicode()) for x, y in t.inclusions]}")

        consistent = dl.abox_consistent(ab, t)
        stats["consistent" if consistent else "inconsistent"] += 1
        status = _qkb_status(FNot(kb.formula), kb.axioms)
        verdict = {"proved": not consistent, "refuted": consistent}.get(status)
        outcome = "undecided" if verdict is None else ("agree" if verdict else "disagree")
        stats[outcome] += 1
        if outcome == "disagree":
            stats.setdefault("failures", []).append(
                f"consistency: tableau={consistent} fol={status} abox={ab} "
                f"incl={t.role_inclusions} trans={sorted(t.transitive_roles)} "
                f"gcis={[(x.to_unicode(), y.to_unicode()) for x, y in t.inclusions]}")
    return stats


def test_differential_kb_to_fol_alchq_knowledge_bases_vs_tableau():
    stats = run_qkb_differential(seed=20261005, n=100)
    assert not stats.get("failures"), stats
    assert stats["disagree"] == 0
    assert stats["agree"] >= 0.95 * (2 * stats["kbs"]), stats
    # the battery reaches number restrictions (the Count image) and both verdicts of each question
    assert stats["with_number_restriction"] >= 20, stats
    assert min(stats["subsumed"], stats["not_subsumed"],
               stats["inconsistent"], stats["consistent"]) >= 5, stats
