r"""A8: ``SameIndividual`` and ``NegativeObjectPropertyAssertion``.

The two OWL 2 ABox assertion kinds this kit had no entry point for. Eight of
the Open Energy Ontology's axioms use them, and the caller's only workaround
went through ``dl.Nominal`` — which the in-house tableau refuses outright, so
the tableau could not see either assertion at all.

Both are stored NATIVELY and decided, not approximated:

* ``assert_same(a, b)`` is the mirror of ``assert_distinct``. There is no
  unique name assumption here, so two names MAY denote one element; this says
  they DO. The tableau decides it by genuine node MERGING — the ≤-rule's own
  ``_merge``, reused — applied once the branch is set up and before any
  completion rule runs, closed under the equivalence the assertions generate.
* ``assert_negative_role(a, b, role)`` is a ground FACT about two individuals,
  so its image is the ground literal ``¬role(a, b)`` rather than a concept
  assertion about a nominal, and the tableau decides it by a clash condition
  over the branch's FORBIDDEN edges, closed under the role hierarchy exactly
  as every other edge condition is.

Two defects found while building this are tested here, because both are
reachable only once these exist:

* **F2** — ``_merge`` DROPPED a distinctness pair whose two endpoints
  collapsed onto one node. Unreachable from the ≤-rule (which only ever merges
  a pair it has checked is not marked distinct), reachable the moment a merge
  can come from somewhere else: ``assert_same(a, b)`` with
  ``assert_distinct(a, b)`` would have been reported CONSISTENT while its own
  FOL image ``a = b ∧ a ≠ b`` is refutable. The control that proves the new
  branch is still unreachable from the ≤-rule is here too.
* **F5** — ``instance_check`` rebuilt its probe ABox FIELD BY FIELD, so every
  assertion kind added to ``ABox`` had to be remembered there as well, and
  forgetting it was SILENT: ``instance_check``/``instance_retrieval``/
  ``realize``/``realize_all`` would answer about a strictly weaker knowledge
  base than ``abox_consistent`` sees on the same ABox.

Every image and verdict is hand-derived from the OWL 2 direct semantics first
and then compared with the code, and every tableau verdict is also asked of the
FOL route. Z3-backed calls take their ``timeout`` in MILLISECONDS; it is never
shrunk.
"""

import itertools

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl import owl_reasoner as _owl_reasoner
from unicode_logic_kit.dl.tableau import _Branch, _merge
from unicode_logic_kit.fol.nodes import Not as FNot

TIMEOUT_MS = 20000

C, D = dl.Atomic("C"), dl.Atomic("D")


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


def _both_routes_consistent(abox, tbox=None, *, consistent: bool) -> None:
    """Assert the hand-derived consistency verdict, from BOTH routes.

    The FOL spelling is ``kb_to_fol``'s own: ``prove(Not(kb.formula),
    kb.axioms)`` is "proved" exactly when the knowledge base is INCONSISTENT.
    """
    assert dl.abox_consistent(abox, tbox) is consistent, "the tableau disagrees"
    kb = dl.kb_to_fol(tbox, abox)
    status = _status(FNot(kb.formula), kb.axioms)
    assert status == ("refuted" if consistent else "proved"), (
        f"the FOL route said {status!r} where the hand-derived answer is "
        f"consistent={consistent}")


# --------------------------------------------------------------------------- #
# The images, as exact strings.
# --------------------------------------------------------------------------- #

def test_the_same_individual_image_is_the_equality_atom():
    # OWL 2 direct semantics: SameIndividual(a1 … ak) holds iff
    # a1^I = … = ak^I. The kit renders a ≠ b as a bare Atom("≠", …) already;
    # this is its exact mirror, and `=` is native in every backend.
    # ax03484 is SameIndividual(CRFSectorIPCC2006Transport NCBRSectorTransport).
    assert dl.abox_to_fol(dl.ABox().assert_same(
        "CRFSectorIPCC2006Transport", "NCBRSectorTransport")).to_unicode_str() == \
        "CRFSectorIPCC2006Transport = NCBRSectorTransport"


def test_the_negative_role_image_is_the_negated_ground_literal():
    # NegativeObjectPropertyAssertion(P a b) holds iff <a^I, b^I> ∉ P^OP, i.e.
    # ¬P(a, b). ax04031 is the OEO one.
    assert dl.abox_to_fol(dl.ABox().assert_negative_role(
        "MMRSectorMInternationalAviationInTheEUETS", "GovRegSectorDivision",
        "IsDefinedBy")).to_unicode_str() == \
        "¬IsDefinedBy(MMRSectorMInternationalAviationInTheEUETS, GovRegSectorDivision)"


def test_the_five_assertion_kinds_conjoin_in_kind_order():
    # The conjunct order is assertion-kind order -- concept assertions, role
    # assertions, distinctness, sameness, negative role assertions -- and the
    # list is folded by the BALANCED _conjoin, which for five conjuncts groups
    # the middle pair: ((p0 ∧ p1) ∧ (p2 ∧ p3)) ∧ p4. Only the printed
    # parenthesisation differs from a left fold; ∧ is associative, so the
    # models are the same.
    abox = (dl.ABox()
            .assert_concept("a", C)
            .assert_role("a", "b", "r")
            .assert_distinct("a", "c")
            .assert_same("a", "d")
            .assert_negative_role("a", "c", "r"))
    assert dl.abox_to_fol(abox).to_unicode_str() == \
        "C(a) ∧ r(a, b) ∧ (a ≠ c ∧ a = d) ∧ ¬r(a, c)"


def test_the_new_endpoints_are_in_the_knowledge_bases_individuals():
    # kb.individuals is documented as "what a goal about an individual has to
    # use", so an individual named only by one of the new assertion kinds must
    # be in it. The scan is driven by _AXIOM_KINDS' individual_positions
    # column, which is what makes a new kind contribute without being
    # remembered in two independent field-by-field loops.
    kb = dl.kb_to_fol(None, dl.ABox()
                      .assert_same("x1", "y1")
                      .assert_negative_role("p1", "q1", "r"))
    assert kb.individuals == ("p1", "q1", "x1", "y1")


def test_the_images_read_back_when_the_individuals_are_lower_case():
    for abox in (dl.ABox().assert_same("alice", "bob"),
                 dl.ABox().assert_negative_role("alice", "bob", "HasPart")):
        text = dl.abox_to_fol(abox).to_unicode_str()
        assert api.parse_any(text).ok, text


# --------------------------------------------------------------------------- #
# SameIndividual: merging, and the equivalence closure.
# --------------------------------------------------------------------------- #

def test_sameness_carries_a_class_across_both_names():
    # a = b and a : C put C on the single element both names denote, so b : C
    # is entailed -- and this is instance_check working "for free" off the
    # merge, with no new rule: the merged node's label holds both C and the
    # probe's ¬C, which is the existing atomic clash.
    abox = dl.ABox().assert_concept("a", C).assert_same("a", "b")
    assert dl.instance_check(abox, "b", C) is True
    kb = dl.kb_to_fol(None, abox)
    assert _status(dl.abox_to_fol(dl.ABox().assert_concept("b", C)),
                   kb.premises) == "proved"
    # ... and says nothing about an unrelated class: Δ = {d}, a = b = d,
    # C = {d}, D = ∅ is a model.
    assert dl.instance_check(abox, "b", D) is False
    assert _status(dl.abox_to_fol(dl.ABox().assert_concept("b", D)),
                   kb.premises) == "refuted"


def test_sameness_against_a_contradictory_class_has_no_model():
    # a : C, b : ¬C, a = b: one element in both C and ¬C.
    _both_routes_consistent(dl.ABox()
                            .assert_concept("a", C)
                            .assert_concept("b", dl.Not(C))
                            .assert_same("a", "b"), consistent=False)


def test_sameness_and_distinctness_of_the_same_pair_have_no_model():
    # F2, and the verdict that was WRONG before 0.30.0. a = b and a ≠ b have no
    # common model; the tableau's representation of a = b is ONE node, and the
    # representation of a ≠ b is a pair in branch.distinct, so collapsing the
    # pair onto a single node is exactly the self-distinctness _clash already
    # returns True for. _merge DROPPED the collapsing pair instead, so nothing
    # clashed and the answer came back True while the FOL image `a = b ∧ a ≠ b`
    # is refutable -- the two routes disagreeing on a two-line ABox.
    _both_routes_consistent(dl.ABox().assert_same("a", "b").assert_distinct("a", "b"),
                            consistent=False)
    # order of assertion is irrelevant
    _both_routes_consistent(dl.ABox().assert_distinct("a", "b").assert_same("a", "b"),
                            consistent=False)


def test_merge_records_a_collapsing_distinctness_pair_as_self_distinctness():
    # The fix at the level it is written, so the mechanism is pinned and not
    # only its consequence: after merging b into a, the pair {a, b} has both
    # endpoints equal to a, which is `a ≠ a`.
    branch = _Branch()
    branch.add_node("a")
    branch.add_node("b")
    branch.mark_distinct("a", "b")
    assert branch.distinct == {frozenset(("a", "b"))}
    assert branch.self_distinct is False
    _merge(branch, "a", "b")
    assert branch.distinct == set()          # the pair is gone ...
    assert branch.self_distinct is True      # ... recorded, not dropped


def test_the_at_most_rule_never_reaches_the_new_branch():
    # The control for the argument that F2's fix is safe for the existing
    # caller: the ≤-rule only ever merges a pair it has already checked is NOT
    # marked distinct, so a2 == b2 can only happen for the merged pair itself
    # and the new else-branch is unreachable from there. If it WERE reachable,
    # these verdicts would flip to "inconsistent".
    assert dl.concept_satisfiable(
        dl.And(dl.AtLeast(2, "r", C), dl.AtMost(1, "r", dl.Top()))) is False
    # ≥2 r.C with ≤2 r.⊤ is satisfiable, and getting there needs the ≤-rule to
    # merge nothing; ≥3 against ≤2 is not.
    assert dl.concept_satisfiable(
        dl.And(dl.AtLeast(2, "r", C), dl.AtMost(2, "r", dl.Top()))) is True
    # and the ABox merge case: two named successors under ≤1 r.⊤ MAY merge,
    # unless they are forced apart.
    mergeable = (dl.ABox()
                 .assert_concept("x", dl.AtMost(1, "r", dl.Top()))
                 .assert_role("x", "b", "r").assert_role("x", "c", "r"))
    assert dl.abox_consistent(mergeable) is True
    forced = (dl.ABox()
              .assert_concept("x", dl.AtMost(1, "r", dl.Top()))
              .assert_role("x", "b", "r").assert_role("x", "c", "r")
              .assert_distinct("b", "c"))
    assert dl.abox_consistent(forced) is False


def test_the_oeo_four_element_equality_class_collapses_to_one_node():
    # The corpus really contains one: two of OEO's seven SameIndividual axioms
    # share the owner CRFSectorIPCC2006LandUseLandUseChangeAndForestry, so the
    # equivalence closure over the stored PAIRS has four members. The chain
    # a = b, b = c, c = d is consistent on its own ...
    names = ("a", "b", "c", "d")

    def chain():
        return (dl.ABox().assert_same("a", "b")
                .assert_same("b", "c").assert_same("c", "d"))

    _both_routes_consistent(chain(), consistent=True)
    # ... and every element is entailed to carry a class asserted of any other,
    # which is only true if all four really are ONE node.
    typed = chain()
    typed.assert_concept("a", C)
    for name in names:
        assert dl.instance_check(typed, name, C) is True, name
    # ... and asserting ANY two of the four distinct is inconsistent, including
    # the non-consecutive pairs the stored chain never names directly. That is
    # the closure: without it, only (a, b), (b, c) and (c, d) would clash.
    for left, right in itertools.combinations(names, 2):
        _both_routes_consistent(chain().assert_distinct(left, right),
                                consistent=False)


def test_asserting_an_individual_the_same_as_itself_is_a_no_op():
    # Accepted, like assert_distinct(a, a) is accepted and inconsistent: an
    # ABox assembled from a real ontology may contain either, and the honest
    # answer is the verdict, not a constructor exception. a = a holds in every
    # model, so it constrains nothing.
    abox = dl.ABox().assert_same("a", "a").assert_concept("a", C)
    assert abox.same_assertions == [("a", "a")]
    _both_routes_consistent(abox, consistent=True)
    assert dl.instance_check(abox, "a", C) is True


def test_the_tbox_still_applies_after_a_merge():
    # The merged node keeps the internalised GCIs (they are on both endpoints
    # before the merge and the labels are unioned), so C ⊑ ¬D with a : C and
    # b : D is inconsistent once a = b.
    tbox = dl.TBox().add(C, dl.Not(D))
    abox = dl.ABox().assert_concept("a", C).assert_concept("b", D)
    _both_routes_consistent(abox, tbox, consistent=True)
    _both_routes_consistent(abox.assert_same("a", "b"), tbox, consistent=False)


# --------------------------------------------------------------------------- #
# NegativeObjectPropertyAssertion: the clash condition over forbidden edges.
# --------------------------------------------------------------------------- #

def test_asserting_and_forbidding_the_same_edge_has_no_model():
    _both_routes_consistent(dl.ABox()
                            .assert_role("a", "b", "r")
                            .assert_negative_role("a", "b", "r"),
                            consistent=False)


def test_an_edge_to_a_different_name_is_consistent():
    # ... and stays consistent WITHOUT a unique name assumption, because a
    # model may read the names apart: Δ = {d, e, f}, a = d, c = e, b = f,
    # r = {(d, e)} satisfies both assertions.
    _both_routes_consistent(dl.ABox()
                            .assert_role("a", "c", "r")
                            .assert_negative_role("a", "b", "r"),
                            consistent=True)


def test_the_forbidden_edge_is_role_hierarchy_aware():
    # With s ⊑ r, every s-edge IS an r-edge in every model, so a forbidden
    # r-edge forbids the s-edge too.
    tbox = dl.TBox().add_role_inclusion("s", "r")
    _both_routes_consistent(dl.ABox()
                            .assert_role("a", "b", "s")
                            .assert_negative_role("a", "b", "r"),
                            tbox, consistent=False)
    # The converse does not hold: an r-edge need not be an s-edge, so
    # Δ = {d, e}, r = {(d, e)}, s = ∅ is a model.
    _both_routes_consistent(dl.ABox()
                            .assert_role("a", "b", "r")
                            .assert_negative_role("a", "b", "s"),
                            tbox, consistent=True)


def test_a_merge_re_parents_the_forbidden_edge():
    # r(a, c) with ¬r(a, b) is consistent on its own (previous test), and
    # b = c makes it a contradiction -- which only shows up if _merge
    # re-maps branch.negative_edges exactly as it re-maps the real ones.
    _both_routes_consistent(dl.ABox()
                            .assert_role("a", "c", "r")
                            .assert_negative_role("a", "b", "r")
                            .assert_same("b", "c"),
                            consistent=False)


def test_a_forbidden_edge_meets_a_value_restriction():
    # The two packages' constructs against each other: a : ∃r.{b} forces the
    # very edge ¬r(a, b) forbids, so there is no model. The FOL route proves it
    # (r(a, b) and ¬r(a, b)); the in-house tableau does not decide a value
    # restriction (a nominal in disguise) and RAISES instead of answering.
    abox = (dl.ABox()
            .assert_concept("a", dl.HasValue("r", "b"))
            .assert_negative_role("a", "b", "r"))
    kb = dl.kb_to_fol(None, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "proved"
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        dl.abox_consistent(abox)


def test_a_negative_role_assertion_on_a_transitive_role_is_refused_by_name():
    # The tableau propagates transitivity through its ∀+-rule and never
    # materialises the derived edge,
    # so a two-step r-path a → m → b would entail r(a, b) in every model while
    # leaving the branch with no edge for the clash condition to find.
    tbox = dl.TBox().add_transitive_role("r")
    with pytest.raises(dl.NonSimpleRoleError) as info:
        dl.abox_consistent(dl.ABox().assert_negative_role("a", "b", "r"), tbox)
    message = str(info.value)
    assert "NegativeObjectPropertyAssertion" in message
    assert "NON-SIMPLE" in message
    for pointer in ("dl.kb_to_fol", "api.prove", "dl.owl_reasoner"):
        assert pointer in message
    # A POSITIVE role assertion on the same role stays fine.
    assert dl.abox_consistent(dl.ABox().assert_role("a", "b", "r"), tbox) is True


def test_a_negative_role_assertion_on_a_role_with_a_transitive_sub_role_too():
    tbox = dl.TBox().add_transitive_role("s").add_role_inclusion("s", "r")
    with pytest.raises(dl.NonSimpleRoleError, match="'r'"):
        dl.abox_consistent(dl.ABox().assert_negative_role("a", "b", "r"), tbox)


# --------------------------------------------------------------------------- #
# _merge carries a FORBIDDEN edge with the node that is merged away.
# --------------------------------------------------------------------------- #
#
# `_merge` redirects the edges, the forbidden edges (negative_edges) and the
# distinctness pairs of the dropped node. The positive and the distinctness
# remaps were pinned; the NEGATIVE one was not: reverting it left every test
# green although it changes a verdict (mutation M6 of the verification round:
# `abox_consistent` answered True for the first KB below).
#
# `_merge_order` keeps the node that was added to the branch first, and the
# nodes are added in sorted order, so in same(b, c) the node `c` is DROPPED.

_NEGATIVE_EDGE_MERGES = [
    # not r(a, c), r(a, b), same(b, c): b = c, so r(a, b) IS r(a, c), which the
    # negative assertion denies -- INCONSISTENT. The forbidden edge's TARGET is
    # the dropped node c.
    ("target dropped",
     dl.ABox().assert_negative_role("a", "c", "r").assert_role("a", "b", "r")
     .assert_same("b", "c"), False),
    # not r(c, a), r(b, a), same(b, c): the forbidden edge's SOURCE is the
    # dropped node c, and the same reading makes r(b, a) = r(c, a) -- INCONSISTENT.
    ("source dropped",
     dl.ABox().assert_negative_role("c", "a", "r").assert_role("b", "a", "r")
     .assert_same("b", "c"), False),
    # the same identity stated the other way round (same(c, b)): one
    # equivalence class, the same verdict.
    ("target dropped, identity reversed",
     dl.ABox().assert_negative_role("a", "c", "r").assert_role("a", "b", "r")
     .assert_same("c", "b"), False),
    # Controls, one per way a remap could over-reach. Without the identity the
    # edge to b and the denial about c are about two elements: consistent.
    ("control: no identity",
     dl.ABox().assert_negative_role("a", "c", "r").assert_role("a", "b", "r"), True),
    # The identity merges b and c only, so a denial about a pair that does not
    # involve them is untouched: consistent.
    ("control: the denial concerns another pair",
     dl.ABox().assert_negative_role("a", "d", "r").assert_role("a", "b", "r")
     .assert_same("b", "c"), True),
]


@pytest.mark.parametrize("label, abox, consistent", _NEGATIVE_EDGE_MERGES,
                         ids=[c[0] for c in _NEGATIVE_EDGE_MERGES])
def test_a_forbidden_edge_travels_with_the_node_that_is_merged_away(label, abox, consistent):
    _both_routes_consistent(abox, consistent=consistent)


def test_merge_rewrites_the_forbidden_edge_at_both_ends():
    # The unit: _merge(branch, keep=b, drop=c) replaces every occurrence of c by
    # b in a forbidden edge, source and target alike, and leaves the rest alone.
    # Derived by hand from "the node c is now the node b".
    branch = _Branch()
    for node in ("a", "b", "c"):
        branch.add_node(node)
    branch.negative_edges = {("a", "r", "c"), ("c", "r", "a"), ("c", "r", "c"),
                             ("a", "r", "b")}
    _merge(branch, "b", "c")
    assert branch.negative_edges == {("a", "r", "b"), ("b", "r", "a"), ("b", "r", "b")}


# --------------------------------------------------------------------------- #
# F5: the probe ABox must carry EVERY assertion kind.
# --------------------------------------------------------------------------- #

def test_instance_check_sees_a_same_assertion():
    # Red with the field-by-field copy: the probe ABox would have no
    # same_assertions, so instance_check would answer about a strictly weaker
    # knowledge base than abox_consistent sees on the same input.
    abox = dl.ABox().assert_concept("a", C).assert_same("a", "b")
    assert dl.instance_check(abox, "b", C) is True


def test_instance_check_sees_a_negative_role_assertion():
    # Red with a probe that drops the field: the KB r(a, b), ¬r(a, b) has no
    # model (<a, b> is in r^I and is not), so it entails EVERY membership, C(a)
    # included -- and instance_check says so only if the probe ABox still
    # carries the negative assertion. A probe without it is {r(a, b), a : ¬C},
    # which is consistent, and the answer would flip to False. The FOL route
    # agrees: the premises are inconsistent, so C(a) is proved.
    abox = dl.ABox().assert_role("a", "b", "r").assert_negative_role("a", "b", "r")
    assert dl.instance_check(abox, "a", C) is True
    kb = dl.kb_to_fol(None, abox)
    assert _status(dl.abox_to_fol(dl.ABox().assert_concept("a", C)), kb.premises) == "proved"
    # The control: with the edge alone C(a) is not entailed (r(a, b) says
    # nothing about a's classes).
    edge_only = dl.ABox().assert_role("a", "b", "r")
    assert dl.instance_check(edge_only, "a", C) is False


def test_a_negative_role_assertion_is_a_negated_value_restriction_for_the_fol_route():
    # ¬r(a, b) says exactly what a : ¬∃r.{b} says, so the knowledge base
    # entails the second. The FOL route proves it; the in-house tableau does not
    # decide a value restriction and raises (see tests/test_dl_has_value.py).
    abox = dl.ABox().assert_negative_role("a", "b", "r")
    kb = dl.kb_to_fol(None, abox)
    goal = dl.abox_to_fol(dl.ABox().assert_concept(
        "a", dl.Not(dl.HasValue("r", "b"))))
    assert _status(goal, kb.premises) == "proved"
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        dl.instance_check(abox, "a", dl.Not(dl.HasValue("r", "b")))


def test_instance_retrieval_and_realization_see_the_new_endpoints():
    abox = dl.ABox().assert_concept("a", C).assert_same("a", "b")
    assert dl.instance_retrieval(abox, C) == {"a", "b"}
    assert sorted(dl.realize_all(abox, [C])) == ["a", "b"]
    assert dl.realize(abox, "b", [C]) == [C]
    # an individual named only by a negative role assertion is an individual too
    other = dl.ABox().assert_negative_role("p", "q", "r")
    assert sorted(dl.realize_all(other, [C])) == ["p", "q"]


def test_the_abox_copy_carries_every_field_by_construction():
    # The mechanism, pinned at the level it is written: ABox.copy enumerates
    # the dataclass FIELDS, so a field added later is carried over without
    # anyone remembering -- and the lists are fresh, because every assert_*
    # mutates in place.
    import dataclasses

    original = (dl.ABox()
                .assert_concept("a", C)
                .assert_role("a", "b", "r")
                .assert_distinct("a", "c")
                .assert_same("a", "d")
                .assert_negative_role("a", "e", "r"))
    clone = original.copy()
    assert clone == original
    for declared in dataclasses.fields(dl.ABox):
        mine = getattr(clone, declared.name)
        theirs = getattr(original, declared.name)
        assert mine == theirs
        assert mine is not theirs, f"{declared.name} is SHARED, not copied"
    clone.assert_concept("z", D)
    assert len(original.concept_assertions) == 1


# --------------------------------------------------------------------------- #
# Round trips.
# --------------------------------------------------------------------------- #

def test_the_functional_syntax_round_trips_both_kinds():
    document = ("Ontology(SameIndividual(a b) "
                "NegativeObjectPropertyAssertion(r m g))")
    tbox, abox = dl.parse_owl_functional(document)
    assert tbox == dl.TBox()
    assert abox == dl.ABox().assert_same("a", "b").assert_negative_role("m", "g", "r")
    text = dl.to_owl_functional(tbox, abox)
    assert "SameIndividual(a b)" in text
    assert "NegativeObjectPropertyAssertion(r m g)" in text
    assert dl.parse_owl_functional(text) == (tbox, abox)


def test_an_n_ary_same_individual_is_the_consecutive_chain():
    # Equality is transitive, so the chain entails every pair -- the same
    # shortcut EquivalentClasses uses, and deliberately NOT
    # DifferentIndividuals' all-pairs expansion, which distinctness needs
    # because it has no transitive closure.
    _tbox, abox = dl.parse_owl_functional("Ontology(SameIndividual(a b c d))")
    assert abox.same_assertions == [("a", "b"), ("b", "c"), ("c", "d")]
    # and the entailment the shortcut relies on really holds for a
    # non-consecutive pair
    typed = dl.parse_owl_functional(
        "Ontology(SameIndividual(a b c d) ClassAssertion(C a))")[1]
    assert dl.instance_check(typed, "d", C) is True


@pytest.mark.parametrize("document, keyword", [
    ("Ontology(SameIndividual(a))", "SameIndividual"),
    ("Ontology(DifferentIndividuals(a))", "DifferentIndividuals"),
], ids=["same", "different"])
def test_a_one_individual_identity_axiom_is_a_syntax_error(document, keyword):
    # OWL 2's grammar is `(a a+)`, minimum arity two, for both; the two share
    # one reader so the message reads the same.
    with pytest.raises(dl.OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional(document)
    assert f"{keyword} expects at least 2 individuals, found 1" in str(info.value)


def test_a_negative_role_assertion_with_a_missing_argument_is_a_syntax_error():
    with pytest.raises(dl.OwlFunctionalSyntaxError):
        dl.parse_owl_functional("Ontology(NegativeObjectPropertyAssertion(r a))")


def test_the_mcp_row_shapes_build_both_kinds():
    from unicode_logic_kit.mcp.server import _build_dl_abox, dl_abox_consistent

    abox, err = _build_dl_abox(None, None, None, "alc",
                               same=[["a", "b"]],
                               negative_roles=[["a", "b", "r"]])
    assert err is None
    assert abox.same_assertions == [("a", "b")]
    assert abox.negative_role_assertions == [("a", "b", "r")]
    # ... and the tools really answer about them: a = b with a ≠ b has no model
    assert dl_abox_consistent([], None, [["a", "b"]], None, "alc",
                              same=[["a", "b"]]) == {"ok": True, "consistent": False}
    # a malformed row is a caller mistake, named
    _abox, err = _build_dl_abox(None, None, None, "alc", same=[["a"]])
    assert err is not None and "same[0]" in err["error"]["message"]
    _abox, err = _build_dl_abox(None, None, None, "alc", negative_roles=[["a", "b"]])
    assert err is not None and "negative_roles[0]" in err["error"]["message"]


@pytest.mark.skipif(not _owl_reasoner.available(),
                    reason="owlready2 is not installed ([owl] extra)")
@pytest.mark.parametrize("build, consistent", [
    (lambda: dl.ABox().assert_same("a", "b").assert_distinct("a", "b"), False),
    (lambda: (dl.ABox().assert_concept("a", C).assert_concept("b", dl.Not(C))
              .assert_same("a", "b")), False),
    (lambda: dl.ABox().assert_same("a", "b"), True),
    (lambda: dl.ABox().assert_role("a", "b", "r").assert_negative_role("a", "b", "r"),
     False),
    (lambda: dl.ABox().assert_role("a", "c", "r").assert_negative_role("a", "b", "r"),
     True),
], ids=["same-and-distinct", "same-and-contradictory-classes", "same-alone",
        "edge-and-its-negation", "edge-to-another-name"])
def test_hermit_agrees_on_the_same_hand_derived_verdicts(build, consistent):
    abox = build()
    assert dl.external_abox_consistent(abox) is consistent
    assert dl.abox_consistent(abox) is consistent
