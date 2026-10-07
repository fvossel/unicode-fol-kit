"""Merged-away individual NAMES, and what a value restriction made of them.

``dl.tableau._merge`` removes one of its two nodes. Until the value-rule was
removed, a concept could go on mentioning the removed node BY NAME —
``HasValue("r", "c")`` after ``c`` was merged into ``a`` — and the rule read the
name raw and RE-CREATED a node ``c``, a different element from ``a``. The
equality the merge had established was silently undone for everything that
named ``c``. A differential fuzz of the tableau against the FOL image
(``dl.kb_to_fol`` + ``api.prove``) found it; the first disagreement was::

    a : ∃r.{c}      a = c      ¬r(c, c)

Hand-derived: ``a : ∃r.{c}`` puts ``<a, c>`` in ``r``; ``a = c`` makes that
``<c, c>``; the negative assertion says ``<c, c>`` is NOT in ``r``. No model.

An alias map repaired that case — and a second one, a hole in the METHOD and not
in one function, could not be repaired by a patch (``tests/test_dl_has_value.py``
and the "Value restrictions (ObjectHasValue)" section of ``dl.tableau`` have the
two-axiom counterexample). So the in-house tableau no longer decides a value
restriction at all: it RAISES ``UnsupportedConceptError``, as it does for a
nominal. This file therefore has two halves.

* Every case that involves a value restriction keeps its hand-derived verdict
  and asks it of the route that answers, the FOL image; the tableau half is that
  it refuses.
* The cases that involve NO value restriction — a ``SameIndividual`` chain with
  a negative role assertion, and the ≤-rule identifying two named individuals —
  stay tableau tests, each also asked of the FOL route. They are what is left of
  the merge machinery's own obligations: after a merge, every edge, forbidden
  edge and distinctness pair is rewritten in place, and a later
  ``SameIndividual`` pair that names a node merged away EARLIER is resolved to
  the node that now stands for it.

Every expectation below is derived by hand first.
"""
import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl import tableau
from unicode_logic_kit.fol.nodes import Not as FNot

A, B = dl.Atomic("A"), dl.Atomic("B")
HV = dl.HasValue

# Not a shrunken budget: a tiny one makes a backend answer "unknown", which is
# not a verdict, so a test built on it would assert nothing.
TIMEOUT_MS = 30000


def _fol_consistent(abox, tbox=None) -> bool:
    kb = dl.kb_to_fol(tbox, abox)
    status = api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status
    assert status in ("proved", "refuted"), status      # "unknown" measures nothing
    return status == "refuted"


def _refused(abox, tbox=None) -> None:
    """The in-house tableau does not decide a value restriction: it raises."""
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        dl.abox_consistent(abox, tbox)


def _both_routes(abox, tbox=None, *, consistent: bool) -> None:
    """The hand-derived verdict of a knowledge base with NO value restriction,
    asked of both routes."""
    assert dl.abox_consistent(abox, tbox) is consistent, "the tableau disagrees"
    assert _fol_consistent(abox, tbox) is consistent, "the FOL route disagrees"


def _value_then_same(*extra, tbox=None, same=("a", "c")):
    """``a : ∃r.{c}`` and ``a = c`` — so the value edge is the loop ``r(c, c)``."""
    abox = dl.ABox().assert_concept("a", HV("r", "c")).assert_same(*same)
    for method, args in extra:
        abox = getattr(abox, method)(*args)
    return abox, tbox


# --------------------------------------------------------------------------- #
# The value-restriction cases: the FOL route answers, the tableau refuses.
# --------------------------------------------------------------------------- #

#: (label, abox, tbox) — every one INCONSISTENT, for the reason in the label.
_LOOP_CASES = [
    ("the loop r(c, c) is forbidden, named through c",
     *_value_then_same(("assert_negative_role", ("c", "c", "r")))),
    ("the loop is forbidden, named through a (the same element)",
     *_value_then_same(("assert_negative_role", ("a", "a", "r")))),
    ("the loop is forbidden, named through both",
     *_value_then_same(("assert_negative_role", ("a", "c", "r")))),
    ("SameIndividual written the other way round",
     *_value_then_same(("assert_negative_role", ("c", "c", "r")), same=("c", "a"))),
    ("r is irreflexive, and r(c, c) is a loop",
     *_value_then_same(tbox=dl.TBox().add_irreflexive_role("r"))),
    ("r is asymmetric, and asymmetry entails irreflexivity",
     *_value_then_same(tbox=dl.TBox().add_asymmetric_role("r"))),
    ("c : ¬∃r.{a} denies the very edge a : ∃r.{c} asserts, once a = c",
     *_value_then_same(("assert_concept", ("c", dl.Not(HV("r", "a")))))),
]


@pytest.mark.parametrize("label, abox, tbox", _LOOP_CASES, ids=[c[0] for c in _LOOP_CASES])
def test_a_value_restriction_on_a_merged_individual_is_a_loop(label, abox, tbox):
    # Each case has no model: a = c makes the value edge r(a, c) the loop
    # r(c, c), and the case's own axiom forbids exactly that loop (or, for the
    # last one, forbids the edge r(c, a) = r(c, c) under the other name).
    assert _fol_consistent(abox, tbox) is False, label
    _refused(abox, tbox)


def _controls():
    """The same constraints WITHOUT ``a = c``, each on a FRESH ABox (the
    builders mutate and return self, so a shared base would accumulate)."""
    def base():
        return dl.ABox().assert_concept("a", HV("r", "c"))
    return [
        (base().assert_negative_role("c", "c", "r"), None),
        (base().assert_negative_role("a", "a", "r"), None),
        (base(), dl.TBox().add_irreflexive_role("r")),
        (base(), dl.TBox().add_asymmetric_role("r")),
        (base().assert_concept("c", dl.Not(HV("r", "a"))), None),
    ]


def test_without_the_equality_none_of_it_is_a_loop():
    """The controls: the same constraints WITHOUT ``a = c`` leave the edge
    ``r(a, c)`` between two elements that may differ, and every one is consistent
    (Δ = {d, e}, a = d, c = e, r = {(d, e)} satisfies each).

    This is what makes the cases above about the MERGE and not about HasValue.
    """
    for abox, tbox in _controls():
        assert _fol_consistent(abox, tbox) is True
        _refused(abox, tbox)
    # ... and the one that is inconsistent with or without the equality stays so:
    # a : ∃r.{c} is r(a, c), which ¬r(a, c) denies outright.
    denied = (dl.ABox().assert_concept("a", HV("r", "c"))
              .assert_negative_role("a", "c", "r"))
    assert _fol_consistent(denied) is False
    _refused(denied)


def test_the_target_of_a_value_restriction_may_be_the_merged_name():
    """``a : ∃r.{b}`` with ``b = c``: the edge reaches the element BOTH names denote.

    Hand-derived: the edge is ``r(a, b)``, and ``b = c``, so ``¬r(a, c)`` denies
    it; likewise ``c : A`` puts the r-successor in ``A`` and ``a : ∀r.¬A`` forbids
    that. Both inconsistent, whichever way round ``same`` is written.
    """
    for same in (("b", "c"), ("c", "b")):
        denied = (dl.ABox().assert_concept("a", HV("r", "b"))
                  .assert_same(*same).assert_negative_role("a", "c", "r"))
        assert _fol_consistent(denied) is False
        _refused(denied)
        filler = (dl.ABox()
                  .assert_concept("a", dl.And(HV("r", "b"), dl.ForAll("r", dl.Not(A))))
                  .assert_same(*same).assert_concept("c", A))
        assert _fol_consistent(filler) is False
        _refused(filler)


def test_a_chain_of_equalities_through_a_value_restriction():
    """``c = b`` and ``b = a``: the name ``c`` denotes the element ``a`` does.

    ``d : ∃r.{c}`` therefore asserts ``r(d, a)``, which ``¬r(d, a)`` denies.
    """
    abox = (dl.ABox().assert_concept("d", HV("r", "c"))
            .assert_same("c", "b").assert_same("b", "a")
            .assert_negative_role("d", "a", "r"))
    assert _fol_consistent(abox) is False
    _refused(abox)


def test_a_value_restriction_after_the_number_rule_merges_two_named_individuals():
    """The ≤-rule is the OTHER caller of ``_merge``, and it runs mid-search.

    ``a : ≤1 r.⊤`` with ``r(a, b)`` and ``r(a, c)`` forces ``b = c`` (nothing
    says they differ). ``b : ∃s.{c}`` then asserts the loop ``s(b, b)``, which an
    irreflexive ``s`` forbids. Inconsistent — and reached without any
    SameIndividual assertion. The control without the ``≤1`` is consistent
    (nothing forces ``b = c``).
    """
    abox = (dl.ABox()
            .assert_concept("a", dl.AtMost(1, "r", dl.Top()))
            .assert_role("a", "b", "r").assert_role("a", "c", "r")
            .assert_concept("b", HV("s", "c")))
    tbox = dl.TBox().add_irreflexive_role("s")
    assert _fol_consistent(abox, tbox) is False
    _refused(abox, tbox)
    free = (dl.ABox().assert_role("a", "b", "r").assert_role("a", "c", "r")
            .assert_concept("b", HV("s", "c")))
    assert _fol_consistent(free, tbox) is True
    _refused(free, tbox)


def test_value_restrictions_in_the_tbox_follow_the_merge_as_well():
    """A value restriction that reaches a node through a GCI, asked of the FOL
    route (the tableau refuses a TBox that holds one, so it never sees the merge).

    Hand-derived. ``⊤ ⊑ ∃r.{c}`` gives EVERY element an r-edge to ``c``, so ``c``
    itself has the loop ``r(c, c)`` — with or without ``a = c``. What the
    equality adds is that ``a`` IS that element:

    * consistent: one element for both names, with ``r`` and ``s`` loops; then
      ``a : ≤1 r.⊤`` (one r-successor) and ``a : ∃s.{a}`` hold;
    * ``a : ∀r.A`` and ``c : ¬A``: the loop puts ``c`` in ``A``. Inconsistent
      even without the equality (c is its own r-successor) — the control;
    * ``a : ∀s.A``, ``a : ∃s.{c}`` and ``a : ¬A``: the s-edge goes from ``a`` to
      ``c``; only ``a = c`` makes its target ``a`` itself, hence in ``A`` and not
      in ``A``. Inconsistent WITH the equality, consistent without it.
    """
    tbox = dl.TBox().add(dl.Top(), HV("r", "c"))
    ok = (dl.ABox()
          .assert_concept("a", dl.And(dl.AtMost(1, "r", dl.Top()), HV("s", "a")))
          .assert_same("a", "c"))
    assert _fol_consistent(ok, tbox) is True
    _refused(ok, tbox)

    def loop():
        return dl.ABox().assert_concept("a", dl.ForAll("r", A)).assert_concept("c", dl.Not(A))
    assert _fol_consistent(loop().assert_same("a", "c"), tbox) is False
    _refused(loop().assert_same("a", "c"), tbox)

    def only_merged():
        return (dl.ABox()
                .assert_concept("a", dl.And(dl.ForAll("s", A), HV("s", "c")))
                .assert_concept("a", dl.Not(A)))
    assert _fol_consistent(only_merged(), tbox) is True
    assert _fol_consistent(only_merged().assert_same("a", "c"), tbox) is False
    _refused(only_merged(), tbox)
    _refused(only_merged().assert_same("a", "c"), tbox)


# --------------------------------------------------------------------------- #
# What the tableau still decides: merges with NO value restriction.
# --------------------------------------------------------------------------- #

def test_a_same_individual_chain_meets_a_negative_role_assertion():
    """``c = b`` and ``c = a`` — the second pair NAMES ``c``, which the first
    merge has already removed — with ``r(a, d)`` and ``¬r(b, d)``.

    Hand-derived: the two equalities make ``a = b = c`` one element. ``r(a, d)``
    is then ``r(b, d)``, which the negative assertion denies. Inconsistent. The
    tableau can see it only if the second pair is resolved to the node that now
    stands for ``c`` (here ``b``, itself merged into ``a`` by that pair), and the
    forbidden edge ``(b, r, d)`` is rewritten to ``(a, r, d)`` by the merge.
    """
    abox = (dl.ABox()
            .assert_role("a", "d", "r")
            .assert_same("c", "b").assert_same("c", "a")
            .assert_negative_role("b", "d", "r"))
    _both_routes(abox, consistent=False)
    # The control, one link short: with only c = b, a stays free to differ from
    # b, so r(a, d) and ¬r(b, d) are about two elements (Δ = {e1, e2, e3},
    # a = e1, b = c = e2, d = e3, r = {(e1, e3)}). Consistent.
    short = (dl.ABox()
             .assert_role("a", "d", "r")
             .assert_same("c", "b")
             .assert_negative_role("b", "d", "r"))
    _both_routes(short, consistent=True)


def test_a_same_individual_chain_in_either_orientation_collapses_to_one_node():
    """The unit under the chain: after ``same(c, b)`` and ``same(c, a)`` the
    branch holds ONE node, and no merged-away name was added back.

    Hand-derived: nodes are added in sorted order, ``_merge_order`` keeps the
    node added first and drops the other, so ``same(c, b)`` drops ``c`` (keeping
    ``b``) and ``same(c, a)`` — ``c`` resolved to ``b`` — drops ``b`` (keeping
    ``a``). Whichever way a pair is written the three names end as one node.
    """
    for pairs in ([("c", "b"), ("c", "a")], [("b", "c"), ("a", "c")],
                  [("c", "b"), ("b", "a")], [("a", "b"), ("c", "a")]):
        branch = tableau._Branch()
        for name in ("a", "b", "c"):
            branch.add_node(name)
        abox = dl.ABox()
        for left, right in pairs:
            abox.assert_same(left, right)
        tableau._apply_same_assertions(branch, abox)
        assert set(branch.label) == {"a"}, pairs
        assert branch.order == ["a"], pairs


def test_the_number_rule_merging_two_named_individuals_rewrites_the_edges():
    """The ≤-rule identifying two NAMED individuals, mid-search, with no
    SameIndividual assertion and no value restriction.

    ``a : ≤1 r.⊤`` with ``r(a, b)`` and ``r(a, c)`` forces ``b = c`` (nothing
    says they differ). ``s(b, c)`` is then the loop ``s(b, b)``, which an
    irreflexive ``s`` forbids. Inconsistent. The control without the ``≤1`` is
    consistent: nothing forces ``b = c``, so ``s(b, c)`` is an edge between two
    elements (Δ = {e1, e2, e3}, b = e2, c = e3, s = {(e2, e3)}); and so is the
    one where ``b ≠ c`` is ASSERTED but the ``≤1`` is dropped.
    """
    tbox = dl.TBox().add_irreflexive_role("s")
    forced = (dl.ABox()
              .assert_concept("a", dl.AtMost(1, "r", dl.Top()))
              .assert_role("a", "b", "r").assert_role("a", "c", "r")
              .assert_role("b", "c", "s"))
    _both_routes(forced, tbox, consistent=False)
    free = (dl.ABox().assert_role("a", "b", "r").assert_role("a", "c", "r")
            .assert_role("b", "c", "s"))
    _both_routes(free, tbox, consistent=True)
    apart = free.copy().assert_distinct("b", "c")
    _both_routes(apart, tbox, consistent=True)
    # with the distinctness AND the ≤1, the merge is impossible: two distinct
    # r-successors against ≤1 — inconsistent for that reason instead.
    stuck = forced.copy().assert_distinct("b", "c")
    _both_routes(stuck, tbox, consistent=False)
