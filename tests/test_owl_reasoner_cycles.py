"""The external (HermiT) route states a ring of named inclusions, as ``EquivalentClasses`` reads.

owlready2 keeps a named class under another as a Python base class, and Python refuses a cycle of
bases, so ``A ⊑ B`` together with ``B ⊑ A`` (what ``TBox.add_equivalence`` and the reading of
``EquivalentClasses`` give), ``A ⊑ A``, and a longer ring raised ``TypeError`` out of every function that
builds a knowledge base. The same holds for two properties below each other (``r ⊑ s``, ``s ⊑ r``, and
``EquivalentObjectProperties``). An inclusion that would close such a ring is stated as the equivalence it
makes, and an entity below itself is not stated: the ring ``A ⊑ B ⊑ … ⊑ A`` makes every entity on it equal.

The first tier needs owlready2 only; the live tier needs a JVM as well. Every expectation is derived by hand.
"""

import shutil

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl import owl_reasoner as owl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

needs_owlready2 = pytest.mark.skipif(not owl.available(), reason="owlready2 not installed")
live = pytest.mark.skipif(not (owl.available() and shutil.which("java")),
                          reason="owlready2 and/or a JVM (java on PATH) not found")


def a_is(*concepts):
    abox = dl.ABox()
    for concept in concepts:
        abox.assert_concept("a", concept)
    return abox


# ---------------------------------------------------------------------------
# The ontology that is built (owlready2 only, no JVM)
# ---------------------------------------------------------------------------

@needs_owlready2
class TestTheOntologyThatIsBuilt:
    @staticmethod
    def _built(tbox):
        ow = owl._require_available()
        world = ow.World()
        onto = world.get_ontology("http://unicode-logic-kit.invalid/kb#")
        ctx = owl._Ctx(ow, world, onto, owl._characteristics(tbox))
        with onto:
            owl._build_kb(ctx, tbox, dl.ABox())
        return ctx

    def test_two_classes_below_each_other_are_built_as_equivalent(self):
        ctx = self._built(dl.TBox().add(A, B).add(B, A))
        assert ctx.cls("A") in ctx.cls("B").equivalent_to or ctx.cls("B") in ctx.cls("A").equivalent_to
        assert ctx.cls("B") in ctx.cls("A").is_a             # the first inclusion stays a sub-class link

    def test_a_class_below_itself_states_nothing(self):
        ctx = self._built(dl.TBox().add(A, A))
        assert ctx.cls("A").equivalent_to == [] and ctx.cls("A") not in ctx.cls("A").is_a

    def test_a_ring_of_three_is_built(self):
        ctx = self._built(dl.TBox().add(A, B).add(B, C).add(C, A))
        assert ctx.cls("C") in ctx.cls("B").is_a and ctx.cls("B") in ctx.cls("A").is_a
        assert ctx.cls("A") in ctx.cls("C").equivalent_to or ctx.cls("C") in ctx.cls("A").equivalent_to

    def test_a_chain_without_a_ring_keeps_every_link_as_a_sub_class(self):
        ctx = self._built(dl.TBox().add(A, B).add(B, C))
        assert ctx.cls("B") in ctx.cls("A").is_a and ctx.cls("C") in ctx.cls("B").is_a
        assert not any(ctx.cls(name).equivalent_to for name in "ABC")

    def test_two_properties_below_each_other_are_built_as_equivalent(self):
        ctx = self._built(dl.TBox().add_equivalent_roles("r", "s"))
        assert ctx.role_obj("s") in ctx.role_obj("r").equivalent_to or \
            ctx.role_obj("r") in ctx.role_obj("s").equivalent_to

    def test_a_property_below_itself_states_nothing(self):
        ctx = self._built(dl.TBox().add_role_inclusion("r", "r"))
        assert ctx.role_obj("r").equivalent_to == []


# ---------------------------------------------------------------------------
# What HermiT says (live)
# ---------------------------------------------------------------------------

@live
@pytest.mark.owl_live
class TestAnswers:
    def test_two_classes_below_each_other_are_one_class(self):
        # A ⊑ B and B ⊑ A: a : A and a : ¬B contradict; a : A and a : B do not.
        tbox = dl.TBox().add(A, B).add(B, A)
        assert dl.external_abox_consistent(a_is(A, dl.Not(B)), tbox) is False
        assert dl.external_abox_consistent(a_is(B, dl.Not(A)), tbox) is False
        assert dl.external_abox_consistent(a_is(A, B), tbox) is True

    def test_add_equivalence_is_read_both_ways(self):
        tbox = dl.TBox().add_equivalence(A, B)
        assert dl.external_instance_check(dl.ABox().assert_concept("a", A), "a", B, tbox) is True
        assert dl.external_instance_check(dl.ABox().assert_concept("a", B), "a", A, tbox) is True
        assert dl.external_instance_check(dl.ABox().assert_concept("a", A), "a", C, tbox) is False

    def test_a_ring_of_three_makes_the_three_equal(self):
        # A ⊑ B ⊑ C ⊑ A: a : A gives a : C and a : B; a : C gives a : A.
        tbox = dl.TBox().add(A, B).add(B, C).add(C, A)
        assert dl.external_abox_consistent(a_is(A, dl.Not(C)), tbox) is False
        assert dl.external_abox_consistent(a_is(C, dl.Not(A)), tbox) is False
        assert dl.external_abox_consistent(a_is(B, dl.Not(A)), tbox) is False

    def test_the_ring_may_be_closed_by_the_first_inclusion_written(self):
        tbox = dl.TBox().add(C, A).add(B, C).add(A, B)
        assert dl.external_abox_consistent(a_is(A, dl.Not(C)), tbox) is False
        assert dl.external_abox_consistent(a_is(C, dl.Not(B)), tbox) is False

    def test_a_class_below_itself_says_nothing(self):
        tbox = dl.TBox().add(A, A)
        assert dl.external_abox_consistent(a_is(A), tbox) is True
        assert dl.external_instance_check(a_is(A), "a", B, tbox) is False

    def test_a_chain_is_not_taken_for_a_ring(self):
        # A ⊑ B ⊑ C: a : C and a : ¬A are consistent; a : A and a : ¬C are not.
        tbox = dl.TBox().add(A, B).add(B, C)
        assert dl.external_abox_consistent(a_is(C, dl.Not(A)), tbox) is True
        assert dl.external_abox_consistent(a_is(A, dl.Not(C)), tbox) is False

    def test_two_properties_below_each_other_are_one_property(self):
        # r ≡ s: s(a, b) gives r(a, b), so a : ¬∃r.⊤ contradicts it, and likewise from r to s.
        tbox = dl.TBox().add_equivalent_roles("r", "s")
        some_r, some_s = dl.Exists("r", dl.Top()), dl.Exists("s", dl.Top())
        from_s = dl.ABox().assert_role("a", "b", "s").assert_concept("a", dl.Not(some_r))
        from_r = dl.ABox().assert_role("a", "b", "r").assert_concept("a", dl.Not(some_s))
        assert dl.external_abox_consistent(from_s, tbox) is False
        assert dl.external_abox_consistent(from_r, tbox) is False

    def test_two_inclusions_between_two_properties_are_the_same(self):
        tbox = dl.TBox().add_role_inclusion("r", "s").add_role_inclusion("s", "r")
        from_s = dl.ABox().assert_role("a", "b", "s").assert_concept("a", dl.Not(dl.Exists("r", dl.Top())))
        assert dl.external_abox_consistent(from_s, tbox) is False

    def test_one_inclusion_between_two_properties_is_not_an_equivalence(self):
        # r ⊑ s only: r(a, b) gives s(a, b), but s(a, b) does not give r(a, b).
        tbox = dl.TBox().add_role_inclusion("r", "s")
        some_r, some_s = dl.Exists("r", dl.Top()), dl.Exists("s", dl.Top())
        from_r = dl.ABox().assert_role("a", "b", "r").assert_concept("a", dl.Not(some_s))
        from_s = dl.ABox().assert_role("a", "b", "s").assert_concept("a", dl.Not(some_r))
        assert dl.external_abox_consistent(from_r, tbox) is False
        assert dl.external_abox_consistent(from_s, tbox) is True

    def test_a_property_below_itself_says_nothing(self):
        tbox = dl.TBox().add_role_inclusion("r", "r")
        assert dl.external_abox_consistent(dl.ABox().assert_role("a", "b", "r"), tbox) is True

    def test_the_owl_reader_gives_a_knowledge_base_the_route_answers(self):
        text = ("Prefix(:=<http://ex.org/>)\n"
                "Ontology(<http://ex.org/o>\n"
                "  EquivalentClasses(:A :B)\n"
                "  ClassAssertion(:A :a)\n"
                "  ClassAssertion(ObjectComplementOf(:B) :a)\n"
                ")")
        tbox, abox = dl.parse_owl_functional(text)[:2]
        assert dl.abox_consistent(abox, tbox) is False
        assert dl.external_abox_consistent(abox, tbox) is False
