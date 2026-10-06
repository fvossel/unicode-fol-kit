"""The external (HermiT) route asserts a role that the TBox declares functional.

owlready2 stores the value of a FUNCTIONAL property as one attribute (``None`` while unset), not
as a list, so appending to it raised ``AttributeError`` for the knowledge base
``FunctionalObjectProperty(r)``, ``ObjectPropertyAssertion(r a b)`` — which is consistent: ``a``
has exactly one ``r``-successor, ``b``. A second assignment to such an attribute would also
replace the first, so two successors of one individual must both reach the reasoner.

Every expectation is derived by hand and written next to the test. The first tier needs
owlready2 only (it builds the ontology and reads it back); the live tier needs a JVM as well.
"""

import shutil

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import owl_reasoner as owl

A, B = dl.Atomic("A"), dl.Atomic("B")
SOME_R = dl.Exists("r", dl.Top())

needs_owlready2 = pytest.mark.skipif(not owl.available(), reason="owlready2 not installed")
live = pytest.mark.skipif(not (owl.available() and shutil.which("java")),
                          reason="owlready2 and/or a JVM (java on PATH) not found")


def functional():
    return dl.TBox().add_functional_role("r")


def role(*pairs):
    abox = dl.ABox()
    for a, b in pairs:
        abox.assert_role(a, b, "r")
    return abox


# ---------------------------------------------------------------------------
# The ontology that is built (owlready2 only, no JVM)
# ---------------------------------------------------------------------------

@needs_owlready2
class TestTheOntologyThatIsBuilt:
    @staticmethod
    def _built(tbox, abox):
        ow = owl._require_available()
        world = ow.World()
        onto = world.get_ontology("http://unicode-fol-kit.invalid/kb#")
        ctx = owl._Ctx(ow, world, onto, owl._characteristics(tbox))
        with onto:
            owl._build_kb(ctx, tbox, abox)
        return ow, ctx

    @staticmethod
    def _successors(ow, ctx, individual):
        return [(item.property, item.value) for item in ctx.ind(individual).is_a
                if isinstance(item, ow.Restriction) and item.type == ow.VALUE]

    def test_a_functional_assertion_is_built(self):
        ow, ctx = self._built(functional(), role(("a", "b")))
        assert self._successors(ow, ctx, "a") == [(ctx.role_obj("r"), ctx.ind("b"))]

    def test_two_successors_of_one_individual_are_both_kept(self):
        ow, ctx = self._built(functional(), role(("a", "b"), ("a", "c")))
        assert self._successors(ow, ctx, "a") == [(ctx.role_obj("r"), ctx.ind("b")),
                                                   (ctx.role_obj("r"), ctx.ind("c"))]

    def test_the_role_is_functional_in_the_ontology(self):
        ow, ctx = self._built(functional(), role(("a", "b")))
        assert ow.FunctionalProperty in ctx.role_obj("r").is_a

    def test_a_role_that_is_not_functional_keeps_the_property_assertion(self):
        # The path that always worked: the successor is a value of the property itself.
        ow, ctx = self._built(dl.TBox(), role(("a", "b")))
        assert getattr(ctx.ind("a"), ctx.role_obj("r").name) == [ctx.ind("b")]
        assert self._successors(ow, ctx, "a") == []

    def test_a_sub_property_of_a_functional_property_is_built(self):
        # s ⊑ r with r functional: owlready2 makes s a Python subclass of r, so s holds one value too
        # (and every s-successor is an r-successor, which OWL 2 entails anyway).
        tbox = functional().add_role_inclusion("s", "r")
        ow, ctx = self._built(tbox, dl.ABox().assert_role("a", "b", "s"))
        assert issubclass(ctx.role_obj("s"), ow.FunctionalProperty)
        assert self._successors(ow, ctx, "a") == [(ctx.role_obj("s"), ctx.ind("b"))]

    def test_an_inverse_functional_role_still_builds(self):
        tbox = dl.TBox().add_inverse_functional_role("r")
        ow, ctx = self._built(tbox, role(("a", "b")))
        assert ow.InverseFunctionalProperty in ctx.role_obj("r").is_a


# ---------------------------------------------------------------------------
# What HermiT says (live)
# ---------------------------------------------------------------------------

@live
@pytest.mark.owl_live
class TestAnswers:
    def test_one_successor_is_consistent(self):
        # Two elements a, b with r = {(a, b)}: functionality holds.
        assert dl.external_abox_consistent(role(("a", "b")), functional()) is True

    def test_two_successors_are_identified_not_contradictory(self):
        # r(a,b), r(a,c) and r functional: b = c is forced, and that is consistent
        # (one element b = c, r = {(a, b)}).
        assert dl.external_abox_consistent(role(("a", "b"), ("a", "c")), functional()) is True

    def test_two_distinct_successors_are_inconsistent(self):
        # Functionality forces b = c, and b != c is asserted. Without functionality they
        # are two successors of a, which is fine: that variant shows that both assertions
        # reached the reasoner (an assertion replaced by its successor would make the
        # functional case consistent).
        abox = role(("a", "b"), ("a", "c")).assert_distinct("b", "c")
        assert dl.external_abox_consistent(abox, functional()) is False
        assert dl.external_abox_consistent(abox, dl.TBox()) is True

    def test_two_required_successors_of_a_functional_role_are_inconsistent(self):
        # a : (>= 2 r.Top) needs two r-successors of a; functionality allows one.
        abox = role(("a", "b")).assert_concept("a", dl.AtLeast(2, "r", dl.Top()))
        assert dl.external_abox_consistent(abox, functional()) is False

    def test_a_universal_restriction_reaches_the_successor(self):
        # a : ∀r.A and r(a,b) give b : A; b : B follows from nothing.
        abox = role(("a", "b")).assert_concept("a", dl.ForAll("r", A))
        assert dl.external_instance_check(abox, "b", A, functional()) is True
        assert dl.external_instance_check(abox, "b", B, functional()) is False

    def test_functionality_identifies_the_two_successors(self):
        # b = c follows from r(a,b), r(a,c) and functionality, so b is the nominal {c}; with no
        # functionality the two successors may differ.
        abox = role(("a", "b"), ("a", "c"))
        assert dl.external_instance_check(abox, "b", dl.Nominal("c"), functional()) is True
        assert dl.external_instance_check(abox, "b", dl.Nominal("c"), dl.TBox()) is False

    def test_retrieval_finds_the_individuals_with_a_successor(self):
        # ∃r.⊤ holds of exactly the individuals that have an r-successor: a and c.
        abox = role(("a", "b"), ("c", "d"))
        assert dl.external_instance_retrieval(abox, SOME_R, functional()) == {"a", "c"}

    def test_realization_of_one_individual(self):
        assert dl.external_realize(role(("a", "b")), "a", [SOME_R], functional()) == [SOME_R]

    def test_realization_of_every_individual(self):
        # a has the successor b; b has none.
        assert dl.external_realize_all(role(("a", "b")), [SOME_R], functional()) == {"a": [SOME_R], "b": []}

    def test_a_sub_property_of_a_functional_property_is_functional_too(self):
        # s ⊑ r with r functional: s(a, b) and s(a, c) give r(a, b) and r(a, c), hence b = c.
        tbox = functional().add_role_inclusion("s", "r")
        one = dl.ABox().assert_role("a", "b", "s")
        assert dl.external_abox_consistent(one, tbox) is True
        two = dl.ABox().assert_role("a", "b", "s").assert_role("a", "c", "s").assert_distinct("b", "c")
        assert dl.external_abox_consistent(two, tbox) is False
        assert dl.external_abox_consistent(two, dl.TBox().add_role_inclusion("s", "r")) is True

    def test_two_demands_on_the_one_successor_cannot_both_be_met(self):
        # ∃r.A ⊓ ∃r.¬A: the one r-successor would be in A and in ¬A. Without functionality there
        # are two successors and it is satisfiable.
        both = dl.And(dl.Exists("r", A), dl.Exists("r", dl.Not(A)))
        assert dl.external_concept_satisfiable(both, functional()) is False
        assert dl.external_concept_unsatisfiable(both, functional()) is True
        assert dl.external_concept_satisfiable(both, dl.TBox()) is True

    def test_subsumption_and_equivalence_follow_the_single_successor(self):
        # With at most one r-successor, the successor that is in A is the only one: ∃r.A ⊑ ∀r.A,
        # and ∃r.A ≡ ∀r.A ⊓ ∃r.⊤. Without functionality a second successor outside A breaks the first.
        some_a, all_a = dl.Exists("r", A), dl.ForAll("r", A)
        assert dl.external_subsumes(some_a, all_a, functional()) is True
        assert dl.external_subsumes(some_a, all_a, dl.TBox()) is False
        assert dl.external_equivalent(some_a, dl.And(all_a, SOME_R), functional()) is True
        assert dl.external_equivalent(some_a, dl.And(all_a, SOME_R), dl.TBox()) is False

    def test_a_functional_role_nobody_asserts_is_consistent(self):
        assert dl.external_abox_consistent(dl.ABox().assert_concept("a", A), functional()) is True

    def test_the_owl_reader_produces_a_knowledge_base_the_route_answers(self):
        text = ("Prefix(:=<http://ex.org/>)\n"
                "Ontology(<http://ex.org/o>\n"
                "  FunctionalObjectProperty(:r)\n"
                "  ObjectPropertyAssertion(:r :a :b)\n"
                ")")
        tbox, abox = dl.parse_owl_functional(text)[:2]
        assert dl.abox_consistent(abox, tbox) is True
        assert dl.external_abox_consistent(abox, tbox) is True
