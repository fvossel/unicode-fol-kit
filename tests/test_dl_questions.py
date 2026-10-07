r"""How a knowledge base with a data layer is ASKED about: ``kb_to_fol(query=)``,
the three goal methods, the verdict contract, and the refusals that make the
wrong spelling impossible to follow silently.

The first-order image of the data layer was checked against the OWL 2 Direct
Semantics and its axioms are right. What went wrong was the QUESTION: the sort
axioms, the typing and the datatype lattice are derived from the vocabulary the
knowledge base MENTIONS, so a goal that names a datatype, a data property, a
literal or an object property the knowledge base does not was asked of a weaker
theory, and the documented recipe (``Not(∃x concept_to_fol(C))``, an
unrelativised ``subsumption_to_fol``) answered ``refuted`` for entailments OWL 2
makes. The bundle now builds the question itself.

Every expected verdict below is derived by hand from the OWL 2 Direct Semantics
in the comment above it, never read off the code. Z3 budgets are in
MILLISECONDS and are never shrunk: ``unknown`` is not a verdict.

Which tests are RED on the code before the fix is said in each comment
("RED before"): the ones about a method or a keyword that did not exist fail
with ``AttributeError``/``TypeError`` there, the ones about a refusal fail by
the refusal not being raised.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.fol.nodes import Not as FNot, Quantifier, Variable

TIMEOUT_MS = 30000

L = dl.Literal
INT, DEC, STR = (dl.Datatype("xsd:integer"), dl.Datatype("xsd:decimal"),
                 dl.Datatype("xsd:string"))
A, B, C, D = (dl.Atomic(name) for name in "ABCD")


def _status(goal, premises) -> str:
    verdict = api.prove(goal, list(premises), timeout=TIMEOUT_MS).status
    assert verdict in ("proved", "refuted"), verdict      # unknown measures nothing
    return verdict


# --------------------------------------------------------------------------- #
# 1. The two examples, now answered through the bundle.
# --------------------------------------------------------------------------- #

def test_a_concept_that_clashes_only_through_the_datatype_lattice_is_unsatisfiable():
    # C = ∃HasV.xsd:integer ⊓ ∀HasV.xsd:string.
    # OWL 2: an instance x needs a HasV-value v in xsd:integer (the ∃), and every
    # HasV-value is in xsd:string (the ∀), so v is in both datatypes. The OWL 2
    # datatype map makes xsd:integer (owl:real family) and xsd:string
    # (rdf:PlainLiteral family) DISJOINT, so no such v exists: C is unsatisfiable.
    # RED before: kb_to_fol took no query=, and the documented recipe
    # (Not(∃x concept_to_fol(C)) over kb_to_fol(TBox()).tbox_premises) said
    # `refuted` -- a data value satisfied the existential.
    concept = dl.And(dl.DataExists("HasV", INT), dl.DataForAll("HasV", STR))
    kb = dl.kb_to_fol(dl.TBox(), query=[concept])
    assert kb.separation == "two-sorted" and kb.data_layer is True
    assert [f.to_unicode_str() for f in kb.axioms_of_kind("DatatypeDisjointness")] == [
        "∀v ¬(xsd:integer(v) ∧ xsd:string(v))"]
    goal = kb.unsatisfiability_goal(concept)
    assert goal.to_unicode_str() == (
        "¬∃x (OwlThing(x) ∧ (∃x0 (HasV(x, x0) ∧ xsd:integer(x0)) "
        "∧ ∀x1 (HasV(x, x1) → xsd:string(x1))))")
    assert _status(goal, kb.tbox_premises) == "proved"


def test_the_bare_closure_is_not_the_question_the_bundle_asks():
    # The contrast that makes the test above discriminate: the closure the old
    # recipe asked, over the SAME bundle's premises, is the wrong question -- a
    # data value x (not an object) has a HasV-value only in the sense that it is
    # one, and OwlThing is nowhere required, so the image has a model of it.
    concept = dl.And(dl.DataExists("HasV", INT), dl.DataForAll("HasV", STR))
    kb = dl.kb_to_fol(dl.TBox(), query=[concept])
    bare = FNot(Quantifier("∃", Variable("x"), dl.concept_to_fol(concept)))
    assert bare != kb.unsatisfiability_goal(concept)
    assert "OwlThing" not in bare.to_unicode_str()
    assert "OwlThing" in kb.unsatisfiability_goal(concept).to_unicode_str()


def test_a_concept_the_terminology_makes_empty_is_unsatisfiable_beside_a_data_layer():
    # TBox: A ⊑ ⊥, plus DataPropertyRange(HasV xsd:integer) (the data layer).
    # OWL 2: A^I ⊆ ∅, so A is unsatisfiable. The image relativises the GCI to the
    # objects, ∀x (OwlThing(x) ∧ A(x) → x ≠ x), so ¬∃x (OwlThing(x) ∧ A(x)).
    # RED before: no unsatisfiability_goal; the recipe answered `refuted` (A was
    # reported satisfiable, a data value being an A).
    kb = dl.kb_to_fol(dl.TBox().add(A, dl.Bottom()).add_data_property_range("HasV", INT))
    assert _status(kb.unsatisfiability_goal(A), kb.tbox_premises) == "proved"
    # B is mentioned nowhere: it is satisfiable (a model with one B object), and
    # the image says so too -- but see test_a_refuted_verdict_is_decisive_only_... :
    # with a data layer that is the image's answer, not a guarantee.
    assert _status(kb.unsatisfiability_goal(B), kb.tbox_premises) == "refuted"


def test_an_entailment_through_the_datatype_lattice_needs_the_goals_datatype_in_the_bundle():
    # DataPropertyRange(HasV xsd:integer). OWL 2: every HasV-value is an integer,
    # and xsd:integer is below xsd:decimal, so  ∃HasV.xsd:integer ⊑ ∃HasV.xsd:decimal
    # holds (the integer value is the decimal witness).
    # RED before: kb_to_fol(tbox) alone has no integer ⊑ decimal axiom (xsd:decimal
    # is not mentioned), and the goal came back `refuted`.
    tbox = dl.TBox().add_data_property_range("HasV", INT)
    sub, sup = dl.DataExists("HasV", INT), dl.DataExists("HasV", DEC)
    kb = dl.kb_to_fol(tbox, query=[sub, sup])
    assert _status(kb.subsumption_goal(sub, sup), kb.tbox_premises) == "proved"
    # Without query= the bundle does not cover xsd:decimal, and says so, by name,
    # instead of answering `refuted`.
    with pytest.raises(dl.UnsupportedDatatypeError, match="xsd:decimal") as info:
        dl.kb_to_fol(tbox).subsumption_goal(sub, sup)
    assert "query=" in str(info.value) and "dl.kb_to_fol" in str(info.value)


def test_a_datatype_disjoint_from_the_ranges_empties_the_restriction():
    # Same knowledge base. OWL 2: a HasV-value is an integer, integer and string
    # are disjoint, so no value is a string and  ∃HasV.xsd:string ⊑ ⊥  holds.
    # RED before: `refuted` (xsd:string was not mentioned, so no disjointness).
    tbox = dl.TBox().add_data_property_range("HasV", INT)
    strings = dl.DataExists("HasV", STR)
    kb = dl.kb_to_fol(tbox, query=[strings])
    assert _status(kb.subsumption_goal(strings, dl.Bottom()), kb.tbox_premises) == "proved"
    with pytest.raises(dl.UnsupportedDatatypeError, match="xsd:string"):
        dl.kb_to_fol(tbox).subsumption_goal(strings, dl.Bottom())


def test_an_object_level_subsumption_beside_a_data_layer_is_proved_by_the_bundles_goal():
    # A ⊑ B, B ⊑ C, plus a data property range. OWL 2: A ⊑ C by transitivity of ⊑.
    # The default spelling subsumption_to_fol(A, C) asks it of data values too and
    # comes back `refuted` -- silently. The bundle relativises to the objects.
    # RED before: no subsumption_goal.
    tbox = dl.TBox().add(A, B).add(B, C).add_data_property_range("HasV", INT)
    kb = dl.kb_to_fol(tbox)
    goal = kb.subsumption_goal(A, C)
    assert goal.to_unicode_str() == "∀x (OwlThing(x) ∧ A(x) → C(x))"
    assert _status(goal, kb.tbox_premises) == "proved"
    # and a subsumption that does NOT hold is not proved: nothing says C ⊑ A
    assert _status(kb.subsumption_goal(C, A), kb.tbox_premises) == "refuted"
    # the plain spelling is the pitfall the method removes
    assert _status(dl.subsumption_to_fol(A, C), kb.tbox_premises) == "refuted"


def test_an_instance_goal_follows_the_knowledge_base_and_the_lattice():
    # Alpha ⊑ DataHasValue(HasV 1^^xsd:integer), alice : Alpha.
    # OWL 2: HasV(alice, 1) and 1 is an xsd:integer, so alice : ∃HasV.xsd:integer;
    # and integer ⊆ decimal, so alice : ∃HasV.xsd:decimal as well. Not a string:
    # a model whose only HasV-value of alice is 1 has no string value (and the
    # image's countermodel is that very model).
    alpha = dl.Atomic("Alpha")
    tbox = dl.TBox().add(alpha, dl.DataHasValue("HasV", L("1", "xsd:integer")))
    abox = dl.ABox().assert_concept("alice", alpha)
    kb = dl.kb_to_fol(tbox, abox)
    integer = dl.DataExists("HasV", INT)
    assert _status(kb.instance_goal("alice", integer), kb.premises) == "proved"
    # xsd:decimal is not mentioned by the knowledge base: refused, not `refuted`
    decimal = dl.DataExists("HasV", DEC)
    with pytest.raises(dl.UnsupportedDatatypeError, match="xsd:decimal"):
        kb.instance_goal("alice", decimal)
    kb = dl.kb_to_fol(tbox, abox, query=[decimal, dl.DataExists("HasV", STR)])
    assert _status(kb.instance_goal("alice", decimal), kb.premises) == "proved"
    assert _status(kb.instance_goal("alice", dl.DataExists("HasV", STR)),
                   kb.premises) == "refuted"


def test_an_individual_the_bundle_does_not_type_is_asked_about_as_an_object():
    # Every OWL 2 individual is in the object domain, so `zed : ⊤` is entailed by
    # anything; on a two-sorted bundle the goal says so, OwlThing(zed) → π(C, zed),
    # because no axiom of the bundle types an individual it never saw.
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT))
    assert kb.instance_goal("zed", A).to_unicode_str() == "OwlThing(zed) → A(zed)"
    assert _status(kb.instance_goal("zed", dl.Top()), kb.premises) == "proved"
    # one the bundle does type needs no relativisation
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT),
                      dl.ABox().assert_concept("alice", A))
    assert kb.instance_goal("alice", B).to_unicode_str() == "B(alice)"


# --------------------------------------------------------------------------- #
# 2. Without a data layer the three goals are the spellings the kit always had,
#    and agree with the tableau.
# --------------------------------------------------------------------------- #

def test_without_a_data_layer_the_goals_are_the_documented_spellings():
    tbox = dl.TBox().add(A, B).add(B, C)
    kb = dl.kb_to_fol(tbox, dl.ABox().assert_concept("a", A))
    concept = dl.Exists("r", A)
    assert kb.separation == "none" and kb.data_layer is False
    assert kb.subsumption_goal(A, C) == dl.subsumption_to_fol(A, C)
    assert kb.unsatisfiability_goal(concept) == FNot(
        Quantifier("∃", Variable("x"), dl.concept_to_fol(concept)))
    assert kb.instance_goal("a", concept) == dl.abox_to_fol(
        dl.ABox().assert_concept("a", concept))


def test_the_goals_agree_with_the_tableau_on_a_knowledge_base_without_a_data_layer():
    # TBox: Dog ⊑ Mammal, Mammal ⊑ Animal, Ghost ⊑ ∃haunts.Void, Void ⊑ ⊥; rex : Dog.
    # By hand: Dog ⊑ Animal holds, Animal ⊑ Dog does not; rex : Animal holds,
    # rex : Cat does not (open world); Ghost is unsatisfiable (it needs a haunts-
    # successor in the empty Void), Dog is satisfiable.
    dog, mammal, animal, cat = (dl.Atomic(n) for n in ("Dog", "Mammal", "Animal", "Cat"))
    ghost, void = dl.Atomic("Ghost"), dl.Atomic("Void")
    tbox = (dl.TBox().add(dog, mammal).add(mammal, animal)
            .add(ghost, dl.Exists("haunts", void)).add(void, dl.Bottom()))
    abox = dl.ABox().assert_concept("rex", dog)
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.refutation_is_decisive is True
    for sub, sup, holds in ((dog, animal, True), (animal, dog, False)):
        assert dl.subsumes(sub, sup, tbox) is holds
        assert _status(kb.subsumption_goal(sub, sup), kb.tbox_premises) == (
            "proved" if holds else "refuted")
    for concept, holds in ((animal, True), (cat, False)):
        assert dl.instance_check(abox, "rex", concept, tbox) is holds
        assert _status(kb.instance_goal("rex", concept), kb.premises) == (
            "proved" if holds else "refuted")
    for concept, satisfiable in ((ghost, False), (dog, True)):
        assert dl.concept_satisfiable(concept, tbox) is satisfiable
        assert _status(kb.unsatisfiability_goal(concept), kb.tbox_premises) == (
            "refuted" if satisfiable else "proved")


# --------------------------------------------------------------------------- #
# 3. What a "refuted" is worth.
# --------------------------------------------------------------------------- #

def test_a_refuted_verdict_is_decisive_only_when_there_is_no_data_layer():
    # decisive: the image of an object-only knowledge base is faithful
    assert dl.kb_to_fol(dl.TBox().add(A, B)).refutation_is_decisive is True
    assert dl.kb_to_fol(dl.TBox().add(A, B), query=[C, dl.Exists("r", D)]
                        ).refutation_is_decisive is True
    # not decisive: any data property, datatype or literal, wherever it comes from
    assert dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT)
                        ).refutation_is_decisive is False
    assert dl.kb_to_fol(dl.TBox(), dl.ABox().assert_data("a", "HasV", L("1", "xsd:integer"))
                        ).refutation_is_decisive is False
    assert dl.kb_to_fol(dl.TBox().add(A, B), query=[dl.DataExists("HasV", INT)]
                        ).refutation_is_decisive is False
    # ... including the mode in which the caller supplies the sort discipline
    assert dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT),
                        separation="none").refutation_is_decisive is False


def test_the_property_is_read_only():
    kb = dl.kb_to_fol(dl.TBox().add(A, B))
    assert kb.refutation_is_decisive is True
    with pytest.raises(AttributeError):
        kb.refutation_is_decisive = False


# --------------------------------------------------------------------------- #
# 4. query=: its vocabulary joins everything derived from the vocabulary.
# --------------------------------------------------------------------------- #

def test_a_data_restriction_in_the_query_makes_the_image_two_sorted():
    # Hand-derived. TBox A ⊑ B has no data layer: with no query the bundle has no
    # side axioms and the GCI is as written. A query that names a data property
    # and a datatype brings the data layer in: the GCI is restricted to the object
    # domain, and the side axioms are the separation (one, plus the two
    # non-emptiness sentences), the typing of the one data property, and the
    # guard of the one datatype -- no object role, no individual, no literal, no
    # data-box axiom.
    tbox = dl.TBox().add(A, B)
    plain = dl.kb_to_fol(tbox)
    assert plain.separation == "none" and plain.side_axioms == ()
    assert plain.formula.to_unicode_str() == "∀x (A(x) → B(x))"
    kb = dl.kb_to_fol(tbox, query=[dl.DataExists("d", INT)])
    assert kb.separation == "two-sorted"
    assert kb.formula.to_unicode_str() == "∀x (OwlThing(x) ∧ A(x) → B(x))"
    assert [(a.kind, a.group) for a in kb.side_axioms] == [
        ("DomainSeparation", "sort"), ("DomainNonEmptiness", "sort"),
        ("DomainNonEmptiness", "sort"), ("DataPropertyTyping", "sort"),
        ("DatatypeGuard", "datatype")]
    assert [a.to_unicode_str() for a in kb.axioms_of_kind("DataPropertyTyping")] == [
        "∀x ∀v (d(x, v) → OwlThing(x) ∧ OwlData(v))"]


def test_the_queries_object_properties_are_typed_too():
    # A ⊑ ∃r.⊤ and ⊤ ⊑ B, one data property. OWL 2: every A has an r-successor,
    # which is an object (an r-edge relates individuals), and every object is a
    # B, so A ⊑ ∃r.B. Proved only if r is TYPED (object-to-object): the typing
    # is derived from the vocabulary, so r must be in it. Here r is in the TBox,
    # which is the case where it always was; with a role only the QUESTION names
    # the bundle refuses until query= brings it in.
    tbox = dl.TBox().add(A, dl.Exists("r", dl.Top())).add(dl.Top(), B).add_data_property_range(
        "HasV", INT)
    kb = dl.kb_to_fol(tbox)
    assert _status(kb.subsumption_goal(A, dl.Exists("r", B)), kb.tbox_premises) == "proved"
    # a role the knowledge base never mentions: any s-successor of an A is an
    # object, a B -- so  A ⊓ ∃s.⊤ ⊑ ∃s.B  holds in OWL 2 (TBox: ⊤ ⊑ B)
    sub, sup = dl.And(A, dl.Exists("s", dl.Top())), dl.Exists("s", B)
    with pytest.raises(dl.UnsupportedDatatypeError, match="object property 's'"):
        kb.subsumption_goal(sub, sup)
    kb = dl.kb_to_fol(tbox, query=[sub, sup])
    assert _status(kb.subsumption_goal(sub, sup), kb.tbox_premises) == "proved"


def test_a_binder_avoids_the_individuals_of_the_query():
    # Variable("x") and Constant("x") are the same constant to every backend, so
    # a GCI binder called x would capture a queried individual called x: the
    # binder is renamed to the first free letter+digits, x0 -- exactly as it is
    # for an individual of the knowledge base.
    kb = dl.kb_to_fol(dl.TBox().add(A, B), query=[dl.Nominal("x")])
    assert kb.formula.to_unicode_str() == "∀x0 (A(x0) → B(x0))"
    two = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT), query=[dl.Nominal("x")])
    assert two.unsatisfiability_goal(dl.And(A, dl.Nominal("x"))).to_unicode_str() == (
        "¬∃x0 (OwlThing(x0) ∧ (A(x0) ∧ x0 = x))")
    # and an individual of the query is typed like any other
    assert [a.to_unicode_str() for a in two.axioms_of_kind("IndividualTyping")] == [
        "OwlThing(x)"]


def test_data_sort_axioms_takes_the_same_query():
    tbox = dl.TBox().add(A, B)
    query = [dl.DataExists("d", INT)]
    assert dl.data_sort_axioms(tbox) == ()
    assert dl.data_sort_axioms(tbox, query=query) == dl.kb_to_fol(tbox, query=query).side_axioms


@pytest.mark.parametrize("query", [A, "A", [1], [A, "B"]], ids=["concept", "str", "int", "mixed"])
def test_query_is_an_iterable_of_concepts(query):
    # "query=" is in the refusal's own text; the TypeError an unknown keyword
    # raises says "'query'" and so would not satisfy this
    with pytest.raises(TypeError, match="query="):
        dl.kb_to_fol(dl.TBox(), query=query)


def test_a_query_refuses_what_no_goal_could_be_built_from():
    # a literal with no first-order term, an OWL 2 built-in property name as a role
    with pytest.raises(dl.UnsupportedDatatypeError, match="xsd:double"):
        dl.kb_to_fol(dl.TBox(), query=[dl.DataHasValue("d", L("1.5", "xsd:double"))])
    with pytest.raises(dl.RoleExpressionError):
        dl.kb_to_fol(dl.TBox(), query=[dl.Exists("owl:topObjectProperty", A)])


# --------------------------------------------------------------------------- #
# 5. A goal over a name the bundle does not cover is refused, by name.
# --------------------------------------------------------------------------- #

def test_a_bundle_without_a_data_layer_refuses_a_data_goal():
    kb = dl.kb_to_fol(dl.TBox().add(A, B))
    concept = dl.DataExists("HasV", INT)
    for ask in (lambda: kb.unsatisfiability_goal(concept),
                lambda: kb.subsumption_goal(A, concept),
                lambda: kb.instance_goal("a", concept)):
        with pytest.raises(dl.UnsupportedDatatypeError) as info:
            ask()
        message = str(info.value)
        assert "data property 'HasV'" in message and "xsd:integer" in message
        assert "no data layer" in message and "query=" in message


def test_a_two_sorted_bundle_refuses_an_uncovered_data_property_datatype_or_literal():
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT),
                      dl.ABox().assert_data("a", "HasV", L("1", "xsd:integer")))
    # covered: the property, the datatype and the literal all occur in the knowledge base
    kb.unsatisfiability_goal(dl.DataHasValue("HasV", L("1", "xsd:integer")))
    # uncovered, each by name:
    for concept, name in (
            (dl.DataExists("Other", INT), "data property 'Other'"),
            (dl.DataExists("HasV", DEC), "datatype 'xsd:decimal'"),
            (dl.DataHasValue("HasV", L("2", "xsd:integer")), 'literal "2"^^xsd:integer'),
            # the SAME value written in another datatype is another typing fact
            (dl.DataHasValue("HasV", L("1.0", "xsd:decimal")), 'literal "1.0"^^xsd:decimal')):
        with pytest.raises(dl.UnsupportedDatatypeError) as info:
            kb.unsatisfiability_goal(concept)
        assert name in str(info.value), (name, str(info.value))
        # and query= is the way out
        covered = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT),
                               dl.ABox().assert_data("a", "HasV", L("1", "xsd:integer")),
                               query=[concept])
        covered.unsatisfiability_goal(concept)


def test_rdfs_literal_needs_no_axiom_of_its_own():
    # rdfs:Literal IS the data domain, rendered as OwlData: nothing to cover.
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT))
    goal = kb.unsatisfiability_goal(dl.DataExists("HasV", dl.Datatype("rdfs:Literal")))
    assert "OwlData(x0)" in goal.to_unicode_str()


@pytest.mark.parametrize("separation", ["data-lattice", "none"])
def test_a_data_layer_bundle_that_is_not_two_sorted_builds_no_goal(separation):
    # Without the two-sorted relativisation an inclusion also ranges over DATA
    # values, so the premises are STRONGER than OWL 2's and a proof over them does
    # not transfer. The goal methods say so instead of building a goal.
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT), separation=separation)
    assert kb.separation == separation and kb.data_layer is True
    for build in (lambda: kb.subsumption_goal(A, B),
                  lambda: kb.unsatisfiability_goal(A),
                  lambda: kb.instance_goal("a", A)):
        with pytest.raises(dl.UnsupportedDatatypeError, match="STRONGER") as refusal:
            build()
        assert separation in str(refusal.value)
        assert "two-sorted" in str(refusal.value)


def test_why_the_data_lattice_regime_is_refused_a_consistent_knowledge_base_with_an_inconsistent_image():
    # TBox:  ⊤ ⊑ {a}      range(d) = {1, 2}
    #
    # OWL 2, by hand: one object a, A = {a}, d empty. Everything holds — ⊤ is the
    # OBJECT domain {a}, and the two data values 1 and 2 live in the data domain,
    # which ⊤ does not range over. CONSISTENT, and A is satisfiable.
    #
    # The data-lattice image writes the inclusion as ∀x (x = a), over everything.
    # The literals 1 and 2 are terms of the image and its literal axioms say
    # 1 ≠ 2; but 1 = a and 2 = a, so 1 = 2. The IMAGE is inconsistent, and from
    # an inconsistent image every goal is proved.
    tbox = (dl.TBox().add(dl.Top(), dl.Nominal("a"))
            .add_data_property_range("d", dl.DataOneOf((L("1", "xsd:integer"),
                                                         L("2", "xsd:integer")))))
    lattice = dl.kb_to_fol(tbox, separation="data-lattice", query=[A])
    assert _status(FNot(lattice.formula), list(lattice.axioms)) == "proved"
    # ... which is exactly why no goal is handed out for it
    with pytest.raises(dl.UnsupportedDatatypeError, match="STRONGER"):
        lattice.unsatisfiability_goal(A)
    # The default regime restricts the inclusion to the objects, and is right:
    two_sorted = dl.kb_to_fol(tbox, query=[A])
    assert two_sorted.separation == "two-sorted"
    assert _status(FNot(two_sorted.formula), list(two_sorted.axioms)) == "refuted"
    assert _status(two_sorted.unsatisfiability_goal(A), list(two_sorted.tbox_premises)) == "refuted"


@pytest.mark.parametrize("separation", ["two-sorted", "data-lattice", "none"])
def test_without_a_data_layer_the_separation_asked_for_changes_nothing(separation):
    # No data property, datatype or literal anywhere: nothing is added whatever
    # was asked for, the image is the faithful one, and the goal is the plain
    # closure — so the refusal above cannot be met here.
    kb = dl.kb_to_fol(dl.TBox().add(A, B), separation=separation)
    assert kb.separation == "none" and kb.data_layer is False
    assert kb.refutation_is_decisive is True
    assert kb.subsumption_goal(A, B).to_unicode_str() == "∀x (A(x) → B(x))"
    assert _status(kb.subsumption_goal(A, B), list(kb.tbox_premises)) == "proved"


def test_a_goal_name_that_clashes_with_the_bundles_is_refused():
    # OWL 2 DL: a class and a datatype of one name, or an object property and a
    # data property of one name, are not allowed, and the image has one predicate
    # per name. The clash across the bundle and the goal is refused like one
    # inside a knowledge base.
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("HasV", INT))
    with pytest.raises(dl.UnsupportedDatatypeError, match="class and a datatype"):
        kb.subsumption_goal(dl.Atomic("xsd:integer"), B)
    with pytest.raises(dl.UnsupportedDatatypeError, match="object property and a data"):
        kb.subsumption_goal(dl.Exists("HasV", A), B)
    # a goal class named like the reserved guard predicate
    with pytest.raises(dl.UnsupportedDatatypeError, match="OwlThing"):
        kb.subsumption_goal(dl.Atomic("OwlThing"), B)


def test_a_bundle_not_built_by_kb_to_fol_cannot_build_a_goal():
    kb = dl.kb_to_fol(dl.TBox().add(A, B))
    by_hand = dl.KnowledgeBaseFOL(formula=kb.formula, side_axioms=(), tbox=kb.tbox,
                                  abox=kb.abox)
    with pytest.raises(ValueError, match="not built by dl.kb_to_fol"):
        by_hand.subsumption_goal(A, B)


def test_the_goal_methods_reject_a_non_name_individual():
    kb = dl.kb_to_fol(dl.TBox().add(A, B))
    for bad in ("", None, 3):
        with pytest.raises(TypeError, match="non-empty name"):
            kb.instance_goal(bad, A)


# --------------------------------------------------------------------------- #
# 6. The refusals of the in-house tableau name the methods, and the MCP tools
#    carry those messages.
# --------------------------------------------------------------------------- #

def test_the_tableaus_refusal_of_a_data_concept_names_the_methods():
    # RED before: it named the old recipe, api.prove(goal, kb_to_fol(...).premises),
    # which is the spelling that answered wrongly.
    with pytest.raises(dl.UnsupportedConceptError) as info:
        dl.concept_satisfiable(dl.DataExists("d", INT))
    message = str(info.value)
    assert "no data domain" in message
    for fragment in ("query=[concept]", "kb.unsatisfiability_goal(concept)",
                     "kb.subsumption_goal", "kb.instance_goal",
                     "kb.refutation_is_decisive", "atp.z3_arith"):
        assert fragment in message, (fragment, message)
    assert "kb_to_fol(tbox, abox).premises" not in message


def test_the_tableaus_refusal_of_a_data_axiom_names_the_methods():
    with pytest.raises(dl.UnsupportedAxiomError) as info:
        dl.abox_consistent(dl.ABox(), dl.TBox().add_functional_data_property("P"))
    message = str(info.value)
    for fragment in ("no data domain", "dl.kb_to_fol(tbox, abox, query=", "kb.subsumption_goal",
                     "kb.unsatisfiability_goal", "kb.instance_goal",
                     "kb.refutation_is_decisive", "atp.z3_arith", "not wired"):
        assert fragment in message, (fragment, message)


def test_the_mcp_dl_tools_carry_the_refusals_that_name_the_methods():
    pytest.importorskip("mcp", reason="optional [mcp] extra not installed")
    from unicode_logic_kit.mcp.server import dl_classify, dl_concept_satisfiable, translate

    concept = dl_concept_satisfiable("d some xsd:integer", syntax="manchester")
    assert concept["error"]["type"] == "UnsupportedConceptError"
    for fragment in ("DataExists", "query=[concept]", "kb.unsatisfiability_goal(concept)"):
        assert fragment in concept["error"]["message"], concept
    axiom = dl_classify(tbox=[{"functionaldata": "d"}])
    assert axiom["error"]["type"] == "UnsupportedAxiomError"
    assert "kb.subsumption_goal" in axiom["error"]["message"]
    # the translate tool reads an alc term with the glyph grammar, which cannot say
    # a data restriction at all, so it never reaches the edge that refuses one
    glyph = translate("∃d.xsd:integer", "alc", "fol")
    assert glyph["ok"] is False and "DATATYPE, not a class" in glyph["errors"][0]["message"]


# --------------------------------------------------------------------------- #
# 7. Name clashes OWL 2 DL forbids: still refused.
# --------------------------------------------------------------------------- #

def test_an_object_property_and_a_data_property_of_one_name_are_refused():
    # Has is an object role in a GCI and a data property in a range axiom.
    tbox = dl.TBox().add(A, dl.Exists("Has", B)).add_data_property_range("Has", INT)
    with pytest.raises(dl.UnsupportedDatatypeError, match="object property and a data property"):
        dl.kb_to_fol(tbox, dl.ABox().assert_concept("a", A))
    # the natural trigger: Manchester `d min 1` (no filler) stays an OBJECT
    # restriction, and `d` is also a data property of an assertion
    tbox = dl.TBox().add(A, dl.parse_manchester("d min 1"))
    abox = dl.ABox().assert_data("a", "d", L("3", "xsd:integer")).assert_concept("a", A)
    with pytest.raises(dl.UnsupportedDatatypeError, match="object property and a data property"):
        dl.kb_to_fol(tbox, abox)


def test_every_function_that_collects_the_vocabulary_refuses_the_clash():
    # The guide says dl.kb_to_fol AND the functions that collect the vocabulary
    # refuse it; each is checked on a clash of its own input.
    tbox = dl.TBox().add(A, dl.Exists("Has", B)).add_data_property_range("Has", INT)
    abox = dl.ABox().assert_role("a", "b", "p").assert_data("a", "p", L("1", "xsd:integer"))
    for ask in (lambda: dl.kb_to_fol(tbox), lambda: dl.data_sort_axioms(tbox),
                lambda: dl.databox_to_fol(tbox), lambda: dl.abox_to_fol(abox),
                lambda: dl.data_sort_axioms(None, abox), lambda: dl.kb_to_fol(None, abox)):
        with pytest.raises(dl.UnsupportedDatatypeError, match="object property and a data property"):
            ask()


def test_a_class_and_a_datatype_of_one_name_are_refused():
    tbox = dl.TBox().add_datatype_definition("Digit", dl.DataOneOf((L("1", "xsd:integer"),
                                                                    L("2", "xsd:integer"))))
    abox = dl.ABox().assert_concept("a", dl.Atomic("Digit"))
    with pytest.raises(dl.UnsupportedDatatypeError, match="class and a datatype"):
        dl.kb_to_fol(tbox, abox)


# --------------------------------------------------------------------------- #
# 8. A pun in the QUESTION is refused too, not only one in the knowledge base.
# --------------------------------------------------------------------------- #

def test_a_goal_that_puns_a_name_of_the_knowledge_base_is_refused_by_the_goal_methods():
    # TBox: P is an OBJECT property (ObjectPropertyDomain(P A)). The concept
    # C = ∃P.xsd:integer ⊓ ¬A uses P as a DATA property, which OWL 2 DL forbids
    # (the two are disjoint kinds) -- the question has no OWL 2 answer. The image
    # has one predicate per name, so asked of the conflated predicate the goal
    # C ⊑ ⊥ came back `proved` ("C unsatisfiable": every P-edge is typed A on the
    # left, ¬A on the right), a verdict about nothing; with the data property
    # renamed it is `refuted`.
    # RED before: no goal methods, and the free functions never see the knowledge
    # base, so nothing refused it.
    tbox = dl.TBox().add_role_domain("P", A)
    clash = dl.And(dl.DataExists("P", INT), dl.Not(A))
    kb = dl.kb_to_fol(tbox)
    for ask in (lambda: kb.subsumption_goal(clash, dl.Bottom()),
                lambda: kb.unsatisfiability_goal(clash),
                lambda: kb.instance_goal("a", clash)):
        with pytest.raises(dl.UnsupportedDatatypeError,
                           match="object property and a data property") as info:
            ask()
        assert "'P'" in str(info.value)
    # the same pun handed to kb_to_fol as a query is refused where the bundle is built
    with pytest.raises(dl.UnsupportedDatatypeError, match="object property and a data property"):
        dl.kb_to_fol(tbox, query=[clash])
    # with the data property renamed there is no pun, and the question is asked
    renamed = dl.And(dl.DataExists("PD", INT), dl.Not(A))
    kb = dl.kb_to_fol(tbox, query=[renamed])
    assert _status(kb.unsatisfiability_goal(renamed), kb.tbox_premises) == "refuted"


def test_a_class_that_puns_a_datatype_of_the_knowledge_base_is_refused_by_the_goal_methods():
    # DataPropertyRange(d xsd:integer) makes xsd:integer a datatype; a goal that
    # uses a CLASS of that name conflates the two predicates.
    kb = dl.kb_to_fol(dl.TBox().add_data_property_range("d", INT))
    with pytest.raises(dl.UnsupportedDatatypeError, match="class and a datatype"):
        kb.unsatisfiability_goal(dl.Atomic("xsd:integer"))
    # and a datatype of the name of a class of the knowledge base
    kb = dl.kb_to_fol(dl.TBox().add(dl.Atomic("Digit"), dl.Top()))
    with pytest.raises(dl.UnsupportedDatatypeError, match="class and a datatype"):
        kb.subsumption_goal(dl.DataExists("d", dl.Datatype("Digit")), dl.Bottom())


@pytest.mark.parametrize("ask", [
    lambda: dl.concept_to_fol(dl.And(dl.Exists("P", B), dl.DataExists("P", INT))),
    lambda: dl.subsumption_to_fol(dl.Exists("P", B), dl.DataExists("P", INT)),
    lambda: dl.subsumption_to_fol(A, dl.And(dl.DataExists("P", INT), dl.ForAll("P", A))),
    lambda: dl.concept_to_fol(dl.And(dl.Atomic("Digit"), dl.DataExists("d", dl.Datatype("Digit")))),
    lambda: dl.tbox_to_fol(dl.TBox().add(dl.Exists("P", B), dl.DataExists("P", INT))),
], ids=["concept", "subsumption", "subsumption-one-side", "class-datatype", "tbox"])
def test_the_renderers_refuse_a_pun_inside_what_they_are_given(ask):
    # ∃P.B ⊓ ∃P.xsd:integer uses P as an object property and as a data property
    # at once: the image would print one conflated P(x, x0) for both. RED before:
    # it printed it.
    with pytest.raises(dl.UnsupportedDatatypeError, match="OWL 2 DL forbids"):
        ask()


def test_the_renderers_still_render_what_has_no_pun():
    # a class, an object property and a data property of DIFFERENT names; and a
    # class, an object property and an individual of ONE name (the punning OWL 2
    # DL allows)
    assert dl.concept_to_fol(dl.And(dl.Exists("r", B), dl.DataExists("d", INT))).to_unicode_str() == (
        "∃x0 (r(x, x0) ∧ B(x0)) ∧ ∃x1 (d(x, x1) ∧ xsd:integer(x1))")
    same = dl.And(dl.Atomic("Thing1"), dl.Exists("Thing1", dl.Nominal("Thing1")))
    assert dl.concept_to_fol(same).to_unicode_str() == (
        "Thing1(x) ∧ ∃x0 (Thing1(x, x0) ∧ x0 = Thing1)")


# --------------------------------------------------------------------------- #
# 9. What the bundle prints reads back (house rule 5), within the one documented
#    carve-out of the data layer (a built-in datatype name is not text the kit's
#    grammar reads: see dl.datatypes).
# --------------------------------------------------------------------------- #

def _assert_reads_back(node, what):
    from unicode_logic_kit.atp.tstp_check import _formula_alpha_equal

    text = node.to_unicode_str()
    result = api.parse_any(text)
    assert result.ok, f"{what}: printed text the kit cannot parse: {text!r} ({result.errors})"
    assert _formula_alpha_equal(node, result.formula), (
        f"{what}: parsed, but as a DIFFERENT formula: {text!r}")


def test_the_goals_of_an_object_only_bundle_read_back_as_the_same_formula():
    # no data layer: every goal is a plain closure over CamelCase names
    kb = dl.kb_to_fol(dl.TBox().add(A, dl.Exists("Has", B)), dl.ABox().assert_concept("alice", A))
    for what, goal in (
            ("subsumption goal", kb.subsumption_goal(A, dl.Exists("Has", B))),
            ("unsatisfiability goal", kb.unsatisfiability_goal(dl.And(A, dl.Exists("Has", B)))),
            ("instance goal", kb.instance_goal("alice", dl.Exists("Has", B))),
            ("instance goal, unknown individual", kb.instance_goal("zed", dl.ForAll("Has", A)))):
        _assert_reads_back(goal, what)


def test_the_goals_of_a_two_sorted_bundle_read_back_when_no_built_in_name_is_printed():
    # A data layer whose datatype is the user's own CamelCase name and whose
    # literals are numbers: the guard predicates OwlThing/OwlData are ordinary
    # predicate names, so the relativised goals read back too.
    digit = dl.Datatype("Digit")
    tbox = dl.TBox().add_datatype_definition("Digit", dl.DataOneOf((L("1", "xsd:integer"),)))
    tbox.add(A, dl.DataExists("HasAge", digit))
    concept = dl.And(A, dl.DataForAll("HasAge", digit))
    kb = dl.kb_to_fol(tbox, dl.ABox().assert_concept("alice", A), query=[concept])
    assert kb.separation == "two-sorted"
    for what, goal in (
            ("subsumption goal", kb.subsumption_goal(A, dl.DataExists("HasAge", digit))),
            ("unsatisfiability goal", kb.unsatisfiability_goal(concept)),
            ("instance goal", kb.instance_goal("alice", concept)),
            ("instance goal, unknown individual", kb.instance_goal("zed", concept))):
        _assert_reads_back(goal, what)
