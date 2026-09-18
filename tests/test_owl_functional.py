"""Tests for the OWL 2 Functional-Style Syntax reader/writer, ALCHQ fragment
(unicode_fol_kit.dl.owl_functional).

Round-trip is the primary correctness property, exactly as in
tests/test_owl_manchester.py: `parse_owl_functional_class_expression(
to_owl_functional_class_expression(c)) == c` for every constructor and every
nesting, and `parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox,
abox)` for a whole document. Unlike Manchester Syntax, Functional-Style
Syntax is fully parenthesised by its own keywords, so there is no precedence
lattice to hand-check here -- the interesting hand-checked property instead
is the AXIOM-LEVEL decomposition (EquivalentClasses/DisjointClasses/
DifferentIndividuals each expand to a specific, worked-out set of TBox/ABox
primitives -- see the module docstring's "EquivalentClasses and
DisjointClasses" / "DifferentIndividuals").

Every rejection test exercises real OWL 2 Functional-Style Syntax outside
ALCHQ (inverse roles, nominals, role chains, datatype/data-property
constructs, property characteristics other than Transitive, ...); the kit's
honesty convention requires a loud, precise ValueError naming the construct,
so each test asserts the offending construct's OWL name appears in the
message.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.owl_functional import (
    parse_owl_functional, to_owl_functional,
    parse_owl_functional_class_expression, to_owl_functional_class_expression,
    OwlFunctionalSyntaxError,
)
from unicode_fol_kit.dl.owl_manchester import parse_manchester, parse_manchester_axiom

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")


# --------------------------------------------------------------------------- #
# Class expressions: round-trip, one case per constructor.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.Top(),
    dl.Bottom(),
    dl.Atomic("Person"),
    dl.Not(A),
    dl.And(A, B),
    dl.Or(A, B),
    dl.Exists("r", A),
    dl.ForAll("r", A),
    dl.AtLeast(2, "r", A),
    dl.AtMost(1, "r", A),
    dl.And(dl.AtLeast(1, "r", A), dl.AtMost(1, "r", A)),   # 'exactly' shape
], ids=lambda c: c.to_unicode())
def test_round_trip_one_case_per_constructor(concept):
    rendered = to_owl_functional_class_expression(concept)
    assert parse_owl_functional_class_expression(rendered) == concept


def test_top_and_bottom_render_as_owl_prefixed_names():
    assert to_owl_functional_class_expression(dl.Top()) == "owl:Thing"
    assert to_owl_functional_class_expression(dl.Bottom()) == "owl:Nothing"


def test_top_and_bottom_also_parse_from_the_full_iri_spelling():
    # The W3C standard vocabulary IRIs for owl:Thing/owl:Nothing, as they
    # appear in machine-generated Functional-Syntax output (e.g. from ROBOT).
    assert (parse_owl_functional_class_expression("<http://www.w3.org/2002/07/owl#Thing>")
            == dl.Top())
    assert (parse_owl_functional_class_expression("<http://www.w3.org/2002/07/owl#Nothing>")
            == dl.Bottom())


# --------------------------------------------------------------------------- #
# Class expressions: round-trip, nested/compound.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, rendered", [
    (dl.Not(dl.Not(A)), "ObjectComplementOf(ObjectComplementOf(A))"),
    (dl.Exists("r", dl.ForAll("s", A)),
     "ObjectSomeValuesFrom(r ObjectAllValuesFrom(s A))"),
    (dl.Exists("r", dl.And(A, dl.Not(B))),
     "ObjectSomeValuesFrom(r ObjectIntersectionOf(A ObjectComplementOf(B)))"),
    # ObjectIntersectionOf/ObjectUnionOf are n-ary in the grammar but fold
    # LEFT into the binary And/Or AST (see the module docstring) -- a
    # three-way chain built the SAME way the parser builds it, i.e.
    # (A and B) and C, not A and (B and C).
    (dl.And(dl.And(A, B), C), "ObjectIntersectionOf(A B C)"),
    (dl.Or(dl.Or(A, B), C), "ObjectUnionOf(A B C)"),
    (dl.And(dl.Top(), dl.Or(dl.Bottom(), A)),
     "ObjectIntersectionOf(owl:Thing ObjectUnionOf(owl:Nothing A))"),
], ids=lambda x: x if isinstance(x, str) else None)
def test_round_trip_nested_cases(concept, rendered):
    # The n-ary ObjectIntersectionOf/ObjectUnionOf spelling is only checked
    # on the PARSE side here (rendering always uses the binary form, since
    # to_owl_functional_class_expression walks the binary AST) -- see below
    # for the explicit render-side left-fold check.
    assert parse_owl_functional_class_expression(rendered) == concept


def test_render_uses_the_binary_ast_form_not_the_nary_grammar_shorthand():
    # to_owl_functional_class_expression always emits nested binary
    # ObjectIntersectionOf(ObjectIntersectionOf(A B) C), not the flat n-ary
    # ObjectIntersectionOf(A B C) -- both are valid Functional Syntax and
    # both parse back to the identical AST, so this is a renderer choice,
    # not a correctness requirement; asserted here so the choice is documented.
    concept = dl.And(dl.And(A, B), C)
    rendered = to_owl_functional_class_expression(concept)
    assert rendered == "ObjectIntersectionOf(ObjectIntersectionOf(A B) C)"
    assert parse_owl_functional_class_expression(rendered) == concept


# --------------------------------------------------------------------------- #
# Cardinalities: unqualified (2-arg, defaults to owl:Thing) and qualified
# (3-arg) forms both parse; ObjectExactCardinality desugars to AtLeast+AtMost.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, expected", [
    ("ObjectMinCardinality(2 r A)", dl.AtLeast(2, "r", A)),
    ("ObjectMaxCardinality(3 r A)", dl.AtMost(3, "r", A)),
    ("ObjectMinCardinality(2 r)", dl.AtLeast(2, "r", dl.Top())),   # unqualified
    ("ObjectMaxCardinality(3 r)", dl.AtMost(3, "r", dl.Top())),    # unqualified
    ("ObjectExactCardinality(1 r)",                                # unqualified
     dl.And(dl.AtLeast(1, "r", dl.Top()), dl.AtMost(1, "r", dl.Top()))),
    ("ObjectExactCardinality(1 r A)",
     dl.And(dl.AtLeast(1, "r", A), dl.AtMost(1, "r", A))),
])
def test_cardinality_restrictions_parse_to_number_restrictions(text, expected):
    assert parse_owl_functional_class_expression(text) == expected


@pytest.mark.parametrize("concept, rendered", [
    (dl.AtLeast(2, "r", dl.Top()), "ObjectMinCardinality(2 r owl:Thing)"),
    (dl.AtMost(3, "r", dl.Top()), "ObjectMaxCardinality(3 r owl:Thing)"),
])
def test_writer_always_emits_the_qualified_three_arg_form(concept, rendered):
    # Unlike Manchester's terse "role min n" omission of a Top filler, the
    # Functional writer always spells out the qualifying class explicitly
    # (see the module docstring's "Qualified number restrictions") -- this is
    # a renderer choice, but documenting the exact text keeps it pinned down.
    # Covers both AtLeast and AtMost, since the writer has one branch per
    # constructor (see _render_ce) and either could regress independently.
    assert to_owl_functional_class_expression(concept) == rendered
    assert parse_owl_functional_class_expression(rendered) == concept


# --------------------------------------------------------------------------- #
# Full IRIs: stored without angle brackets, re-wrapped deterministically on
# render (the "contains '://' " heuristic -- see the module docstring's
# "IRIs and names").
# --------------------------------------------------------------------------- #

def test_full_iri_class_name_round_trips():
    concept = parse_owl_functional_class_expression("<http://example.org/Doctor>")
    assert concept == dl.Atomic("http://example.org/Doctor")
    rendered = to_owl_functional_class_expression(concept)
    assert rendered == "<http://example.org/Doctor>"
    assert parse_owl_functional_class_expression(rendered) == concept


def test_prefixed_name_is_taken_verbatim():
    # No prefix resolution happens anywhere in this module (see the module
    # docstring) -- "ex:Doctor" is stored, and rendered back, as the exact
    # literal string "ex:Doctor".
    concept = parse_owl_functional_class_expression("ex:Doctor")
    assert concept == dl.Atomic("ex:Doctor")
    assert to_owl_functional_class_expression(concept) == "ex:Doctor"


def test_name_with_whitespace_renders_but_loudly_fails_to_reparse():
    # Documented (module docstring, "IRIs and names") pre-existing limitation
    # shared with dl.owl_manchester: there is no escaping mechanism for a bare
    # name, so a kit name containing whitespace or a structural character
    # round-trips through the RENDERER (there is no validation on the way out)
    # but does not survive a re-PARSE -- the tokenizer splits it into more than
    # one token, and the parser then loudly rejects the resulting trailing
    # input rather than silently reading back a different/truncated name.
    concept = dl.Atomic("Has Value")
    rendered = to_owl_functional_class_expression(concept)
    assert rendered == "Has Value"   # written back unquoted, unescaped
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional_class_expression(rendered)
    assert "trailing input" in str(exc.value)


# --------------------------------------------------------------------------- #
# Whitespace insignificance and redundant nesting.
# --------------------------------------------------------------------------- #

def test_whitespace_between_tokens_is_insignificant():
    assert parse_owl_functional_class_expression(
        "ObjectIntersectionOf(  A   B  )") == dl.And(A, B)
    assert parse_owl_functional_class_expression(
        "ObjectSomeValuesFrom(r\nA)") == dl.Exists("r", A)


# --------------------------------------------------------------------------- #
# Rejected class-expression constructs: real OWL 2 syntax outside ALCHQ.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, needle", [
    ("ObjectHasValue(hasFriend John)", "value"),
    ("ObjectHasSelf(r)", "Self"),
    ("ObjectOneOf(a b)", "nominal"),
    ("DataSomeValuesFrom(hasAge xsd:integer)", "Data"),
    ("DataHasValue(hasAge 18)", "Data"),
])
def test_rejected_class_expressions(text, needle):
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional_class_expression(text)
    assert needle in str(exc.value)


def test_inverse_object_property_is_rejected():
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional_class_expression("ObjectSomeValuesFrom(ObjectInverseOf(r) A)")
    assert "ObjectInverseOf" in str(exc.value)


def test_unknown_class_expression_keyword_is_rejected():
    with pytest.raises(OwlFunctionalSyntaxError):
        parse_owl_functional_class_expression("NotARealConstruct(A B)")


# --------------------------------------------------------------------------- #
# Malformed input.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "",
    "ObjectIntersectionOf(A",
    "ObjectIntersectionOf(A)",       # needs at least 2 arguments
    "ObjectComplementOf()",
    "ObjectSomeValuesFrom(r)",
    "A B",
    "<unterminated",
])
def test_malformed_class_expression_raises(text):
    with pytest.raises(OwlFunctionalSyntaxError):
        parse_owl_functional_class_expression(text)


# --------------------------------------------------------------------------- #
# Document-level: SubClassOf, EquivalentClasses, DisjointClasses.
# --------------------------------------------------------------------------- #

def test_subclassof_document():
    tbox, abox = parse_owl_functional("Ontology(SubClassOf(A B))")
    assert tbox == dl.TBox().add(A, B)
    assert abox == dl.ABox()


def test_equivalentclasses_two_way():
    tbox, _ = parse_owl_functional("Ontology(EquivalentClasses(A B))")
    assert tbox == dl.TBox().add_equivalence(A, B)


def test_equivalentclasses_multiway_decomposes_as_a_consecutive_chain():
    # EquivalentClasses(A B C) -> add_equivalence(A, B), add_equivalence(B, C)
    # -- pairwise-consecutive, not a "star" from the first element (either is
    # sound; this module picks the consecutive chain -- see the module
    # docstring's "EquivalentClasses and DisjointClasses").
    tbox, _ = parse_owl_functional("Ontology(EquivalentClasses(A B C))")
    expected = dl.TBox().add_equivalence(A, B).add_equivalence(B, C)
    assert tbox == expected
    assert tbox.inclusions == [(A, B), (B, A), (B, C), (C, B)]


def test_disjointclasses_reduces_to_pairwise_gcis():
    # DisjointClasses(A B C) -> all 3 pairs (A,B), (A,C), (B,C) each get
    # C_i ⊓ C_j ⊑ ⊥ -- worked out by hand: 3 classes have C(3,2) = 3 pairs.
    tbox, _ = parse_owl_functional("Ontology(DisjointClasses(A B C))")
    expected = (dl.TBox()
                .add(dl.And(A, B), dl.Bottom())
                .add(dl.And(A, C), dl.Bottom())
                .add(dl.And(B, C), dl.Bottom()))
    assert tbox == expected


@pytest.mark.parametrize("keyword", ["EquivalentClasses", "DisjointClasses"])
def test_nary_class_axioms_require_at_least_two_arguments(keyword):
    with pytest.raises(OwlFunctionalSyntaxError):
        parse_owl_functional(f"Ontology({keyword}(A))")


# --------------------------------------------------------------------------- #
# Document-level: RBox (SubObjectPropertyOf, TransitiveObjectProperty).
# --------------------------------------------------------------------------- #

def test_role_inclusion_and_transitivity():
    tbox, _ = parse_owl_functional(
        "Ontology(SubObjectPropertyOf(hasChild hasDescendant) "
        "TransitiveObjectProperty(hasDescendant))")
    expected = dl.TBox().add_role_inclusion(
        "hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    assert tbox == expected
    # And it actually feeds the RBox-aware tableau correctly (same textbook
    # entailment as docs/guide/description-logic.md's RBox example): two
    # hasChild-hops compose into one hasDescendant-hop.
    C_ = dl.Atomic("C")
    assert dl.subsumes(
        dl.Exists("hasChild", dl.Exists("hasChild", C_)),
        dl.Exists("hasDescendant", C_), expected) is True


def test_property_chain_is_rejected():
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional(
            "Ontology(SubObjectPropertyOf(ObjectPropertyChain(hasParent hasParent) hasGrandparent))")
    assert "ObjectPropertyChain" in str(exc.value)


@pytest.mark.parametrize("keyword, args", [
    ("FunctionalObjectProperty", "(r)"),
    ("InverseFunctionalObjectProperty", "(r)"),
    ("SymmetricObjectProperty", "(r)"),
    ("AsymmetricObjectProperty", "(r)"),
    ("ReflexiveObjectProperty", "(r)"),
    ("IrreflexiveObjectProperty", "(r)"),
    ("ObjectPropertyDomain", "(r A)"),
    ("ObjectPropertyRange", "(r A)"),
    ("DisjointObjectProperties", "(r s)"),
])
def test_rejected_property_characteristic_axioms(keyword, args):
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional(f"Ontology({keyword}{args})")
    assert keyword in str(exc.value)


# --------------------------------------------------------------------------- #
# Document-level: ABox (ClassAssertion, ObjectPropertyAssertion,
# DifferentIndividuals).
# --------------------------------------------------------------------------- #

def test_class_and_property_assertions():
    tbox, abox = parse_owl_functional(
        "Ontology(ClassAssertion(A alice) ObjectPropertyAssertion(hasChild alice bob))")
    assert tbox == dl.TBox()
    expected = dl.ABox().assert_concept("alice", A).assert_role("alice", "bob", "hasChild")
    assert abox == expected


def test_differentindividuals_binary():
    _, abox = parse_owl_functional("Ontology(DifferentIndividuals(bob carol))")
    assert abox == dl.ABox().assert_distinct("bob", "carol")


def test_differentindividuals_kary_asserts_every_pair_not_just_a_chain():
    # DifferentIndividuals(a b c) means ALL THREE pairwise distinct: a≠b,
    # a≠c, b≠c -- a consecutive chain (a≠b, b≠c alone) would NOT entail a≠c
    # (distinctness has no transitive closure, unlike equivalence -- see the
    # module docstring's "DifferentIndividuals"), so all C(3,2)=3 pairs must
    # appear.
    _, abox = parse_owl_functional("Ontology(DifferentIndividuals(a b c))")
    pairs = {frozenset(p) for p in abox.distinct_assertions}
    assert pairs == {frozenset(("a", "b")), frozenset(("a", "c")), frozenset(("b", "c"))}


def test_same_individual_is_rejected():
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional("Ontology(SameIndividual(a b))")
    assert "SameIndividual" in str(exc.value)


def test_anonymous_individual_is_rejected():
    with pytest.raises(OwlFunctionalSyntaxError) as exc:
        parse_owl_functional("Ontology(ClassAssertion(A _:x1))")
    assert "anonymous" in str(exc.value)


# --------------------------------------------------------------------------- #
# Declaration / Annotation / AnnotationAssertion / Prefix: parsed and
# discarded -- documenting the intentional no-op (test_oracle #5).
# --------------------------------------------------------------------------- #

def test_declarations_are_a_no_op():
    bare = parse_owl_functional("Ontology(SubClassOf(A B))")
    declared = parse_owl_functional(
        "Ontology(Declaration(Class(A)) Declaration(Class(B)) "
        "Declaration(ObjectProperty(r)) Declaration(NamedIndividual(alice)) "
        "SubClassOf(A B))")
    assert bare == declared


def test_axiom_annotation_is_a_no_op():
    bare = parse_owl_functional("Ontology(SubClassOf(A B))")
    annotated = parse_owl_functional(
        'Ontology(SubClassOf(Annotation(rdfs:label "why") A B))')
    assert bare == annotated


def test_standalone_annotation_assertion_is_a_no_op():
    bare = parse_owl_functional("Ontology(SubClassOf(A B))")
    with_assertion = parse_owl_functional(
        'Ontology(AnnotationAssertion(rdfs:comment A "a comment") SubClassOf(A B))')
    assert bare == with_assertion


def test_prefix_declarations_are_a_no_op():
    bare = parse_owl_functional("Ontology(SubClassOf(A B))")
    with_prefixes = parse_owl_functional(
        "Prefix(:=<http://example.org/>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(SubClassOf(A B))")
    assert bare == with_prefixes


def test_ontology_and_version_iri_are_discarded():
    bare = parse_owl_functional("Ontology(SubClassOf(A B))")
    with_iris = parse_owl_functional(
        "Ontology(<http://example.org/onto> <http://example.org/onto/1.0> "
        "SubClassOf(A B))")
    assert bare == with_iris


# --------------------------------------------------------------------------- #
# Document-level round-trip: a knowledge base covering every supported axiom
# and class-expression shape at once.
# --------------------------------------------------------------------------- #

def test_full_document_round_trip():
    Doctor, Person, Rich = dl.Atomic("Doctor"), dl.Atomic("Person"), dl.Atomic("Rich")
    tbox = dl.TBox()
    tbox.add(Doctor, dl.And(Person, dl.Not(Rich)))
    tbox.add_equivalence(A, B)
    tbox.add_equivalence(B, C)                       # multi-way chain
    tbox.add(dl.And(A, B), dl.Bottom())               # a DisjointClasses-shaped GCI
    tbox.add_role_inclusion("hasSon", "hasChild")
    tbox.add_transitive_role("hasChild")
    tbox.add(dl.Exists("hasChild", dl.Top()), dl.AtLeast(1, "hasChild", Person))

    abox = dl.ABox()
    abox.assert_concept("alice", Doctor)
    abox.assert_role("alice", "bob", "hasChild")
    abox.assert_role("alice", "carol", "hasSon")
    abox.assert_distinct("bob", "carol")

    text = to_owl_functional(tbox, abox, ontology_iri="http://example.org/onto")
    tbox2, abox2 = parse_owl_functional(text)
    assert tbox2 == tbox
    assert abox2 == abox


def test_empty_document_round_trip():
    tbox, abox = dl.TBox(), dl.ABox()
    text = to_owl_functional(tbox, abox)
    assert text == "Ontology()"
    assert parse_owl_functional(text) == (tbox, abox)


def test_declaration_block_covers_every_referenced_name():
    tbox = dl.TBox().add(dl.Atomic("Doctor"), dl.Exists("hasChild", dl.Atomic("Person")))
    abox = dl.ABox().assert_concept("alice", dl.Atomic("Doctor"))
    text = to_owl_functional(tbox, abox)
    assert "Declaration(Class(Doctor))" in text
    assert "Declaration(Class(Person))" in text
    assert "Declaration(ObjectProperty(hasChild))" in text
    assert "Declaration(NamedIndividual(alice))" in text


# --------------------------------------------------------------------------- #
# Cross-format agreement: the SAME knowledge base, written by hand once in
# Manchester Syntax and once in Functional Syntax, must parse to structurally
# identical Concepts/axioms -- an independent second route not available from
# either module alone.
# --------------------------------------------------------------------------- #

def test_cross_format_agreement_class_expression():
    manchester_text = "Person and hasChild some (Doctor and not Rich)"
    functional_text = (
        "ObjectIntersectionOf(Person ObjectSomeValuesFrom(hasChild "
        "ObjectIntersectionOf(Doctor ObjectComplementOf(Rich))))")
    assert parse_manchester(manchester_text) == parse_owl_functional_class_expression(functional_text)


def test_cross_format_agreement_cardinality():
    assert (parse_manchester("hasChild min 2 Person")
            == parse_owl_functional_class_expression("ObjectMinCardinality(2 hasChild Person)"))
    assert (parse_manchester("hasChild exactly 1 Person")
            == parse_owl_functional_class_expression("ObjectExactCardinality(1 hasChild Person)"))


def test_cross_format_agreement_subclassof_axiom():
    _, sub_m, sup_m = parse_manchester_axiom("Doctor SubClassOf Person and hasChild some Doctor")
    tbox, _ = parse_owl_functional(
        "Ontology(SubClassOf(Doctor ObjectIntersectionOf(Person "
        "ObjectSomeValuesFrom(hasChild Doctor))))")
    assert tbox == dl.TBox().add(sub_m, sup_m)


# --------------------------------------------------------------------------- #
# Textbook cross-check: a small hand-transcribed ontology in the style of the
# W3C OWL 2 Primer (https://www.w3.org/TR/owl2-primer/) -- a handful of
# family-relationship axioms about people, parents, and animal-lovers.
# --------------------------------------------------------------------------- #

def test_primer_style_textbook_ontology():
    text = """
    Prefix(:=<http://example.org/family#>)
    Ontology(<http://example.org/family>
        Declaration(Class(:Person))
        Declaration(Class(:Parent))
        Declaration(ObjectProperty(:hasChild))
        SubClassOf(:Parent ObjectIntersectionOf(:Person ObjectSomeValuesFrom(:hasChild :Person)))
        EquivalentClasses(:Mother ObjectIntersectionOf(:Parent :Woman))
        SubObjectPropertyOf(:hasSon :hasChild)
        ClassAssertion(:Parent :john)
        ObjectPropertyAssertion(:hasChild :john :mary)
        DifferentIndividuals(:john :mary)
    )
    """
    tbox, abox = parse_owl_functional(text)

    Person, Parent = dl.Atomic(":Person"), dl.Atomic(":Parent")
    Mother, Woman = dl.Atomic(":Mother"), dl.Atomic(":Woman")
    expected_tbox = (dl.TBox()
                      .add(Parent, dl.And(Person, dl.Exists(":hasChild", Person)))
                      .add_equivalence(Mother, dl.And(Parent, Woman))
                      .add_role_inclusion(":hasSon", ":hasChild"))
    assert tbox == expected_tbox

    expected_abox = (dl.ABox()
                      .assert_concept(":john", Parent)
                      .assert_role(":john", ":mary", ":hasChild")
                      .assert_distinct(":john", ":mary"))
    assert abox == expected_abox


# --------------------------------------------------------------------------- #
# Integration: parse_owl_functional_class_expression feeds directly into the
# existing ALCHQ tableau (same hand-checked shapes as
# tests/test_owl_manchester.py's tableau-integration tests).
# --------------------------------------------------------------------------- #

def test_parsed_concept_feeds_the_tableau_unsatisfiable():
    # "A and not A" is the textbook clash: {x:A, x:¬A} is a clash by
    # definition, so it is unsatisfiable in EVERY model.
    concept = parse_owl_functional_class_expression("ObjectIntersectionOf(A ObjectComplementOf(A))")
    assert dl.concept_satisfiable(concept) is False


def test_parsed_concept_feeds_the_tableau_satisfiable():
    concept = parse_owl_functional_class_expression("ObjectUnionOf(A ObjectComplementOf(A))")
    assert dl.concept_satisfiable(concept) is True


def test_parsed_concept_matches_hand_checked_tableau_clash():
    # (∃r.A ⊓ ∀r.¬A, False): any r-successor is forced into both A (by the
    # ∃) and ¬A (by the ∀ on that same successor) -- a clash, so no model
    # exists. Same shape as test_dl_alc.py's hand-checked case.
    concept = parse_owl_functional_class_expression(
        "ObjectIntersectionOf(ObjectSomeValuesFrom(r A) ObjectAllValuesFrom(r ObjectComplementOf(A)))")
    assert concept == dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A)))
    assert dl.concept_satisfiable(concept) is False


def test_parsed_abox_feeds_the_tableau():
    # Pigeonhole-flavoured consistency check, mirroring
    # docs/guide/description-logic.md's ABox distinctness example: two named
    # hasChild-successors stay mergeable until asserted distinct, and a
    # global ≤1 hasChild.⊤ bound then makes the KB inconsistent only once
    # they are.
    tbox, abox = parse_owl_functional(
        "Ontology("
        "SubClassOf(owl:Thing ObjectMaxCardinality(1 hasChild owl:Thing)) "
        "ObjectPropertyAssertion(hasChild alice bob) "
        "ObjectPropertyAssertion(hasChild alice carol))")
    assert dl.abox_consistent(abox, tbox) is True   # bob and carol may still merge

    tbox2, abox2 = parse_owl_functional(
        "Ontology("
        "SubClassOf(owl:Thing ObjectMaxCardinality(1 hasChild owl:Thing)) "
        "ObjectPropertyAssertion(hasChild alice bob) "
        "ObjectPropertyAssertion(hasChild alice carol) "
        "DifferentIndividuals(bob carol))")
    assert dl.abox_consistent(abox2, tbox2) is False   # now genuinely 2 successors


# --------------------------------------------------------------------------- #
# Rendering a concept/TBox/ABox built with dl.InverseRole/dl.Nominal (I, O):
# both are outside ALCHQ, exactly like this module's own parser already
# refuses ObjectInverseOf/ObjectOneOf on the way IN (see
# test_inverse_object_property_is_rejected / test_rejected_class_expressions
# above) -- the renderer must refuse them just as loudly on the way OUT,
# instead of crashing with a low-level TypeError that never names the
# construct (this was a real bug: `to_owl_functional_class_expression` on an
# InverseRole-valued role field used to crash inside `_render_name` with
# "argument of type 'InverseRole' is not iterable", and
# `to_owl_functional`'s Declaration-collecting walker would instead corrupt
# its role-name set with a non-str member).
# --------------------------------------------------------------------------- #

def test_render_class_expression_refuses_nominal():
    with pytest.raises(TypeError) as exc:
        to_owl_functional_class_expression(dl.Nominal("alice"))
    assert "Nominal" in str(exc.value)
    assert "alice" in str(exc.value)


def test_render_class_expression_refuses_inverse_role():
    concept = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
    with pytest.raises(TypeError) as exc:
        to_owl_functional_class_expression(concept)
    assert "InverseRole" in str(exc.value)
    assert "hasChild" in str(exc.value)


@pytest.mark.parametrize("concept", [
    dl.ForAll(dl.InverseRole("r"), A),
    dl.AtLeast(2, dl.InverseRole("r"), A),
    dl.AtMost(1, dl.InverseRole("r"), A),
    dl.And(A, dl.Exists(dl.InverseRole("r"), B)),   # nested, not top-level
    dl.Or(dl.Nominal("a"), dl.Nominal("b")),         # the {a,b} multi-nominal shape
])
def test_render_class_expression_refuses_inverse_role_and_nominal_nested(concept):
    with pytest.raises(TypeError):
        to_owl_functional_class_expression(concept)


def test_render_document_refuses_inverse_role_in_tbox():
    # The bug this pins: _collect_names walks the TBox/ABox BEFORE
    # _render_tbox_axioms/_render_ce ever run, so the InverseRole-valued role
    # field must be caught in that first walk too, or it silently corrupts
    # the role-name set collected for the Declaration(...) block instead of
    # raising at all.
    tbox = dl.TBox().add(dl.Atomic("A"), dl.Exists(dl.InverseRole("hasChild"), dl.Top()))
    with pytest.raises(TypeError) as exc:
        to_owl_functional(tbox, dl.ABox())
    assert "InverseRole" in str(exc.value)


def test_render_document_refuses_nominal_in_abox():
    abox = dl.ABox().assert_concept("a", dl.Nominal("bob"))
    with pytest.raises(TypeError) as exc:
        to_owl_functional(dl.TBox(), abox)
    assert "Nominal" in str(exc.value)


def test_render_document_unaffected_by_io_check_for_ordinary_alchq():
    # Regression guard: the new InverseRole/Nominal checks must not disturb
    # ordinary ALCHQ rendering (plain str role names still render/round-trip
    # exactly as before).
    tbox = dl.TBox().add(dl.Atomic("Person"), dl.Exists("hasChild", dl.Atomic("Doctor")))
    abox = (dl.ABox()
            .assert_concept("alice", dl.Atomic("Person"))
            .assert_role("alice", "bob", "hasChild"))
    doc = to_owl_functional(tbox, abox)
    assert parse_owl_functional(doc) == (tbox, abox)
