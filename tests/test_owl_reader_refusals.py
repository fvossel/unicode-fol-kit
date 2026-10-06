r"""The two OWL readers must refuse the same things, and the lenient reader's
``accepted`` must predict ``to_kb()``.

A datatype name in CLASS position
---------------------------------
OWL 2 does not let one name be both a class and a datatype (Structural
Specification, section 5.8.1), and ``xsd:integer`` is a datatype by
definition. The Manchester reader refuses ``A SubClassOf xsd:integer`` BY NAME;
the Functional-Syntax reader used to read it as an ordinary class called
``xsd:integer``, whose image is the very predicate datatype membership uses, so
the verdict changed. Both readers now refuse, with the same wording. Symmetrically
``owl:Thing`` and ``owl:Nothing`` are CLASSES: a data range may not be one.

A bracketed IRI is one name in Manchester syntax
------------------------------------------------
A full IRI ``<http://x.org/a,b>`` is a single atomic name; the ``,`` inside it is
part of the IRI, not the data-range separator the tokenizer learned to split on.

``accepted`` predicts ``to_kb``
-------------------------------
A literal with no first-order term (``xsd:double``/``xsd:float``, a decimal no
``Number`` holds exactly) is refused at READ time, by name, so an axiom the
reader reports as accepted is one ``to_kb()`` can translate.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.owl_functional import (
    OwlFunctionalUnsupportedError, parse_owl_functional,
    parse_owl_functional_axioms, parse_owl_functional_class_expression,
)
from unicode_fol_kit.dl.owl_manchester import ManchesterSyntaxError

XSD = "http://www.w3.org/2001/XMLSchema#"
OWL = "http://www.w3.org/2002/07/owl#"


def _doc(*axioms):
    return "Ontology(\n" + "\n".join("  " + a for a in axioms) + "\n)"


# --------------------------------------------------------------------------- #
# A built-in datatype name where a class is wanted
# --------------------------------------------------------------------------- #

#: One axiom per position a class expression can occupy, each carrying
#: ``xsd:integer`` where the grammar wants a CLASS.
_CLASS_POSITIONS = [
    "SubClassOf(A xsd:integer)",
    "SubClassOf(xsd:integer A)",
    "SubClassOf(A ObjectSomeValuesFrom(r xsd:integer))",
    "ClassAssertion(xsd:integer a)",
    "ObjectPropertyRange(r xsd:integer)",
    "ObjectPropertyDomain(r xsd:integer)",
    "DataPropertyDomain(p xsd:integer)",
    "EquivalentClasses(A xsd:integer)",
    "SubClassOf(A ObjectComplementOf(xsd:integer))",
]


@pytest.mark.parametrize("axiom", _CLASS_POSITIONS)
def test_a_datatype_in_class_position_is_a_refused_axiom_naming_it(axiom):
    result = parse_owl_functional_axioms(_doc(axiom))
    assert not result.ok and result.accepted == 0
    (refused,) = result.refused
    assert refused.keyword == "xsd:integer"
    assert "DATATYPE, not a class" in refused.reason
    assert "'xsd:integer'" in refused.reason
    # nothing of the refused axiom is left behind
    assert result.tbox == dl.TBox() and result.abox == dl.ABox()
    # the strict reader raises the same refusal
    with pytest.raises(OwlFunctionalUnsupportedError, match="DATATYPE, not a class"):
        parse_owl_functional(_doc(axiom))


def test_the_full_iri_spellings_of_a_datatype_are_the_same_refusal():
    for spelling in (f"<{XSD}integer>", f"{XSD}integer"):
        axiom = f"SubClassOf(A {spelling})"
        (refused,) = parse_owl_functional_axioms(_doc(axiom)).refused
        assert refused.keyword == f"{XSD}integer"
        assert "DATATYPE, not a class" in refused.reason


def test_the_class_expression_entry_point_refuses_it_too():
    with pytest.raises(OwlFunctionalUnsupportedError, match="DATATYPE, not a class"):
        parse_owl_functional_class_expression("xsd:string")
    with pytest.raises(OwlFunctionalUnsupportedError, match="DATATYPE, not a class"):
        parse_owl_functional_class_expression("rdfs:Literal")


def test_both_readers_say_the_same_thing_about_the_same_mistake():
    with pytest.raises(ManchesterSyntaxError) as manchester:
        dl.parse_manchester_axiom("A SubClassOf xsd:integer")
    (refused,) = parse_owl_functional_axioms(_doc("SubClassOf(A xsd:integer)")).refused
    shared = "is a DATATYPE, not a class — OWL 2 does not let one name be both"
    assert shared in str(manchester.value)
    assert shared in refused.reason


def test_a_class_with_an_ordinary_name_is_still_read():
    # The refusal is about the name being a built-in datatype, not about the
    # position: a user class called IntegerClass is an ordinary class.
    result = parse_owl_functional_axioms(_doc(
        "SubClassOf(A IntegerClass)", "ClassAssertion(IntegerClass a)",
        "DataPropertyRange(P xsd:integer)"))
    assert result.ok and result.accepted == 3


def test_a_refused_neighbour_does_not_take_its_siblings_with_it():
    result = parse_owl_functional_axioms(_doc(
        "SubClassOf(A B)", "SubClassOf(A xsd:integer)", "ClassAssertion(A a)"))
    assert result.accepted == 2 and len(result.refused) == 1
    assert result.tbox.inclusions == [(dl.Atomic("A"), dl.Atomic("B"))]
    assert result.abox.concept_assertions == [("a", dl.Atomic("A"))]


#: A data range that is really a class, in each position a data range occupies.
_DATA_POSITIONS = [
    "SubClassOf(A DataSomeValuesFrom(p {name}))",
    "SubClassOf(A DataAllValuesFrom(p {name}))",
    "SubClassOf(A DataMinCardinality(1 p {name}))",
    "DataPropertyRange(p {name})",
    "DataPropertyRange(p DataComplementOf({name}))",
    "DataPropertyRange(p DataUnionOf(xsd:integer {name}))",
    "DatatypeDefinition(D {name})",
    'DatatypeDefinition(D DatatypeRestriction({name} xsd:minInclusive "1"^^xsd:integer))',
]


@pytest.mark.parametrize("name", ["owl:Thing", "owl:Nothing", f"<{OWL}Thing>", f"<{OWL}Nothing>"])
@pytest.mark.parametrize("template", _DATA_POSITIONS)
def test_a_class_in_data_range_position_is_refused_by_name(template, name):
    axiom = template.format(name=name)
    result = parse_owl_functional_axioms(_doc(axiom))
    assert not result.ok and result.accepted == 0
    (refused,) = result.refused
    assert refused.keyword == name.strip("<>")
    assert "CLASS, not a data range" in refused.reason
    assert result.tbox == dl.TBox()


def test_the_defined_datatype_may_not_be_a_class_name_either():
    (refused,) = parse_owl_functional_axioms(
        _doc("DatatypeDefinition(owl:Thing xsd:integer)")).refused
    assert refused.keyword == "owl:Thing"
    assert "CLASS, not a data range" in refused.reason


def test_a_class_expression_keyword_in_data_range_position_is_refused_by_name():
    # this half held from the start -- pinned so the two halves of the rule stay one
    # policy: the construct is named, the axiom is not read.
    (refused,) = parse_owl_functional_axioms(
        _doc("DataPropertyRange(p ObjectUnionOf(A B))")).refused
    assert refused.keyword == "ObjectUnionOf"


@pytest.mark.parametrize("name", ["owl:Thing", "owl:Nothing"])
def test_the_manchester_reader_refuses_a_class_as_a_data_range_too(name):
    # one policy for both readers: the Functional-Syntax reader refuses it above,
    # and this reader used to read it as a datatype called owl:Thing
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester_data_range(name)
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester(f"d some (xsd:integer or {name})")


def test_an_object_restriction_over_owl_thing_is_still_an_object_restriction():
    # with nothing to say the filler is a data range, `d some owl:Thing` is the
    # object restriction over the class ⊤ -- unchanged
    assert dl.parse_manchester("d some owl:Thing") == dl.Exists("d", dl.Top())


def test_rdfs_literal_and_owl_real_are_ordinary_data_ranges():
    result = parse_owl_functional_axioms(_doc(
        "DataPropertyRange(p rdfs:Literal)", "DataPropertyRange(q owl:real)"))
    assert result.ok and result.accepted == 2


# --------------------------------------------------------------------------- #
# '<...>' is one NAME in Manchester syntax
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("iri", [
    "http://x.org/a,b",
    "http://x.org/a,b,c",
    "http://x.org/a(b)",
    "http://x.org/{a}",
    "http://x.org/a[1]",
])
def test_a_bracketed_iri_with_structural_characters_is_one_class_name(iri):
    # The characters , ( ) { } [ ] are legal inside an IRI; inside <...> they are
    # part of the NAME, whatever else they mean outside it. The name is stored
    # WITHOUT its brackets, as dl.parse_owl_functional stores it.
    concept = dl.parse_manchester(f"r some <{iri}>")
    assert concept == dl.Exists("r", dl.Atomic(iri))


def test_a_name_with_a_comma_round_trips_through_manchester():
    concept = dl.Exists("r", dl.Atomic("http://x.org/a,b"))
    assert dl.parse_manchester(dl.to_manchester(concept)) == concept


def test_a_bracketed_iri_beside_the_data_range_comma_still_separates():
    # the comma OUTSIDE the brackets is still the one-of separator
    concept = dl.parse_manchester('d some {"1"^^xsd:integer, "2"^^xsd:integer}')
    assert concept == dl.DataExists("d", dl.DataOneOf(
        (dl.Literal("1", "xsd:integer"), dl.Literal("2", "xsd:integer"))))


def test_a_bracketed_iri_in_a_whole_axiom():
    kind, sub, sup = dl.parse_manchester_axiom(
        "<http://x.org/a,b> SubClassOf r some <http://x.org/c,d>")
    assert kind == "subclass"
    assert sub == dl.Atomic("http://x.org/a,b")
    assert sup == dl.Exists("r", dl.Atomic("http://x.org/c,d"))


def test_an_iri_followed_directly_by_text_is_the_one_odd_word_it_always_was():
    # '>' is not legal inside an IRI, so `<http://x.org/a>b` was never an IRI
    # followed by a name; it stays ONE name, exactly as it always was
    assert dl.parse_manchester("r some <http://x.org/a>b") == dl.Exists(
        "r", dl.Atomic("<http://x.org/a>b"))


def test_the_facet_symbols_are_not_mistaken_for_an_iri():
    # '<' and '<=' open a facet when a bound follows; the glued, comma-separated
    # spelling with no spaces is the one a greedy '<...>' scan would swallow as
    # the "IRI" '<5,>'. An IRI opens with a scheme letter; a bound never does.
    concept = dl.parse_manchester("d some xsd:integer[>=3,<5]")
    assert concept == dl.DataExists("d", dl.DatatypeRestriction(
        dl.Datatype("xsd:integer"),
        (("xsd:minInclusive", dl.Literal("3", "xsd:integer")),
         ("xsd:maxExclusive", dl.Literal("5", "xsd:integer")))))
    glued = dl.parse_manchester("d some xsd:integer[<5,>=3]")
    assert glued == dl.DataExists("d", dl.DatatypeRestriction(
        dl.Datatype("xsd:integer"),
        (("xsd:maxExclusive", dl.Literal("5", "xsd:integer")),
         ("xsd:minInclusive", dl.Literal("3", "xsd:integer")))))


def test_a_datatype_iri_inside_a_typed_literal_may_hold_a_comma():
    # the literal "5"^^<http://x.org/dt,x> is one token: its datatype IRI is a
    # name, so the comma inside it does not end the literal
    concept = dl.parse_manchester('d value "5"^^<http://x.org/dt,x>')
    assert concept == dl.DataHasValue("d", dl.Literal("5", "http://x.org/dt,x"))


# --------------------------------------------------------------------------- #
# The lenient reader's `accepted` predicts what to_kb() can do
# --------------------------------------------------------------------------- #

#: Each literal below has no first-order term (Literal.to_term refuses it):
#: float/double have a value space of their own (-0, NaN, INF), and a decimal
#: with more digits than a float prints cannot be one Number exactly.
_NO_TERM = [
    '"1e3"^^xsd:double',
    '"NaN"^^xsd:float',
    '"1.5"^^xsd:float',
    '"1234567890123456789.123456789"^^xsd:decimal',
]


@pytest.mark.parametrize("literal", _NO_TERM)
@pytest.mark.parametrize("template", [
    "DataPropertyAssertion(p a {lit})",
    "NegativeDataPropertyAssertion(p a {lit})",
    "ClassAssertion(DataHasValue(p {lit}) a)",
    "SubClassOf(A DataHasValue(p {lit}))",
    "SubClassOf(A DataSomeValuesFrom(p DataOneOf({lit})))",
    "DataPropertyRange(p DataOneOf({lit}))",
])
def test_a_literal_without_a_first_order_term_is_refused_at_read_time(template, literal):
    axiom = template.format(lit=literal)
    result = parse_owl_functional_axioms(_doc(axiom))
    assert result.accepted == 0
    (refused,) = result.refused
    assert "no first-order image" in refused.reason or "cannot be held exactly" in refused.reason
    assert result.tbox == dl.TBox() and result.abox == dl.ABox()
    with pytest.raises(OwlFunctionalUnsupportedError):
        parse_owl_functional(_doc(axiom))


def test_accepted_predicts_to_kb():
    # a mixed document: whatever the reader accepted, to_kb() translates.
    result = parse_owl_functional_axioms(_doc(
        'DataPropertyAssertion(p a "1"^^xsd:integer)',
        'DataPropertyAssertion(p a "1e3"^^xsd:double)',
        'DataPropertyAssertion(p a "2.5"^^xsd:decimal)',
        'DataPropertyAssertion(q a "NaN"^^xsd:float)',
        'SubClassOf(A DataHasValue(p "x"))'))
    assert result.accepted == 3 and len(result.refused) == 2
    result.to_kb()          # does not raise


def test_a_term_literal_of_a_non_number_datatype_stays_accepted():
    # hexBinary / dateTime literals are constants named by their OWL text: they
    # HAVE a term, so they are not refused here.
    result = parse_owl_functional_axioms(_doc(
        'DataPropertyAssertion(p a "0A"^^xsd:hexBinary)',
        'DataPropertyAssertion(p a "2020-01-01T00:00:00"^^xsd:dateTime)'))
    assert result.ok and result.accepted == 2
    result.to_kb()
