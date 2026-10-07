r"""One IRI, ONE stored name: both OWL readers and both OWL writers.

The rule
--------
An IRI has ONE stored spelling in a TBox / ABox, whichever reader produced it: the
IRI WITHOUT angle brackets, which is what the Functional-Syntax reader always
stored. So

* the Manchester reader strips the brackets of a full IRI in EVERY position (a
  class, a datatype, an object or data property, an individual, the datatype of a
  literal), where it used to keep them on all but the last -- so a datatype read
  from Manchester never matched its own literals;
* the two writers add the brackets on the way out and only there: ``to_manchester``
  brackets a name that is a full IRI (it holds ``://``) or holds a structural
  character a bare name could not carry, and ``to_owl_functional`` never writes
  ``<<...>>``;
* ``owl:Thing`` / ``owl:Nothing`` are compared in CANONICAL form in both readers --
  abbreviated or full IRI, bracketed or not -- in every position where one of them
  is special or refused, including the datatype of a literal.

How the expected values are derived
-----------------------------------
Every expected value below is written out by hand from those three clauses and
from OWL's own grammar (a name inside ``<...>`` is ONE name; the stored name is the
text between the brackets), never read off the code. The end-to-end question of the first clause
(through ``kb_to_fol`` and the prover) is in ``test_owl_iri_names_e2e.py``.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl.owl_functional import (
    OwlFunctionalUnsupportedError, parse_owl_functional, parse_owl_functional_axioms,
    parse_owl_functional_class_expression, to_owl_functional,
    to_owl_functional_class_expression,
)
from unicode_logic_kit.dl.owl_manchester import ManchesterSyntaxError

OWL = "http://www.w3.org/2002/07/owl#"
SMALL = "http://ex.org/dt#Small"

#: Names that are legal inside an IRI but are structure outside it -- a comma, two
#: commas, parentheses, square brackets and braces -- plus a plain one.
IRIS = [
    "http://x.org/a,b",
    "http://x.org/a,b,c",
    "http://x.org/a(b)",
    "http://x.org/a[1]",
    "http://x.org/{a}",
    "https://ex.org/A#B",
]


def _doc(*axioms):
    return "Ontology(\n" + "\n".join("  " + a for a in axioms) + "\n)"


# --------------------------------------------------------------------------- #
# The Manchester reader stores an IRI without its brackets, everywhere
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, expected", [
    # a class
    ("<http://x.org/C>", dl.Atomic("http://x.org/C")),
    # an object property and its filler class
    ("<http://x.org/r> some <http://x.org/C>",
     dl.Exists("http://x.org/r", dl.Atomic("http://x.org/C"))),
    ("<http://x.org/r> only <http://x.org/C>",
     dl.ForAll("http://x.org/r", dl.Atomic("http://x.org/C"))),
    ("<http://x.org/r> min 2 <http://x.org/C>",
     dl.AtLeast(2, "http://x.org/r", dl.Atomic("http://x.org/C"))),
    # an object property and an individual
    ("<http://x.org/r> value <http://x.org/a>", dl.HasValue("http://x.org/r", "http://x.org/a")),
    # a data property, with a built-in datatype
    ("<http://x.org/d> some xsd:integer",
     dl.DataExists("http://x.org/d", dl.Datatype("xsd:integer"))),
    # a data property and the datatype of its literal
    ('<http://x.org/d> value "5"^^<http://x.org/dt>',
     dl.DataHasValue("http://x.org/d", dl.Literal("5", "http://x.org/dt"))),
])
def test_manchester_stores_a_bracketed_iri_without_its_brackets(text, expected):
    assert dl.parse_manchester(text) == expected


@pytest.mark.parametrize("declared", ["http://x.org/dt", "<http://x.org/dt>"])
def test_a_declared_datatype_is_one_datatype_in_either_spelling(declared):
    # `datatypes=` names the datatypes the text does not mark; the bracketed and the
    # bare spelling of one IRI name ONE datatype, and the read name has no brackets
    expected = dl.DataExists("http://x.org/d", dl.Datatype("http://x.org/dt"))
    assert dl.parse_manchester("<http://x.org/d> some <http://x.org/dt>",
                               datatypes=(declared,)) == expected
    assert dl.parse_manchester("<http://x.org/d> some http://x.org/dt",
                               datatypes=(declared,)) == expected


def test_a_user_datatype_read_from_manchester_is_the_datatype_of_its_literals():
    # The IRI is the datatype; the literal "5"^^<IRI> has the
    # datatype named by that IRI. Same IRI, so the same stored name.
    datarange = dl.parse_manchester_data_range(f"<{SMALL}>")
    literal = dl.parse_manchester_literal(f'"5"^^<{SMALL}>')
    assert datarange == dl.Datatype(SMALL)
    assert literal == dl.Literal("5", SMALL)
    assert datarange.name == literal.datatype == SMALL


@pytest.mark.parametrize("manchester, functional", [
    ("<http://x.org/C>", "<http://x.org/C>"),
    ("r some <http://x.org/a,b>", "ObjectSomeValuesFrom(r <http://x.org/a,b>)"),
    ("<http://x.org/r(1)> only <http://x.org/a[1]>",
     "ObjectAllValuesFrom(<http://x.org/r(1)> <http://x.org/a[1]>)"),
    ("<http://x.org/r> value <http://x.org/a,b>",
     "ObjectHasValue(<http://x.org/r> <http://x.org/a,b>)"),
    (f"<http://x.org/d> some <{SMALL}>",
     f"DataSomeValuesFrom(<http://x.org/d> <{SMALL}>)"),
    (f'<http://x.org/d> value "5"^^<{SMALL}>',
     f'DataHasValue(<http://x.org/d> "5"^^<{SMALL}>)'),
])
def test_the_two_readers_store_one_iri_as_one_string(manchester, functional):
    # The Manchester text declares the datatype where it has to (a user datatype has
    # no marker a context-free parse could see)
    from_manchester = dl.parse_manchester(manchester, datatypes=(SMALL,))
    from_functional = parse_owl_functional_class_expression(functional)
    assert from_manchester == from_functional


def test_the_same_knowledge_base_read_either_way_is_one_knowledge_base():
    functional = _doc(
        f'DatatypeDefinition(<{SMALL}> DatatypeRestriction(xsd:integer '
        f'xsd:minInclusive "0"^^xsd:integer))',
        f'DataPropertyAssertion(<http://ex.org/p> <http://ex.org/a> "5"^^<{SMALL}>)',
        f'ClassAssertion(DataSomeValuesFrom(<http://ex.org/p> <{SMALL}>) <http://ex.org/a>)',
    )
    tbox, abox = parse_owl_functional(functional)

    by_hand_tbox = dl.TBox().add_datatype_definition(
        SMALL, dl.parse_manchester_data_range("xsd:integer[>= 0]"))
    by_hand_abox = (dl.ABox()
                    .assert_data("http://ex.org/a", "http://ex.org/p",
                                 dl.parse_manchester_literal(f'"5"^^<{SMALL}>'))
                    .assert_concept("http://ex.org/a", dl.parse_manchester(
                        f"<http://ex.org/p> some <{SMALL}>", datatypes=(SMALL,))))
    assert (tbox, abox) == (by_hand_tbox, by_hand_abox)


# --------------------------------------------------------------------------- #
# The writers bracket on the way out, and only there
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, expected", [
    # a name that holds '://' is a full IRI: bracketed, wherever a name stands
    (dl.Exists("r", dl.Atomic("http://x.org/a,b")), "r some <http://x.org/a,b>"),
    (dl.Atomic("http://x.org/a(b)"), "<http://x.org/a(b)>"),
    (dl.ForAll("http://x.org/r[1]", dl.Atomic("A")), "<http://x.org/r[1]> only A"),
    (dl.HasValue("r", "http://x.org/{a}"), "r value <http://x.org/{a}>"),
    (dl.Nominal("http://x.org/a,b"), "{<http://x.org/a,b>}"),
    (dl.Exists(dl.InverseRole("http://x.org/r,s"), dl.Atomic("A")),
     "inverse <http://x.org/r,s> some A"),
    (dl.DataExists("http://x.org/d,e", dl.Datatype("http://ex.org/dt,Small")),
     "<http://x.org/d,e> some <http://ex.org/dt,Small>"),
    (dl.DataAtLeast(2, "d", dl.Datatype("http://ex.org/dt,Small")),
     "d min 2 <http://ex.org/dt,Small>"),
    # a literal's datatype is a name like any other
    (dl.DataHasValue("d", dl.Literal("5", "http://ex.org/dt,Small")),
     'd value "5"^^<http://ex.org/dt,Small>'),
    (dl.DataExists("d", dl.DataOneOf((dl.Literal("5", "http://ex.org/dt,Small"),
                                      dl.Literal("x", "xsd:string")))),
     'd some {"5"^^<http://ex.org/dt,Small>, "x"^^xsd:string}'),
    # a scheme and a structural character, but no '://'
    (dl.Atomic("urn:x:a,b"), "<urn:x:a,b>"),
])
def test_to_manchester_brackets_an_iri(concept, expected):
    assert dl.to_manchester(concept) == expected


@pytest.mark.parametrize("name", [
    "Person", "ex:Person", "urn:x:Thing", "ns:cls.v2", "x-y",
])
def test_a_name_that_is_no_iri_is_written_as_it_always_was(name):
    assert dl.to_manchester(dl.Atomic(name)) == name
    assert to_owl_functional_class_expression(dl.Atomic(name)) == name


@pytest.mark.parametrize("name", ["a,b", "Has Value"])
def test_a_name_no_manchester_iri_can_carry_is_refused_and_the_functional_syntax_brackets_it(name):
    # "a,b" and "Has Value" are no full IRI (no scheme), and Manchester Syntax has
    # no other escape: the old writer printed them as they were, and the text
    # splits when it is read back ("A and Has Value" is a conjunction of three
    # classes). A name the syntax cannot carry is now refused, by name.
    with pytest.raises(ValueError, match="cannot be written so that parse_manchester"):
        dl.to_manchester(dl.Atomic(name))
    # The Functional-Style syntax can: everything up to the first '>' is one name
    # ("a,b" needs nothing, it is one word there; the whitespace needs the brackets)
    expected = {"a,b": "a,b", "Has Value": "<Has Value>"}[name]
    assert to_owl_functional_class_expression(dl.Atomic(name)) == expected
    assert parse_owl_functional_class_expression(expected) == dl.Atomic(name)


@pytest.mark.parametrize("name", [
    "<http://x.org/a>b",        # the one odd word the tokenizer reads, as it always did
    "http://x.org/a>b",         # a '>' no bracket can enclose
])
def test_a_name_no_bracket_can_carry_is_still_written_as_it_is_and_reads_back(name):
    # `<name>` would not read back as this name (it holds a '>'), but the bare name
    # does, and bare is what it always was
    assert dl.to_manchester(dl.Atomic(name)) == name
    assert dl.parse_manchester(name) == dl.Atomic(name)


@pytest.mark.parametrize("iri", IRIS)
def test_a_name_survives_both_syntaxes_whoever_built_it(iri):
    # Built three ways: by hand, read by the Manchester reader, read by the
    # Functional reader. All three are the SAME concept (clause one), and each of
    # them round-trips through BOTH writers (clause two).
    by_hand = dl.Exists("r", dl.Atomic(iri))
    from_manchester = dl.parse_manchester(f"r some <{iri}>")
    from_functional = parse_owl_functional_class_expression(
        f"ObjectSomeValuesFrom(r <{iri}>)")
    assert by_hand == from_manchester == from_functional
    for concept in (by_hand, from_manchester, from_functional):
        assert dl.parse_manchester(dl.to_manchester(concept)) == by_hand
        assert parse_owl_functional_class_expression(
            to_owl_functional_class_expression(concept)) == by_hand


def test_a_functional_read_name_with_a_comma_reaches_manchester_and_back():
    # The Functional reader stores 'http://x.org/a,b'; the
    # Manchester writer used to write it bare, and the tokenizer split it at the comma
    concept = parse_owl_functional_class_expression("ObjectSomeValuesFrom(r <http://x.org/a,b>)")
    assert dl.to_manchester(concept) == "r some <http://x.org/a,b>"
    assert dl.parse_manchester("r some <http://x.org/a,b>") == concept


def test_a_literal_datatype_holding_a_comma_round_trips():
    # A literal whose datatype IRI holds a comma
    for value in (dl.Literal("5", "http://ex.org/dt,Small"),
                  dl.Literal("5", "http://ex.org/dt(Small)")):
        concept = dl.DataHasValue("p", value)
        assert dl.parse_manchester(dl.to_manchester(concept)) == concept
    one_of = dl.DataOneOf((dl.Literal("5", "http://ex.org/dt,Small"),
                           dl.Literal("6", "http://ex.org/dt,Small")))
    assert dl.parse_manchester_data_range(dl.to_manchester_data_range(one_of)) == one_of
    assert dl.to_manchester_data_range(one_of) == (
        '{"5"^^<http://ex.org/dt,Small>, "6"^^<http://ex.org/dt,Small>}')


@pytest.mark.parametrize("axiom, text", [
    (("subproperty", "http://x.org/r,1", "http://x.org/s"),
     "<http://x.org/r,1> SubPropertyOf <http://x.org/s>"),
    (("inverse", "http://x.org/r", "partOf"), "<http://x.org/r> InverseOf partOf"),
    (("transitive", "http://x.org/r(1)"), "<http://x.org/r(1)> Characteristics: Transitive"),
    (("domain", "http://x.org/r", dl.Atomic("http://x.org/A,B")),
     "<http://x.org/r> Domain: <http://x.org/A,B>"),
])
def test_a_role_axiom_over_iris_round_trips(axiom, text):
    assert dl.role_axiom_to_manchester(*axiom) == text
    assert dl.parse_manchester_role_axiom(text) == axiom


def test_a_manchester_read_class_is_written_once_bracketed_by_the_functional_writer():
    # The Manchester reader used to keep the brackets, and the
    # Functional writer, which wraps a name holding '://', wrote '<<...>>'
    concept = dl.parse_manchester("<http://ex.org/A> and <http://ex.org/B>")
    tbox = dl.TBox().add(dl.Atomic("X"), concept)
    text = to_owl_functional(tbox, dl.ABox())
    assert "<<" not in text and ">>" not in text
    assert "  SubClassOf(X ObjectIntersectionOf(<http://ex.org/A> <http://ex.org/B>))" in text
    assert "  Declaration(Class(<http://ex.org/A>))" in text
    assert parse_owl_functional(text) == (tbox, dl.ABox())


def test_a_hand_built_name_that_carries_its_brackets_is_refused_by_both_writers():
    # The Functional reader would refuse '<<...>>', and written as it is, the
    # name "<http://ex.org/A>" read back as "http://ex.org/A": ANOTHER name (the
    # one stored spelling of the IRI has no brackets), so a knowledge base with
    # both names, which the kit tells apart, came back with one. The old writers
    # wrote it once-bracketed for that reason; a text that reads back as another
    # name is not written, whatever the reason, and the caller is told to rename.
    for write in (to_owl_functional_class_expression, dl.to_manchester):
        with pytest.raises(ValueError, match="already holds the angle brackets"):
            write(dl.Atomic("<http://ex.org/A>"))
    tbox = dl.TBox().add(dl.Atomic("<http://ex.org/A>"), dl.Atomic("B"))
    with pytest.raises(ValueError, match="already holds the angle brackets"):
        to_owl_functional(tbox, dl.ABox())
    # the IRI in its one stored spelling is written once-bracketed, as it always was,
    # and reads back as itself
    stored = dl.TBox().add(dl.Atomic("http://ex.org/A"), dl.Atomic("B"))
    text = to_owl_functional(stored, dl.ABox())
    assert "<<" not in text and "SubClassOf(<http://ex.org/A> B)" in text
    assert parse_owl_functional(text) == (stored, dl.ABox())


def _knowledge_base_by_hand(iri_class, iri_role, iri_individual, iri_datatype):
    tbox = (dl.TBox()
            .add(dl.Atomic(iri_class), dl.Exists(iri_role, dl.Atomic("B")))
            .add_role_domain(iri_role, dl.Atomic(iri_class))
            .add_data_property_range("p", dl.Datatype(iri_datatype)))
    abox = (dl.ABox()
            .assert_concept(iri_individual, dl.Atomic(iri_class))
            .assert_role(iri_individual, "b", iri_role)
            .assert_data(iri_individual, "p", dl.Literal("5", iri_datatype)))
    return tbox, abox


def _knowledge_base_from_manchester(iri_class, iri_role, iri_individual, iri_datatype):
    tbox = dl.TBox()
    kind, sub, sup = dl.parse_manchester_axiom(
        f"<{iri_class}> SubClassOf <{iri_role}> some B")
    tbox.add(sub, sup)
    tag, role, filler = dl.parse_manchester_role_axiom(f"<{iri_role}> Domain: <{iri_class}>")
    tbox.add_role_domain(role, filler)
    tbox.add_data_property_range("p", dl.parse_manchester_data_range(f"<{iri_datatype}>"))
    abox = (dl.ABox()
            .assert_concept(iri_individual, dl.parse_manchester(f"<{iri_class}>"))
            .assert_role(iri_individual, "b", dl.parse_manchester(f"<{iri_role}> some B").role)
            .assert_data(iri_individual, "p",
                         dl.parse_manchester_literal(f'"5"^^<{iri_datatype}>')))
    return tbox, abox


def _knowledge_base_from_functional(iri_class, iri_role, iri_individual, iri_datatype):
    return parse_owl_functional(_doc(
        f"SubClassOf(<{iri_class}> ObjectSomeValuesFrom(<{iri_role}> B))",
        f"ObjectPropertyDomain(<{iri_role}> <{iri_class}>)",
        f"DataPropertyRange(p <{iri_datatype}>)",
        f"ClassAssertion(<{iri_class}> <{iri_individual}>)",
        f"ObjectPropertyAssertion(<{iri_role}> <{iri_individual}> b)",
        f'DataPropertyAssertion(p <{iri_individual}> "5"^^<{iri_datatype}>)',
    ))


@pytest.mark.parametrize("make", [
    _knowledge_base_by_hand, _knowledge_base_from_manchester, _knowledge_base_from_functional])
@pytest.mark.parametrize("names", [
    ("http://x.org/a,b", "http://x.org/r(1)", "http://x.org/i[2]", "http://x.org/dt,x"),
    ("http://x.org/A", "http://x.org/r", "http://x.org/i", "http://ex.org/dt#Small"),
])
def test_a_document_round_trips_whoever_built_it(make, names):
    # Through the Functional writer: (tbox, abox) -> text -> (tbox, abox), for a
    # knowledge base built by hand, read by Manchester, read by Functional.
    # The expected knowledge base is the hand-built one: the stored names are the IRIs.
    expected = _knowledge_base_by_hand(*names)
    made = make(*names)
    assert made == expected
    text = to_owl_functional(*made)
    assert "<<" not in text
    assert parse_owl_functional(text) == expected


# --------------------------------------------------------------------------- #
# The reserved names are compared in canonical form, in both readers
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("spelling", ["owl:Thing", f"<{OWL}Thing>", f"{OWL}Thing"])
def test_owl_thing_is_top_in_every_spelling_in_class_position(spelling):
    assert dl.parse_manchester(f"p only {spelling}") == dl.ForAll("p", dl.Top())
    assert dl.parse_manchester(f"{spelling} and A") == dl.And(dl.Top(), dl.Atomic("A"))
    assert parse_owl_functional_class_expression(
        f"ObjectAllValuesFrom(p {spelling})") == dl.ForAll("p", dl.Top())


@pytest.mark.parametrize("spelling", ["owl:Nothing", f"<{OWL}Nothing>", f"{OWL}Nothing"])
def test_owl_nothing_is_bottom_in_every_spelling_in_class_position(spelling):
    assert dl.parse_manchester(f"A or {spelling}") == dl.Or(dl.Atomic("A"), dl.Bottom())


@pytest.mark.parametrize("name", [
    "owl:Thing", "owl:Nothing", f"<{OWL}Thing>", f"<{OWL}Nothing>", f"{OWL}Thing"])
def test_manchester_refuses_a_class_as_a_data_range_in_every_spelling(name):
    # a class is not a data range, however its name is spelled
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester_data_range(name)
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester(f"d some (xsd:integer or {name})")


#: A literal whose datatype is a class: one text per position a literal occupies.
_LITERAL_POSITIONS_MANCHESTER = [
    'd value "1"^^{name}',
    'd some {{"1"^^{name}}}',
    'd only {{"2"^^xsd:integer, "1"^^{name}}}',
    'd some xsd:integer[>= "1"^^{name}]',
]


@pytest.mark.parametrize("name", [
    "owl:Thing", "owl:Nothing", f"<{OWL}Thing>", f"<{OWL}Nothing>"])
@pytest.mark.parametrize("template", _LITERAL_POSITIONS_MANCHESTER)
def test_manchester_refuses_a_class_as_the_datatype_of_a_literal(template, name):
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester(template.format(name=name))


@pytest.mark.parametrize("name", [
    "owl:Thing", "owl:Nothing", f"<{OWL}Thing>", f"<{OWL}Nothing>"])
def test_manchester_literal_reader_refuses_it_too(name):
    with pytest.raises(ManchesterSyntaxError, match="CLASS, not a data range"):
        dl.parse_manchester_literal(f'"1"^^{name}')


_LITERAL_POSITIONS_FUNCTIONAL = [
    'DataPropertyAssertion(p a "1"^^{name})',
    'NegativeDataPropertyAssertion(p a "1"^^{name})',
    'DataPropertyRange(p DataOneOf("1"^^{name}))',
    'SubClassOf(A DataHasValue(p "1"^^{name}))',
    'DataPropertyRange(p DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^{name}))',
]


@pytest.mark.parametrize("name", [
    "owl:Thing", "owl:Nothing", f"<{OWL}Thing>", f"<{OWL}Nothing>", f"{OWL}Thing"])
@pytest.mark.parametrize("template", _LITERAL_POSITIONS_FUNCTIONAL)
def test_functional_refuses_a_class_as_the_datatype_of_a_literal(template, name):
    axiom = template.format(name=name)
    result = parse_owl_functional_axioms(_doc(axiom))
    assert not result.ok and result.accepted == 0
    (refused,) = result.refused
    assert refused.keyword == name.strip("<>")
    assert "CLASS, not a data range" in refused.reason
    assert result.tbox == dl.TBox() and result.abox == dl.ABox()
    with pytest.raises(OwlFunctionalUnsupportedError, match="CLASS, not a data range"):
        parse_owl_functional(_doc(axiom))


def test_a_literal_of_an_ordinary_user_datatype_is_still_read():
    # the refusal is about the two class names, not about a user datatype's IRI
    result = parse_owl_functional_axioms(_doc(
        f'DataPropertyAssertion(p a "1"^^<{SMALL}>)', 'DataPropertyAssertion(p a "2"^^xsd:integer)'))
    assert result.ok and result.accepted == 2
    assert dl.parse_manchester_literal(f'"1"^^<{SMALL}>') == dl.Literal("1", SMALL)


@pytest.mark.parametrize("spelling", [
    "owl:topObjectProperty", f"<{OWL}topObjectProperty>", f"{OWL}topObjectProperty"])
def test_a_builtin_property_is_refused_in_every_spelling_by_both_readers(spelling):
    # the Manchester reader compared the BRACKETED full IRI to nothing and read it
    # as an ordinary role of that name, whose verdict is not the universal property's
    with pytest.raises(ManchesterSyntaxError, match="BUILT-IN property"):
        dl.parse_manchester(f"{spelling} some A")
    with pytest.raises(ManchesterSyntaxError, match="BUILT-IN property"):
        dl.parse_manchester_role_axiom(f"{spelling} Characteristics: Transitive")
    result = parse_owl_functional_axioms(_doc(
        f"SubClassOf(A ObjectSomeValuesFrom({spelling} B))"))
    assert result.accepted == 0 and "BUILT-IN property" in result.refused[0].reason


@pytest.mark.parametrize("spelling", [
    "xsd:integer", "<http://www.w3.org/2001/XMLSchema#integer>",
    "http://www.w3.org/2001/XMLSchema#integer"])
def test_a_builtin_datatype_is_refused_as_a_class_in_every_spelling_by_both_readers(spelling):
    with pytest.raises(ManchesterSyntaxError, match="DATATYPE, not a class"):
        dl.parse_manchester_axiom(f"A SubClassOf {spelling}")
    (refused,) = parse_owl_functional_axioms(
        _doc(f"SubClassOf(A {spelling})")).refused
    assert "DATATYPE, not a class" in refused.reason
