r"""A printed name reads back as THAT name, or the printer refuses it by name.

The three writers (glyph, Manchester, Functional-Style) used to print every name as
it was, and a name that is not one plain token of the reader's grammar then read
back as something else: a class called ``owl:Thing`` as the top class, a class
called ``Has Value`` inside ``ObjectIntersectionOf(Has Value Z)`` as TWO classes, a
class called ``A and B`` as a conjunction, a hand-built ``<http://x.org/a>`` as the
IRI without its brackets.

The rule, derived from what each reader does with a token:

* a syntax with an escape for a name (the Functional-Style ``<...>``: the reader
  takes everything up to the first ``>`` for one name) writes the escape whenever
  the bare name would not be read as one name;
* Manchester's escape is a full IRI, which needs a scheme and no whitespace, so a
  keyword, a name with whitespace or with a bracket and no scheme, and the empty
  name have no spelling and are REFUSED, by name;
* a name for which NO spelling reads back as itself is refused in every syntax:
  ``owl:Thing`` / ``owl:Nothing`` in class position (the reader makes them the top
  and bottom class in every spelling), a name that already holds the brackets of a
  full IRI (``<...>`` reads back without them), and, in the Functional-Style
  syntax, a name that holds ``>``;
* a text the reader REFUSES is not another reading. A class named like a built-in
  datatype (``xsd:integer``) is written as given by the Functional-Style writer,
  whose reader refuses it in every position (the keyword of a restriction says
  object or data there, so the filler is read as a class), as the module
  documentation of ``owl_functional`` says;
* Manchester Syntax has no such keyword: its reader tells a data restriction from an
  object restriction by the FILLER, so ``r some xsd:integer`` is a data restriction
  whatever the writer meant, and the full IRI of the datatype reads the same way. A
  class named like a built-in datatype therefore has no Manchester spelling and is
  REFUSED by the writer, in every position.

Every expected spelling below is derived by hand from those clauses and from the
tokenizers of the two readers, never read off the printers.
"""

import ast
import inspect
import textwrap

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import owl_functional
from unicode_fol_kit.dl.datatypes import BUILTIN_DATATYPES, canonical_datatype_name
from unicode_fol_kit.dl.owl_functional import (
    OwlFunctionalSyntaxError, parse_owl_functional, parse_owl_functional_class_expression,
    to_owl_functional, to_owl_functional_class_expression,
)
from unicode_fol_kit.dl.owl_manchester import ManchesterSyntaxError, parse_manchester, to_manchester

Z = dl.Atomic("Z")
OWL = "http://www.w3.org/2002/07/owl#"

MANCHESTER_KEYWORDS = ["and", "or", "not", "some", "only", "min", "max", "exactly", "value", "Self",
                       "inverse", "SubClassOf", "EquivalentTo", "SubPropertyOf", "Characteristics",
                       "InverseOf", "DisjointWith", "Domain", "Range", "SubClassOf:", "Domain:"]
TOP_AND_BOTTOM = ["owl:Thing", "owl:Nothing", f"{OWL}Thing", f"{OWL}Nothing"]
HAS_NO_SCHEME_AND_A_BRACKET = ["a(b", "a)b", "a{b", "a}b", "a[b", "a]b", "a,b"]


def _concepts(name):
    """The same name in the positions a printer writes one. The first four are the
    ones the refusal tests below are written for; the others put a CLASS name where the
    Manchester reader decides between an object and a data restriction: the head of
    the filler of ``some`` / ``only`` / ``min`` / ``max``."""
    return {
        "class": dl.And(dl.Atomic(name), Z),
        "role": dl.Exists(name, Z),
        "cardinality role": dl.AtLeast(2, name, Z),
        "individual": dl.HasValue("r", name),
        "filler": dl.Exists("r", dl.Atomic(name)),
        "number filler": dl.AtMost(1, "r", dl.Atomic(name)),
        "negated filler": dl.ForAll("r", dl.Not(dl.Atomic(name))),
        "conjunction filler": dl.Exists("r", dl.And(dl.Atomic(name), Z)),
    }


# --------------------------------------------------------------------------- #
# Manchester Syntax
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", MANCHESTER_KEYWORDS)
@pytest.mark.parametrize("position", ["class", "role", "cardinality role", "individual"])
def test_manchester_refuses_a_keyword_it_cannot_escape(name, position):
    # `and some Z` and `A and and` do not read as these names, and a keyword has
    # no escape: <and> is not a full IRI (no scheme), so it would read as the name
    # "<and>"
    with pytest.raises(ValueError, match=r"cannot be written so that parse_manchester") as info:
        to_manchester(_concepts(name)[position])
    assert repr(name) in str(info.value) and "keyword" in str(info.value)


@pytest.mark.parametrize("name", ["Has Value", "A and B", "a\tb", "x:y z"])
@pytest.mark.parametrize("position", ["class", "role", "cardinality role", "individual"])
def test_manchester_refuses_whitespace(name, position):
    # "A and B and Z" is a conjunction of three classes, not of a class named
    # "A and B" and Z: whitespace splits a name, and an IRI holds none
    with pytest.raises(ValueError, match="whitespace") as info:
        to_manchester(_concepts(name)[position])
    assert repr(name) in str(info.value)


@pytest.mark.parametrize("name", HAS_NO_SCHEME_AND_A_BRACKET)
def test_manchester_refuses_a_structural_character_it_has_no_iri_for(name):
    with pytest.raises(ValueError, match="no scheme"):
        to_manchester(dl.Atomic(name))


def test_manchester_refuses_the_empty_name():
    with pytest.raises(ValueError, match="empty"):
        to_manchester(dl.And(dl.Atomic(""), Z))


@pytest.mark.parametrize("name", TOP_AND_BOTTOM)
def test_manchester_refuses_the_top_and_bottom_class_names_as_classes(name):
    # `owl:Thing and Z` is Top and Z in EVERY spelling of the name, bracketed or not
    with pytest.raises(ValueError, match="top and the bottom class"):
        to_manchester(dl.And(dl.Atomic(name), Z))


@pytest.mark.parametrize("name", ["owl:Thing", "owl:Nothing"])
def test_manchester_writes_those_names_where_they_are_no_class(name):
    # as a role the name is an ordinary one: `owl:Thing some Z` reads back as that role
    concept = dl.Exists(name, Z)
    assert to_manchester(concept) == f"{name} some Z"
    assert parse_manchester(f"{name} some Z") == concept
    # and as an individual: `r value owl:Thing`
    value = dl.HasValue("r", name)
    assert to_manchester(value) == f"r value {name}"
    assert parse_manchester(f"r value {name}") == value


@pytest.mark.parametrize("position", ["class", "role", "individual"])
def test_manchester_refuses_a_name_that_carries_its_own_iri_brackets(position):
    # the reader stores an IRI WITHOUT its brackets, so "<http://x.org/a>" written
    # as it is reads back as "http://x.org/a": another name. Written twice, the
    # reader takes "<<http://x.org/a>>" for one odd word
    with pytest.raises(ValueError, match="already holds the angle brackets"):
        to_manchester(_concepts("<http://x.org/a>")[position])


@pytest.mark.parametrize("name, spelling", [
    ("Person", "Person"),
    ("ex:Person", "ex:Person"),
    ("x:and", "x:and"),                       # a keyword is a whole word, not a part of one
    ("andy", "andy"),
    ("Domainx", "Domainx"),
    ("self", "self"),                         # Self is capitalised
    ("a=b", "a=b"),
    ("a.b", "a.b"),
    ("http://x.org/a", "<http://x.org/a>"),
    ("http://x.org/a,b", "<http://x.org/a,b>"),
    ("urn:x:a,b", "<urn:x:a,b>"),             # a scheme and a structural character
    ("http://x.org/a>b", "http://x.org/a>b"), # a '>' no bracket can enclose, still one bare word
])
def test_manchester_writes_what_the_reader_reads_back_as_one_name(name, spelling):
    assert to_manchester(dl.Atomic(name)) == spelling
    assert parse_manchester(spelling) == dl.Atomic(name)
    for position, concept in _concepts(name).items():
        assert parse_manchester(to_manchester(concept)) == concept, position


@pytest.mark.parametrize("write", [
    lambda name: dl.role_axiom_to_manchester("subproperty", name, "s"),
    lambda name: dl.role_axiom_to_manchester("domain", "r", dl.Atomic(name)),
    lambda name: dl.to_manchester_data_range(dl.Datatype(name)),
    lambda name: to_manchester(dl.DataExists("d", dl.Datatype(name))),
    lambda name: to_manchester(dl.DataHasValue("d", dl.Literal("5", name))),
])
@pytest.mark.parametrize("name", ["and", "part of"])
def test_manchester_refuses_the_same_names_in_role_axioms_and_data_ranges(write, name):
    with pytest.raises(ValueError, match="cannot be written so that parse_manchester"):
        write(name)


def test_manchester_a_numeral_is_a_class_and_a_role_name_but_no_individual_name():
    # `3 and Z`, `3 some Z` are the class and the role "3"; `r value 3` is a data
    # value, so no spelling of an INDIVIDUAL named 3 reads back as one
    assert parse_manchester(to_manchester(dl.And(dl.Atomic("3"), Z))) == dl.And(dl.Atomic("3"), Z)
    assert parse_manchester(to_manchester(dl.Exists("3", Z))) == dl.Exists("3", Z)
    for numeral in ("1.5", "3", "-3", "1.5f"):
        with pytest.raises(ValueError, match="spelled like a numeral"):
            to_manchester(dl.HasValue("r", numeral))


#: Every datatype of the OWL 2 datatype map, once as the usual prefix form and once as the
#: full IRI of its namespace: the reader treats both spellings as the one datatype.
_NAMESPACE_IRI = {"xsd:": "http://www.w3.org/2001/XMLSchema#",
                  "rdfs:": "http://www.w3.org/2000/01/rdf-schema#",
                  "rdf:": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
                  "owl:": OWL}
BUILTIN_DATATYPE_NAMES = sorted(BUILTIN_DATATYPES) + [
    _NAMESPACE_IRI[name[:name.index(":") + 1]] + name[name.index(":") + 1:]
    for name in sorted(BUILTIN_DATATYPES)]


def test_the_datatype_names_of_the_tests_are_each_datatype_in_both_spellings():
    # one prefix form and one full IRI per datatype of the map, all different, and the
    # reader's own canonical form maps every one of them back to a datatype of the map
    assert len(BUILTIN_DATATYPE_NAMES) == 2 * len(BUILTIN_DATATYPES)
    assert len(set(BUILTIN_DATATYPE_NAMES)) == len(BUILTIN_DATATYPE_NAMES)
    assert {canonical_datatype_name(name) for name in BUILTIN_DATATYPE_NAMES} == set(BUILTIN_DATATYPES)
    assert "xsd:integer" in BUILTIN_DATATYPE_NAMES
    assert f"{_NAMESPACE_IRI['xsd:']}integer" in BUILTIN_DATATYPE_NAMES


def test_manchester_reads_a_datatype_name_after_a_role_keyword_as_a_data_restriction():
    # This is WHY the writer must refuse it: written as given, the object
    # restriction reads back as the DATA restriction of the same text, a different
    # node of a different sort. Hand-derived from the grammar: `r some xsd:integer`
    # puts the datatype in the filler, which is what makes a restriction a data one.
    for text, data_class in (("r some xsd:integer", dl.DataExists),
                             ("r only not xsd:integer", dl.DataForAll),
                             ("r max 1 xsd:integer", dl.DataAtMost),
                             ("r some (xsd:integer and Z)", dl.DataExists),
                             ("r some <http://www.w3.org/2001/XMLSchema#integer>", dl.DataExists)):
        assert isinstance(parse_manchester(text), data_class), text
    # and anywhere else the reader refuses the name, by name: it is no class
    with pytest.raises(ManchesterSyntaxError, match="DATATYPE"):
        parse_manchester("xsd:integer")
    with pytest.raises(ManchesterSyntaxError, match="DATATYPE"):
        parse_manchester("Z and xsd:integer")


@pytest.mark.parametrize("position", ["class", "filler", "number filler", "negated filler",
                                      "conjunction filler"])
def test_manchester_refuses_a_class_named_like_a_builtin_datatype_in_every_position(position):
    # No spelling of the name reads back as that CLASS: after a role keyword the reader
    # reads it as the datatype (test above), and elsewhere it refuses the text. So the
    # writer refuses, BY NAME, in every datatype of the map and both spellings of it.
    for name in BUILTIN_DATATYPE_NAMES:
        with pytest.raises(ValueError, match=r"cannot be written so that parse_manchester") as info:
            to_manchester(_concepts(name)[position])
        assert repr(name) in str(info.value) and "built-in datatype" in str(info.value), name


def test_manchester_refuses_a_class_named_like_a_datatype_in_a_role_axiom_and_in_a_bare_class():
    for name in ("xsd:integer", "rdfs:Literal", "owl:rational", f"{OWL}real"):
        for axiom in (("domain", "r", dl.Atomic(name)), ("range", "r", dl.Atomic(name)),
                      ("domain", "r", dl.Exists("s", dl.Atomic(name))),
                      ("range", "r", dl.AtLeast(2, "s", dl.Atomic(name)))):
            with pytest.raises(ValueError, match="built-in datatype"):
                dl.role_axiom_to_manchester(*axiom)
        with pytest.raises(ValueError, match="built-in datatype"):
            to_manchester(dl.Atomic(name))
        with pytest.raises(ValueError, match="built-in datatype"):
            to_manchester(dl.Not(dl.Atomic(name)))


def test_manchester_still_writes_a_datatype_name_where_it_is_a_role_an_individual_or_a_datatype():
    # In the role slot, as an individual and in the data layer the name is an ordinary
    # one. Hand-derived: `xsd:integer some Z` has the role xsd:integer (the filler Z is
    # no datatype); `r value xsd:integer` has an individual (not a literal: it is no
    # numeral and has no quotes); `d some xsd:integer` is the data restriction itself.
    for concept, text in ((dl.Exists("xsd:integer", Z), "xsd:integer some Z"),
                          (dl.AtLeast(2, "xsd:integer", Z), "xsd:integer min 2 Z"),
                          (dl.HasValue("r", "xsd:integer"), "r value xsd:integer"),
                          (dl.DataExists("d", dl.Datatype("xsd:integer")), "d some xsd:integer")):
        assert to_manchester(concept) == text
        assert parse_manchester(text) == concept
    assert dl.role_axiom_to_manchester("subproperty", "xsd:integer", "s") == "xsd:integer SubPropertyOf s"
    assert dl.parse_manchester_role_axiom("xsd:integer SubPropertyOf s") == ("subproperty", "xsd:integer", "s")


@pytest.mark.parametrize("numeral", ["3", "-3", "1.5", "1.5f"])
def test_manchester_refuses_a_nominal_whose_individual_is_spelled_like_a_numeral(numeral):
    # `r some {3}` is a restriction over the DATA set {3}: the reader takes a brace list
    # that starts with a numeral for a list of literals. No spelling reads back as the
    # nominal, so the writer refuses, as it does for the value restriction.
    assert isinstance(parse_manchester(f"r some {{{numeral}}}"), dl.DataExists)
    for concept in (dl.Nominal(numeral), dl.Exists("r", dl.Nominal(numeral))):
        with pytest.raises(ValueError, match="spelled like a numeral"):
            to_manchester(concept)


# --------------------------------------------------------------------------- #
# Functional-Style Syntax
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, spelling", [
    ("Has Value", "<Has Value>"),             # whitespace: the reader splits a bare name
    ("a\tb", "<a\tb>"),
    ("", "<>"),                               # the empty name: <> is one empty IRI
    ("a(b", "<a(b>"),                         # ( ) = " and < are structure outside <...>
    ("a)b", "<a)b>"),
    ("a=b", "<a=b>"),
    ('a"b', '<a"b>'),
    ("ObjectUnionOf", "<ObjectUnionOf>"),     # a bare keyword is read as the keyword
    ("ObjectIntersectionOf", "<ObjectIntersectionOf>"),
    ("DataSomeValuesFrom", "<DataSomeValuesFrom>"),
    ("DataUnionOf", "<DataUnionOf>"),
    ("ObjectOneOf", "<ObjectOneOf>"),
    ("Annotation", "<Annotation>"),           # skipped in front of an axiom's first argument
    ("_:x", "<_:x>"),                         # a bare _:x is an anonymous individual: refused
    ("http://x.org/a", "<http://x.org/a>"),   # as it always was
    ("Person", "Person"),                     # and what needs nothing stays bare
    ("ex:Person", "ex:Person"),
    ("a,b", "a,b"),
    ("and", "and"),                           # Manchester's keywords are no keywords here
])
def test_functional_style_writes_the_escape_where_a_bare_name_would_not_read_back(name, spelling):
    assert to_owl_functional_class_expression(dl.Atomic(name)) == spelling
    for position, concept in _concepts(name).items():
        text = to_owl_functional_class_expression(concept)
        assert parse_owl_functional_class_expression(text) == concept, (position, text)


def test_functional_style_a_name_with_whitespace_is_one_class_not_two():
    # ObjectIntersectionOf(a b Z) is a conjunction of THREE classes: the bare
    # spelling of "a b" read back as another tree, silently
    text = to_owl_functional_class_expression(dl.And(dl.Atomic("a b"), Z))
    assert text == "ObjectIntersectionOf(<a b> Z)"
    assert parse_owl_functional_class_expression(text) == dl.And(dl.Atomic("a b"), Z)
    three = parse_owl_functional_class_expression("ObjectIntersectionOf(a b Z)")
    assert three == dl.And(dl.And(dl.Atomic("a"), dl.Atomic("b")), Z)


def test_functional_style_the_empty_role_name_is_not_swallowed():
    # "ObjectMinCardinality(2  Z)" read the class Z as the ROLE and defaulted the filler
    concept = dl.AtLeast(2, "", Z)
    text = to_owl_functional_class_expression(concept)
    assert text == "ObjectMinCardinality(2 <> Z)"
    assert parse_owl_functional_class_expression(text) == concept


@pytest.mark.parametrize("name", TOP_AND_BOTTOM)
def test_functional_style_refuses_the_top_and_bottom_class_names_as_classes(name):
    with pytest.raises(ValueError, match="top and the bottom class"):
        to_owl_functional_class_expression(dl.And(dl.Atomic(name), Z))
    with pytest.raises(ValueError, match="top and the bottom class"):
        to_owl_functional(dl.TBox().add(dl.Atomic(name), Z), dl.ABox())


@pytest.mark.parametrize("name", ["owl:Thing", "owl:Nothing"])
def test_functional_style_writes_those_names_where_they_are_no_class(name):
    concept = dl.Exists(name, Z)
    text = to_owl_functional_class_expression(concept)
    assert text == f"ObjectSomeValuesFrom({name} Z)"
    assert parse_owl_functional_class_expression(text) == concept
    abox = dl.ABox().assert_concept(name, Z)
    assert parse_owl_functional(to_owl_functional(dl.TBox(), abox)) == (dl.TBox(), abox)


@pytest.mark.parametrize("name", ["a>b", "http://x.org/a>b"])
def test_functional_style_refuses_a_name_with_a_closing_bracket(name):
    # <a>b> ends at the first '>', and a bare a>b is a name and a stray '>'
    with pytest.raises(ValueError, match="'>'"):
        to_owl_functional_class_expression(dl.Atomic(name))


def test_functional_style_refuses_a_name_that_carries_its_own_iri_brackets():
    with pytest.raises(ValueError, match="already holds the angle brackets"):
        to_owl_functional_class_expression(dl.Atomic("<http://ex.org/A>"))
    with pytest.raises(ValueError, match="already holds the angle brackets"):
        to_owl_functional(dl.TBox(), dl.ABox().assert_concept("<http://ex.org/a>", Z))


def test_functional_style_writes_a_class_named_like_a_datatype_as_given_and_the_reader_refuses_it():
    text = to_owl_functional_class_expression(dl.Atomic("xsd:integer"))
    assert text == "xsd:integer"
    with pytest.raises(OwlFunctionalSyntaxError, match="DATATYPE"):
        parse_owl_functional_class_expression(text)


def test_functional_style_a_document_with_odd_names_in_every_position_round_trips():
    tbox = (dl.TBox()
            .add(dl.Atomic("Has Value"), dl.Exists("part of", dl.Atomic("ObjectUnionOf")))
            .add_role_domain("part of", dl.Atomic("Annotation"))
            .add_transitive_role("part of"))
    abox = (dl.ABox()
            .assert_concept("the individual", dl.Atomic("Has Value"))
            .assert_role("the individual", "_:b", "part of")
            .assert_distinct("the individual", "_:b"))
    text = to_owl_functional(tbox, abox)
    # the declarations and the axioms carry the escape, hand-derived line by line
    for line in ("Declaration(Class(<Has Value>))", "Declaration(Class(<ObjectUnionOf>))",
                 "Declaration(Class(<Annotation>))", "Declaration(ObjectProperty(<part of>))",
                 "Declaration(NamedIndividual(<_:b>))", "Declaration(NamedIndividual(<the individual>))",
                 "SubClassOf(<Has Value> ObjectSomeValuesFrom(<part of> <ObjectUnionOf>))",
                 "ObjectPropertyDomain(<part of> <Annotation>)",
                 "ClassAssertion(<Has Value> <the individual>)",
                 "ObjectPropertyAssertion(<part of> <the individual> <_:b>)",
                 "DifferentIndividuals(<the individual> <_:b>)"):
        assert f"  {line}" in text, line
    assert parse_owl_functional(text) == (tbox, abox)


@pytest.mark.parametrize("prop, datatype", [
    ("has amount", "my type"),           # whitespace
    ("d", "ObjectUnionOf"),              # a datatype spelled like a class-expression keyword
    ("a(b", "DataUnionOf"),              # a data-range keyword as a datatype
    ("", "x y"),
])
def test_functional_style_a_data_layer_with_odd_names_round_trips(prop, datatype):
    tbox = dl.TBox()
    tbox.add(Z, dl.DataExists(prop, dl.Datatype(datatype)))
    tbox.add_data_property_range(prop, dl.Datatype(datatype))
    abox = dl.ABox().assert_data("a b", prop, dl.Literal("5", datatype))
    assert parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)


def test_the_keyword_set_covers_every_keyword_the_class_expression_reader_dispatches_on():
    # The writer brackets a bare name that is one of these. A keyword added to the
    # reader and not to the set would be written bare, and read as the keyword.
    words = set()
    for function in (owl_functional._Parser.parse_class_expression, owl_functional._Parser._parse_data_range,
                     owl_functional._Parser._parse_object_property_expression,
                     owl_functional._Parser._skip_leading_annotations):
        tree = ast.parse(textwrap.dedent(inspect.getsource(function)))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                # a keyword is CamelCase; the token types the parser compares are ALL CAPS
                if node.value[:1].isupper() and node.value.isidentifier() and node.value != node.value.upper():
                    words.add(node.value)
    assert words, "the scan found no keyword at all"
    assert words <= owl_functional._NAME_KEYWORDS, sorted(words - owl_functional._NAME_KEYWORDS)


# --------------------------------------------------------------------------- #
# Whatever the name, no printer writes text that reads back as another tree.
# --------------------------------------------------------------------------- #

ADVERSARIAL_NAMES = (
    MANCHESTER_KEYWORDS + TOP_AND_BOTTOM + HAS_NO_SCHEME_AND_A_BRACKET + BUILTIN_DATATYPE_NAMES + [
        f"<{OWL}Thing>", "xsd:integer", "rdfs:Literal", "a b", "A and B", "a>b", "a<b", 'a"b', "a=b", "a.b", "a:", "", "3",
        "_:x", "a\tb", "http://x.org/a", "http://x.org/a,b", "<http://x.org/a>", "urn:x", "x:y", "1.5", "-3",
        "1e5", "0x10", "A not B", "r some B", "r value a", "ObjectUnionOf", "ObjectOneOf", "Annotation",
        "DataOneOf", "ObjectInverseOf", "Declaration", "a⊓b", "¬a", "⊤", "⊥", "∃", "a⁻", "≥", "x⊑y", "A.B",
        "owl:topObjectProperty", "owl:bottomObjectProperty", "=", "≠",
    ])


def _outcome(printer, reader, concept):
    try:
        text = printer(concept)
    except ValueError:
        return "refused by the printer"
    try:
        back = reader(text)
    except ValueError:
        return "refused by the reader"
    return "same" if back == concept else f"ANOTHER: {text!r} -> {back!r}"


@pytest.mark.parametrize("printer, reader", [
    (lambda c: c.to_unicode(), dl.parse_concept),
    (to_manchester, parse_manchester),
    (to_owl_functional_class_expression, parse_owl_functional_class_expression),
], ids=["glyph", "manchester", "functional-style"])
@pytest.mark.parametrize("position", ["class", "role", "cardinality role", "individual", "filler",
                                      "number filler", "negated filler", "conjunction filler"])
def test_no_name_is_written_so_that_it_reads_back_as_another_expression(printer, reader, position):
    others = []
    for name in ADVERSARIAL_NAMES:
        outcome = _outcome(printer, reader, _concepts(name)[position])
        if outcome.startswith("ANOTHER"):
            others.append((name, outcome))
    assert others == []


@pytest.mark.parametrize("position", ["class", "role", "individual"])
def test_no_name_is_written_into_a_document_so_that_it_reads_back_as_another_document(position):
    others = []
    for name in ADVERSARIAL_NAMES:
        tbox, abox = dl.TBox(), dl.ABox()
        if position == "class":
            tbox.add(dl.Atomic(name), Z)
            abox.assert_concept("a", dl.Atomic(name))
        elif position == "role":
            tbox.add(Z, dl.Exists(name, Z))
            abox.assert_role("a", "b", name)
        else:
            abox.assert_concept(name, Z)
            abox.assert_role(name, "b", "r")
        try:
            text = to_owl_functional(tbox, abox)
        except (ValueError, TypeError):
            continue                       # refused by the writer, by name
        try:
            back = parse_owl_functional(text)
        except ValueError:
            continue                       # refused by the reader
        if back != (tbox, abox):
            others.append((name, text))
    assert others == []


def test_the_functional_style_writer_refuses_only_what_no_spelling_carries():
    # Everything the Functional-Style escape can carry IS written (and reads back):
    # the only refusals are the top and bottom class names as classes, a '>', and a
    # name that holds its own brackets
    refused = []
    for name in ADVERSARIAL_NAMES:
        try:
            to_owl_functional_class_expression(dl.Atomic(name))
        except ValueError:
            refused.append(name)
    assert sorted(refused) == sorted(TOP_AND_BOTTOM + ["a>b", "<http://x.org/a>", f"<{OWL}Thing>"])
