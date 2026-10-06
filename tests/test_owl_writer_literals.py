r"""A literal's datatype goes through the writer's NAME renderer.

Both OWL writers render a datatype NAME through a renderer of their own: the
Functional-Syntax writer brackets an IRI (``<http://ex.org/dt#Small>``), and the
Hets document writer replaces every user-defined datatype by a synthetic token
(``:T1``), because it never writes the kit's own name verbatim. A LITERAL carries
its datatype too (``"5"^^dt``), and the literal's text used to bypass that
renderer: the Hets document declared ``:T1`` and then wrote
``"5"^^http://ex.org/dt#Small`` -- a name bound nowhere -- and the Functional
writer wrote an unbracketed IRI after ``^^``, which is not OWL 2 syntax (the
kit's own reader tolerates it, so the round trip stayed green).

How the expected text is derived
--------------------------------
``dl.owl_functional._render_name`` wraps a name that contains ``://`` in angle
brackets and writes any other name bare, so for the datatype
``http://ex.org/dt#Small`` every position -- a declaration, a data range, a
literal -- reads ``<http://ex.org/dt#Small>``, and for the datatype ``MyDt`` it
reads ``MyDt``. ``hets.owl_backend._render_document`` allocates its tokens in the
order it visits the axioms: the data box first (ranges, then datatype
definitions), then the concept inclusions, then the ABox, so the knowledge base
below allocates ``:P1`` for ``p`` and ``:P2`` for ``q`` (their ranges come
first), ``:T1`` for the datatype at the first range that names it, ``:C1`` for
``A`` and ``:I1`` for ``a``. A BUILT-IN datatype (``xsd:integer``) keeps its own
name in both writers.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.datatypes import render_literal_fs
from unicode_fol_kit.dl.owl_functional import (
    parse_owl_functional, parse_owl_functional_axioms, to_owl_functional,
)
from unicode_fol_kit.hets.owl_backend import _render_document

IRI = "http://ex.org/dt#Small"
SMALL = dl.Datatype(IRI)


def _kb(datatype_name=IRI):
    """One user datatype ``datatype_name`` used in a definition, two ranges, a
    value restriction, a negative and a positive data assertion."""
    small = dl.Datatype(datatype_name)
    tbox = dl.TBox()
    tbox.add_datatype_definition(datatype_name, dl.DatatypeRestriction(
        dl.Datatype("xsd:integer"),
        (("xsd:maxInclusive", dl.Literal("9", "xsd:integer")),)))
    tbox.add_data_property_range("p", small)
    tbox.add(dl.Atomic("A"), dl.DataHasValue("p", dl.Literal("7", datatype_name)))
    tbox.add_data_property_range("q", dl.DataOneOf((
        dl.Literal("1", datatype_name), dl.Literal("2", "xsd:integer"))))
    abox = (dl.ABox()
            .assert_data("a", "p", dl.Literal("5", datatype_name))
            .assert_negative_data("a", "p", dl.Literal("6", datatype_name)))
    return tbox, abox


def _lines(document):
    return {line.strip() for line in document.splitlines() if line.startswith("  ")}


# --------------------------------------------------------------------------- #
# the literal renderer itself
# --------------------------------------------------------------------------- #

def test_render_literal_fs_passes_the_datatype_through_the_renderer():
    literal = dl.Literal("5", IRI)
    assert render_literal_fs(literal) == f'"5"^^{IRI}'          # default: verbatim
    assert render_literal_fs(literal, lambda n: f"<{n}>") == f'"5"^^<{IRI}>'
    assert render_literal_fs(literal, lambda n: ":T1") == '"5"^^:T1'


def test_a_language_tagged_literal_has_no_datatype_to_render():
    # "abc"@en is an rdf:PlainLiteral; its text is the tag, never a name
    literal = dl.Literal("abc", language="en")
    assert render_literal_fs(literal, lambda n: "SHOULD-NOT-BE-CALLED") == '"abc"@en'


def test_quotes_and_backslashes_are_still_escaped():
    literal = dl.Literal('a"b\\c')
    assert render_literal_fs(literal, lambda n: n) == '"a\\"b\\\\c"^^xsd:string'


# --------------------------------------------------------------------------- #
# the Hets document
# --------------------------------------------------------------------------- #

def test_the_hets_document_writes_a_literals_datatype_as_its_declared_token():
    tbox, abox = _kb()
    lines = _lines(_render_document(tbox, abox))
    # the one user datatype is declared, under a synthetic token ...
    assert "Declaration(Datatype(:T1))" in lines
    # ... and every position that names it uses that token, the literals included
    assert "DataPropertyRange(:P1 :T1)" in lines
    assert 'DataPropertyRange(:P2 DataOneOf("1"^^:T1 "2"^^xsd:integer))' in lines
    assert ('DatatypeDefinition(:T1 DatatypeRestriction(xsd:integer '
            'xsd:maxInclusive "9"^^xsd:integer))') in lines
    assert 'SubClassOf(:C1 DataHasValue(:P1 "7"^^:T1))' in lines
    assert 'DataPropertyAssertion(:P1 :I1 "5"^^:T1)' in lines
    assert 'NegativeDataPropertyAssertion(:P1 :I1 "6"^^:T1)' in lines


def test_no_name_of_the_knowledge_base_leaks_into_the_hets_document():
    tbox, abox = _kb()
    document = _render_document(tbox, abox)
    # the only IRIs a document may contain are the prefix and ontology headers
    body = [line for line in document.splitlines() if line.startswith("  ")]
    assert body and not any("ex.org" in line for line in body)


def test_a_literal_of_an_undefined_user_datatype_is_still_declared():
    # a literal alone names the datatype: it must still be declared, under the
    # token the literal uses (OWL 2 requires every datatype to be declared)
    abox = dl.ABox().assert_data("a", "p", dl.Literal("5", "MyDt"))
    lines = _lines(_render_document(dl.TBox(), abox))
    assert "Declaration(Datatype(:T1))" in lines
    assert 'DataPropertyAssertion(:P1 :I1 "5"^^:T1)' in lines


def test_a_builtin_datatype_literal_is_unchanged_in_the_hets_document():
    abox = dl.ABox().assert_data("a", "p", dl.Literal("5", "xsd:integer"))
    lines = _lines(_render_document(dl.TBox(), abox))
    assert 'DataPropertyAssertion(:P1 :I1 "5"^^xsd:integer)' in lines
    assert not any(line.startswith("Declaration(Datatype") for line in lines)


# --------------------------------------------------------------------------- #
# the Functional-Syntax writer
# --------------------------------------------------------------------------- #

def test_to_owl_functional_brackets_an_iri_datatype_everywhere():
    tbox, abox = _kb()
    lines = _lines(to_owl_functional(tbox, abox))
    assert f"Declaration(Datatype(<{IRI}>))" in lines
    assert f"DataPropertyRange(p <{IRI}>)" in lines
    assert f'DataPropertyRange(q DataOneOf("1"^^<{IRI}> "2"^^xsd:integer))' in lines
    assert f'SubClassOf(A DataHasValue(p "7"^^<{IRI}>))' in lines
    assert f'DataPropertyAssertion(p a "5"^^<{IRI}>)' in lines
    assert f'NegativeDataPropertyAssertion(p a "6"^^<{IRI}>)' in lines
    assert not any("^^http" in line for line in lines)


def test_the_bracketed_document_still_reads_back_to_the_same_knowledge_base():
    tbox, abox = _kb()
    assert parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)


def test_a_valid_document_is_written_back_with_its_brackets():
    # the text below is valid OWL 2 Functional-Style Syntax; reading it and
    # writing it back must not strip the brackets from the literal's datatype
    text = ('Ontology(\n'
            '  DataPropertyAssertion(<http://ex.org/p> <http://ex.org/a> '
            '"5"^^<http://ex.org/dt#Small>)\n'
            '  SubClassOf(<http://ex.org/A> DataHasValue(<http://ex.org/p> '
            '"7"^^<http://ex.org/dt#Small>))\n'
            ')')
    result = parse_owl_functional_axioms(text)
    assert result.ok
    written = to_owl_functional(result.tbox, result.abox)
    assert '"5"^^<http://ex.org/dt#Small>' in written
    assert '"7"^^<http://ex.org/dt#Small>' in written
    assert "^^http" not in written


def test_a_bare_user_datatype_name_is_written_bare():
    # a name with no "://" is a prefixed/plain name: rendered as it is, in the
    # declaration, the range AND the literal alike
    tbox, abox = _kb("MyDt")
    lines = _lines(to_owl_functional(tbox, abox))
    assert "Declaration(Datatype(MyDt))" in lines
    assert "DataPropertyRange(p MyDt)" in lines
    assert 'DataPropertyAssertion(p a "5"^^MyDt)' in lines
    assert parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)


def test_a_builtin_literal_and_a_language_tag_are_unchanged():
    abox = (dl.ABox()
            .assert_data("a", "p", dl.Literal("5", "xsd:integer"))
            .assert_data("a", "p", dl.Literal("abc", language="en")))
    lines = _lines(to_owl_functional(dl.TBox(), abox))
    assert 'DataPropertyAssertion(p a "5"^^xsd:integer)' in lines
    assert 'DataPropertyAssertion(p a "abc"@en)' in lines


def test_a_full_iri_spelling_of_a_builtin_datatype_is_still_the_prefixed_name():
    # canonical_datatype_name folds it to xsd:integer at construction, so the
    # writer never sees the namespace spelling: nothing to bracket
    abox = dl.ABox().assert_data(
        "a", "p", dl.Literal("5", "http://www.w3.org/2001/XMLSchema#integer"))
    lines = _lines(to_owl_functional(dl.TBox(), abox))
    assert 'DataPropertyAssertion(p a "5"^^xsd:integer)' in lines


@pytest.mark.parametrize("name", [IRI, "MyDt", "urn:x:Small"])
def test_the_round_trip_holds_for_each_spelling_of_a_user_datatype(name):
    tbox, abox = _kb(name)
    assert parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)
