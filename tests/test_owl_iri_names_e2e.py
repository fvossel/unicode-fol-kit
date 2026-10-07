r"""A Manchester knowledge base with an IRI-named user datatype, end to end.

The two OWL readers used to name one IRI two ways: a bracketed IRI kept its
brackets as a datatype or class name but lost them as the datatype of a literal. So a
user datatype read from Manchester never matched its own literals, and the
first-order image answered a question wrongly. Both readers now store the IRI
without its brackets (see ``test_owl_iri_names.py``); this file asks the question
through ``dl.kb_to_fol`` and ``api.prove``.

How the expected verdicts are derived
-------------------------------------
The knowledge base::

    DatatypeDefinition(Small = xsd:integer[>= 0])
    DatatypeDefinition(Large = xsd:integer[>= 100])
    p(a, "5"^^Small)

The image types a literal by its datatype (``LiteralTyping``: the literal's term
is a data value of ``Small``), and a defined datatype IS its definition
(``∀v (Small(v) ↔ xsd:integer(v) ∧ v ≥ 0)``). Hence

* ``a : p some Small`` is ENTAILED -- the one data value ``p`` relates ``a`` to is
  in ``Small`` -- so PROVED (OWL says entailed; the readers used to
  say refuted, because the query's ``Small`` and the literal's ``Small`` were two
  different predicate names);
* ``a : p some xsd:integer`` is entailed too, through ``Small ⊑ xsd:integer``;
* ``a : p some Large`` is NOT entailed: the value's term is an uninterpreted
  constant that is only known to be a non-negative integer, so a model where it is
  below 100 exists -- and ``a : p some xsd:string`` is not either (``xsd:string``
  is a datatype family disjoint from the numbers, so the one value is no string);
* the knowledge base HAS a model (so the PROVED above is not the vacuous
  "everything follows from an inconsistent knowledge base").

Z3-backed calls take their budget in MILLISECONDS; "unknown" is not a verdict, so
every assertion below is ``proved`` or ``refuted``, never a weaker word.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.owl_functional import parse_owl_functional
from unicode_logic_kit.fol.nodes import Not as FNot

TIMEOUT_MS = 30000
SMALL = "http://ex.org/dt#Small"
LARGE = "http://ex.org/dt#Large"


def _manchester_knowledge_base():
    tbox = (dl.TBox()
            .add_datatype_definition(SMALL, dl.parse_manchester_data_range("xsd:integer[>= 0]"))
            .add_datatype_definition(LARGE, dl.parse_manchester_data_range("xsd:integer[>= 100]")))
    abox = dl.ABox().assert_data("a", "p", dl.parse_manchester_literal(f'"5"^^<{SMALL}>'))
    return tbox, abox


def _functional_knowledge_base():
    return parse_owl_functional(
        "Ontology(\n"
        f'  DatatypeDefinition(<{SMALL}> DatatypeRestriction(xsd:integer xsd:minInclusive "0"^^xsd:integer))\n'
        f'  DatatypeDefinition(<{LARGE}> DatatypeRestriction(xsd:integer xsd:minInclusive "100"^^xsd:integer))\n'
        f'  DataPropertyAssertion(p a "5"^^<{SMALL}>)\n'
        ")")


def _entailed(tbox, abox, concept):
    """``prove(a : concept)`` against the knowledge base's own image."""
    kb = dl.kb_to_fol(tbox, abox)
    goal = dl.abox_to_fol(dl.ABox().assert_concept("a", concept))
    status = api.prove(goal, list(kb.premises), timeout=TIMEOUT_MS).status
    assert status in ("proved", "refuted"), status
    return status == "proved"


def _query(text):
    return dl.parse_manchester(text, datatypes=(SMALL, LARGE))


@pytest.mark.parametrize("make", [_manchester_knowledge_base, _functional_knowledge_base])
@pytest.mark.parametrize("text, entailed", [
    (f"p some <{SMALL}>", True),            # the question that used to be answered wrongly
    ("p some xsd:integer", True),           # Small is below xsd:integer
    (f"p some <{LARGE}>", False),           # a model where the value is below 100
    ("p some xsd:string", False),           # the value is a number, not a string
])
def test_a_manchester_query_over_an_iri_named_datatype(make, text, entailed):
    tbox, abox = make()
    assert _entailed(tbox, abox, _query(text)) is entailed


def test_the_knowledge_base_has_a_model():
    tbox, abox = _manchester_knowledge_base()
    kb = dl.kb_to_fol(tbox, abox)
    # `proved` would be "the negation of the knowledge base follows" = no model
    assert api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status == "refuted"


def test_the_two_readers_meet_in_one_query():
    # A TBox read by one reader, an ABox by the other, the question by the first:
    # entailed iff the three name the class by one string. A mismatch would be silent.
    tbox = dl.TBox()
    kind, sub, sup = dl.parse_manchester_axiom("<http://ex.org/A> SubClassOf <http://ex.org/B>")
    tbox.add(sub, sup)
    _, abox = parse_owl_functional('Ontology(ClassAssertion(<http://ex.org/A> a))')
    assert _entailed(tbox, abox, dl.parse_manchester("<http://ex.org/B>")) is True
    # the same knowledge base does not entail an unrelated class
    assert _entailed(tbox, abox, dl.parse_manchester("<http://ex.org/C>")) is False
