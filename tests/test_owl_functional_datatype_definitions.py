"""The per-axiom Functional-Style reader and ``DatatypeDefinition``.

OWL 2 (Structural Specification §9.4) gives a datatype ONE definition and requires
the definitions to be acyclic. ``dl.TBox.add_datatype_definition`` checks both
against the definitions it already holds, and ``dl.parse_owl_functional`` reads
through it, so the strict reader raises at the axiom that breaks a rule.

``dl.parse_owl_functional_axioms`` reads each axiom into a scratch ``TBox`` of its
own and merges it on success, so the scratch ``TBox`` knows no earlier definition.
Until the reader checked a definition against the ones read before it, a definition
that closed a cycle with an earlier one, or gave a name a second and different
definition, was stored; the knowledge base it handed on was refused, by name, only
when it was rendered. The reader now reports it when it reads it, the way it reports
every other axiom it does not store.

Hand-derived expectations, for the documents below (``¬`` is ``DataComplementOf``):

* ``P ≡ ¬Q`` then ``Q ≡ ¬P``: ``P`` refers to ``Q``, which has no definition yet, so
  the first is a legal set of one. The second makes ``P → Q → P``, a cycle: refused,
  and only ``P ≡ ¬Q`` is stored. Whatever is stored is acyclic, so rendering the
  knowledge base works.
* ``D ≡ xsd:integer`` then ``D ≡ xsd:string``: two different definitions of ``D``;
  the second is refused. ``D ≡ xsd:integer`` twice is ONE axiom said twice: both are
  accepted, as the builder accepts it.
* ``A ≡ B ∪ xsd:integer``, ``B ≡ C ∪ xsd:string``, ``C ≡ ¬A``: the third closes
  ``A → B → C → A`` and is refused; the first two stay.
"""

import pytest

import unicode_fol_kit.dl as dl

INT, STRING = dl.Datatype("xsd:integer"), dl.Datatype("xsd:string")
P, Q = dl.Datatype("P"), dl.Datatype("Q")

CYCLE = """Ontology(
  DatatypeDefinition(P DataComplementOf(Q))
  DatatypeDefinition(Q DataComplementOf(P))
)"""

TWO_DEFINITIONS = """Ontology(
  DatatypeDefinition(D xsd:integer)
  DatatypeDefinition(D xsd:string)
)"""

REPEAT = """Ontology(
  DatatypeDefinition(D xsd:integer)
  DatatypeDefinition(D xsd:integer)
)"""

THREE_STEPS = """Ontology(
  DatatypeDefinition(A DataUnionOf(B xsd:integer))
  DatatypeDefinition(B DataUnionOf(C xsd:string))
  DatatypeDefinition(C DataComplementOf(A))
)"""


def test_a_definition_that_closes_a_cycle_with_an_earlier_one_is_refused_when_it_is_read():
    doc = dl.parse_owl_functional_axioms(CYCLE)
    assert doc.ok is False
    assert doc.refused_keywords == {"DatatypeDefinition": 1}
    assert doc.accepted == 1
    refused = doc.refused[0]
    # the offset is the datatype NAME of the second definition, as for any other
    # datatype construct the reader refuses
    assert refused.position == CYCLE.index("Q DataComplementOf(P)")
    assert refused.text == "DatatypeDefinition(Q DataComplementOf(P))"
    assert "cyclic" in refused.reason and "P" in refused.reason and "Q" in refused.reason
    # only the first definition is stored
    assert doc.tbox.datatype_definitions == [("P", dl.DataComplementOf(Q))]


def test_what_the_reader_kept_is_a_knowledge_base_that_renders():
    # Hand-derived: P ≡ ¬Q alone is acyclic, so every route takes it.
    kb = dl.parse_owl_functional_axioms(CYCLE).to_kb()
    assert kb.data_layer is True


def test_a_second_and_different_definition_of_a_name_is_refused_when_it_is_read():
    doc = dl.parse_owl_functional_axioms(TWO_DEFINITIONS)
    assert doc.refused_keywords == {"DatatypeDefinition": 1}
    assert "two DatatypeDefinitions" in doc.refused[0].reason
    assert doc.tbox.datatype_definitions == [("D", INT)]
    doc.to_kb()


def test_an_identical_repeat_is_one_axiom_said_twice_and_is_accepted():
    doc = dl.parse_owl_functional_axioms(REPEAT)
    assert doc.ok is True and doc.accepted == 2
    assert doc.tbox.datatype_definitions == [("D", INT), ("D", INT)]
    doc.to_kb()


def test_a_cycle_through_three_definitions_is_refused_at_the_one_that_closes_it():
    doc = dl.parse_owl_functional_axioms(THREE_STEPS)
    assert doc.refused_keywords == {"DatatypeDefinition": 1}
    assert doc.accepted == 2
    assert doc.refused[0].text == "DatatypeDefinition(C DataComplementOf(A))"
    assert [name for name, _ in doc.tbox.datatype_definitions] == ["A", "B"]
    doc.to_kb()


@pytest.mark.parametrize("text", [CYCLE, TWO_DEFINITIONS, THREE_STEPS],
                         ids=["cycle", "two-definitions", "three-steps"])
def test_the_two_readers_refuse_at_the_same_axiom_with_the_same_reason(text):
    with pytest.raises(dl.OwlFunctionalUnsupportedError) as strict:
        dl.parse_owl_functional(text)
    lenient = dl.parse_owl_functional_axioms(text).refused[0]
    assert lenient.reason == str(strict.value)
    assert strict.value.keyword == lenient.keyword == "DatatypeDefinition"
    assert strict.value.position == lenient.position


def test_a_refused_definition_costs_exactly_its_own_axiom():
    # The axioms around it are read as if it were not there, and a refused
    # definition takes no part in the cycle test of the ones after it: Q is not
    # defined, so ``R ≡ ¬Q`` cannot close anything.
    text = """Ontology(
  DatatypeDefinition(P DataComplementOf(Q))
  SubClassOf(A B)
  DatatypeDefinition(Q DataComplementOf(P))
  SubClassOf(B C)
  DatatypeDefinition(R DataComplementOf(Q))
)"""
    doc = dl.parse_owl_functional_axioms(text)
    assert doc.refused_keywords == {"DatatypeDefinition": 1}
    assert doc.accepted == 4
    assert [(sub, sup) for sub, sup in doc.tbox.inclusions] == [
        (dl.Atomic("A"), dl.Atomic("B")), (dl.Atomic("B"), dl.Atomic("C"))]
    assert [name for name, _ in doc.tbox.datatype_definitions] == ["P", "R"]


def test_a_definition_is_checked_against_definitions_of_the_same_document_only():
    # Two documents, one reader call each: the definitions of the first are not
    # remembered by the second.
    first = dl.parse_owl_functional_axioms("Ontology(DatatypeDefinition(D xsd:integer))")
    second = dl.parse_owl_functional_axioms("Ontology(DatatypeDefinition(D xsd:string))")
    assert first.ok and second.ok
    assert first.tbox.datatype_definitions == [("D", INT)]
    assert second.tbox.datatype_definitions == [("D", STRING)]


def test_to_kb_still_refuses_a_cyclic_set_it_is_handed():
    # The refusal at render time stays: a result assembled by hand, or from two
    # documents, can still carry a cycle the reader never saw.
    handed = dl.OwlFunctionalResult(
        tbox=dl.TBox(datatype_definitions=[("P", dl.DataComplementOf(Q)),
                                           ("Q", dl.DataComplementOf(P))]),
        abox=dl.ABox())
    with pytest.raises(dl.UnsupportedDatatypeError, match="cyclic"):
        handed.to_kb()
