r"""A10: ``parse_owl_functional_axioms`` — a whole ontology, refusals as data.

``dl.parse_owl_functional`` raises on the FIRST construct outside the fragment
and returns nothing, so a real ontology carrying one ``DataPropertyRange``
yields no TBox at all. The requesting project worked around that by wrapping
EVERY one of the Open Energy Ontology's 4041 axioms in its own
``Ontology(...)`` string, calling the parser 4041 times, catching
``BaseException`` and keeping the message as a string to regex later — and then
conjoining ``tbox_to_fol + rbox_to_fol + abox_to_fol`` into one formula, which
is exactly the TBox/RBox trap ``kb_to_fol`` and ``RoleBoxOmittedError`` exist
to prevent.

``parse_owl_functional_axioms`` is the entry point that makes all of that
unnecessary, and it is better than the wrapper in four specific ways, one
section each below:

* ONE tokenization and ONE pass over the document, recovering at AXIOM
  boundaries — the caller should not have to split a document to find out what
  is in it;
* STRUCTURED refusals: a frozen ``RefusedAxiom`` with the keyword, the offset,
  the axiom's own source text and the full message, so a census needs no regex;
* it returns the TBox/ABox and offers ``to_kb()``, so the obvious next call is
  ``kb_to_fol`` and the role box ends up as PREMISES;
* it recovers from an out-of-fragment CONSTRUCT and from nothing else:
  malformed input still raises, because skipping an unbalanced paren could
  drop arbitrary content.

Z3-backed calls take their ``timeout`` in MILLISECONDS; it is never shrunk.
"""

import dataclasses
import json

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.owl_functional import (
    OwlFunctionalResult, OwlFunctionalSyntaxError, OwlFunctionalUnsupportedError,
    RefusedAxiom,
)
from unicode_logic_kit.fol.nodes import Not as FNot

TIMEOUT_MS = 30000

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")


# --------------------------------------------------------------------------- #
# One pass, and a refused axiom leaves NOTHING behind.
# --------------------------------------------------------------------------- #

def test_one_supported_and_one_unsupported_axiom():
    text = "Ontology(SubClassOf(A B) HasKey(A () (r)))"
    doc = dl.parse_owl_functional_axioms(text)
    assert isinstance(doc, OwlFunctionalResult)
    assert doc.accepted == 1
    assert doc.skipped == 0
    assert len(doc.refused) == 1
    assert doc.ok is False
    refused = doc.refused[0]
    assert isinstance(refused, RefusedAxiom)
    assert refused.keyword == "HasKey"
    assert refused.position == text.index("HasKey")
    assert refused.text == "HasKey(A () (r))"
    assert "HasKey" in refused.reason
    # the TBox holds EXACTLY the supported axiom -- no partial mutation
    assert doc.tbox == dl.TBox().add(A, B)
    assert doc.abox == dl.ABox()


def test_a_document_inside_the_fragment_is_ok():
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) ClassAssertion(A alice))")
    assert doc.ok is True
    assert doc.refused == ()
    assert doc.refused_keywords == {}
    assert doc.accepted == 2
    assert (doc.tbox, doc.abox) == (dl.TBox().add(A, B),
                                    dl.ABox().assert_concept("alice", A))


def test_the_three_no_ops_are_counted_separately():
    # Declaration/Annotation/AnnotationAssertion carry no logical content, so
    # they are neither "accepted" (nothing was read into the TBox) nor
    # "refused" (nothing was lost): accepted + skipped + len(refused) is the
    # document's axiom count.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(Declaration(Class(A)) Declaration(ObjectProperty(r)) "
        'AnnotationAssertion(rdfs:label A "a") '
        "SubClassOf(A B) HasKey(A () (r)))")
    assert (doc.accepted, doc.skipped, len(doc.refused)) == (1, 3, 1)
    assert doc.refused_keywords == {"HasKey": 1}
    assert doc.tbox == dl.TBox().add(A, B)


def test_refused_keywords_counts_per_keyword():
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) "
        "HasKey(A () (r)) "
        "HasKey(B () (s)) "
        "DisjointUnion(C A B))")
    assert doc.refused_keywords == {"HasKey": 2, "DisjointUnion": 1}
    assert [axiom.keyword for axiom in doc.refused] == [
        "HasKey", "HasKey", "DisjointUnion"]   # document order


def test_a_refusal_nested_inside_an_axiom_recovers_at_the_axiom_boundary():
    # The keyword reported is the INNER construct -- that is what a caller
    # would have to add support for -- while the TEXT skipped is the whole
    # AXIOM, which is the unit that was lost. `A` must NOT be left in the TBox:
    # the axiom is parsed into a scratch TBox and merged only on success, which
    # makes "no partial mutation" structural rather than a reading of the
    # parser's code.
    text = "Ontology(SubClassOf(A ObjectHasSelf(r)) SubClassOf(B C))"
    doc = dl.parse_owl_functional_axioms(text)
    assert doc.accepted == 1
    assert len(doc.refused) == 1
    assert doc.refused[0].keyword == "ObjectHasSelf"
    assert doc.refused[0].position == text.index("ObjectHasSelf")
    assert doc.refused[0].text == "SubClassOf(A ObjectHasSelf(r))"
    assert doc.tbox == dl.TBox().add(B, C)


def test_an_unknown_future_keyword_is_collected_not_raised():
    # A keyword this kit has never heard of is still "valid OWL 2 outside this
    # fragment" as far as a reader can tell, so it is reported rather than
    # raised -- which is what makes the reader usable against a newer OWL
    # profile than it was written for.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) DLSafeRule(Body(X) Head(Y)))")
    assert doc.accepted == 1
    assert doc.refused_keywords == {"DLSafeRule": 1}
    assert doc.refused[0].text == "DLSafeRule(Body(X) Head(Y))"


def test_a_built_in_property_name_is_recovered_from_too():
    # The OWL 2 built-in properties are valid OWL 2 that ALCHQ has no reading
    # for (it has neither the universal nor the empty role), which is the same
    # class of refusal -- so one such axiom must not abort a whole-document
    # read. The TAUTOLOGICAL inclusion INTO owl:topObjectProperty stays a
    # documented no-op that keeps nothing -- and is REPORTED, as consumed, so
    # it does not vanish from a census of the document.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubObjectPropertyOf(P owl:topObjectProperty) "
        "ObjectPropertyAssertion(owl:topObjectProperty a b) "
        "SubClassOf(A B))")
    assert doc.accepted == 1                   # the SubClassOf alone
    assert [c.keyword for c in doc.consumed] == ["SubObjectPropertyOf"]
    assert doc.consumed[0].text == "SubObjectPropertyOf(P owl:topObjectProperty)"
    assert doc.refused_keywords == {"owl:topObjectProperty": 1}
    assert doc.tbox == dl.TBox().add(A, B)
    assert doc.abox == dl.ABox()


def test_every_axiom_after_a_refusal_is_still_read():
    # The property the whole entry point exists for: a refusal in the middle
    # costs exactly its own axiom.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) HasKey(A () (r)) SubClassOf(B C) "
        "DisjointUnion(D A B) ClassAssertion(C alice))")
    assert doc.accepted == 3
    assert len(doc.refused) == 2
    assert doc.tbox == dl.TBox().add(A, B).add(B, C)
    assert doc.abox == dl.ABox().assert_concept("alice", C)


# --------------------------------------------------------------------------- #
# What it recovers from, and what it does NOT.
# --------------------------------------------------------------------------- #

def test_the_unsupported_error_is_a_subclass_of_the_syntax_error():
    # A subclass on purpose: every existing `except OwlFunctionalSyntaxError`
    # and every pytest.raises in the suite keeps working unchanged.
    assert issubclass(OwlFunctionalUnsupportedError, OwlFunctionalSyntaxError)
    assert issubclass(OwlFunctionalUnsupportedError, ValueError)
    with pytest.raises(OwlFunctionalSyntaxError):
        dl.parse_owl_functional("Ontology(HasKey(A () (r)))")
    with pytest.raises(OwlFunctionalUnsupportedError) as info:
        dl.parse_owl_functional("Ontology(HasKey(A () (r)))")
    assert info.value.keyword == "HasKey"
    assert info.value.position == len("Ontology(")


@pytest.mark.parametrize("text, what", [
    ("SubClassOf(A B)", "no Ontology( wrapper"),
    ("Ontology(SubClassOf(A B)", "an unbalanced paren"),
    ("Ontology(SubClassOf(A <unterminated))", "an unterminated IRI"),
    ('Ontology(AnnotationAssertion(l A "unterminated))', "an unterminated string"),
    ("Ontology(SubClassOf(A B)) trailing", "trailing input"),
    ("Ontology(SubClassOf(A ))", "a missing argument"),
], ids=["no-wrapper", "unbalanced", "unterminated-iri", "unterminated-string",
        "trailing", "missing-argument"])
def test_malformed_input_still_raises(text, what):
    # These are questions about the DOCUMENT, not about the fragment, and
    # recovering from one of them could silently drop arbitrary content.
    with pytest.raises(OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional_axioms(text)
    assert not isinstance(info.value, OwlFunctionalUnsupportedError), (
        f"{what} must raise the plain error, so the lenient reader does NOT "
        f"recover from it")


def test_an_anonymous_individual_is_recovered_from_not_raised():
    # `_:nodeID` is VALID OWL 2 that this kit has no representation for (an
    # ABox individual is a name), so it belongs on the fragment side of the
    # line: the axiom is reported, by name, with its own source text, and
    # every other axiom in the document is still read.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(ClassAssertion(A _:x1) SubClassOf(A B))")
    assert doc.accepted == 1
    assert doc.tbox == dl.TBox().add(A, B)
    assert doc.abox == dl.ABox()         # no partial ClassAssertion left
    assert len(doc.refused) == 1
    assert doc.refused[0].keyword == "_:x1"
    assert doc.refused[0].text == "ClassAssertion(A _:x1)"
    assert "anonymous" in doc.refused[0].reason
    # the strict reader still raises, as it always did
    with pytest.raises(OwlFunctionalSyntaxError, match="anonymous"):
        dl.parse_owl_functional("Ontology(ClassAssertion(A _:x1))")


def test_an_unbalanced_paren_inside_a_refused_axiom_still_raises():
    # Recovery skips the keyword plus its BALANCED parens, so a group that
    # never closes is still malformed input and still raises -- it is not
    # quietly swallowed as "the rest of the refused axiom".
    with pytest.raises(OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional_axioms("Ontology(HasKey(A () (r) SubClassOf(A B))")
    assert not isinstance(info.value, OwlFunctionalUnsupportedError)


# --------------------------------------------------------------------------- #
# What to do with the result: to_kb(), and the trap it closes.
# --------------------------------------------------------------------------- #

def test_to_kb_is_kb_to_fol_of_the_two_boxes():
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) ClassAssertion(A alice) "
        "TransitiveObjectProperty(R))")
    assert doc.to_kb() == dl.kb_to_fol(doc.tbox, doc.abox)


def test_to_kb_succeeds_where_tbox_to_fol_refuses():
    # THE regression guard for the mistake the requesting project's own
    # translator made. A document carrying domain/range axioms has a role box,
    # so tbox_to_fol refuses to hand back the concept-inclusion image alone --
    # and to_kb() is the call that does the right thing with it, carrying the
    # role box as separate premises.
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) ObjectPropertyDomain(R A) "
        "ObjectPropertyRange(R B))")
    assert doc.ok is True
    with pytest.raises(dl.RoleBoxOmittedError) as info:
        dl.tbox_to_fol(doc.tbox)
    assert "ObjectPropertyDomain" in str(info.value)
    kb = doc.to_kb()
    assert [axiom.kind for axiom in kb.side_axioms] == [
        "ObjectPropertyDomain", "ObjectPropertyRange"]
    assert len(kb.axioms) == 2


def test_to_dict_is_json_serializable():
    doc = dl.parse_owl_functional_axioms(
        "Ontology(SubClassOf(A B) HasKey(A () (r)))")
    payload = doc.to_dict()
    assert json.loads(json.dumps(payload)) == payload
    assert payload["ok"] is False
    assert payload["accepted"] == 1
    assert payload["refused_keywords"] == {"HasKey": 1}
    assert payload["refused"][0]["keyword"] == "HasKey"
    assert payload["refused"][0]["text"] == "HasKey(A () (r))"


def test_the_strict_reader_is_unchanged_and_documented_as_such():
    # parse_owl_functional stays backwards compatible: same signature, same
    # all-or-nothing behaviour, same exception type caught.
    assert dl.parse_owl_functional("Ontology(SubClassOf(A B))") == \
        (dl.TBox().add(A, B), dl.ABox())
    with pytest.raises(OwlFunctionalSyntaxError):
        dl.parse_owl_functional("Ontology(SubClassOf(A B) HasKey(A () (r)))")


# --------------------------------------------------------------------------- #
# An OEO-shaped document, through BOTH routes.
#
# Hand-written in the style of the Open Energy Ontology (which is NOT
# committed -- the kit holds tools, not corpora) and deliberately mixed: every
# axiom kind this package added, the role box, an ABox, and two axioms from
# the constructs this kit chooses not to carry, which must come back as refusals.
# --------------------------------------------------------------------------- #

_OEO_SHAPED = """Prefix(:=<http://openenergy-platform.org/ontology/oeo/>)
Ontology(<http://openenergy-platform.org/ontology/oeo/oeo-full.owl>
  Declaration(Class(EnergyCarrier))
  Declaration(ObjectProperty(HasStateOfMatter))
  Declaration(NamedIndividual(Gaseous))
  SubClassOf(EnergyCarrier MaterialEntity)
  SubClassOf(Fuel EnergyCarrier)
  SubClassOf(CarbonDioxide ObjectHasValue(HasNormalStateOfMatter Gaseous))
  SubClassOf(LiquidFuel ObjectIntersectionOf(Fuel
      ObjectHasValue(HasStateOfMatter Liquid)))
  SubClassOf(GasFiredPowerUnit ObjectSomeValuesFrom(Uses
      ObjectIntersectionOf(Fuel ObjectHasValue(HasNormalStateOfMatter Gaseous))))
  EquivalentClasses(LiquidAir ObjectIntersectionOf(Air
      ObjectHasValue(HasStateOfMatter Liquid)))
  DisjointClasses(Fuel Occurrent)
  SubClassOf(PowerPlant ObjectMinCardinality(1 HasPart PowerUnit))
  SubClassOf(SinglePartPlant ObjectMaxCardinality(1 HasPart PowerUnit))
  SubClassOf(Occurrent ObjectComplementOf(MaterialEntity))
  SubClassOf(EnergyCarrier ObjectAllValuesFrom(HasStateOfMatter StateOfMatter))
  SubObjectPropertyOf(PartOf OverlapsWith)
  TransitiveObjectProperty(PartOf)
  EquivalentObjectProperties(HasPart HasProperPart)
  DisjointObjectProperties(HasSink HasSource)
  IrreflexiveObjectProperty(HasPhysicalInput)
  AsymmetricObjectProperty(HasPhysicalInput)
  FunctionalObjectProperty(HasStateOfMatter)
  ObjectPropertyDomain(IsAbout InformationContentEntity)
  ObjectPropertyDomain(HasClient ObjectUnionOf(InformationContentEntity Model))
  ObjectPropertyRange(HasUnit Unit)
  ObjectPropertyRange(HasStateOfMatter StateOfMatter)
  ObjectPropertyRange(HasAuthor ObjectSomeValuesFrom(HasRole Author))
  ClassAssertion(EnergyCarrier Methane)
  ClassAssertion(StateOfMatter Gaseous)
  ClassAssertion(StateOfMatter Liquid)
  ObjectPropertyAssertion(HasStateOfMatter Methane Gaseous)
  ObjectPropertyAssertion(IsDefinedBy MMRSectorM GovRegSectorDivision)
  DifferentIndividuals(Gaseous Liquid)
  SameIndividual(CRFSectorIPCC2006Transport NCBRSectorTransport)
  SameIndividual(CRFSectorIPCC2006LULUCF KSGSectorLULUCF EUEmissionSectorLULUCF)
  NegativeObjectPropertyAssertion(IsDefinedBy Methane GovRegSectorDivision)
  HasKey(ScenarioFactsheet () (HasNumber))
  DisjointUnion(StateOfMatter Gaseous Liquid Solid)
)"""

#: Hand-counted from the document above, by kind: 9 SubClassOf, 1
#: EquivalentClasses, 1 DisjointClasses, 1 SubObjectPropertyOf, 1
#: TransitiveObjectProperty, 1 EquivalentObjectProperties, 1
#: DisjointObjectProperties, 1 IrreflexiveObjectProperty, 1
#: AsymmetricObjectProperty, 1 FunctionalObjectProperty, 2
#: ObjectPropertyDomain, 3 ObjectPropertyRange, 3 ClassAssertion, 2
#: ObjectPropertyAssertion, 1 DifferentIndividuals, 2 SameIndividual and 1
#: NegativeObjectPropertyAssertion = 32 inside the fragment (``accepted``);
#: 3 declarations (``skipped``); HasKey and DisjointUnion (``refused``); 37
#: axioms in all. Written out here rather than read off the result, so the
#: numbers are an expectation and not a restatement.
_EXPECTED_ACCEPTED = 32
_EXPECTED_SKIPPED = 3
_EXPECTED_REFUSED_KEYWORDS = {"HasKey": 1, "DisjointUnion": 1}


def test_the_oeo_shaped_document_reads_in_one_pass():
    doc = dl.parse_owl_functional_axioms(_OEO_SHAPED)
    assert doc.skipped == _EXPECTED_SKIPPED
    assert doc.accepted == _EXPECTED_ACCEPTED
    assert doc.refused_keywords == _EXPECTED_REFUSED_KEYWORDS
    assert doc.ok is False
    # Every refusal names a construct and points somewhere, and its recorded
    # text really is the slice of the document at its position.
    for axiom in doc.refused:
        assert axiom.keyword in axiom.reason
        assert _OEO_SHAPED[axiom.position:].startswith(axiom.keyword)
        assert _OEO_SHAPED[_OEO_SHAPED.index(axiom.text):].startswith(axiom.text)
    # and the constructs THIS package added really are in the boxes
    assert len(doc.tbox.role_domains) == 2
    assert len(doc.tbox.role_ranges) == 3
    assert doc.abox.same_assertions == [
        ("CRFSectorIPCC2006Transport", "NCBRSectorTransport"),
        ("CRFSectorIPCC2006LULUCF", "KSGSectorLULUCF"),
        ("KSGSectorLULUCF", "EUEmissionSectorLULUCF"),
    ]
    assert doc.abox.negative_role_assertions == [
        ("Methane", "GovRegSectorDivision", "IsDefinedBy")]
    assert any(isinstance(sup, dl.HasValue) for _sub, sup in doc.tbox.inclusions)


def _mentions_value_restriction(concept) -> bool:
    """Does a ``HasValue`` occur anywhere inside ``concept`` (any depth)?"""
    if isinstance(concept, dl.HasValue):
        return True
    if dataclasses.is_dataclass(concept):
        return any(_mentions_value_restriction(getattr(concept, f.name))
                   for f in dataclasses.fields(concept))
    return False


def _without_value_restrictions(tbox):
    """``tbox`` with every inclusion that mentions an ObjectHasValue dropped.

    Five of the document's twelve inclusions do, counted by hand from the text
    above: CarbonDioxide, LiquidFuel, GasFiredPowerUnit (inside the filler of
    an ObjectSomeValuesFrom) and the two halves of LiquidAir's equivalence.
    """
    kept = [(sub, sup) for sub, sup in tbox.inclusions
            if not (_mentions_value_restriction(sub)
                    or _mentions_value_restriction(sup))]
    assert len(tbox.inclusions) - len(kept) == 5
    return dataclasses.replace(tbox, inclusions=kept)


def test_the_two_routes_agree_on_the_oeo_shaped_document():
    # The document is satisfiable -- nothing in it forces a contradiction --
    # but it carries ObjectHasValue inclusions, and the in-house tableau
    # REFUSES a value restriction by name (a value restriction is a nominal in
    # disguise, and a tableau rule for one is unsound under subset blocking;
    # see tableau.py, 'Value restrictions (ObjectHasValue)'). So the routes
    # answer different parts of the question, and each is checked where it can
    # speak:
    doc = dl.parse_owl_functional_axioms(_OEO_SHAPED)
    # (1) the tableau refuses the whole document, and says which construct;
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.abox_consistent(doc.abox, doc.tbox)
    # (2) the FOL route decides the WHOLE document: the negation of the
    #     knowledge base is REFUTED (a model exists), no timeout is shrunk;
    kb = doc.to_kb()
    status = api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status
    assert status == "refuted", (
        f"the FOL route said {status!r}; 'unknown' would mean this test "
        f"measured nothing, and 'proved' that the document is inconsistent")
    # (3) on the document WITHOUT its value-restriction inclusions both routes
    #     answer, and they must agree. Dropping axioms cannot turn a
    #     consistent knowledge base inconsistent: every model of the whole
    #     document is a model of any sub-document (OWL entailment is
    #     monotone), so the sub-document is consistent too.
    sub = _without_value_restrictions(doc.tbox)
    assert dl.abox_consistent(doc.abox, sub) is True
    sub_kb = dl.kb_to_fol(sub, doc.abox)
    status = api.prove(FNot(sub_kb.formula), list(sub_kb.axioms),
                       timeout=TIMEOUT_MS).status
    assert status == "refuted", (
        f"the FOL route said {status!r} for the sub-document; 'unknown' would "
        f"mean this test measured nothing, 'proved' that the routes disagree")


def test_the_two_routes_agree_when_the_document_IS_inconsistent():
    # The agreement above would be worth little without its twin: add one
    # axiom that contradicts the document's own ABox. Gaseous and Liquid are
    # asserted DIFFERENT, HasStateOfMatter is FUNCTIONAL, and Methane already
    # has Gaseous -- so a second, distinct state has no model.
    text = _OEO_SHAPED.rstrip()[:-1] + (
        "  ObjectPropertyAssertion(HasStateOfMatter Methane Liquid)\n)")
    doc = dl.parse_owl_functional_axioms(text)
    # (1) the tableau still refuses the whole document by name: the value
    #     restrictions are in the TBox whether or not the contradiction needs
    #     them;
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.abox_consistent(doc.abox, doc.tbox)
    # (2) the FOL route proves the whole document inconsistent;
    kb = doc.to_kb()
    status = api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status
    assert status == "proved", (
        f"the FOL route said {status!r} for a document with no model")
    # (3) without the value-restriction inclusions the contradiction is
    #     still there, because it does not involve them: it follows from four
    #     axioms alone -- FunctionalObjectProperty(HasStateOfMatter),
    #     DifferentIndividuals(Gaseous Liquid) and the two
    #     ObjectPropertyAssertions of HasStateOfMatter from Methane (functional
    #     forces Gaseous = Liquid, which the difference denies) -- and none of
    #     the four is an inclusion. A subset of the axioms can only gain
    #     models, and any model of the sub-document would satisfy those four.
    #     So the sub-document is inconsistent too, and both routes say so.
    sub = _without_value_restrictions(doc.tbox)
    assert dl.abox_consistent(doc.abox, sub) is False
    sub_kb = dl.kb_to_fol(sub, doc.abox)
    status = api.prove(FNot(sub_kb.formula), list(sub_kb.axioms),
                       timeout=TIMEOUT_MS).status
    assert status == "proved", (
        f"the FOL route said {status!r} for the inconsistent sub-document; "
        f"the tableau found it inconsistent")


def test_the_oeo_shaped_document_round_trips_through_the_writer():
    # to_owl_functional is the writer dual, and a kind the reader reads while
    # the writer drops it is a round-trip bug -- on a document of this size
    # that is the only practical way to notice one.
    doc = dl.parse_owl_functional_axioms(_OEO_SHAPED)
    written = dl.to_owl_functional(doc.tbox, doc.abox)
    assert dl.parse_owl_functional(written) == (doc.tbox, doc.abox)


# --------------------------------------------------------------------------- #
# Consumed without content: read, built into nothing, and REPORTED.
# --------------------------------------------------------------------------- #

def test_the_tautologies_are_reported_not_vanished():
    # 31 of the OEO's axioms are `P ⊑ owl:topObjectProperty`. Dropping them is
    # sound (each holds in every interpretation) but a census of the document
    # must still find them: they are consumed as DATA, one ConsumedAxiom each,
    # and the four counters partition the document's axioms.
    n = 31
    text = ("Ontology(" + " ".join(
        f"SubObjectPropertyOf(P{i} owl:topObjectProperty)" for i in range(n))
        + " SubClassOf(A B))")
    doc = dl.parse_owl_functional_axioms(text)
    assert doc.ok is True
    assert len(doc.consumed) == n
    assert all(isinstance(c, dl.ConsumedAxiom) for c in doc.consumed)
    assert [c.text for c in doc.consumed] == [
        f"SubObjectPropertyOf(P{i} owl:topObjectProperty)" for i in range(n)]
    assert all(text[c.position:].startswith(c.text) for c in doc.consumed)
    assert all("tautology" in c.reason for c in doc.consumed)
    assert (doc.accepted, doc.skipped, len(doc.refused)) == (1, 0, 0)
    assert doc.accepted + doc.skipped + len(doc.consumed) + len(doc.refused) == n + 1
    assert (doc.tbox, doc.abox) == (dl.TBox().add(A, B), dl.ABox())


@pytest.mark.parametrize("axiom", [
    "SubObjectPropertyOf(P owl:topObjectProperty)",
    "SubObjectPropertyOf(owl:bottomObjectProperty P)",
    "SubDataPropertyOf(d owl:topDataProperty)",
    "SubDataPropertyOf(owl:bottomDataProperty d)",
    "SubAnnotationPropertyOf(l label)",
    "AnnotationPropertyDomain(l A)",
    "AnnotationPropertyRange(l A)",
], ids=["top-object", "bottom-object", "top-data", "bottom-data",
        "sub-annotation", "annotation-domain", "annotation-range"])
def test_each_consumed_kind_is_read_builds_nothing_and_is_reported(axiom):
    doc = dl.parse_owl_functional_axioms(f"Ontology({axiom})")
    assert (doc.tbox, doc.abox) == (dl.TBox(), dl.ABox())
    assert [c.text for c in doc.consumed] == [axiom]
    assert doc.consumed[0].keyword == axiom.split("(")[0]
    assert (doc.accepted, doc.skipped, len(doc.refused)) == (0, 0, 0)
    # the strict reader reads it the same way
    assert dl.parse_owl_functional(f"Ontology({axiom})") == (dl.TBox(), dl.ABox())


@pytest.mark.parametrize("axiom, keyword", [
    # a tautology of ONE family is not one of the other: `d ⊑ owl:topObjectProperty`
    # with a DATA property on the left is ill-typed OWL 2, not a no-op
    ("SubDataPropertyOf(d owl:topObjectProperty)", "owl:topObjectProperty"),
    ("SubObjectPropertyOf(P owl:topDataProperty)", "owl:topDataProperty"),
    # the OTHER direction is a real constraint, not a tautology
    ("SubObjectPropertyOf(owl:topObjectProperty P)", "owl:topObjectProperty"),
    ("SubObjectPropertyOf(P owl:bottomObjectProperty)", "owl:bottomObjectProperty"),
], ids=["data-below-object-top", "object-below-data-top", "top-below-P", "P-below-bottom"])
def test_what_is_not_a_tautology_is_refused_not_consumed(axiom, keyword):
    doc = dl.parse_owl_functional_axioms(f"Ontology({axiom})")
    assert doc.consumed == ()
    assert doc.refused_keywords == {keyword: 1}


# --------------------------------------------------------------------------- #
# The data layer, through a whole document and both routes.
# --------------------------------------------------------------------------- #

_DATA_DOCUMENT = """Ontology(
  Declaration(DataProperty(HasNumber))
  SubClassOf(ScenarioFactsheet DataSomeValuesFrom(HasNumber xsd:decimal))
  DataPropertyDomain(HasNumber ScenarioFactsheet)
  DataPropertyRange(HasNumber xsd:decimal)
  DataPropertyAssertion(HasNumber ScenarioA "42"^^xsd:integer)
  DatatypeDefinition(PositiveDecimal DatatypeRestriction(xsd:decimal xsd:minExclusive "0"^^xsd:decimal))
  ClassAssertion(ScenarioFactsheet ScenarioA)
  SubObjectPropertyOf(PartOf owl:topObjectProperty)
  SubAnnotationPropertyOf(BFOLabel Label)
)"""


def test_a_data_document_reads_in_one_pass():
    # Hand-counted: 6 read (SubClassOf, the domain, the range, the assertion,
    # the definition, ClassAssertion), 1 Declaration skipped, 2 consumed (the
    # tautology and the annotation-property axiom), none refused.
    doc = dl.parse_owl_functional_axioms(_DATA_DOCUMENT)
    assert (doc.accepted, doc.skipped, len(doc.consumed), len(doc.refused)) == (6, 1, 2, 0)
    assert doc.ok is True
    assert [c.keyword for c in doc.consumed] == [
        "SubObjectPropertyOf", "SubAnnotationPropertyOf"]
    assert doc.tbox.data_property_domains == [("HasNumber", dl.Atomic("ScenarioFactsheet"))]
    assert doc.tbox.data_property_ranges == [("HasNumber", dl.Datatype("xsd:decimal"))]
    assert doc.abox.data_assertions == [
        ("ScenarioA", "HasNumber", dl.Literal("42", "xsd:integer"))]
    assert [name for name, _ in doc.tbox.datatype_definitions] == ["PositiveDecimal"]


def test_the_tableau_refuses_the_data_document_by_name():
    doc = dl.parse_owl_functional_axioms(_DATA_DOCUMENT)
    with pytest.raises(dl.UnsupportedAxiomError) as info:
        dl.abox_consistent(doc.abox, doc.tbox)
    message = str(info.value)
    for kind in ("DataPropertyDomain", "DataPropertyRange", "DatatypeDefinition",
                 "DataPropertyAssertion"):
        assert kind in message, kind


def test_the_fol_route_answers_the_data_document():
    doc = dl.parse_owl_functional_axioms(_DATA_DOCUMENT)
    kb = doc.to_kb()
    # the document is satisfiable: its negation has a countermodel
    assert api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status == "refuted"
    # Hand-derived: DataPropertyAssertion gives HasNumber(ScenarioA, 42) and the
    # DataPropertyRange gives ∀x ∀v (HasNumber(x, v) → xsd:decimal(v)), so the
    # literal's term is a decimal -- without any use of the datatype lattice.
    term = dl.Literal("42", "xsd:integer").to_term()
    decimal = dl.datarange_to_fol(dl.Datatype("xsd:decimal"), term)
    assert api.prove(decimal, list(kb.premises), timeout=TIMEOUT_MS).status == "proved"
    # and the twin: nothing makes it an xsd:string -- indeed the number and
    # string families are disjoint, so the verdict is a refutation, not a timeout
    text = dl.datarange_to_fol(dl.Datatype("xsd:string"), term)
    assert api.prove(text, list(kb.premises), timeout=TIMEOUT_MS).status == "refuted"


def test_the_data_document_round_trips_through_the_writer():
    doc = dl.parse_owl_functional_axioms(_DATA_DOCUMENT)
    written = dl.to_owl_functional(doc.tbox, doc.abox)
    assert dl.parse_owl_functional(written) == (doc.tbox, doc.abox)


def test_to_dict_reports_the_consumed_axioms():
    doc = dl.parse_owl_functional_axioms(_DATA_DOCUMENT)
    payload = doc.to_dict()
    assert json.loads(json.dumps(payload)) == payload
    assert [c["keyword"] for c in payload["consumed"]] == [
        "SubObjectPropertyOf", "SubAnnotationPropertyOf"]
    assert payload["consumed"][1]["text"] == "SubAnnotationPropertyOf(BFOLabel Label)"
    assert "annotation-property axiom" in payload["consumed"][1]["reason"]
