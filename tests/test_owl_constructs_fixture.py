r"""Every OWL 2 construct the CCG2MSFL extension request names, one axiom each.

``tests/fixtures/owl/oeo_constructs.ofn`` is the COMMITTED stand-in for the
Open Energy Ontology: the kit holds tools, not corpora, so the 4041-axiom
corpus is reached only through an opt-in environment variable
(``tests/test_owl_corpus.py``) and never committed. This file is what the
default suite can measure, and it is a ratchet. For every line the expectation
below is either

* the exact ``(TBox, ABox)`` the parser builds — hand-written here, never read
  off what the code produced — or
* the exact phrase the reason of a CONSUMED axiom must carry (an axiom the
  parser reads and finds to carry no logical content: it builds nothing, and the
  lenient reader REPORTS it), or
* the exact construct phrase the refusal must name.

Each package flips its own lines from "refused, naming the construct" to
"accepted, with this image", and the diff of this file is then the honest
record of what that package added. After the data layer (A7) the only lines
still refused are the four constructs this kit has chosen not to carry: nominals,
Self restrictions, DisjointUnion and HasKey.

The expectations are keyed by the axiom's full text, so a fixture line nobody
wrote an expectation for fails loudly rather than going unchecked.
"""

import io
from pathlib import Path

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl.owl_functional import _merge_axiom_holder

_FIXTURE = Path(__file__).parent / "fixtures" / "owl" / "oeo_constructs.ofn"

ICE = dl.Atomic("InformationContentEntity")
GDC = dl.Atomic("GenericallyDependentContinuant")
INDEPENDENT = dl.Atomic("IndependentContinuant")
DEPENDENT = dl.Atomic("SpecificallyDependentContinuant")


def _accepted(build):
    return ("accepted", build)


def _refused(phrase):
    return ("refused", phrase)


def _consumed(phrase):
    return ("consumed", phrase)


def _mk(*literals):
    """``dl.Literal`` shorthand: ``_mk("400", "xsd:integer")``."""
    return dl.Literal(*literals)


def _restriction(base, lower, upper):
    """``DatatypeRestriction(base xsd:minInclusive lower xsd:maxInclusive
    upper)`` over a numeric base, bounds typed with the base."""
    return dl.DatatypeRestriction(dl.Datatype(base), (
        ("xsd:minInclusive", _mk(lower, base)),
        ("xsd:maxInclusive", _mk(upper, base))))


# One entry per axiom line of the fixture, keyed by that line's exact text.
_EXPECTED = {
    # --- accepted today -----------------------------------------------------
    # SubClassOf(C D) is TBox.add(C, D), verbatim.
    "SubClassOf(InformationContentEntity GenericallyDependentContinuant)":
        _accepted(lambda: (dl.TBox().add(ICE, GDC), dl.ABox())),
    # EquivalentClasses(C D) is the pair of inclusions it abbreviates, and
    # ObjectIntersectionOf/ObjectSomeValuesFrom are And/Exists.
    "EquivalentClasses(ChemicalEnergy ObjectIntersectionOf(Energy "
    "ObjectSomeValuesFrom(HasCharacteristic ChemicalPotential)))":
        _accepted(lambda: (dl.TBox().add_equivalence(
            dl.Atomic("ChemicalEnergy"),
            dl.And(dl.Atomic("Energy"),
                   dl.Exists("HasCharacteristic", dl.Atomic("ChemicalPotential")))),
            dl.ABox())),
    # DisjointClasses(C D) has no ALCHQ primitive, so it is the GCI C ⊓ D ⊑ ⊥ —
    # one per unordered pair, which for two classes is one.
    "DisjointClasses(IndependentContinuant SpecificallyDependentContinuant)":
        _accepted(lambda: (dl.TBox().add(dl.And(INDEPENDENT, DEPENDENT), dl.Bottom()),
                           dl.ABox())),
    "SubObjectPropertyOf(PartOf OverlapsWith)":
        _accepted(lambda: (dl.TBox().add_role_inclusion("PartOf", "OverlapsWith"),
                           dl.ABox())),
    "TransitiveObjectProperty(PartOf)":
        _accepted(lambda: (dl.TBox().add_transitive_role("PartOf"), dl.ABox())),
    # ClassAssertion(CE a) names the CLASS first and the individual second.
    "ClassAssertion(Modus Active)":
        _accepted(lambda: (dl.TBox(),
                           dl.ABox().assert_concept("Active", dl.Atomic("Modus")))),
    # ObjectPropertyAssertion(P a b) names the property first; ABox.assert_role
    # takes (a, b, role).
    "ObjectPropertyAssertion(Uses GeneralAlgebraicModelingSystem "
    "GAMSProgrammingLanguage)":
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_role(
            "GeneralAlgebraicModelingSystem", "GAMSProgrammingLanguage", "Uses"))),
    "DifferentIndividuals(EUEmissionSectorETS EUEmissionSectorEffortSharing)":
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_distinct(
            "EUEmissionSectorETS", "EUEmissionSectorEffortSharing"))),

    # --- A1 -----------------------------------------------------------------
    # ObjectHasValue(P a) is dl.HasValue(P, a) -- a concept kind of its own,
    # deliberately NOT Exists(P, Nominal(a)): the latter spells OWL's
    # ObjectSomeValuesFrom(P ObjectOneOf(a)), which is a different structural
    # object and is still refused (see the ObjectOneOf line below).
    "SubClassOf(CarbonDioxide ObjectHasValue(HasNormalStateOfMatter Gaseous))":
        _accepted(lambda: (dl.TBox().add(
            dl.Atomic("CarbonDioxide"),
            dl.HasValue("HasNormalStateOfMatter", "Gaseous")), dl.ABox())),
    # --- A2 -----------------------------------------------------------------
    # ObjectPropertyDomain/Range are stored NATIVELY in the role box, not
    # desugared into the equivalent GCIs ExistsP.Top <= C / Top <= AllP.C:
    # their FOL image must be the direct two-variable sentence and
    # to_owl_functional must round-trip them to themselves. So
    # tbox.inclusions stays EMPTY for both.
    "ObjectPropertyDomain(IsAbout InformationContentEntity)":
        _accepted(lambda: (dl.TBox().add_role_domain("IsAbout", ICE), dl.ABox())),
    "ObjectPropertyRange(HasCharacteristic SpecificallyDependentContinuant)":
        _accepted(lambda: (dl.TBox().add_role_range("HasCharacteristic", DEPENDENT),
                           dl.ABox())),
    # --- A3 -----------------------------------------------------------------
    # InverseObjectProperties(P Q) asserts (P)^OP = ((Q)^OP)^-, i.e. the single
    # biconditional <x,y> in P^I iff <y,x> in Q^I -- an EQUALITY of relations,
    # so one dedicated field, not two role inclusions.
    "InverseObjectProperties(PartOf HasPart)":
        _accepted(lambda: (dl.TBox().add_inverse_roles("PartOf", "HasPart"), dl.ABox())),
    # --- A4 -----------------------------------------------------------------
    # The chain is stored as a TUPLE with its super-role; the in-house tableau
    # refuses to REASON over it by name (the R of SROIQ), while the FOL image
    # renders it -- see tests/test_dl_route_agreement.py.
    "SubObjectPropertyOf(ObjectPropertyChain(IsAbout CoversEnergyCarrier) "
    "CoversEnergyCarrierShortcut)":
        _accepted(lambda: (dl.TBox().add_role_chain(
            ("IsAbout", "CoversEnergyCarrier"), "CoversEnergyCarrierShortcut"),
            dl.ABox())),
    # --- A5 -----------------------------------------------------------------
    # Expanded at parse time into every unordered pair, each stored SORTED
    # ('HasSink' < 'HasSource'), exactly as DisjointClasses becomes GCIs above.
    "DisjointObjectProperties(HasSink HasSource)":
        _accepted(lambda: (dl.TBox().add_disjoint_roles("HasSink", "HasSource"),
                           dl.ABox())),
    # --- A6 -----------------------------------------------------------------
    # All seven characteristics are READ (a parser never refuses an axiom
    # KIND); the tableau decides Asymmetric/Irreflexive/Functional and refuses
    # Symmetric/Reflexive/InverseFunctional by name at QUERY time.
    "SymmetricObjectProperty(IsConnectedTo)":
        _accepted(lambda: (dl.TBox().add_symmetric_role("IsConnectedTo"), dl.ABox())),
    "AsymmetricObjectProperty(HasPhysicalInput)":
        _accepted(lambda: (dl.TBox().add_asymmetric_role("HasPhysicalInput"), dl.ABox())),
    "IrreflexiveObjectProperty(HasPhysicalInput)":
        _accepted(lambda: (dl.TBox().add_irreflexive_role("HasPhysicalInput"), dl.ABox())),
    "ReflexiveObjectProperty(OverlapsWith)":
        _accepted(lambda: (dl.TBox().add_reflexive_role("OverlapsWith"), dl.ABox())),
    "FunctionalObjectProperty(HasNormalStateOfMatter)":
        _accepted(lambda: (dl.TBox().add_functional_role("HasNormalStateOfMatter"),
                           dl.ABox())),
    "InverseFunctionalObjectProperty(HasNormalStateOfMatter)":
        _accepted(lambda: (dl.TBox().add_inverse_functional_role(
            "HasNormalStateOfMatter"), dl.ABox())),
    # EquivalentObjectProperties has no field of its own: it is stored as the
    # role inclusions it abbreviates, both ways round per CONSECUTIVE pair --
    # sound because inclusion IS transitive, unlike disjointness above.
    "EquivalentObjectProperties(HasSink HasOutput)":
        _accepted(lambda: (dl.TBox().add_equivalent_roles("HasSink", "HasOutput"),
                           dl.ABox())),
    # --- A7 -----------------------------------------------------------------
    # The two-sorted data layer. Every one of these is stored NATIVELY, in a
    # field of its own, so the writer can print it back and the FOL image can be
    # the direct sentence (tests/test_dl_data.py and tests/test_dl_route_agreement.py
    # hold the images). A data property and an object role are different
    # things: none of these touches the role box.
    "DataPropertyDomain(HasScenarioYearValue ScenarioFactsheet)":
        _accepted(lambda: (dl.TBox().add_data_property_domain(
            "HasScenarioYearValue", dl.Atomic("ScenarioFactsheet")), dl.ABox())),
    # A bare datatype name in range position is the datatype itself.
    "DataPropertyRange(HasScenarioYearValue xsd:dateTime)":
        _accepted(lambda: (dl.TBox().add_data_property_range(
            "HasScenarioYearValue", dl.Datatype("xsd:dateTime")), dl.ABox())),
    "SubDataPropertyOf(HasScenarioYearValue HasNumber)":
        _accepted(lambda: (dl.TBox().add_data_property_inclusion(
            "HasScenarioYearValue", "HasNumber"), dl.ABox())),
    # DataHasValue(P lt) is its own concept, deliberately NOT
    # DataSomeValuesFrom(P DataOneOf(lt)): the same models, a different
    # structural object, exactly as ObjectHasValue is not ObjectOneOf above.
    'SubClassOf(TypicalYear DataHasValue(HasNumber "1"^^xsd:integer))':
        _accepted(lambda: (dl.TBox().add(
            dl.Atomic("TypicalYear"),
            dl.DataHasValue("HasNumber", _mk("1", "xsd:integer"))), dl.ABox())),
    'ClassAssertion(DataSomeValuesFrom(HasNumber DatatypeRestriction(xsd:decimal '
    'xsd:minInclusive "10000"^^xsd:decimal xsd:maxInclusive "30000"^^xsd:decimal)) '
    'MediumElectricityGridVoltageLevel)':
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_concept(
            "MediumElectricityGridVoltageLevel",
            dl.DataExists("HasNumber", _restriction("xsd:decimal", "10000", "30000"))))),
    'DatatypeDefinition(OboRoIdrange1 DatatypeRestriction(xsd:integer '
    'xsd:minInclusive "10502"^^xsd:integer xsd:maxInclusive "19999"^^xsd:integer))':
        _accepted(lambda: (dl.TBox().add_datatype_definition(
            "OboRoIdrange1", _restriction("xsd:integer", "10502", "19999")), dl.ABox())),
    # DataPropertyAssertion(P a lt) names the PROPERTY first, the individual
    # second; ABox.assert_data takes (individual, property, literal).
    'DataPropertyAssertion(HasNumber LowElectricityGridVoltageLevel "400"^^xsd:integer)':
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_data(
            "LowElectricityGridVoltageLevel", "HasNumber", _mk("400", "xsd:integer")))),
    'NegativeDataPropertyAssertion(HasNumber LowElectricityGridVoltageLevel '
    '"401"^^xsd:integer)':
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_negative_data(
            "LowElectricityGridVoltageLevel", "HasNumber", _mk("401", "xsd:integer")))),
    "FunctionalDataProperty(HasNumber)":
        _accepted(lambda: (dl.TBox().add_functional_data_property("HasNumber"),
                           dl.ABox())),
    # Stored as the pair, sorted ('HasNumber' < 'HasScenarioYearValue').
    "DisjointDataProperties(HasNumber HasScenarioYearValue)":
        _accepted(lambda: (dl.TBox().add_disjoint_data_properties(
            "HasNumber", "HasScenarioYearValue"), dl.ABox())),
    # --- A8 -----------------------------------------------------------------
    # SameIndividual(a b) is one assert_same pair; a k-ary axiom would be the
    # CONSECUTIVE chain, since equality is transitive (contrast
    # DifferentIndividuals, which needs every pair).
    "SameIndividual(CRFSectorIPCC2006Transport NCBRSectorTransport)":
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_same(
            "CRFSectorIPCC2006Transport", "NCBRSectorTransport"))),
    # NegativeObjectPropertyAssertion(P a b) is a ground FACT about two
    # individuals, stored natively; note assert_negative_role takes the two
    # individuals FIRST and the role last, matching assert_role.
    "NegativeObjectPropertyAssertion(IsDefinedBy "
    "MMRSectorMInternationalAviationInTheEUETS GovRegSectorDivision)":
        _accepted(lambda: (dl.TBox(), dl.ABox().assert_negative_role(
            "MMRSectorMInternationalAviationInTheEUETS",
            "GovRegSectorDivision", "IsDefinedBy"))),
    # --- A9 -----------------------------------------------------------------
    # owl:topObjectProperty / owl:topDataProperty are the OWL 2 built-in
    # UNIVERSAL properties, so `P ⊑ top` is valid in every interpretation. The
    # axiom is consumed as a documented NO-OP: the TBox is empty afterwards and
    # the lenient reader REPORTS it as consumed (it looks logical, so it must
    # not vanish). Until 0.30.0 it was accepted as an ordinary uninterpreted
    # role name, which shipped a weaker theory (31 of the OEO formulas carried a
    # bogus `TopObjectProperty` predicate) under a name that looks like a
    # built-in. Dropping a tautology is not the silent weakening this kit
    # forbids -- a tautology carries no truth to lose. Every OTHER use of a
    # built-in property name is refused by name; see tests/test_owl_functional.py.
    "SubObjectPropertyOf(PartOf owl:topObjectProperty)":
        _consumed("is a tautology"),
    "SubDataPropertyOf(HasScenarioYearValue owl:topDataProperty)":
        _consumed("is a tautology"),
    # --- further constructs the scouting pass named -------------------------
    "SubClassOf(Gaseous ObjectOneOf(Gaseous Liquid Solid))":
        _refused("nominal concepts (ObjectOneOf)"),
    "SubClassOf(SelfConnectedObject ObjectHasSelf(IsConnectedTo))":
        _refused("Self restrictions (ObjectHasSelf)"),
    "DisjointUnion(StateOfMatter Gaseous Liquid Solid)":
        _refused("disjoint union class axioms (DisjointUnion)"),
    "HasKey(ScenarioFactsheet () (HasScenarioYearValue))":
        _refused("keys (HasKey)"),
    # --- A10 ----------------------------------------------------------------
    # Annotation properties carry no content under the OWL 2 direct semantics,
    # so this is what AnnotationAssertion already was: read, builds nothing --
    # and, unlike a Declaration, REPORTED.
    "SubAnnotationPropertyOf(BFOOWLSpecificationLabel Label)":
        _consumed("annotation-property axiom"),
}

_COMMENT = "  # "


def _read_lines():
    """``(axiom_text, comment)`` per axiom line of the fixture.

    ``.splitlines()`` so a CRLF checkout (which is what a Windows CI runner
    produces from an LF-committed fixture) reads the same as an LF one.
    """
    text = io.open(_FIXTURE, encoding="utf-8").read()
    rows = []
    for raw in text.splitlines():
        line = raw.rstrip()
        if not line or line.lstrip().startswith("#") or line in ("Ontology(", ")"):
            continue
        axiom, _, comment = line.partition(_COMMENT)
        rows.append((axiom.strip(), comment.strip()))
    return rows


_LINES = _read_lines()


def test_the_fixture_is_one_document_with_one_axiom_per_line():
    text = io.open(_FIXTURE, encoding="utf-8").read()
    assert text.count("Ontology(") == 1 and text.rstrip().endswith(")")
    # A Windows CI runner checks an LF-committed fixture out as CRLF, so the
    # reader must give the same answer either way -- and no axiom may carry a
    # stray CR into the parser.
    assert all("\r" not in axiom for axiom, _ in _LINES)
    crlf = text.replace("\r\n", "\n").replace("\n", "\r\n")
    assert [line.partition(_COMMENT)[0].strip() for line in crlf.splitlines()
            if line.strip() and not line.lstrip().startswith("#")
            and line.strip() not in ("Ontology(", ")")] == [a for a, _ in _LINES]
    assert len(_LINES) == len(_EXPECTED), (
        f"{len(_LINES)} axiom lines against {len(_EXPECTED)} expectations")
    assert len({axiom for axiom, _ in _LINES}) == len(_LINES), "a duplicated axiom line"


def test_every_axiom_line_says_which_construct_it_is_there_for():
    """The fixture's whole value is that each line is labelled, so a later
    package knows which line is its own to flip.
    """
    for axiom, comment in _LINES:
        assert comment, f"no '{_COMMENT.strip()}' comment on {axiom!r}"
        assert ("ax" in comment or "not in OEO" in comment or "accepted today" in comment), (
            f"the comment on {axiom!r} names neither an OEO record id nor "
            f"'not in OEO': {comment!r}")


def test_every_fixture_line_has_a_hand_written_expectation():
    """A line with no expectation is a line nothing below checks."""
    in_file = {axiom for axiom, _ in _LINES}
    assert in_file == set(_EXPECTED), (
        f"lines with no expectation: {sorted(in_file - set(_EXPECTED))}; "
        f"expectations for lines that are gone: {sorted(set(_EXPECTED) - in_file)}")


@pytest.mark.parametrize("axiom", [a for a, _ in _LINES],
                         ids=[a.split("(")[0] + "-" + str(i)
                              for i, (a, _) in enumerate(_LINES)])
def test_each_construct_is_accepted_with_its_image_or_refused_by_name(axiom):
    kind, payload = _EXPECTED[axiom]
    document = f"Ontology({axiom})"
    if kind == "accepted":
        got = dl.parse_owl_functional(document)
        assert got == payload(), f"{axiom!r} did not build the expected TBox/ABox"
        return
    if kind == "consumed":
        # Read, builds NOTHING, and is reported -- by both readers' contract.
        assert dl.parse_owl_functional(document) == (dl.TBox(), dl.ABox()), axiom
        doc = dl.parse_owl_functional_axioms(document)
        assert doc.ok and doc.accepted == 0 and doc.skipped == 0 and not doc.refused
        assert [c.text for c in doc.consumed] == [axiom]
        assert doc.consumed[0].keyword == axiom.split("(")[0]
        assert payload in doc.consumed[0].reason, doc.consumed[0].reason
        return
    with pytest.raises(dl.OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional(document)
    message = str(info.value)
    assert payload in message, (
        f"{axiom!r} must be refused by NAME. Expected the phrase {payload!r} in "
        f"the message; got: {message}")
    assert "outside ALCHQ" in message, (
        "the refusal must say what fragment the construct is outside of")


def test_the_refused_lines_are_exactly_the_four_chosen_not_to_carry():
    """After the data layer nothing is refused for being unbuilt: what is left
    is deliberate, and each refusal names its construct."""
    refused = {a.split("(")[0] for a, _ in _LINES if _EXPECTED[a][0] == "refused"}
    assert refused == {"SubClassOf", "DisjointUnion", "HasKey"}
    phrases = sorted(_EXPECTED[a][1] for a, _ in _LINES if _EXPECTED[a][0] == "refused")
    assert phrases == sorted(["disjoint union class axioms (DisjointUnion)",
                              "keys (HasKey)",
                              "nominal concepts (ObjectOneOf)",
                              "Self restrictions (ObjectHasSelf)"])


def test_the_accepted_lines_round_trip_through_the_writer():
    """Writer dual: every accepted axiom must come back out of
    ``to_owl_functional`` and parse to the same TBox/ABox. A kind the parser
    reads and the writer drops is a round-trip bug.
    """
    for axiom, _ in _LINES:
        kind, payload = _EXPECTED[axiom]
        if kind != "accepted":
            continue
        tbox, abox = payload()
        assert dl.parse_owl_functional(dl.to_owl_functional(tbox, abox)) == (tbox, abox), axiom


def _whole_document() -> str:
    """The fixture with its trailing ``#`` comments stripped — a real
    Functional-Syntax document.
    """
    document = io.open(_FIXTURE, encoding="utf-8").read()
    return "\n".join(
        line.partition(_COMMENT)[0].rstrip()
        for line in document.splitlines()
        if not line.lstrip().startswith("#"))


def test_the_strict_reader_still_stops_at_the_first_refused_construct():
    """``parse_owl_functional`` is all-or-nothing, deliberately and still: one
    construct outside ALCHQ loses the other 4040 axioms of a real ontology.

    A1's ObjectHasValue stood here until 0.30.0 and the data layer's
    ``DataPropertyDomain`` after it. The first refusal in DOCUMENT order is now
    the first of the four constructs this kit has chosen not to carry, the
    nominal ``ObjectOneOf`` -- the honest record of what the data layer moved.
    """
    with pytest.raises(dl.OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional(_whole_document())
    assert "nominal concepts (ObjectOneOf)" in str(info.value)


def test_the_lenient_reader_reads_the_whole_document_and_reports_the_rest():
    """A10: ``parse_owl_functional_axioms`` is the per-axiom reader, so the
    accepted axioms are USABLE and the refused ones are DATA.

    The counts are not read off the result — they are this file's own
    hand-written expectations, which makes this a cross-check of the two
    readers rather than a restatement of one.
    """
    expected_accepted = [a for a, _ in _LINES if _EXPECTED[a][0] == "accepted"]
    expected_consumed = [a for a, _ in _LINES if _EXPECTED[a][0] == "consumed"]
    expected_refused = [a for a, _ in _LINES if _EXPECTED[a][0] == "refused"]
    text = _whole_document()
    doc = dl.parse_owl_functional_axioms(text)
    assert doc.accepted == len(expected_accepted)
    assert len(doc.refused) == len(expected_refused)
    assert doc.skipped == 0            # the fixture has no Declaration lines
    assert doc.ok is False
    # the consumed axioms are REPORTED, in document order, each with its own
    # source text -- and every axiom of the document is accounted for
    assert [c.text for c in doc.consumed] == expected_consumed
    assert doc.accepted + doc.skipped + len(doc.consumed) + len(doc.refused) == len(_LINES)
    for axiom in doc.consumed:
        assert _EXPECTED[axiom.text][1] in axiom.reason
        assert text[axiom.position:].startswith(axiom.keyword)
    # every refused line is reported with its OWN source text, at the offset of
    # the construct that was refused, and the reason still names it
    assert {axiom.text for axiom in doc.refused} == set(expected_refused)
    for axiom in doc.refused:
        assert _EXPECTED[axiom.text][1] in axiom.reason
        assert text[axiom.position:].startswith(axiom.keyword)
    # and what it DID read is exactly the accepted lines, merged: the TBox/ABox
    # the strict reader would have built from those alone
    merged_tbox, merged_abox = dl.TBox(), dl.ABox()
    for axiom in expected_accepted:
        tbox, abox = _EXPECTED[axiom][1]()
        _merge_axiom_holder(merged_tbox, tbox)
        _merge_axiom_holder(merged_abox, abox)
    assert (doc.tbox, doc.abox) == (merged_tbox, merged_abox)


def test_the_lenient_reader_still_raises_on_malformed_input():
    """It recovers from an out-of-fragment CONSTRUCT and from nothing else: a
    question about the DOCUMENT must still raise, or recovery could silently
    drop arbitrary content.
    """
    truncated = _whole_document().rstrip()[:-1]        # the closing ')' gone
    with pytest.raises(dl.OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional_axioms(truncated)
    assert not isinstance(info.value, dl.OwlFunctionalUnsupportedError)


def test_the_accepted_count_is_the_ratchet():
    """The number this fixture exists to move. Eight of the 40 lines were
    accepted before the role box landed; the role-box package adds ten (A3, A4,
    A5 and all seven A6 characteristics), the class-expression/ABox package five
    more (A1 ObjectHasValue, A2 ObjectPropertyDomain and ObjectPropertyRange, A8
    SameIndividual and NegativeObjectPropertyAssertion), and the data layer ten
    (A7). Three lines are CONSUMED -- the two tautological inclusions into a
    built-in top property (A9) and the annotation-property axiom (A10) -- which
    is neither accepted nor refused, and the four that remain refused are the
    constructs this kit has chosen not to carry.
    """
    accepted = [a for a, _ in _LINES if _EXPECTED[a][0] == "accepted"]
    consumed = [a for a, _ in _LINES if _EXPECTED[a][0] == "consumed"]
    refused = [a for a, _ in _LINES if _EXPECTED[a][0] == "refused"]
    assert len(_LINES) == 40
    assert len(accepted) == 33, sorted(accepted)
    assert len(consumed) == 3, sorted(consumed)
    assert len(refused) == 4, sorted(refused)
