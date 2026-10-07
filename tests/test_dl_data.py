r"""The data layer: OWL 2's second sort, stored, read, written, translated, refused.

OWL 2 has two domains -- individuals and the data values of datatypes -- that
are disjoint, and a data property relates an individual to a value. This kit
stores all of it (``dl.DataExists`` and its four siblings, ``dl.Literal``, the
data ranges, ``TBox.add_data_property_*``, ``ABox.assert_data``), reads and writes
it in Manchester and Functional-Style Syntax, and translates it to a *guarded
one-sorted* FOL image over two reserved predicates, ``OwlThing`` and ``OwlData``.
The in-house tableau has no data domain and REFUSES every data kind by name.

Every expected string below is hand-derived from the OWL 2 direct semantics and
the standard translation (written out in the comment above it), never read off
what the code prints. Z3 timeouts are in MILLISECONDS and are never shrunk: a
tiny budget makes a backend answer "unknown", which several APIs report as "not
valid" -- so a non-entailment test with a 2 ms budget would assert nothing.

What this file pins, section by section:

1. the datatype map (ancestors, families, canonical names);
2. literals (well-typedness, the term a literal becomes, what is refused);
3. data ranges and their images, and the facet scope;
4. the five data restrictions' images, including the two A7 corpus records the
   scouting pass measured;
5. the data box and the ABox's data assertions;
6. the side axioms -- the two-sorted discipline, the datatype lattice, the
   vocabulary walk that scopes them, the reserved names -- and WHY the GCIs are
   relativised;
7. the tableau's refusals, and ``dl.classify``'s guard;
8. the readers and writers: Manchester (including the A7-11 defect), Functional;
9. what the image can and cannot prove, and what ``atp.z3_arith`` adds.
"""

import dataclasses

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.atp.z3_arith import is_valid_arith
from unicode_logic_kit.dl import datatypes as _dt
from unicode_logic_kit.dl import tableau as _tableau
from unicode_logic_kit.dl.translate import _collect_vocabulary
from unicode_logic_kit.fol.nodes import (
    And as FAnd, Atom, Constant, Implies, Not as FNot, Number, Quantifier, Variable,
)

TIMEOUT_MS = 30000

L = dl.Literal
INT = dl.Datatype("xsd:integer")
ALPHA, BETA = dl.Atomic("Alpha"), dl.Atomic("Beta")


def _integer(value) -> dl.Literal:
    return L(str(value), "xsd:integer")


def _image(concept) -> str:
    return dl.concept_to_fol(concept, "x").to_unicode_str()


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


def _inconsistent(tbox, abox) -> bool:
    """Does the FOL image say the knowledge base has NO model?

    ``proved`` is "the negation of the knowledge base follows from the side
    axioms" and ``refuted`` is "it has a model". ``unknown`` would mean the test
    measured nothing, so it is neither.
    """
    kb = dl.kb_to_fol(tbox, abox)
    status = _status(FNot(kb.formula), kb.axioms)
    assert status in ("proved", "refuted"), status
    return status == "proved"


# --------------------------------------------------------------------------- #
# 1. The datatype map.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, expected", [
    # The OWL 2 datatype map, Structural Specification §4: each datatype's value
    # space is a subset of its parents'. xsd:int is below xsd:long, which is
    # below xsd:integer, below xsd:decimal, below owl:rational, below owl:real.
    ("xsd:int", {"xsd:long", "xsd:integer", "xsd:decimal", "owl:rational", "owl:real"}),
    ("xsd:integer", {"xsd:decimal", "owl:rational", "owl:real"}),
    ("owl:real", set()),
    ("owl:rational", {"owl:real"}),
    # positiveInteger < nonNegativeInteger < integer; the unsigned chain ends in
    # nonNegativeInteger too.
    ("xsd:positiveInteger", {"xsd:nonNegativeInteger", "xsd:integer", "xsd:decimal",
                             "owl:rational", "owl:real"}),
    ("xsd:unsignedByte", {"xsd:unsignedShort", "xsd:unsignedInt", "xsd:unsignedLong",
                          "xsd:nonNegativeInteger", "xsd:integer", "xsd:decimal",
                          "owl:rational", "owl:real"}),
    # xsd:string is below rdf:PlainLiteral; token < normalizedString < string.
    ("xsd:string", {"rdf:PlainLiteral"}),
    ("xsd:token", {"xsd:normalizedString", "xsd:string", "rdf:PlainLiteral"}),
    ("xsd:dateTimeStamp", {"xsd:dateTime"}),
    # the roots with nothing above them
    ("xsd:boolean", set()),
    ("xsd:double", set()),
    ("xsd:float", set()),
    ("rdfs:Literal", set()),
])
def test_the_datatype_lattice_is_the_owl2_datatype_map(name, expected):
    assert set(_dt.datatype_ancestors(name)) == expected


@pytest.mark.parametrize("name, family", [
    ("xsd:int", "owl:real"), ("xsd:decimal", "owl:real"), ("owl:rational", "owl:real"),
    ("xsd:string", "rdf:PlainLiteral"), ("xsd:Name", "rdf:PlainLiteral"),
    ("xsd:boolean", "xsd:boolean"), ("xsd:dateTimeStamp", "xsd:dateTime"),
    ("xsd:float", "xsd:float"), ("xsd:double", "xsd:double"),
])
def test_a_datatype_family_is_its_root(name, family):
    assert _dt.datatype_family(name) == family


def test_an_unknown_datatype_and_rdfs_literal_have_no_family():
    # Not a root: rdfs:Literal contains everything, so nothing is disjoint from
    # it; and a user-defined name is not in the map, so nothing is claimed.
    assert _dt.datatype_family("rdfs:Literal") is None
    assert _dt.datatype_family("Digit") is None
    assert not _dt.is_builtin_datatype("Digit")
    assert _dt.is_builtin_datatype("rdfs:Literal") and _dt.is_builtin_datatype("xsd:int")


@pytest.mark.parametrize("name, canonical", [
    ("xsd:integer", "xsd:integer"),
    ("http://www.w3.org/2001/XMLSchema#integer", "xsd:integer"),
    ("<http://www.w3.org/2001/XMLSchema#integer>", "xsd:integer"),
    ("<http://www.w3.org/2000/01/rdf-schema#Literal>", "rdfs:Literal"),
    ("<http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral>", "rdf:PlainLiteral"),
    ("<http://www.w3.org/2002/07/owl#real>", "owl:real"),
    # a user datatype's IRI is its own name, brackets and all
    ("<http://example.org/Digit>", "<http://example.org/Digit>"),
    ("Digit", "Digit"),
])
def test_a_built_in_namespace_is_one_name_whichever_way_it_is_written(name, canonical):
    assert _dt.canonical_datatype_name(name) == canonical


def test_a_datatype_name_is_canonicalised_on_construction():
    assert dl.Datatype("<http://www.w3.org/2001/XMLSchema#integer>") == INT


# --------------------------------------------------------------------------- #
# 2. Literals.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("lexical, datatype", [
    ("abc", "xsd:integer"),          # not digits
    ("1.5", "xsd:integer"),          # a fraction is not an integer
    ("-1", "xsd:nonNegativeInteger"),
    ("0", "xsd:positiveInteger"),
    ("256", "xsd:unsignedByte"),     # one past the range
    ("128", "xsd:byte"),
    ("1e3", "xsd:decimal"),          # xsd:decimal has no exponent
    ("2", "xsd:boolean"),            # one of true, false, 1, 0
    ("x", "rdf:PlainLiteral"),       # a PlainLiteral needs a language tag
])
def test_an_ill_typed_literal_is_refused_by_name(lexical, datatype):
    # An ill-typed literal denotes no data value, and in OWL 2 an ontology
    # containing one is inconsistent -- so the kit does not guess a value.
    with pytest.raises(dl.UnsupportedDatatypeError) as info:
        L(lexical, datatype)
    assert repr(lexical) in str(info.value) or lexical in str(info.value)


@pytest.mark.parametrize("lexical, datatype, text", [
    ("400", "xsd:integer", '"400"^^xsd:integer'),
    ("007", "xsd:integer", '"007"^^xsd:integer'),       # the lexical form is kept
    ("abc", "xsd:string", '"abc"^^xsd:string'),
    ("a\"b", "xsd:string", '"a\\"b"^^xsd:string'),      # the one escape OWL needs
])
def test_a_literal_prints_in_owl_syntax_and_keeps_its_lexical_form(lexical, datatype, text):
    assert L(lexical, datatype).to_unicode() == text
    assert str(L(lexical, datatype)) == text


def test_a_language_tag_belongs_to_plain_literal_alone():
    tagged = L("abc", "xsd:string", "EN")
    assert (tagged.datatype, tagged.language) == ("rdf:PlainLiteral", "en")  # tags fold
    assert tagged.to_unicode() == '"abc"@en'
    with pytest.raises(dl.UnsupportedDatatypeError):
        L("1", "xsd:integer", "en")


@pytest.mark.parametrize("literal, term", [
    # An exact number is the NUMBER itself, whichever integer type or spelling,
    # because OWL compares data VALUES: "007"^^xsd:integer and "7"^^xsd:decimal
    # are one value, and so one term.
    (L("7", "xsd:integer"), Number(7)),
    (L("007", "xsd:integer"), Number(7)),
    (L("+5", "xsd:integer"), Number(5)),
    (L("-0", "xsd:integer"), Number(0)),
    (L("7.0", "xsd:decimal"), Number(7)),
    (L("-3", "xsd:int"), Number(-3)),
    (L("0.10", "xsd:decimal"), Number(0.1)),
    (L("123456789012345678901234567890", "xsd:integer"),
     Number(123456789012345678901234567890)),
    # Every other datatype is a constant NAMED by the literal's own OWL text, and
    # xsd:boolean is folded onto its two canonical values first.
    (L("abc", "xsd:string"), Constant('"abc"^^xsd:string')),
    (L("1", "xsd:boolean"), Constant('"true"^^xsd:boolean')),
    (L("true", "xsd:boolean"), Constant('"true"^^xsd:boolean')),
    (L("abc", "xsd:string", "en"), Constant('"abc"@en')),
])
def test_a_literals_term_is_its_data_value(literal, term):
    assert literal.to_term() == term


@pytest.mark.parametrize("literal", [
    L("1.0", "xsd:double"),
    L("1", "xsd:float"),
    # The nearest float is not this decimal, so rounding would let two different
    # values collapse into one term.
    L("0.1234567890123456789", "xsd:decimal"),
])
def test_a_literal_with_no_exact_term_is_refused_not_rounded(literal):
    with pytest.raises(dl.UnsupportedDatatypeError):
        literal.to_term()


def test_a_float_literal_is_stored_but_refused_by_the_image():
    # A parser never refuses an axiom KIND, so the literal is READ ...
    abox = dl.ABox().assert_data("alice", "HasAmount", L("1.0", "xsd:float"))
    # ... and the translation refuses it, by name, with the reason.
    with pytest.raises(dl.UnsupportedDatatypeError, match="xsd:float"):
        dl.abox_to_fol(abox)


# --------------------------------------------------------------------------- #
# 3. Data ranges and their images.
# --------------------------------------------------------------------------- #

def _range_image(text: str) -> str:
    return dl.datarange_to_fol(
        dl.parse_manchester_data_range(text), Variable("v")).to_unicode_str()


@pytest.mark.parametrize("text, image", [
    # A datatype is a unary predicate; rdfs:Literal IS the data domain.
    ("xsd:integer", "xsd:integer(v)"),
    ("rdfs:Literal", "OwlData(v)"),
    # A restriction is its base AND every facet; >= is xsd:minInclusive, <= is
    # xsd:maxInclusive, > is xsd:minExclusive, < is xsd:maxExclusive.
    ("xsd:integer[>= 18]", "xsd:integer(v) ∧ v ≥ 18"),
    ("xsd:integer[<= 18]", "xsd:integer(v) ∧ v ≤ 18"),
    ("xsd:integer[> 18]", "xsd:integer(v) ∧ v > 18"),
    ("xsd:integer[< 18]", "xsd:integer(v) ∧ v < 18"),
    ("xsd:integer[>= 18, < 99]", "xsd:integer(v) ∧ v ≥ 18 ∧ v < 99"),
    ("xsd:decimal[>= -1.5]", "xsd:decimal(v) ∧ v ≥ -1.5"),
    # an enumeration is the disjunction of the equalities
    ("{1, 2, 3}", "v = 1 ∨ v = 2 ∨ v = 3"),
    # the complement is taken WITHIN the data domain, not in everything
    ("not xsd:integer", "OwlData(v) ∧ ¬xsd:integer(v)"),
    ("xsd:integer and not {1}", "xsd:integer(v) ∧ (OwlData(v) ∧ ¬v = 1)"),
    ("{1} or {2}", "v = 1 ∨ v = 2"),
    ("xsd:integer[> 0] or xsd:decimal[< 0]",
     "(xsd:integer(v) ∧ v > 0) ∨ (xsd:decimal(v) ∧ v < 0)"),
    # the complement of the whole data domain is empty
    ("not rdfs:Literal", "OwlData(v) ∧ ¬OwlData(v)"),
])
def test_a_data_range_image(text, image):
    assert _range_image(text) == image


@pytest.mark.parametrize("text, facet", [
    # String length and regular expressions are not first-order, and a facet that
    # constrained nothing would be a silent weakening of the axiom.
    ('xsd:string[length 3]', "xsd:length"),
    ('xsd:string[minLength 3]', "xsd:minLength"),
    ('xsd:string[maxLength 3]', "xsd:maxLength"),
    ('xsd:string[pattern "a+"]', "xsd:pattern"),
    # An ordering facet needs an order the kit can compare by: exact numbers only.
    ('xsd:string[>= "a"]', "xsd:minInclusive"),
    ('xsd:dateTime[>= "2020-01-01T00:00:00"^^xsd:dateTime]', "xsd:minInclusive"),
    ('xsd:float[>= 1]', "xsd:minInclusive"),
])
def test_a_facet_outside_the_scope_is_refused_by_name(text, facet):
    with pytest.raises(dl.ManchesterSyntaxError) as info:
        dl.parse_manchester_data_range(text)
    assert facet in str(info.value)


@pytest.mark.parametrize("text, facet", [
    # The same refusal on a NUMERIC base, where the base check cannot be what
    # stops it: only a facet with a first-order image is kept, whatever the base.
    ("xsd:integer[length 3]", "xsd:length"),
    ("xsd:decimal[totalDigits 3]", "xsd:totalDigits"),
    ("xsd:decimal[fractionDigits 2]", "xsd:fractionDigits"),
    ('xsd:decimal[pattern "1+"]', "xsd:pattern"),
])
def test_a_facet_without_an_image_is_refused_even_on_a_numeric_base(text, facet):
    with pytest.raises(dl.ManchesterSyntaxError) as info:
        dl.parse_manchester_data_range(text)
    assert facet in str(info.value) and "no first-order image" in str(info.value)


@pytest.mark.parametrize("facet", [
    "xsd:length", "xsd:minLength", "xsd:maxLength", "xsd:pattern",
    "xsd:totalDigits", "xsd:fractionDigits", "rdf:langRange", "xsd:bogus",
])
def test_a_facet_outside_the_four_ordering_facets_cannot_be_built(facet):
    # Direct construction, bypassing every reader: the refusal lives in the
    # data range itself, so a TBox can never hold a facet that constrains nothing.
    with pytest.raises(dl.UnsupportedDatatypeError, match=facet):
        dl.DatatypeRestriction(INT, ((facet, _integer(3)),))
    assert set(_dt.SUPPORTED_FACETS) == {
        "xsd:minInclusive", "xsd:maxInclusive", "xsd:minExclusive", "xsd:maxExclusive"}


def test_a_datatype_restriction_needs_at_least_one_facet():
    with pytest.raises(dl.UnsupportedDatatypeError):
        dl.DatatypeRestriction(INT, ())


def test_an_enumeration_needs_a_literal():
    with pytest.raises(dl.UnsupportedDatatypeError):
        dl.DataOneOf(())


def test_a_facet_bound_must_be_an_exact_number():
    with pytest.raises(dl.UnsupportedDatatypeError, match="not an exact number"):
        dl.DatatypeRestriction(INT, (("xsd:minInclusive", L("a", "xsd:string")),))


# --------------------------------------------------------------------------- #
# 4. The five data restrictions.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, image", [
    # π(∃d.DR, x) = ∃y (d(x, y) ∧ δ(DR, y)) -- the object ∃ with a data guard,
    # and the bound variable minted exactly as for an object restriction.
    (dl.DataExists("HasNumber", INT), "∃x0 (HasNumber(x, x0) ∧ xsd:integer(x0))"),
    # π(∀d.DR, x) = ∀y (d(x, y) → δ(DR, y)).
    (dl.DataForAll("HasNumber", INT), "∀x0 (HasNumber(x, x0) → xsd:integer(x0))"),
    (dl.DataForAll("HasIri", dl.Datatype("rdfs:Literal")),
     "∀x0 (HasIri(x, x0) → OwlData(x0))"),
    # A value restriction is the ONE-POINT reduction of ∃y (d(x, y) ∧ y = lit),
    # the ground atom, exactly as ObjectHasValue is.
    (dl.DataHasValue("HasNumber", _integer(1)), "HasNumber(x, 1)"),
    (dl.DataHasValue("HasNumber", _integer(-3)), "HasNumber(x, -3)"),
    (dl.DataHasValue("HasName", L("abc")), "HasName(x, '\"abc\"^^xsd:string')"),
    # A number restriction counts the values IN the data range -- the same
    # Count node an object number restriction uses.
    (dl.DataAtLeast(2, "HasNumber", INT), "∃≥2 x0 (HasNumber(x, x0) ∧ xsd:integer(x0))"),
    (dl.DataAtMost(1, "HasNumber", INT), "∃≤1 x0 (HasNumber(x, x0) ∧ xsd:integer(x0))"),
    (dl.DataAtMost(0, "HasNumber", INT), "∃≤0 x0 (HasNumber(x, x0) ∧ xsd:integer(x0))"),
    (dl.DataAtMost(1, "HasIri", dl.Datatype("rdfs:Literal")),
     "∃≤1 x0 (HasIri(x, x0) ∧ OwlData(x0))"),
])
def test_a_data_restrictions_image(concept, image):
    assert _image(concept) == image


def test_a_data_restriction_mints_its_variables_like_an_object_one():
    # Two restrictions side by side share the minter: x0, x1 -- never a clash.
    both = dl.And(dl.DataExists("D1", INT), dl.DataExists("D2", INT))
    assert _image(both) == ("∃x0 (D1(x, x0) ∧ xsd:integer(x0)) "
                            "∧ ∃x1 (D2(x, x1) ∧ xsd:integer(x1))")
    nested = dl.Exists("R", dl.DataExists("D", INT))
    assert _image(nested) == "∃x0 (R(x, x0) ∧ ∃x1 (D(x0, x1) ∧ xsd:integer(x1)))"


def test_the_corpus_record_ax01734_prints_exactly():
    # ax01734: SubClassOf(TypicalDay ObjectSomeValuesFrom(HasPart
    #   ObjectIntersectionOf(TimeSpan ObjectSomeValuesFrom(HasUnit Year)
    #   DataHasValue(HasNumber "1"^^xsd:integer)))).
    # ObjectIntersectionOf folds LEFT, so the three conjuncts print as one
    # parenthesised group under ∃x0; the value restriction is the ground atom
    # HasNumber(x0, 1), the restriction's own variable.
    tbox, _ = dl.parse_owl_functional(
        'Ontology(SubClassOf(TypicalDay ObjectSomeValuesFrom(HasPart '
        'ObjectIntersectionOf(TimeSpan ObjectSomeValuesFrom(HasUnit Year) '
        'DataHasValue(HasNumber "1"^^xsd:integer)))))')
    assert dl.tbox_to_fol(tbox).to_unicode_str() == (
        "∀x (TypicalDay(x) → ∃x0 (HasPart(x, x0) ∧ (TimeSpan(x0) ∧ "
        "∃x1 (HasUnit(x0, x1) ∧ Year(x1)) ∧ HasNumber(x0, 1))))")


def test_the_corpus_record_ax04017_prints_exactly():
    # ax04017: ClassAssertion(DataSomeValuesFrom(HasNumber DatatypeRestriction(
    #   xsd:decimal xsd:minInclusive "10000"^^xsd:decimal xsd:maxInclusive
    #   "30000"^^xsd:decimal)) MediumElectricityGridVoltageLevel).
    _, abox = dl.parse_owl_functional(
        'Ontology(ClassAssertion(DataSomeValuesFrom(HasNumber DatatypeRestriction('
        'xsd:decimal xsd:minInclusive "10000"^^xsd:decimal xsd:maxInclusive '
        '"30000"^^xsd:decimal)) MediumElectricityGridVoltageLevel))')
    assert dl.abox_to_fol(abox).to_unicode_str() == (
        "∃x0 (HasNumber('MediumElectricityGridVoltageLevel', x0) ∧ "
        "(xsd:decimal(x0) ∧ x0 ≥ 10000 ∧ x0 ≤ 30000))")


def test_a_data_number_restriction_has_a_non_negative_bound():
    with pytest.raises(ValueError):
        dl.DataAtLeast(-1, "D", INT)
    with pytest.raises(ValueError):
        dl.DataAtMost(-1, "D", INT)


def test_a_data_restrictions_text():
    # The rendering is the glyph syntax with a data range for the filler. It is
    # RENDER-ONLY: ∃d.xsd:integer is also the text of an object restriction, so
    # dl.parse_concept refuses it by name (see the parser tests below).
    assert dl.DataExists("d", INT).to_unicode() == "∃d.xsd:integer"
    assert dl.DataForAll("d", INT).to_unicode() == "∀d.xsd:integer"
    assert dl.DataAtLeast(2, "d", INT).to_unicode() == "≥2 d.xsd:integer"
    assert dl.DataAtMost(1, "d", INT).to_unicode() == "≤1 d.xsd:integer"
    assert dl.DataHasValue("d", _integer(1)).to_unicode() == '∃d.{"1"^^xsd:integer}'


def test_a_compound_data_range_filler_is_parenthesised_in_the_text():
    # Without the parentheses `∃d.xsd:integer ⊔ xsd:string` would read as the
    # union of a restriction and a datatype, a different concept.
    union = dl.DataUnionOf((INT, dl.Datatype("xsd:string")))
    assert dl.DataExists("d", union).to_unicode() == "∃d.(xsd:integer ⊔ xsd:string)"
    assert dl.DataAtLeast(2, "d", dl.DataIntersectionOf((INT, dl.DataComplementOf(
        dl.Datatype("Z"))))).to_unicode() == "≥2 d.(xsd:integer ⊓ ¬Z)"
    assert dl.Or(dl.DataExists("d", union), dl.Atomic("B")).to_unicode() == (
        "∃d.(xsd:integer ⊔ xsd:string) ⊔ B")
    # a negation is one symbol and needs none
    assert dl.DataExists("d", dl.DataComplementOf(INT)).to_unicode() == "∃d.¬xsd:integer"


@pytest.mark.parametrize("concept", [
    dl.DataExists("d", INT), dl.DataForAll("d", INT),
    dl.DataHasValue("d", _integer(1)),
    dl.DataAtLeast(2, "d", INT), dl.DataAtMost(1, "d", INT),
], ids=["exists", "forall", "hasvalue", "atleast", "atmost"])
def test_nnf_refuses_a_data_restriction_by_name(concept):
    # The dual of a data restriction is a restriction over the COMPLEMENT of the
    # data range, taken within the data domain -- a rule nothing implements.
    with pytest.raises(TypeError, match=type(concept).__name__):
        dl.nnf(concept)
    with pytest.raises(TypeError, match=type(concept).__name__):
        dl.nnf(dl.Not(concept))
    with pytest.raises(NotImplementedError, match=type(concept).__name__):
        dl.concept_to_modal(concept)


# --------------------------------------------------------------------------- #
# 5. The data box and the ABox's data assertions.
# --------------------------------------------------------------------------- #

def _box_image(tbox) -> str:
    return dl.databox_to_fol(tbox).to_unicode_str()


@pytest.mark.parametrize("build, image", [
    # SubDataPropertyOf(P Q): P^I ⊆ Q^I as sets of (individual, value) PAIRS.
    (lambda t: t.add_data_property_inclusion("HasScenarioYearValue", "HasNumber"),
     "∀x ∀v (HasScenarioYearValue(x, v) → HasNumber(x, v))"),
    # DisjointDataProperties(P Q): no pair is in both.
    (lambda t: t.add_disjoint_data_properties("HasNumber", "HasScenarioYearValue"),
     "∀x ∀v ¬(HasNumber(x, v) ∧ HasScenarioYearValue(x, v))"),
    # FunctionalDataProperty(P): at most one value per individual.
    (lambda t: t.add_functional_data_property("HasNumber"),
     "∀x ∀v ∀w (HasNumber(x, v) ∧ HasNumber(x, w) → v = w)"),
    # DataPropertyDomain(P C): anything with a P-value is a C -- the DIRECT
    # two-variable sentence, not the GCI ∃P.⊤ ⊑ C with its `x0 = x0` filler.
    (lambda t: t.add_data_property_domain("HasDoi", dl.Atomic("Report")),
     "∀x ∀v (HasDoi(x, v) → Report(x))"),
    # DataPropertyRange(P DR): every P-value is in DR.
    (lambda t: t.add_data_property_range("HasUuid", dl.Datatype("xsd:string")),
     "∀x ∀v (HasUuid(x, v) → xsd:string(v))"),
    (lambda t: t.add_data_property_range("HasIri", dl.Datatype("rdfs:Literal")),
     "∀x ∀v (HasIri(x, v) → OwlData(v))"),
    # DatatypeDefinition(DT DR): DT IS the range -- a biconditional, not a
    # one-way inclusion. ax03411.
    (lambda t: t.add_datatype_definition(
        "OboRoIdrange1", dl.parse_manchester_data_range("xsd:integer[>= 10502, <= 19999]")),
     "∀v (OboRoIdrange1(v) ↔ xsd:integer(v) ∧ v ≥ 10502 ∧ v ≤ 19999)"),
    # a negative bound prints and (with the NUMBER widening) reads back
    (lambda t: t.add_datatype_definition(
        "MyRange", dl.parse_manchester_data_range("xsd:integer[>= -3, <= 3]")),
     "∀v (MyRange(v) ↔ xsd:integer(v) ∧ v ≥ -3 ∧ v ≤ 3)"),
], ids=["sub", "disjoint", "functional", "domain", "range", "range-literal",
        "definition", "definition-negative"])
def test_a_data_box_axiom_image(build, image):
    tbox = dl.TBox()
    build(tbox)
    assert _box_image(tbox) == image


def test_the_data_box_variables_are_the_callers():
    tbox = dl.TBox().add_functional_data_property("HasNumber")
    assert dl.databox_to_fol(tbox, "a", "b", "c").to_unicode_str() == (
        "∀a ∀b ∀c (HasNumber(a, b) ∧ HasNumber(a, c) → b = c)")


@pytest.mark.parametrize("name", ["x", "v", "w"])
def test_a_data_property_domain_names_an_individual_called_like_a_bound_variable(name):
    # The data-box axioms bind x, v and w. An individual of the knowledge base
    # called x, v or w must not be captured by them (Variable("x") and
    # Constant("x") are the texts x and 'x', and two symbols to Z3, but would be
    # one symbol to a target that gives both one namespace).
    #
    # DataPropertyDomain(D {name}) says every individual with a D-value IS `name`,
    # and D(b, 1) gives b a D-value, so OWL 2 entails b = name. A capturing image
    # would read ∀x ∀v (D(x, v) → x = x) for name = x (vacuous) or ... → x = v for
    # name = v (the data variable), and could not prove it. The domain
    # ∃r.{name} (a value restriction) likewise entails r(b, name).
    # Already right: every binder is minted against the knowledge-base-wide avoid
    # set; pinned for individuals named x, v AND w.
    abox = (dl.ABox().assert_data("b", "D", _integer(1)).assert_concept("x", ALPHA)
            .assert_concept("v", ALPHA).assert_concept("w", ALPHA))
    nominal = dl.kb_to_fol(dl.TBox().add_data_property_domain("D", dl.Nominal(name)), abox)
    assert _status(Atom("=", (Constant("b"), Constant(name))), nominal.premises) == "proved"
    # not vacuous: b is not entailed to equal an individual nothing mentions
    assert _status(Atom("=", (Constant("b"), Constant("zz"))), nominal.premises) == "refuted"
    value = dl.kb_to_fol(dl.TBox().add_data_property_domain("D", dl.HasValue("r", name)), abox)
    assert _status(Atom("r", (Constant("b"), Constant(name))), value.premises) == "proved"
    # and the functional axiom, which binds w, still forces two values equal
    functional = (dl.TBox().add_functional_data_property("D"))
    two = (dl.ABox().assert_data("a", "D", _integer(1)).assert_data("a", "D", _integer(2))
           .assert_concept("x", ALPHA).assert_concept("v", ALPHA).assert_concept("w", ALPHA))
    assert _inconsistent(functional, two) is True


def test_the_data_box_images_rename_a_binder_that_an_individual_would_capture():
    # Hand-derived: the binder that clashes with an individual is renamed to the
    # first free letter+digits; one that does not clash is untouched; `w` is
    # bound only by the functional axiom, so a domain over {w} names a constant.
    assert _box_image(dl.TBox().add_data_property_domain("D", dl.Nominal("x"))) == (
        "∀x0 ∀v (D(x0, v) → x0 = 'x')")
    assert _box_image(dl.TBox().add_data_property_domain("D", dl.Nominal("v"))) == (
        "∀x ∀v0 (D(x, v0) → x = 'v')")
    assert _box_image(dl.TBox().add_data_property_domain("D", dl.Nominal("w"))) == (
        "∀x ∀v (D(x, v) → x = 'w')")
    assert _box_image(dl.TBox().add_data_property_domain("D", dl.HasValue("r", "x"))) == (
        "∀x0 ∀v (D(x0, v) → r(x0, 'x'))")
    assert _box_image(dl.TBox().add_data_property_domain("D", dl.Nominal("a"))) == (
        "∀x ∀v (D(x, v) → x = 'a')")


def test_equivalent_data_properties_are_the_inclusions_they_abbreviate():
    # Both ways round per CONSECUTIVE pair: ⊆ is transitive, so a chain suffices.
    tbox = dl.TBox().add_equivalent_data_properties("P", "Q", "R")
    assert tbox.data_property_inclusions == [
        ("P", "Q"), ("Q", "P"), ("Q", "R"), ("R", "Q")]
    with pytest.raises(dl.RoleExpressionError):
        dl.TBox().add_equivalent_data_properties("P")


def test_disjoint_data_properties_are_every_pair_sorted():
    # NOT a consecutive chain: disjointness is not transitive (P ⟂ Q and Q ⟂ R
    # say nothing about P and R).
    tbox = dl.TBox().add_disjoint_data_properties("C", "A", "B")
    assert tbox.disjoint_data_property_pairs == [("A", "C"), ("B", "C"), ("A", "B")]
    with pytest.raises(dl.RoleExpressionError):
        dl.TBox().add_disjoint_data_properties("P")


@pytest.mark.parametrize("build", [
    lambda t: t.add_data_property_inclusion("owl:topDataProperty", "P"),
    lambda t: t.add_functional_data_property("owl:bottomDataProperty"),
    lambda t: t.add_data_property_inclusion(dl.InverseRole("P"), "Q"),
    lambda t: t.add_data_property_domain("owl:topObjectProperty", ALPHA),
], ids=["top", "bottom", "inverse", "object-top"])
def test_a_data_property_builder_refuses_what_is_not_a_usable_property(build):
    with pytest.raises(dl.RoleExpressionError):
        build(dl.TBox())


def test_a_datatype_definition_cannot_redefine_a_built_in_or_itself():
    with pytest.raises(dl.UnsupportedDatatypeError, match="built-in"):
        dl.TBox().add_datatype_definition("xsd:integer", dl.Datatype("xsd:string"))
    with pytest.raises(dl.UnsupportedDatatypeError, match="acyclic"):
        dl.TBox().add_datatype_definition(
            "Loop", dl.DataIntersectionOf((dl.Datatype("Loop"), INT)))


def test_a_datatype_definition_may_not_close_a_cycle_through_the_stored_ones():
    # OWL 2 (Structural Specification §9.4): datatype definitions are ACYCLIC. The
    # image of  DatatypeDefinition(P1 Q1), DatatypeDefinition(Q1 ¬P1)  is
    # ∀v (P1(v) ↔ Q1(v)) ∧ ∀v (Q1(v) ↔ OwlData(v) ∧ ¬P1(v)), which has no model
    # once the data domain is non-empty (P1 ↔ ¬P1 for any data value), so it made
    # every two-sorted knowledge base inconsistent. RED before: the builder only
    # refused a DIRECT self-reference, and the second definition was accepted.
    tbox = dl.TBox().add_datatype_definition("P1", dl.Datatype("Q1"))
    with pytest.raises(dl.UnsupportedDatatypeError, match="acyclic") as info:
        tbox.add_datatype_definition("Q1", dl.DataComplementOf(dl.Datatype("P1")))
    assert "Q1 → P1 → Q1" in str(info.value)
    assert tbox.datatype_definitions == [("P1", dl.Datatype("Q1"))]     # nothing was stored
    # a three-cycle, through a union and an enumeration's neighbour
    chain = (dl.TBox().add_datatype_definition("T1", dl.Datatype("T2"))
             .add_datatype_definition("T2", dl.DataUnionOf((INT, dl.Datatype("T3")))))
    with pytest.raises(dl.UnsupportedDatatypeError, match="T3 → T1 → T2 → T3"):
        chain.add_datatype_definition("T3", dl.DataIntersectionOf((INT, dl.Datatype("T1"))))
    # forward references are fine: P1 is defined in terms of a datatype not
    # defined yet, and the definition of that one is acyclic
    forward = dl.TBox().add_datatype_definition("P1", dl.Datatype("Q1"))
    forward.add_datatype_definition("Q1", INT)
    assert len(forward.datatype_definitions) == 2


def test_a_datatype_has_one_definition():
    # OWL 2 §9.4: one DatatypeDefinition per datatype. Two DIFFERENT ones would be
    # two biconditionals ∀v (D(v) ↔ A(v)) and ∀v (D(v) ↔ B(v)), forcing A and B
    # equal -- a constraint nobody wrote; an IDENTICAL repeat is the same axiom.
    # RED before: the second definition was accepted.
    tbox = dl.TBox().add_datatype_definition("D1", INT)
    with pytest.raises(dl.UnsupportedDatatypeError, match="D1.*two DatatypeDefinitions"):
        tbox.add_datatype_definition("D1", dl.Datatype("xsd:string"))
    tbox.add_datatype_definition("D1", INT)                      # the same axiom again
    assert tbox.datatype_definitions == [("D1", INT), ("D1", INT)]


@pytest.mark.parametrize("entries, needle", [
    ([("P1", dl.Datatype("Q1")), ("Q1", dl.DataComplementOf(dl.Datatype("P1")))], "cyclic"),
    ([("Loop", dl.DataIntersectionOf((dl.Datatype("Loop"), INT)))], "cyclic"),
    ([("D1", INT), ("D1", dl.Datatype("xsd:string"))], "two DatatypeDefinitions"),
    ([("xsd:integer", dl.Datatype("xsd:string"))], "built-in"),
    ([("<http://www.w3.org/2001/XMLSchema#integer>", dl.Datatype("xsd:string"))], "built-in"),
], ids=["indirect-cycle", "self-cycle", "duplicate", "built-in", "built-in-iri"])
def test_a_hand_built_tbox_is_held_to_the_same_rules_by_every_route(entries, needle):
    # The builder is the first line of defence and the shared validation the second
    # (the one the tableau's guard, the FOL image and the writers all run), so a
    # TBox assembled through the dataclass constructor cannot slip past.
    tbox = dl.TBox(datatype_definitions=list(entries))
    for ask in (lambda: dl.kb_to_fol(tbox), lambda: dl.databox_to_fol(tbox),
                lambda: dl.data_sort_axioms(tbox),
                lambda: dl.abox_consistent(dl.ABox(), tbox),
                lambda: dl.concept_satisfiable(ALPHA, tbox),
                lambda: dl.to_owl_functional(tbox, dl.ABox())):
        with pytest.raises(dl.UnsupportedDatatypeError, match=needle):
            ask()


def test_the_functional_style_readers_refuse_a_cyclic_or_repeated_definition():
    cyclic = ("Ontology(Declaration(Datatype(P1)) Declaration(Datatype(Q1)) "
              "DatatypeDefinition(P1 Q1) DatatypeDefinition(Q1 DataComplementOf(P1)))")
    # the strict reader builds through the builder, so it raises on the second one
    with pytest.raises(dl.OwlFunctionalUnsupportedError, match="cyclic"):
        dl.parse_owl_functional(cyclic)
    # The per-axiom reader reports the second one when it reads it: a RefusedAxiom
    # with the strict reader's reason, the definition not stored, the one before it
    # kept. (It used to merge every axiom's scratch TBox without looking at the
    # definitions read earlier, so it accepted the pair and the knowledge base it
    # handed on was refused only when rendered; the old expectation here was that
    # late refusal, which is the behaviour this reader no longer has.)
    doc = dl.parse_owl_functional_axioms(cyclic)
    assert doc.ok is False and doc.refused_keywords == {"DatatypeDefinition": 1}
    assert "cyclic" in doc.refused[0].reason
    assert doc.tbox.datatype_definitions == [("P1", dl.Datatype("Q1"))]
    doc.to_kb()                       # what was kept is a legal set of definitions
    # to_kb() itself keeps refusing a cyclic set it is handed, from any source
    handed = dl.OwlFunctionalResult(
        tbox=dl.TBox(datatype_definitions=[("P1", dl.Datatype("Q1")),
                                           ("Q1", dl.DataComplementOf(dl.Datatype("P1")))]),
        abox=dl.ABox())
    with pytest.raises(dl.UnsupportedDatatypeError, match="cyclic"):
        handed.to_kb()
    twice = ("Ontology(Declaration(Datatype(D1)) DatatypeDefinition(D1 xsd:integer) "
             "DatatypeDefinition(D1 xsd:string))")
    with pytest.raises(dl.OwlFunctionalUnsupportedError, match="two DatatypeDefinitions"):
        dl.parse_owl_functional(twice)


@pytest.mark.parametrize("assertion, image", [
    # DataPropertyAssertion(P a lt): the ground atom P(a, t) -- ax04014.
    (lambda a: a.assert_data("LowElectricityGridVoltageLevel", "HasNumber", _integer(400)),
     "HasNumber('LowElectricityGridVoltageLevel', 400)"),
    (lambda a: a.assert_negative_data("alice", "HasNumber", _integer(401)),
     "¬HasNumber(alice, 401)"),
    (lambda a: a.assert_data("alice", "HasNumber", _integer(-3)), "HasNumber(alice, -3)"),
    (lambda a: a.assert_data("alice", "HasLabel", L("abc")),
     "HasLabel(alice, '\"abc\"^^xsd:string')"),
])
def test_a_data_assertion_image(assertion, image):
    abox = dl.ABox()
    assertion(abox)
    assert dl.abox_to_fol(abox).to_unicode_str() == image


def test_a_data_assertion_names_one_individual_and_one_value_term():
    # Only the individual is an INDIVIDUAL: the literal's term is a data value
    # and is never reported as something the knowledge base makes assertions about.
    abox = dl.ABox().assert_data("alice", "HasNumber", _integer(4))
    abox.assert_negative_data("bob", "HasNumber", _integer(5))
    assert dl.kb_to_fol(dl.TBox(), abox).individuals == ("alice", "bob")


def test_assert_data_wants_a_literal():
    with pytest.raises(TypeError):
        dl.ABox().assert_data("alice", "HasNumber", 400)
    with pytest.raises(TypeError):
        dl.ABox().assert_negative_data("alice", "HasNumber", "400")


# --------------------------------------------------------------------------- #
# 6. The side axioms: the two-sorted discipline.
# --------------------------------------------------------------------------- #

def _side(kb):
    return [(a.kind, a.group, a.formula.to_unicode_str()) for a in kb.side_axioms]


def test_the_two_sorted_side_axioms_of_a_small_knowledge_base():
    # tbox: DataPropertyRange(HasAmount xsd:integer); abox: HasAmount(alice, 3)
    # and HasAmount(alice, 4). Hand-derived, in the order the module documents:
    #  - the data-box image of the range axiom;
    #  - the two-sorted discipline: the domains are disjoint and each non-empty,
    #    every data property relates an individual to a data value, every named
    #    individual is an object;
    #  - the datatype facts for the datatypes MENTIONED (xsd:integer): it is a
    #    subset of the data domain; each literal's term is a data value of its
    #    datatype; two distinct numbers are distinct values.
    tbox = dl.TBox().add_data_property_range("HasAmount", INT)
    abox = (dl.ABox().assert_data("alice", "HasAmount", _integer(3))
            .assert_data("alice", "HasAmount", _integer(4)))
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.separation == "two-sorted"
    assert _side(kb) == [
        ("DataPropertyRange", "data", "∀x ∀v (HasAmount(x, v) → xsd:integer(v))"),
        ("DomainSeparation", "sort", "∀t ¬(OwlThing(t) ∧ OwlData(t))"),
        ("DomainNonEmptiness", "sort", "∃t OwlThing(t)"),
        ("DomainNonEmptiness", "sort", "∃t OwlData(t)"),
        ("DataPropertyTyping", "sort", "∀x ∀v (HasAmount(x, v) → OwlThing(x) ∧ OwlData(v))"),
        ("IndividualTyping", "sort", "OwlThing(alice)"),
        ("DatatypeGuard", "datatype", "∀v (xsd:integer(v) → OwlData(v))"),
        ("LiteralTyping", "datatype", "OwlData(3)"),
        ("LiteralTyping", "datatype", "xsd:integer(3)"),
        ("LiteralTyping", "datatype", "OwlData(4)"),
        ("LiteralTyping", "datatype", "xsd:integer(4)"),
        ("LiteralDistinctness", "datatype", "3 ≠ 4"),
    ]
    assert kb.formula.to_unicode_str() == "HasAmount(alice, 3) ∧ HasAmount(alice, 4)"


def test_the_object_property_typing_is_one_axiom_per_object_role():
    # tbox: hasPart is an object role (in a GCI), HasAmount a data property.
    # data_sort_axioms documents  ∀x ∀y (r(x, y) → OwlThing(x) ∧ OwlThing(y))  per
    # object role, between the two non-emptiness sentences and the data property
    # typing. A role is in the vocabulary through ANY axiom that names it; here a
    # GCI and a transitivity declaration name the same role once.
    tbox = (dl.TBox().add(ALPHA, dl.Exists("hasPart", BETA)).add_transitive_role("hasPart")
            .add_data_property_range("HasAmount", INT))
    kb = dl.kb_to_fol(tbox)
    assert [a.to_unicode_str() for a in kb.axioms_of_kind("ObjectPropertyTyping")] == [
        "∀x ∀y (hasPart(x, y) → OwlThing(x) ∧ OwlThing(y))"]
    assert [kind for kind, group, _f in _side(kb) if group == "sort"] == [
        "DomainSeparation", "DomainNonEmptiness", "DomainNonEmptiness",
        "ObjectPropertyTyping", "DataPropertyTyping"]


def test_an_object_property_is_typed_object_to_object_or_a_relativised_gci_does_not_reach_its_successor():
    # TBox: Alpha ⊑ ∃r.⊤ and ⊤ ⊑ Beta, plus a data property (so the image is
    # two-sorted and every GCI is restricted to the OBJECT domain).
    # OWL 2: an Alpha has an r-successor y; an object property relates individuals,
    # so y is an individual, and every individual is a Beta (⊤ ⊑ Beta): hence
    # Alpha ⊑ ∃r.Beta.
    # In the image the successor y is an OBJECT only because ObjectPropertyTyping
    # says r(x, y) → OwlThing(y); without that axiom y could be a data value, to
    # which the relativised GCI ∀x (OwlThing(x) → Beta(x)) says nothing, and the
    # goal comes back `refuted`. (Mutant: drop the typing loop of _sort_axioms and
    # this goes red, with the exact-axiom test above and the query-side one in
    # tests/test_dl_questions.py.)
    tbox = (dl.TBox().add(ALPHA, dl.Exists("r", dl.Top())).add(dl.Top(), BETA)
            .add_data_property_range("HasAmount", INT))
    kb = dl.kb_to_fol(tbox)
    goal = dl.subsumption_to_fol(ALPHA, dl.Exists("r", BETA), object_sort=True)
    assert _status(goal, kb.tbox_premises) == "proved"
    # the typing axiom is the premise that does it
    without = [f for f in kb.tbox_premises if f not in kb.axioms_of_kind("ObjectPropertyTyping")]
    assert _status(goal, without) == "refuted"


def test_every_data_axiom_view_is_one_field_read_three_ways():
    tbox = dl.TBox().add_data_property_range("HasAmount", INT)
    abox = dl.ABox().assert_data("alice", "HasAmount", _integer(3))
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.axioms == tuple(a.formula for a in kb.side_axioms)
    assert kb.data_axioms == kb.axioms           # every side axiom here is the data layer's
    assert kb.rbox_axioms == ()
    assert kb.axioms_of_kind("DataPropertyRange") == (kb.axioms[0],)
    assert kb.premises == (kb.formula, *kb.axioms)
    # a role box adds axioms the data views do NOT claim
    with_roles = dl.kb_to_fol(dl.TBox().add_transitive_role("R").add_data_property_range(
        "HasAmount", INT), abox)
    assert len(with_roles.rbox_axioms) == 1
    assert len(with_roles.data_axioms) == len(with_roles.axioms) - 1


def test_the_datatype_facts_are_scoped_to_the_datatypes_the_knowledge_base_mentions():
    # xsd:integer, xsd:decimal and xsd:string are mentioned. Hand-derived:
    #  - integer is below decimal (both mentioned): one subsumption;
    #  - integer/string and decimal/string are of different families
    #    (owl:real and rdf:PlainLiteral): two disjointness axioms; integer and
    #    decimal share a family, so none between them.
    # owl:rational, owl:real and rdf:PlainLiteral are NOT mentioned and appear
    # nowhere: a 2-datatype ontology does not drag in the whole datatype map.
    tbox = (dl.TBox().add_data_property_range("D1", INT)
            .add_data_property_range("D2", dl.Datatype("xsd:decimal"))
            .add_data_property_range("D3", dl.Datatype("xsd:string")))
    kb = dl.kb_to_fol(tbox, separation="data-lattice")
    assert [(k, f) for k, g, f in _side(kb) if g == "datatype"] == [
        ("DatatypeGuard", "∀v (xsd:decimal(v) → OwlData(v))"),
        ("DatatypeGuard", "∀v (xsd:integer(v) → OwlData(v))"),
        ("DatatypeGuard", "∀v (xsd:string(v) → OwlData(v))"),
        ("DatatypeSubsumption", "∀v (xsd:integer(v) → xsd:decimal(v))"),
        ("DatatypeDisjointness", "∀v ¬(xsd:decimal(v) ∧ xsd:string(v))"),
        ("DatatypeDisjointness", "∀v ¬(xsd:integer(v) ∧ xsd:string(v))"),
    ]


def test_literal_distinctness_is_claimed_only_where_a_lexical_form_is_one_value():
    # Exact numbers, strings and booleans are in one-to-one correspondence with
    # their values (once folded), so two different terms there are different
    # values. A hexBinary ("0A" and "0a" are ONE value) is not, so nothing is
    # claimed for it -- claiming it would be unsound.
    abox = dl.ABox()
    abox.assert_data("a", "P", _integer(1)).assert_data("a", "P", L("1.0", "xsd:decimal"))
    abox.assert_data("a", "P", L("x")).assert_data("a", "P", L("y"))
    abox.assert_data("a", "P", L("0A", "xsd:hexBinary"))
    abox.assert_data("a", "P", L("0a", "xsd:hexBinary"))
    kb = dl.kb_to_fol(dl.TBox(), abox)
    distinct = [f for k, g, f in _side(kb) if k == "LiteralDistinctness"]
    # "1" and "1.0" are ONE term, 1 (one data value, however many spellings); the
    # two strings are two terms; nothing for the hexBinary pair.
    assert distinct == ["'\"x\"^^xsd:string' ≠ '\"y\"^^xsd:string'"]


def _functional_value_inconsistent(*literals) -> bool:
    """A functional data property with each of ``literals`` as a value of one
    individual: inconsistent exactly when two of them are DIFFERENT values."""
    abox = dl.ABox()
    for literal in literals:
        abox.assert_data("a", "d", literal)
    return _inconsistent(dl.TBox().add_functional_data_property("d"), abox)


@pytest.mark.parametrize("literals, inconsistent", [
    # xsd:token accepts any string after whitespace collapse (XSD §4.3.6), so
    # "x" and "y" are two DIFFERENT values and a functional property cannot hold
    # both. RED before: the two tokens were terms of their own with no
    # distinctness, so the image had a model.
    ((L("x", "xsd:token"), L("y", "xsd:token")), True),
    # "x"^^xsd:string and "x"^^xsd:token are ONE value
    ((L("x", "xsd:string"), L("x", "xsd:token")), False),
    # collapse: "  a  b " is the value "a b"
    ((L("  a  b ", "xsd:token"), L("a b", "xsd:string")), False),
    ((L("  a  b ", "xsd:token"), L("a  b", "xsd:string")), True),    # string PRESERVES: two spaces
    # normalizedString only REPLACES tab/LF/CR by a space and keeps the spaces:
    # "a\tb" is "a b" and "a  b" is not. RED before (no distinctness).
    ((L("a\tb", "xsd:normalizedString"), L("a  b", "xsd:normalizedString")), True),
    ((L("a\tb", "xsd:normalizedString"), L("a b", "xsd:normalizedString")), False),
    ((L("a\tb", "xsd:normalizedString"), L("a\nb", "xsd:normalizedString")), False),
    # xsd:string preserves white space: a trailing space is a different value
    ((L("a "), L("a")), True),
    # xsd:anyURI is its own family: two different texts are two values (RED
    # before: no distinctness); the collapse makes the padded one the same value;
    # and the string "x" is not the URI "x" (disjoint datatypes)
    ((L("http://a", "xsd:anyURI"), L("http://b", "xsd:anyURI")), True),
    ((L(" http://a ", "xsd:anyURI"), L("http://a", "xsd:anyURI")), False),
    ((L("x", "xsd:anyURI"), L("x", "xsd:string")), True),
], ids=["token-xy", "token-string", "token-collapse", "string-preserves", "normalized-spaces",
        "normalized-tab", "normalized-tab-lf", "string-trailing", "uri-ab", "uri-collapse",
        "uri-string"])
def test_the_string_subfamily_is_compared_by_its_whitespace_processed_value(literals, inconsistent):
    assert _functional_value_inconsistent(*literals) is inconsistent


def test_a_token_is_the_same_value_as_the_string_of_the_collapsed_text():
    # d(a, "  a  b "^^xsd:token) entails a : DataHasValue(d "a b"^^xsd:string): both
    # denote the value "a b" (XSD collapse). RED before: two terms, `refuted`.
    # The converse needs the TYPING xsd:token("a b"), which the image does not
    # derive from a string literal (sound, not complete).
    abox = dl.ABox().assert_data("a", "d", L("  a  b ", "xsd:token"))
    for concept in (dl.DataHasValue("d", L("a b", "xsd:string")),
                    dl.DataExists("d", dl.Datatype("xsd:token"))):
        kb = dl.kb_to_fol(dl.TBox(), abox, query=[concept])
        assert _status(kb.instance_goal("a", concept), kb.premises) == "proved"
    uri = dl.ABox().assert_data("a", "d", L(" http://a ", "xsd:anyURI"))
    concept = dl.DataHasValue("d", L("http://a", "xsd:anyURI"))
    kb = dl.kb_to_fol(dl.TBox(), uri, query=[concept])
    assert _status(kb.instance_goal("a", concept), kb.premises) == "proved"


def test_the_terms_of_the_whitespace_processed_literals():
    # The string literals' term is the xsd:string term of the processed text, and
    # the typing keeps the datatype they were written with.
    # (the term is a constant named by the literal's OWL text, so its Unicode
    # text is that name in single quotes)
    assert L("  a  b ", "xsd:token").to_term().to_unicode_str() == "'\"a b\"^^xsd:string'"
    assert L("a\tb", "xsd:normalizedString").to_term().to_unicode_str() == "'\"a b\"^^xsd:string'"
    assert L("a  b", "xsd:normalizedString").to_term().to_unicode_str() == "'\"a  b\"^^xsd:string'"
    assert L(" http://a ", "xsd:anyURI").to_term().to_unicode_str() == "'\"http://a\"^^xsd:anyURI'"
    assert L("  a ", "xsd:string").to_term().to_unicode_str() == "'\"  a \"^^xsd:string'"
    kb = dl.kb_to_fol(dl.TBox(), dl.ABox().assert_data("a", "d", L(" a ", "xsd:token")))
    typing = [f.to_unicode_str() for f in kb.axioms_of_kind("LiteralTyping")]
    assert typing == ["OwlData('\"a\"^^xsd:string')", "xsd:token('\"a\"^^xsd:string')"]


@pytest.mark.parametrize("datatype", ["xsd:language", "xsd:Name", "xsd:NCName", "xsd:NMTOKEN"])
def test_a_literal_whose_lexical_space_is_not_validated_has_no_term(datatype):
    # The kit does not validate the XML name productions, so it cannot say that
    # "x"^^xsd:NCName denotes a value, nor that it is the xsd:token "x": a term of
    # its own would state a distinctness or identity the value space does not
    # guarantee. Refused by name, like xsd:float. RED before: it got a term.
    literal = L("x", datatype)
    with pytest.raises(dl.UnsupportedDatatypeError, match=datatype) as info:
        literal.to_term()
    assert "xsd:token" in str(info.value)          # says what to write instead
    abox = dl.ABox().assert_data("a", "d", literal)
    with pytest.raises(dl.UnsupportedDatatypeError, match=datatype):
        dl.kb_to_fol(dl.TBox(), abox)
    with pytest.raises(dl.UnsupportedDatatypeError, match=datatype):
        dl.abox_to_fol(abox)
    # the Functional-Style readers refuse it at READ time, keyed by the datatype
    text = f'Ontology(DataPropertyAssertion(d a "x"^^{datatype}))'
    with pytest.raises(dl.OwlFunctionalUnsupportedError, match=datatype):
        dl.parse_owl_functional(text)
    doc = dl.parse_owl_functional_axioms(text)
    assert doc.accepted == 0 and doc.refused_keywords == {datatype: 1}


def test_literal_distinctness_is_pairwise_so_quadratic():
    abox = dl.ABox()
    for value in range(5):
        abox.assert_data("a", "P", _integer(value))
    distinct = [f for k, g, f in _side(dl.kb_to_fol(dl.TBox(), abox))
                if k == "LiteralDistinctness"]
    assert len(distinct) == 10        # C(5, 2)


def test_the_separation_modes():
    tbox = dl.TBox().add(ALPHA, dl.DataExists("HasAmount", dl.Datatype("Digit")))
    tbox.add_data_property_domain("HasAmount", ALPHA)
    groups = {}
    for mode in ("two-sorted", "data-lattice", "none"):
        kb = dl.kb_to_fol(tbox, separation=mode)
        assert kb.separation == mode
        groups[mode] = [g for _k, g, _f in _side(kb)]
    # The data-box image is in every mode; the datatype facts in the first two;
    # the object/data separation and typing only in the first.
    assert groups["none"] == ["data"]
    assert groups["data-lattice"] == ["data", "datatype"]
    assert groups["two-sorted"] == ["data", "sort", "sort", "sort", "sort", "datatype"]
    # and only the first relativises the GCIs to the object domain
    two = dl.kb_to_fol(tbox, separation="two-sorted")
    lattice = dl.kb_to_fol(tbox, separation="data-lattice")
    assert two.formula.to_unicode_str() == (
        "∀x (OwlThing(x) ∧ Alpha(x) → ∃x0 (HasAmount(x, x0) ∧ Digit(x0)))")
    assert lattice.formula.to_unicode_str() == (
        "∀x (Alpha(x) → ∃x0 (HasAmount(x, x0) ∧ Digit(x0)))")
    with pytest.raises(dl.UnsupportedDatatypeError, match="bogus"):
        dl.kb_to_fol(tbox, separation="bogus")
    with pytest.raises(dl.UnsupportedDatatypeError, match="bogus"):
        dl.data_sort_axioms(tbox, separation="bogus")


def test_a_knowledge_base_with_no_data_layer_is_rendered_as_it_always_was():
    # Byte-identical, whatever `separation` says: nothing is added, no GCI is
    # relativised, `separation` reports "none".
    tbox = (dl.TBox().add(ALPHA, dl.Exists("R", BETA)).add_transitive_role("R")
            .add_role_domain("R", ALPHA))
    abox = dl.ABox().assert_concept("alice", ALPHA).assert_role("alice", "bob", "R")
    # the knowledge base is (concept inclusions) ∧ (the ABox), and the ABox is
    # itself the conjunction of its two assertions -- so the right operand of
    # the outer ∧ is parenthesised.
    expected_formula = ("∀x (Alpha(x) → ∃x0 (R(x, x0) ∧ Beta(x0))) "
                        "∧ (Alpha(alice) ∧ R(alice, bob))")
    for mode in ("two-sorted", "data-lattice", "none"):
        kb = dl.kb_to_fol(tbox, abox, separation=mode)
        assert kb.separation == "none"
        assert kb.formula.to_unicode_str() == expected_formula
        assert {(k, g) for k, g, _f in _side(kb)} == {
            ("TransitiveObjectProperty", "rbox"), ("ObjectPropertyDomain", "rbox")}
        assert kb.data_axioms == ()
    assert dl.data_sort_axioms(tbox, abox) == ()


def test_a_reserved_name_is_refused_not_overloaded():
    # OwlData is the guard for the data domain: a class of that name would be
    # constrained by the sort axioms as if it were the domain. OwlThing is
    # reserved only when the two-sorted axioms are asked for.
    for reserved, build in (("OwlData", lambda t: t.add(dl.Atomic("OwlData"), ALPHA)),
                            ("OwlThing", lambda t: t.add(dl.Atomic("OwlThing"), ALPHA)),
                            ("OwlData", lambda t: t.add_role_domain("OwlData", ALPHA))):
        tbox = dl.TBox().add_data_property_range("D", INT)
        build(tbox)
        with pytest.raises(dl.UnsupportedDatatypeError, match=reserved):
            dl.kb_to_fol(tbox)
    thing = dl.TBox().add(dl.Atomic("OwlThing"), ALPHA).add_data_property_range("D", INT)
    dl.kb_to_fol(thing, separation="data-lattice")        # OwlThing is free here
    with pytest.raises(dl.UnsupportedDatatypeError, match="OwlData"):
        dl.kb_to_fol(dl.TBox().add(dl.Atomic("OwlData"), ALPHA).add_data_property_range("D", INT),
                     separation="data-lattice")
    # a knowledge base with no data layer has nothing to reserve
    dl.kb_to_fol(dl.TBox().add(dl.Atomic("OwlData"), ALPHA))


# -- the vocabulary walk that scopes the sort axioms --------------------------

#: One sample per (holder, field), each carrying names found nowhere else. The
#: walk is hand-listed over the fields, so a field it does not read would
#: silently SHRINK the sort axioms -- an individual left untyped, a datatype left
#: out of the lattice. This table is what makes that loud.
_WALK = {
    ("tbox", "inclusions"): (
        lambda: (dl.TBox().add(dl.Exists("r_inc", dl.Atomic("C_inc")), dl.Atomic("D_inc")), None),
        {"object_roles": {"r_inc"}, "classes": {"C_inc", "D_inc"}}),
    ("tbox", "role_inclusions"): (
        lambda: (dl.TBox().add_role_inclusion("r_sub", "r_sup"), None),
        {"object_roles": {"r_sub", "r_sup"}}),
    ("tbox", "transitive_roles"): (
        lambda: (dl.TBox().add_transitive_role("r_tr"), None), {"object_roles": {"r_tr"}}),
    ("tbox", "symmetric_roles"): (
        lambda: (dl.TBox().add_symmetric_role("r_sy"), None), {"object_roles": {"r_sy"}}),
    ("tbox", "asymmetric_roles"): (
        lambda: (dl.TBox().add_asymmetric_role("r_as"), None), {"object_roles": {"r_as"}}),
    ("tbox", "reflexive_roles"): (
        lambda: (dl.TBox().add_reflexive_role("r_re"), None), {"object_roles": {"r_re"}}),
    ("tbox", "irreflexive_roles"): (
        lambda: (dl.TBox().add_irreflexive_role("r_ir"), None), {"object_roles": {"r_ir"}}),
    ("tbox", "functional_roles"): (
        lambda: (dl.TBox().add_functional_role("r_fu"), None), {"object_roles": {"r_fu"}}),
    ("tbox", "inverse_functional_roles"): (
        lambda: (dl.TBox().add_inverse_functional_role("r_if"), None),
        {"object_roles": {"r_if"}}),
    ("tbox", "inverse_role_pairs"): (
        lambda: (dl.TBox().add_inverse_roles("r_p", "r_q"), None),
        {"object_roles": {"r_p", "r_q"}}),
    ("tbox", "disjoint_role_pairs"): (
        lambda: (dl.TBox().add_disjoint_roles("r_d1", "r_d2"), None),
        {"object_roles": {"r_d1", "r_d2"}}),
    ("tbox", "role_chains"): (
        lambda: (dl.TBox().add_role_chain(("r_c1", "r_c2"), "r_c3"), None),
        {"object_roles": {"r_c1", "r_c2", "r_c3"}}),
    ("tbox", "role_domains"): (
        lambda: (dl.TBox().add_role_domain("r_do", dl.Atomic("C_do")), None),
        {"object_roles": {"r_do"}, "classes": {"C_do"}}),
    ("tbox", "role_ranges"): (
        lambda: (dl.TBox().add_role_range("r_ra", dl.Atomic("C_ra")), None),
        {"object_roles": {"r_ra"}, "classes": {"C_ra"}}),
    ("tbox", "data_property_inclusions"): (
        lambda: (dl.TBox().add_data_property_inclusion("d_sub", "d_sup"), None),
        {"data_properties": {"d_sub", "d_sup"}}),
    ("tbox", "disjoint_data_property_pairs"): (
        lambda: (dl.TBox().add_disjoint_data_properties("d_d1", "d_d2"), None),
        {"data_properties": {"d_d1", "d_d2"}}),
    ("tbox", "functional_data_properties"): (
        lambda: (dl.TBox().add_functional_data_property("d_fu"), None),
        {"data_properties": {"d_fu"}}),
    ("tbox", "data_property_domains"): (
        lambda: (dl.TBox().add_data_property_domain("d_do", dl.Atomic("C_dd")), None),
        {"data_properties": {"d_do"}, "classes": {"C_dd"}}),
    ("tbox", "data_property_ranges"): (
        lambda: (dl.TBox().add_data_property_range(
            "d_ra", dl.DataUnionOf((dl.Datatype("T_ra"), dl.DataOneOf((L("lit_ra"),))))), None),
        {"data_properties": {"d_ra"}, "datatypes": {"T_ra", "xsd:string"}}),
    ("tbox", "datatype_definitions"): (
        lambda: (dl.TBox().add_datatype_definition(
            "T_def", dl.DataComplementOf(dl.Datatype("T_base"))), None),
        {"datatypes": {"T_def", "T_base"}}),
    ("abox", "concept_assertions"): (
        lambda: (None, dl.ABox().assert_concept("i_cl", dl.Exists("r_cl", dl.Atomic("C_cl")))),
        {"individuals": {"i_cl"}, "object_roles": {"r_cl"}, "classes": {"C_cl"}}),
    ("abox", "role_assertions"): (
        lambda: (None, dl.ABox().assert_role("i_ra", "i_rb", "r_ro")),
        {"individuals": {"i_ra", "i_rb"}, "object_roles": {"r_ro"}}),
    ("abox", "distinct_assertions"): (
        lambda: (None, dl.ABox().assert_distinct("i_d1", "i_d2")),
        {"individuals": {"i_d1", "i_d2"}}),
    ("abox", "same_assertions"): (
        lambda: (None, dl.ABox().assert_same("i_s1", "i_s2")),
        {"individuals": {"i_s1", "i_s2"}}),
    ("abox", "negative_role_assertions"): (
        lambda: (None, dl.ABox().assert_negative_role("i_n1", "i_n2", "r_neg")),
        {"individuals": {"i_n1", "i_n2"}, "object_roles": {"r_neg"}}),
    ("abox", "data_assertions"): (
        lambda: (None, dl.ABox().assert_data("i_da", "d_as", L("7", "xsd:short"))),
        {"individuals": {"i_da"}, "data_properties": {"d_as"}, "datatypes": {"xsd:short"}}),
    ("abox", "negative_data_assertions"): (
        lambda: (None, dl.ABox().assert_negative_data("i_nd", "d_ng", L("v", "xsd:token"))),
        {"individuals": {"i_nd"}, "data_properties": {"d_ng"}, "datatypes": {"xsd:token"}}),
}


def test_the_vocabulary_walk_has_a_sample_for_every_row_of_the_table():
    assert set(_WALK) == {(row.holder, row.field) for row in _tableau._AXIOM_KINDS}, (
        "dl.tableau._AXIOM_KINDS gained or lost a field; the vocabulary walk in "
        "dl.translate._collect_vocabulary must be taught it and this table with it")


@pytest.mark.parametrize("key", sorted(_WALK), ids=[f"{h}.{f}" for h, f in sorted(_WALK)])
def test_the_vocabulary_walk_reads_every_field(key):
    build, expected = _WALK[key]
    tbox, abox = build()
    vocabulary = _collect_vocabulary(tbox, abox)
    for attribute, names in expected.items():
        got = getattr(vocabulary, attribute)
        assert names <= got, f"{key}: {attribute} lost {sorted(names - got)}"


_CONCEPT_WALK = [
    (dl.Not(dl.Atomic("C_not")), {"classes": {"C_not"}}),
    (dl.Exists("r_ex", dl.Atomic("C_ex")), {"object_roles": {"r_ex"}, "classes": {"C_ex"}}),
    (dl.And(dl.Atomic("C_a"), dl.Atomic("C_b")), {"classes": {"C_a", "C_b"}}),
    (dl.Or(dl.Atomic("C_c"), dl.Exists("r_or", dl.Atomic("C_d"))),
     {"classes": {"C_c", "C_d"}, "object_roles": {"r_or"}}),
    (dl.ForAll("r_fa", dl.Atomic("C_fa")), {"object_roles": {"r_fa"}, "classes": {"C_fa"}}),
    (dl.AtLeast(2, "r_al", dl.Atomic("C_al")), {"object_roles": {"r_al"}, "classes": {"C_al"}}),
    (dl.AtMost(1, "r_am", dl.Atomic("C_am")), {"object_roles": {"r_am"}, "classes": {"C_am"}}),
    (dl.Nominal("i_nom"), {"individuals": {"i_nom"}}),
    (dl.HasValue("r_hv", "i_hv"), {"object_roles": {"r_hv"}, "individuals": {"i_hv"}}),
    (dl.DataExists("d_ex", dl.Datatype("T_ex")), {"data_properties": {"d_ex"}, "datatypes": {"T_ex"}}),
    (dl.DataForAll("d_fa", dl.Datatype("T_fa")), {"data_properties": {"d_fa"}, "datatypes": {"T_fa"}}),
    (dl.DataAtLeast(1, "d_al", dl.Datatype("T_al")), {"data_properties": {"d_al"}, "datatypes": {"T_al"}}),
    (dl.DataAtMost(1, "d_am", dl.Datatype("T_am")), {"data_properties": {"d_am"}, "datatypes": {"T_am"}}),
    (dl.DataHasValue("d_hv", L("1", "xsd:byte")), {"data_properties": {"d_hv"}, "datatypes": {"xsd:byte"}}),
]


@pytest.mark.parametrize("concept, expected", _CONCEPT_WALK,
                         ids=[type(c).__name__ for c, _ in _CONCEPT_WALK])
def test_the_vocabulary_walk_reads_every_concept_constructor(concept, expected):
    vocabulary = _collect_vocabulary(dl.TBox().add(dl.Top(), concept), None)
    for attribute, names in expected.items():
        assert names <= getattr(vocabulary, attribute), (attribute, concept)


def test_the_vocabulary_walk_covers_every_concept_class():
    """A constructor added to ``dl.concepts`` and not to the walk would be
    silently ignored; every concept class must appear in the table above (the
    atom, the top and the bottom mention no role and are covered by the first)."""
    import unicode_logic_kit.dl.concepts as concepts
    every = {cls for cls in vars(concepts).values()
             if isinstance(cls, type) and issubclass(cls, dl.Concept) and cls is not dl.Concept}
    covered = {type(concept) for concept, _ in _CONCEPT_WALK}
    covered |= {dl.Atomic, dl.Top, dl.Bottom, dl.InverseRole}
    assert every - covered == set(), f"a concept class the walk may not know: {every - covered}"


# -- WHY the GCIs are relativised ----------------------------------------------

def test_a_gci_must_be_relativised_to_the_object_domain():
    # ⊤ ⊑ {a} says the object domain is the single point a. It says nothing
    # about data values. The knowledge base below is OWL-CONSISTENT: take the
    # object domain {a}, the data domain {5}, D = {(a, 5)}.
    tbox = dl.TBox().add(dl.Top(), dl.Nominal("a")).add_data_property_range("D", INT)
    abox = dl.ABox().assert_data("a", "D", _integer(5))
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.formula.to_unicode_str() == "∀x (OwlThing(x) ∧ x = x → x = 'a') ∧ D('a', 5)"
    assert _status(FNot(kb.formula), kb.axioms) == "refuted"      # it has a model
    # The same GCI NOT relativised ranges over data values too: it forces 5 = a,
    # so the data value 5 is the object a, which the separation forbids. The
    # image would be INCONSISTENT for a consistent ontology -- unsound.
    unrelativised = FAnd(dl.tbox_to_fol(tbox, concept_inclusions_only=True),
                         dl.abox_to_fol(abox))
    assert unrelativised.to_unicode_str() == "∀x (x = x → x = 'a') ∧ D('a', 5)"
    assert _status(FNot(unrelativised), kb.axioms) == "proved"
    # data-lattice mode keeps the GCIs as written, and says so
    assert dl.kb_to_fol(tbox, abox, separation="data-lattice").formula.to_unicode_str() == (
        unrelativised.to_unicode_str())


def test_a_goal_about_concepts_must_be_relativised_too():
    # ⊤ ⊑ Alpha holds in the knowledge base (the object domain is inside Alpha).
    # The unrelativised GOAL ∀x (x = x → Alpha(x)) asks that every data value be
    # an Alpha as well, which nothing says.
    tbox = dl.TBox().add(dl.Top(), ALPHA).add_data_property_range("D", INT)
    kb = dl.kb_to_fol(tbox)
    plain = dl.subsumption_to_fol(dl.Top(), ALPHA)
    sorted_goal = dl.subsumption_to_fol(dl.Top(), ALPHA, object_sort=True)
    assert plain.to_unicode_str() == "∀x (x = x → Alpha(x))"
    assert sorted_goal.to_unicode_str() == "∀x (OwlThing(x) ∧ x = x → Alpha(x))"
    assert _status(plain, kb.tbox_premises) == "refuted"
    assert _status(sorted_goal, kb.tbox_premises) == "proved"


def test_object_sort_changes_nothing_for_a_knowledge_base_without_data():
    assert (dl.subsumption_to_fol(ALPHA, BETA).to_unicode_str()
            == "∀x (Alpha(x) → Beta(x))")
    assert (dl.subsumption_to_fol(ALPHA, BETA, object_sort=True).to_unicode_str()
            == "∀x (OwlThing(x) ∧ Alpha(x) → Beta(x))")


def test_reflexivity_is_relativised_in_the_two_sorted_image():
    # ReflexiveObjectProperty(P) is ∀x P(x, x) over INDIVIDUALS; over all
    # elements it would make every data value P-related to itself, and P is
    # typed object-to-object.
    tbox = dl.TBox().add_reflexive_role("R").add_data_property_range("D", INT)
    kb = dl.kb_to_fol(tbox)
    assert kb.axioms_of_kind("ReflexiveObjectProperty")[0].to_unicode_str() == (
        "∀x (OwlThing(x) → R(x, x))")
    assert dl.kb_to_fol(tbox, separation="data-lattice").axioms_of_kind(
        "ReflexiveObjectProperty")[0].to_unicode_str() == "∀x R(x, x)"
    plain = dl.kb_to_fol(dl.TBox().add_reflexive_role("R"))
    assert plain.axioms_of_kind("ReflexiveObjectProperty")[0].to_unicode_str() == "∀x R(x, x)"


# --------------------------------------------------------------------------- #
# 7. The tableau refuses, by name.
# --------------------------------------------------------------------------- #

_DATA_CONCEPTS = [
    dl.DataExists("d", INT), dl.DataForAll("d", INT), dl.DataHasValue("d", _integer(1)),
    dl.DataAtLeast(2, "d", INT), dl.DataAtMost(1, "d", INT),
]


@pytest.mark.parametrize("concept", _DATA_CONCEPTS, ids=lambda c: type(c).__name__)
def test_the_tableau_refuses_a_data_concept_by_name(concept):
    name = type(concept).__name__
    for ask in (lambda c: dl.concept_satisfiable(c),
                lambda c: dl.concept_satisfiable(dl.Not(dl.And(ALPHA, c))),
                lambda c: dl.concept_satisfiable(dl.Exists("r", c)),
                lambda c: dl.subsumes(ALPHA, c),
                lambda c: dl.subsumes(c, ALPHA),
                lambda c: dl.equivalent(c, ALPHA),
                lambda c: dl.instance_check(dl.ABox().assert_concept("a", ALPHA), "a", c),
                lambda c: dl.abox_consistent(dl.ABox().assert_concept("a", c)),
                lambda c: dl.concept_satisfiable(ALPHA, dl.TBox().add(ALPHA, c))):
        with pytest.raises(dl.UnsupportedConceptError, match=name) as info:
            ask(concept)
        message = str(info.value)
        assert "no data domain" in message, message
        assert "api.prove" in message, message


def test_a_data_concept_is_a_concept_level_refusal_not_an_axiom_level_one():
    with pytest.raises(dl.UnsupportedConceptError):
        dl.concept_satisfiable(dl.DataExists("d", INT))
    assert not issubclass(dl.UnsupportedConceptError, dl.UnsupportedAxiomError)


def test_the_tableau_names_every_data_kind_present_with_its_count():
    tbox = (dl.TBox().add_data_property_inclusion("P", "Q").add_data_property_inclusion("Q", "R")
            .add_functional_data_property("P").add_datatype_definition("T", INT))
    abox = dl.ABox().assert_data("a", "P", _integer(1))
    with pytest.raises(dl.UnsupportedAxiomError) as info:
        dl.abox_consistent(abox, tbox)
    message = str(info.value)
    for fragment in ("SubDataPropertyOf x2", "FunctionalDataProperty x1",
                     "DatatypeDefinition x1", "DataPropertyAssertion x1",
                     "no data domain", "dl.owl_reasoner", "dl.kb_to_fol", "api.prove",
                     "atp.z3_arith"):
        assert fragment in message, (fragment, message)


def test_a_data_only_refusal_does_not_mention_the_object_layers_remedy():
    # The object-layer refusals point at HermiT; HermiT is NOT wired to the
    # data layer, so a message that suggested it would send the caller to a
    # route that refuses too.
    with pytest.raises(dl.UnsupportedAxiomError) as info:
        dl.abox_consistent(dl.ABox(), dl.TBox().add_functional_data_property("P"))
    assert "not wired" in str(info.value)
    with pytest.raises(dl.UnsupportedAxiomError) as info:
        dl.abox_consistent(dl.ABox(), dl.TBox().add_symmetric_role("r"))
    assert "not wired" not in str(info.value)


def test_the_data_rows_are_the_data_layer():
    rows = [r for r in _tableau._AXIOM_KINDS if r.layer == "data"]
    assert {r.kind for r in rows} == {
        "SubDataPropertyOf", "DisjointDataProperties", "FunctionalDataProperty",
        "DataPropertyDomain", "DataPropertyRange", "DatatypeDefinition",
        "DataPropertyAssertion", "NegativeDataPropertyAssertion"}
    assert all(r.tableau == "refused" and r.fol == "fol" for r in rows)
    assert {r.kind for r in _tableau._AXIOM_KINDS if r.layer == "object"}.isdisjoint(
        {r.kind for r in rows})


def test_a_row_with_an_unknown_layer_is_caught_by_the_table_check():
    row = dataclasses.replace(_tableau._AXIOM_KINDS[0], layer="third")
    with pytest.raises(ValueError, match="layer 'third'"):
        _tableau._validate_axiom_kinds((row,) + tuple(_tableau._AXIOM_KINDS[1:]))


# -- dl.classify must run the axiom guard up front -------------------------------

@pytest.mark.parametrize("build", [
    lambda t: t.add_symmetric_role("r"),
    lambda t: t.add_functional_data_property("d"),
    lambda t: t.add_data_property_range("d", INT),
    lambda t: t.add_datatype_definition("T", INT),
], ids=["symmetric-role", "functional-data", "data-range", "datatype-definition"])
def test_classify_refuses_an_unsupported_axiom_even_with_one_named_concept(build):
    # THE hole: classify answers by asking `subsumes` about PAIRS of named
    # concepts. With zero or one named concept there is no pair, no query, and so
    # the shared guard -- called only from concept_satisfiable and abox_consistent
    # -- never ran: classify returned a hierarchy for a knowledge base it had not
    # looked at. It now calls the guard before it begins.
    tbox = dl.TBox()
    build(tbox)
    with pytest.raises(dl.UnsupportedAxiomError):
        dl.classify(tbox, [ALPHA])
    with pytest.raises(dl.UnsupportedAxiomError):
        dl.classify(tbox)
    with pytest.raises(dl.UnsupportedAxiomError):
        dl.classify(tbox.add(ALPHA, ALPHA))      # and with a concept inclusion present


def test_classify_still_classifies_a_knowledge_base_of_decided_kinds():
    tbox = dl.TBox().add(ALPHA, BETA).add_transitive_role("r")
    result = dl.classify(tbox, [ALPHA])
    assert result.ancestors["Alpha"] == frozenset({"Beta"})


def test_classify_refuses_a_data_concept_inside_a_concept_inclusion():
    with pytest.raises(dl.UnsupportedConceptError, match="DataExists"):
        dl.classify(dl.TBox().add(ALPHA, dl.DataExists("d", INT)))
    with pytest.raises(dl.UnsupportedConceptError, match="DataHasValue"):
        dl.classify(dl.TBox(), [dl.DataHasValue("d", _integer(1))])


# --------------------------------------------------------------------------- #
# 8. Readers and writers.
# --------------------------------------------------------------------------- #

# -- Manchester ----------------------------------------------------------------

@pytest.mark.parametrize("text, expected", [
    # A7-11, THE defect. `d some xsd:integer` used to read, silently, as an
    # OBJECT restriction over a class called "xsd:integer" -- a different sort,
    # and an axiom about nothing. The filler's head says which it is.
    ("d some xsd:integer", dl.DataExists("d", INT)),
    ("d only xsd:integer", dl.DataForAll("d", INT)),
    ("d min 2 xsd:integer", dl.DataAtLeast(2, "d", INT)),
    ("d max 1 xsd:integer", dl.DataAtMost(1, "d", INT)),
    ("d exactly 3 xsd:integer",
     dl.And(dl.DataAtLeast(3, "d", INT), dl.DataAtMost(3, "d", INT))),
    ('d value "1"^^xsd:integer', dl.DataHasValue("d", _integer(1))),
    ("d value 5", dl.DataHasValue("d", _integer(5))),            # a bare numeral
    ("d value -3", dl.DataHasValue("d", _integer(-3))),
    ("d value 1.5", dl.DataHasValue("d", L("1.5", "xsd:decimal"))),
    ('d value "abc"', dl.DataHasValue("d", L("abc"))),
    ('d value "abc"@en', dl.DataHasValue("d", L("abc", "xsd:string", "en"))),
    ("d some {1, 2}", dl.DataExists("d", dl.DataOneOf((_integer(1), _integer(2))))),
    ("d some not xsd:integer", dl.DataExists("d", dl.DataComplementOf(INT))),
    ("d some (xsd:integer or xsd:string)",
     dl.DataExists("d", dl.DataUnionOf((INT, dl.Datatype("xsd:string"))))),
    ("d some rdfs:Literal", dl.DataExists("d", dl.Datatype("rdfs:Literal"))),
    ("d some <http://www.w3.org/2001/XMLSchema#integer>", dl.DataExists("d", INT)),
    ("d some xsd:integer[>= 1, <= 9]",
     dl.DataExists("d", dl.DatatypeRestriction(INT, (
         ("xsd:minInclusive", _integer(1)), ("xsd:maxInclusive", _integer(9)))))),
    # nested in a class expression
    ("r some (d some xsd:integer)", dl.Exists("r", dl.DataExists("d", INT))),
    ("not (d some xsd:integer)", dl.Not(dl.DataExists("d", INT))),
])
def test_manchester_reads_a_data_restriction(text, expected):
    assert dl.parse_manchester(text) == expected


@pytest.mark.parametrize("text, expected", [
    # ... and the object restrictions are BYTE-IDENTICAL to what they always were.
    ("hasPet some Dog", dl.Exists("hasPet", dl.Atomic("Dog"))),
    ("hasPet only Dog", dl.ForAll("hasPet", dl.Atomic("Dog"))),
    ("hasPet min 2 Dog", dl.AtLeast(2, "hasPet", dl.Atomic("Dog"))),
    ("hasPet min 2", dl.AtLeast(2, "hasPet", dl.Top())),
    ("hasPet value alice", dl.HasValue("hasPet", "alice")),
])
def test_manchester_still_reads_an_object_restriction_as_one(text, expected):
    assert dl.parse_manchester(text) == expected


def test_an_undeclared_user_datatype_reads_as_an_object_restriction_until_declared():
    # `Digit` is an ordinary name: nothing in the text says it is a datatype, so
    # a context-free reader cannot tell `d some Digit` from `r some Dog`. This is
    # the documented limit, and `datatypes=` is the remedy.
    assert dl.parse_manchester("d some Digit") == dl.Exists("d", dl.Atomic("Digit"))
    assert dl.parse_manchester("d some Digit", datatypes=("Digit",)) == dl.DataExists(
        "d", dl.Datatype("Digit"))
    # a list does as well as a tuple
    assert dl.parse_manchester("d some Digit", datatypes=("Digit",)) == (
        dl.parse_manchester("d some Digit", datatypes=["Digit"]))
    # a facet bracket after ANY name makes it a data range -- and a facet on a
    # name that is not an exact-number datatype is then refused by name, not
    # silently read as an object restriction with a stray bracket
    with pytest.raises(dl.ManchesterSyntaxError, match="xsd:minInclusive"):
        dl.parse_manchester("d some Digit[>= 1]")


def test_a_built_in_datatype_in_class_position_is_refused_by_name():
    # OWL 2 does not let one name be both a class and a datatype.
    for text in ("Dog and xsd:integer", "xsd:integer", "not xsd:string",
                 "r some (Dog and xsd:integer)"):
        with pytest.raises(dl.ManchesterSyntaxError, match="DATATYPE, not a class"):
            dl.parse_manchester(text)


def test_manchester_reads_a_data_range_and_a_literal_on_their_own():
    assert dl.parse_manchester_data_range("xsd:integer[>= 1]") == dl.DatatypeRestriction(
        INT, (("xsd:minInclusive", _integer(1)),))
    assert dl.parse_manchester_data_range("Digit") == dl.Datatype("Digit")
    assert dl.parse_manchester_literal('"400"^^xsd:integer') == _integer(400)
    assert dl.parse_manchester_literal("400") == _integer(400)
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_literal("nope")
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_literal('"abc"^^xsd:integer')       # ill-typed
    with pytest.raises(dl.ManchesterSyntaxError):
        dl.parse_manchester_data_range("xsd:integer[>= 1] xsd:integer")


_ROUND_TRIP_CONCEPTS = [
    dl.DataExists("d", INT),
    dl.DataForAll("d", dl.Datatype("rdfs:Literal")),
    dl.DataHasValue("d", L("abc")),
    dl.DataHasValue("d", L("abc", "xsd:string", "en")),
    dl.DataAtLeast(2, "d", dl.DatatypeRestriction(INT, (("xsd:minExclusive", _integer(-5)),))),
    dl.DataAtMost(1, "d", dl.DataOneOf((_integer(1), _integer(2)))),
    dl.DataExists("d", dl.DataComplementOf(dl.DataUnionOf((INT, dl.Datatype("xsd:string"))))),
    dl.DataExists("d", dl.DataIntersectionOf((INT, dl.DataComplementOf(
        dl.DataOneOf((_integer(0),)))))),
    dl.And(dl.Atomic("Dog"), dl.DataExists("age", dl.DatatypeRestriction(
        INT, (("xsd:minInclusive", _integer(18)),)))),
    dl.Exists("r", dl.Not(dl.DataHasValue("d", L("1.5", "xsd:decimal")))),
]


@pytest.mark.parametrize("concept", _ROUND_TRIP_CONCEPTS, ids=lambda c: c.to_unicode())
def test_manchester_round_trips_a_data_concept(concept):
    assert dl.parse_manchester(dl.to_manchester(concept)) == concept


def test_manchester_round_trips_a_user_datatype_when_told_about_it():
    concept = dl.DataExists("d", dl.Datatype("Digit"))
    assert dl.to_manchester(concept) == "d some Digit"
    assert dl.parse_manchester(dl.to_manchester(concept), datatypes=("Digit",)) == concept


@pytest.mark.parametrize("data_range", [
    dl.Datatype("xsd:integer"), dl.Datatype("rdfs:Literal"),
    dl.DatatypeRestriction(INT, (("xsd:minInclusive", _integer(1)),
                                 ("xsd:maxExclusive", _integer(9)))),
    dl.DatatypeRestriction(dl.Datatype("xsd:decimal"),
                           (("xsd:minInclusive", L("-1.5", "xsd:decimal")),)),
    dl.DataOneOf((_integer(1), L("a"))),
    dl.DataComplementOf(INT),
    dl.DataIntersectionOf((INT, dl.DataComplementOf(dl.DataOneOf((_integer(0),))))),
    dl.DataUnionOf((INT, dl.DataUnionOf((dl.Datatype("xsd:string"), dl.Datatype("xsd:boolean"))))),
], ids=lambda dr: dl.to_manchester_data_range(dr))
def test_manchester_round_trips_a_data_range(data_range):
    assert dl.parse_manchester_data_range(dl.to_manchester_data_range(data_range)) == data_range


def test_a_facet_bound_prints_as_a_bare_numeral_only_when_that_reads_back_the_same():
    # Inside a facet bracket a BARE numeral takes the datatype of the base
    # (`xsd:decimal[>= 1]` bounds by the decimal 1). So a bound typed as its base
    # prints bare, and a bound typed as something ELSE -- here an integer bound on
    # a decimal base -- would read back as a decimal, so it is written typed.
    integer = dl.DatatypeRestriction(INT, (("xsd:minInclusive", _integer(1)),))
    decimal = dl.DatatypeRestriction(dl.Datatype("xsd:decimal"),
                                     (("xsd:minInclusive", L("1", "xsd:decimal")),))
    mixed = dl.DatatypeRestriction(dl.Datatype("xsd:decimal"),
                                   (("xsd:minInclusive", _integer(1)),))
    assert dl.to_manchester_data_range(integer) == "xsd:integer[>= 1]"
    assert dl.to_manchester_data_range(decimal) == "xsd:decimal[>= 1]"
    assert dl.to_manchester_data_range(mixed) == 'xsd:decimal[>= "1"^^xsd:integer]'
    for data_range in (integer, decimal, mixed):
        assert dl.parse_manchester_data_range(
            dl.to_manchester_data_range(data_range)) == data_range


# -- Functional-Style Syntax -----------------------------------------------------

@pytest.mark.parametrize("text, expected", [
    ("DataSomeValuesFrom(d xsd:integer)", dl.DataExists("d", INT)),
    ("DataAllValuesFrom(d xsd:integer)", dl.DataForAll("d", INT)),
    ('DataHasValue(d "1"^^xsd:integer)', dl.DataHasValue("d", _integer(1))),
    ("DataMinCardinality(2 d xsd:integer)", dl.DataAtLeast(2, "d", INT)),
    ("DataMaxCardinality(1 d xsd:integer)", dl.DataAtMost(1, "d", INT)),
    # the range is optional and defaults to rdfs:Literal, as ObjectMinCardinality's
    # filler defaults to owl:Thing
    ("DataMaxCardinality(1 d)", dl.DataAtMost(1, "d", dl.Datatype("rdfs:Literal"))),
    # exact is the pair it abbreviates, as ObjectExactCardinality is
    ("DataExactCardinality(3 d xsd:string)",
     dl.And(dl.DataAtLeast(3, "d", dl.Datatype("xsd:string")),
            dl.DataAtMost(3, "d", dl.Datatype("xsd:string")))),
    ('DataHasValue(d "abc")', dl.DataHasValue("d", L("abc"))),
    ('DataHasValue(d "abc"@en)', dl.DataHasValue("d", L("abc", "xsd:string", "en"))),
    ('DataHasValue(d "a\\"b")', dl.DataHasValue("d", L('a"b'))),
    ('DataHasValue(d "1"^^<http://www.w3.org/2001/XMLSchema#integer>)',
     dl.DataHasValue("d", _integer(1))),
    ("DataSomeValuesFrom(d DataComplementOf(xsd:integer))",
     dl.DataExists("d", dl.DataComplementOf(INT))),
    ('DataSomeValuesFrom(d DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^xsd:integer '
     'xsd:maxExclusive "9"^^xsd:integer))',
     dl.DataExists("d", dl.DatatypeRestriction(INT, (
         ("xsd:minInclusive", _integer(1)), ("xsd:maxExclusive", _integer(9)))))),
])
def test_functional_style_reads_a_data_restriction(text, expected):
    assert dl.parse_owl_functional_class_expression(text) == expected


@pytest.mark.parametrize("text, needle", [
    ('DataHasValue(d "abc"^^xsd:integer)', "not a well-typed xsd:integer"),
    ('DataSomeValuesFrom(d DatatypeRestriction(xsd:string xsd:pattern "a"))', "xsd:pattern"),
    ("DataSomeValuesFrom(d)", "expected a data range"),
    ("DataSomeValuesFrom(d DataIntersectionOf(xsd:integer))", "at least 2"),
    ('DataHasValue(d "1" ^^xsd:integer)', "expected ')'"),         # ^^ must be ADJACENT
])
def test_functional_style_refuses_a_malformed_or_out_of_scope_data_range(text, needle):
    with pytest.raises(dl.OwlFunctionalSyntaxError) as info:
        dl.parse_owl_functional_class_expression(text)
    assert needle in str(info.value)


@pytest.mark.parametrize("concept", _ROUND_TRIP_CONCEPTS + [
    dl.DataExists("d", dl.Datatype("Digit")),
    dl.And(dl.DataAtLeast(2, "d", INT), dl.DataAtMost(2, "d", INT)),
], ids=lambda c: c.to_unicode())
def test_functional_style_round_trips_a_data_concept(concept):
    text = dl.to_owl_functional_class_expression(concept)
    assert dl.parse_owl_functional_class_expression(text) == concept


def _every_data_kind():
    tbox = dl.TBox()
    tbox.add(dl.Atomic("TypicalYear"), dl.DataHasValue("HasNumber", _integer(1)))
    tbox.add_data_property_inclusion("HasYear", "HasNumber")
    tbox.add_disjoint_data_properties("HasNumber", "HasName")
    tbox.add_functional_data_property("HasNumber")
    tbox.add_data_property_domain("HasNumber", dl.Atomic("Factsheet"))
    tbox.add_data_property_range("HasNumber", dl.parse_manchester_data_range("xsd:integer[>= 0]"))
    tbox.add_datatype_definition("Digit", dl.parse_manchester_data_range("xsd:integer[>= 0, <= 9]"))
    abox = (dl.ABox().assert_data("alice", "HasNumber", _integer(400))
            .assert_negative_data("alice", "HasNumber", _integer(401))
            .assert_data("alice", "HasName", L("Alice", "xsd:string", "en"))
            .assert_concept("alice", dl.DataExists("HasNumber", dl.Datatype("Digit"))))
    return tbox, abox


def test_functional_style_round_trips_a_whole_knowledge_base_with_every_data_kind():
    tbox, abox = _every_data_kind()
    text = dl.to_owl_functional(tbox, abox)
    assert "Declaration(DataProperty(HasNumber))" in text
    assert "Declaration(Datatype(Digit))" in text
    assert dl.parse_owl_functional(text) == (tbox, abox)


def test_the_data_writer_covers_every_data_row_of_the_table():
    """A kind the parser reads and the writer drops is a round-trip bug; the
    knowledge base above carries one axiom of each data row."""
    tbox, abox = _every_data_kind()
    for row in _tableau._AXIOM_KINDS:
        if row.layer != "data":
            continue
        holder = tbox if row.holder == "tbox" else abox
        assert len(getattr(holder, row.field)) >= 1, f"{row.kind} has no sample here"


# --------------------------------------------------------------------------- #
# 9. What the image proves, and what it cannot.
# --------------------------------------------------------------------------- #

def test_a_data_property_domain_classifies_the_individual():
    # DataPropertyDomain(HasAmount Alpha) and HasAmount(alice, 3) give Alpha(alice)
    # in every model; Beta(alice) is not entailed (Alpha = Beta = ∅ outside alice).
    tbox = dl.TBox().add_data_property_domain("HasAmount", ALPHA)
    abox = dl.ABox().assert_data("alice", "HasAmount", _integer(3))
    kb = dl.kb_to_fol(tbox, abox)
    alpha = dl.abox_to_fol(dl.ABox().assert_concept("alice", ALPHA))
    beta = dl.abox_to_fol(dl.ABox().assert_concept("alice", BETA))
    assert _status(alpha, kb.premises) == "proved"
    assert _status(beta, kb.premises) == "refuted"


def test_a_functional_data_property_with_two_values_has_no_model():
    # P(alice, 1) ∧ P(alice, 2) with P functional: the two values are the SAME
    # value, but 1 ≠ 2 (the literal-distinctness axiom) -- a contradiction.
    tbox = dl.TBox().add_functional_data_property("HasAmount")
    two = dl.ABox().assert_data("alice", "HasAmount", _integer(1)).assert_data(
        "alice", "HasAmount", _integer(2))
    assert _inconsistent(tbox, two) is True
    # twin: the same value stated twice is ONE term, so it is fine ...
    same = dl.ABox().assert_data("alice", "HasAmount", _integer(1)).assert_data(
        "alice", "HasAmount", L("1.0", "xsd:decimal"))
    assert _inconsistent(tbox, same) is False
    # ... and without functionality two values are fine.
    assert _inconsistent(dl.TBox(), two) is False


def test_disjoint_data_properties_cannot_share_a_pair():
    tbox = dl.TBox().add_disjoint_data_properties("HasA", "HasB")
    shared = dl.ABox().assert_data("alice", "HasA", _integer(1)).assert_data(
        "alice", "HasB", _integer(1))
    apart = dl.ABox().assert_data("alice", "HasA", _integer(1)).assert_data(
        "alice", "HasB", _integer(2))
    assert _inconsistent(tbox, shared) is True
    assert _inconsistent(tbox, apart) is False


def test_a_sub_data_property_carries_its_pairs_up_and_not_down():
    tbox = dl.TBox().add_data_property_inclusion("HasA", "HasB")
    abox = dl.ABox().assert_data("alice", "HasA", _integer(1))
    kb = dl.kb_to_fol(tbox, abox)
    up = dl.abox_to_fol(dl.ABox().assert_data("alice", "HasB", _integer(1)))
    down_kb = dl.kb_to_fol(tbox, dl.ABox().assert_data("alice", "HasB", _integer(1)))
    assert _status(up, kb.premises) == "proved"
    assert _status(dl.abox_to_fol(dl.ABox().assert_data("alice", "HasA", _integer(1))),
                   down_kb.premises) == "refuted"


def test_a_negative_data_assertion_forbids_exactly_its_pair():
    tbox = dl.TBox()
    clash = (dl.ABox().assert_data("alice", "HasA", _integer(3))
             .assert_negative_data("alice", "HasA", _integer(3)))
    fine = (dl.ABox().assert_data("alice", "HasA", _integer(3))
            .assert_negative_data("alice", "HasA", _integer(4)))
    assert _inconsistent(tbox, clash) is True
    assert _inconsistent(tbox, fine) is False


def test_two_disjoint_datatypes_force_a_property_with_a_value_empty():
    # Range integer and range string on one property: a value would be in both.
    tbox = (dl.TBox().add_data_property_range("HasA", INT)
            .add_data_property_range("HasA", dl.Datatype("xsd:string")))
    assert _inconsistent(tbox, dl.ABox().assert_data("alice", "HasA", _integer(3))) is True
    # without a value the property can simply be empty
    assert _inconsistent(tbox, dl.ABox().assert_concept("alice", ALPHA)) is False


def test_a_data_has_value_gci_and_the_existential_it_entails():
    # Alpha ⊑ DataHasValue(HasAmount 1) and alice : Alpha give HasAmount(alice, 1),
    # hence alice : DataExists(HasAmount, xsd:integer) -- the literal 1 is typed
    # xsd:integer by the literal-typing axiom.
    tbox = dl.TBox().add(ALPHA, dl.DataHasValue("HasAmount", _integer(1)))
    abox = dl.ABox().assert_concept("alice", ALPHA)
    kb = dl.kb_to_fol(tbox, abox)
    exists = dl.abox_to_fol(dl.ABox().assert_concept(
        "alice", dl.DataExists("HasAmount", INT)))
    forall_string = dl.abox_to_fol(dl.ABox().assert_concept(
        "alice", dl.DataExists("HasAmount", dl.Datatype("xsd:string"))))
    assert _status(exists, kb.premises) == "proved"
    # Not a string. The integer 1 is in xsd:integer, which is disjoint from
    # xsd:string -- but that disjointness is only STATED for datatypes the
    # knowledge base mentions, and a goal built by hand does not add its
    # datatype to the knowledge base. The status is `refuted`, which over a data
    # layer is NOT a verdict (kb.refutation_is_decisive is False); the way to ask
    # it is kb_to_fol(..., query=[concept]) and kb.instance_goal, which mention
    # the datatype (see tests/test_dl_questions.py).
    assert _status(forall_string, kb.premises) != "proved"
    assert kb.refutation_is_decisive is False


def test_data_number_restrictions_count_distinct_values():
    # Two distinct numbers are two values (literal distinctness), so a
    # DataAtLeast(2) holds; one number is one value, so it does not.
    two = dl.ABox().assert_data("alice", "P", _integer(1)).assert_data("alice", "P", _integer(2))
    one = dl.ABox().assert_data("alice", "P", _integer(1))
    at_least_two = dl.ABox().assert_concept("alice", dl.DataAtLeast(2, "P", INT))
    kb_two, kb_one = dl.kb_to_fol(dl.TBox(), two), dl.kb_to_fol(dl.TBox(), one)
    assert _status(dl.abox_to_fol(at_least_two), kb_two.premises) == "proved"
    assert _status(dl.abox_to_fol(at_least_two), kb_one.premises) == "refuted"
    # DataAtMost(1) with two distinct values has no model
    at_most_one = dl.ABox().assert_concept("alice", dl.DataAtMost(1, "P", INT))
    merged = dl.ABox().assert_data("alice", "P", _integer(1)).assert_data(
        "alice", "P", _integer(2)).assert_concept("alice", dl.DataAtMost(1, "P", INT))
    assert _inconsistent(dl.TBox(), merged) is True
    assert _inconsistent(dl.TBox(), at_most_one) is False


# -- the image is sound, not complete: facets are decided by atp.z3_arith ---------

def test_a_refuted_verdict_over_a_data_layer_is_not_a_verdict_and_z3_arith_decides_the_facet():
    # HasAmount(alice, 15) with a range ≤ 9 is OWL-INCONSISTENT (15 ≤ 9 is false).
    # To api.prove ≤ is an uninterpreted predicate, so the IMAGE has a model and
    # `refuted` ("it has a model") comes back for a knowledge base OWL 2 has none
    # of. That is the documented limit -- the image is SOUND (everything it proves
    # holds), not COMPLETE -- and it is what kb.refutation_is_decisive says: False
    # whenever there is a data layer, so this `refuted` is not an answer about OWL.
    # (This test used to assert that the image missed the inconsistency as if it
    # were a result; it asserts the property that makes the miss harmless.) The
    # arithmetic decides the facet directly.
    tbox = dl.TBox().add_data_property_range(
        "HasAmount", dl.parse_manchester_data_range("xsd:integer[<= 9]"))
    abox = dl.ABox().assert_data("alice", "HasAmount", _integer(15))
    kb = dl.kb_to_fol(tbox, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "refuted"        # missed by the prover
    assert kb.refutation_is_decisive is False
    le = Atom("≤", (Number(15), Number(9)))
    assert is_valid_arith(le, sort="int", timeout=TIMEOUT_MS) is False
    assert is_valid_arith(FNot(le), sort="int", timeout=TIMEOUT_MS) is True


@pytest.mark.parametrize("build, concept, owl_entails_it", [
    # Every row: OWL 2 ENTAILS the instance (hand-derived next to it), and the
    # image answers `refuted` because it does not state the fact the derivation
    # needs -- which is why `refuted` is no verdict over a data layer. When the
    # image states the fact the row flips to `proved`: update this table then.
    #
    # range integer[>= 10], HasN(a, 15): 15 is an integer, 15 ≥ 10, and 10 ≥ 3,
    # so a has a value in integer[>= 3]. The image has no ground comparison
    # 15 ≥ 3 (≥ is uninterpreted).
    (lambda: (dl.TBox().add_data_property_range(
        "HasN", dl.parse_manchester_data_range("xsd:integer[>= 10]")),
        dl.ABox().assert_data("a", "HasN", _integer(15))),
     dl.DataExists("HasN", dl.parse_manchester_data_range("xsd:integer[>= 3]")), True),
    # d(a, "1.0"^^xsd:decimal): the value 1 IS an integer (the value spaces overlap)
    (lambda: (dl.TBox(), dl.ABox().assert_data("a", "d", L("1.0", "xsd:decimal"))),
     dl.DataExists("d", INT), True),
    # d(a, "5"^^xsd:int): 5 is a non-negative integer
    (lambda: (dl.TBox(), dl.ABox().assert_data("a", "d", L("5", "xsd:int"))),
     dl.DataExists("d", dl.Datatype("xsd:nonNegativeInteger")), True),
    # d(a, "-1"^^xsd:int): -1 is a negative integer
    (lambda: (dl.TBox(), dl.ABox().assert_data("a", "d", L("-1", "xsd:int"))),
     dl.DataExists("d", dl.Datatype("xsd:negativeInteger")), True),
], ids=["facet-order", "decimal-is-integer", "int-is-non-negative", "int-is-negative"])
def test_the_limit_of_the_image_is_stated_by_the_property(build, concept, owl_entails_it):
    tbox, abox = build()
    kb = dl.kb_to_fol(tbox, abox, query=[concept])
    assert owl_entails_it is True
    assert _status(kb.instance_goal("a", concept), kb.premises) == "refuted"
    assert kb.refutation_is_decisive is False


def test_the_inconsistency_of_a_value_below_a_range_bound_is_missed_too():
    # range integer[>= 10] and HasN(a, 5): OWL 2 inconsistent (5 ≥ 10 is false);
    # the image has a model. The twin with 15 is consistent in both.
    tbox = dl.TBox().add_data_property_range(
        "HasN", dl.parse_manchester_data_range("xsd:integer[>= 10]"))
    below = dl.kb_to_fol(tbox, dl.ABox().assert_data("a", "HasN", _integer(5)))
    assert _status(FNot(below.formula), below.axioms) == "refuted"
    assert below.refutation_is_decisive is False
    within = dl.kb_to_fol(tbox, dl.ABox().assert_data("a", "HasN", _integer(15)))
    assert _status(FNot(within.formula), within.axioms) == "refuted"


def _entails(sub: str, sup: str, sort: str) -> bool:
    v = Variable("v")
    image = Quantifier("∀", v, Implies(
        dl.datarange_to_fol(dl.parse_manchester_data_range(sub), v),
        dl.datarange_to_fol(dl.parse_manchester_data_range(sup), v)))
    return is_valid_arith(image, sort=sort, timeout=TIMEOUT_MS)


@pytest.mark.parametrize("sub, sup, sort, holds", [
    # [18, 99) is inside [0, ∞) over the integers, and not the other way round.
    ("xsd:integer[>= 18, < 99]", "xsd:integer[>= 0]", "int", True),
    ("xsd:integer[>= 0]", "xsd:integer[>= 18, < 99]", "int", False),
    # Over the INTEGERS v > 0 is v ≥ 1; over the reals it is not (v = 0.5). The
    # datatype predicate itself is uninterpreted for the arithmetic, so it is the
    # solver's SORT that says whether v can be a half.
    ("xsd:integer[> 0]", "xsd:integer[>= 1]", "int", True),
    ("xsd:integer[> 0]", "xsd:integer[>= 1]", "real", False),
    ("xsd:decimal[> 0]", "xsd:decimal[>= 1]", "real", False),
    # a facet pair that is EMPTY (nothing is above 5 and below 3) is inside anything
    ("xsd:integer[> 5, < 3]", "xsd:integer[> 100]", "int", True),
])
def test_a_facet_entailment_is_decided_by_the_arithmetic(sub, sup, sort, holds):
    assert _entails(sub, sup, sort) is holds


# --------------------------------------------------------------------------- #
# The glyph parser refuses what it would otherwise silently misread.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "∃d.xsd:integer", "∀d.rdfs:Literal", "≥2 d.xsd:string", "A ⊓ ∃d.xsd:decimal",
])
def test_the_glyph_parser_refuses_a_built_in_datatype_in_class_position(text):
    # `∃d.xsd:integer` is the rendering of BOTH DataExists(d, xsd:integer) and
    # Exists(d, Atomic("xsd:integer")). Reading it as the second would be the
    # silent misreading dl.parse_manchester had for `d some xsd:integer`.
    with pytest.raises(dl.ConceptSyntaxError, match="DATATYPE, not a class"):
        dl.parse_concept(text)


def test_the_glyph_parser_is_unchanged_for_a_class_of_any_other_name():
    assert dl.parse_concept("∃d.Digit") == dl.Exists("d", dl.Atomic("Digit"))
    assert dl.parse_concept("∃r.A ⊓ B") == dl.And(dl.Exists("r", dl.Atomic("A")), dl.Atomic("B"))
