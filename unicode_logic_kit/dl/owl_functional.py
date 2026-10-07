"""A parser/renderer for the **OWL 2 Functional-Style Syntax**, restricted to ALCHQ.

`OWL 2 Functional-Style Syntax <https://www.w3.org/TR/owl2-syntax/#Functional-Style_Syntax>`_
is the W3C-standardised, S-expression-shaped ``Keyword(arg arg ...)`` concrete
syntax for a whole OWL 2 *ontology document* — Declarations, an ``Ontology(...)``
wrapper, and a flat list of axioms — as opposed to
:mod:`unicode_logic_kit.dl.owl_manchester`'s frame-based, keyword-infix Manchester
Syntax, which this module otherwise mirrors closely: same recursive-descent
style, same "refuse loudly, name the construct" convention, and the same
treatment of prefixed/full-IRI names as opaque :class:`~unicode_logic_kit.dl.concepts.Atomic`/
role/individual strings, with no RDF-graph or IRI-resolution machinery. This is
the *OWL bridge, part 2*: it reads/writes exactly the ALCHQ-expressible fragment
of a Functional-Style ontology document into/from :class:`~unicode_logic_kit.dl.tableau.TBox`/
:class:`~unicode_logic_kit.dl.tableau.ABox`, plus a standalone class-expression
entry point analogous to :func:`~unicode_logic_kit.dl.owl_manchester.parse_manchester`.

Supported fragment (ALCHQ — this kit's DL fragment, see
:mod:`unicode_logic_kit.dl.tableau`'s module docstring for the RBox/counting
machinery this reduces to):

    - **Document shell**: zero or more ``Prefix(pfx:=<iri>)`` lines (parsed and
      discarded — see "IRIs and names" below), then one
      ``Ontology(<iri>? <version-iri>? axiom*)`` wrapper (both IRIs optional and,
      like the prefixes, discarded: this module carries no ontology-metadata
      state, only the TBox/ABox content);
    - **Class expressions**: ``owl:Thing``/``owl:Nothing`` (⊤/⊥, either the
      abbreviated spelling or the resolved full IRI —
      ``<http://www.w3.org/2002/07/owl#Thing>``/``...#Nothing``);
      ``ObjectIntersectionOf(CE CE+)``, ``ObjectUnionOf(CE CE+)`` (n-ary,
      folding **left** into the binary :class:`~unicode_logic_kit.dl.concepts.And`/
      :class:`~unicode_logic_kit.dl.concepts.Or` AST, matching
      :mod:`unicode_logic_kit.dl.owl_manchester`'s documented left-fold for
      ``and``/``or`` chains); ``ObjectComplementOf(CE)``;
      ``ObjectSomeValuesFrom(OPE CE)``, ``ObjectAllValuesFrom(OPE CE)``,
      ``ObjectHasValue(OPE a)`` (a value restriction ->
      :class:`~unicode_logic_kit.dl.concepts.HasValue`, a concept kind of its own
      and NOT ``ObjectSomeValuesFrom(OPE ObjectOneOf(a))``, which stays
      refused -- see that class's docstring);
      ``ObjectMinCardinality(n OPE CE?)``, ``ObjectMaxCardinality(n OPE CE?)``,
      ``ObjectExactCardinality(n OPE CE?)`` (the qualifying class-expression
      argument is OPTIONAL per the W3C grammar's ``'(' n ObjectPropertyExpression
      ClassExpression? ')'`` production, defaulting to ``owl:Thing`` when
      omitted — both the 2-arg "unqualified" and 3-arg "qualified" spellings are
      accepted on read; see "Qualified number restrictions" below); atomic names
      (IRI or prefixed name, taken verbatim — see "IRIs and names").
    - **Axioms**: ``SubClassOf(CE CE)`` -> ``TBox.add``; ``EquivalentClasses(CE
      CE+)`` -> a chain of pairwise ``TBox.add_equivalence`` calls (sound: OWL's
      n-ary ``EquivalentClasses`` is defined as pairwise equivalence — see
      "EquivalentClasses and DisjointClasses" below); ``DisjointClasses(CE CE+)``
      -> reduced to one ``SubClassOf(ObjectIntersectionOf(Ci Cj) owl:Nothing)``
      per unordered pair, since ALCHQ has no primitive "disjoint" TBox axiom
      (see the same section); ``SubObjectPropertyOf(OPE OPE)`` ->
      ``TBox.add_role_inclusion``; ``TransitiveObjectProperty(OPE)`` ->
      ``TBox.add_transitive_role``; ``ObjectPropertyDomain(OPE CE)`` /
      ``ObjectPropertyRange(OPE CE)`` -> ``TBox.add_role_domain`` /
      ``TBox.add_role_range`` (stored NATIVELY in the role box, not desugared
      into the equivalent GCI -- see ``TBox.add_role_domain``);
      ``SameIndividual(a1 a2+)`` -> a CONSECUTIVE chain of
      ``ABox.assert_same`` calls (sound because equality is transitive, so the
      chain entails every pair -- the same argument ``EquivalentClasses`` uses,
      and deliberately NOT ``DifferentIndividuals``' all-pairs expansion);
      ``NegativeObjectPropertyAssertion(OPE a b)`` ->
      ``ABox.assert_negative_role``; ``ClassAssertion(CE a)`` ->
      ``ABox.assert_concept``; ``ObjectPropertyAssertion(OPE a b)`` ->
      ``ABox.assert_role``; the DATA layer -- ``DataSomeValuesFrom(DPE DR)``,
      ``DataAllValuesFrom(DPE DR)``, ``DataHasValue(DPE lt)``,
      ``DataMin/Max/ExactCardinality(n DPE DR?)`` as class expressions (the exact
      form desugared to ``DataAtLeast ⊓ DataAtMost``), the data ranges
      ``DataIntersectionOf``/``DataUnionOf``/``DataComplementOf``/``DataOneOf``/
      ``DatatypeRestriction`` with typed literals (``"400"^^xsd:integer``,
      ``"abc"``, ``"abc"@en``), and ``SubDataPropertyOf``,
      ``EquivalentDataProperties``, ``DisjointDataProperties``,
      ``FunctionalDataProperty``, ``DataPropertyDomain``, ``DataPropertyRange``,
      ``DatatypeDefinition``, ``DataPropertyAssertion`` and
      ``NegativeDataPropertyAssertion`` (see "The data layer" below);
      ``DifferentIndividuals(a1 a2+)`` -> **every**
      pairwise ``ABox.assert_distinct`` (all C(k, 2) pairs, not just a
      consecutive chain — see "DifferentIndividuals" below, this is a
      completeness requirement, not a style choice); ``Declaration(Class(...)
      / ObjectProperty(...) / NamedIndividual(...))`` parsed and discarded
      (declarations carry no ALCHQ-relevant content, since
      :mod:`unicode_logic_kit.dl.concepts`'s ``Atomic``/role/individual names are
      already untyped strings — this is not a silent weakening, just a no-op
      the W3C spec itself defines as non-restrictive); axiom-level and
      standalone ``Annotation(...)``/``AnnotationAssertion(...)`` parsed and
      discarded (annotations are explicitly non-logical in OWL 2, so dropping
      them is not a "weaker than requested" translation of truth-bearing
      content) — an axiom's own leading ``axiomAnnotations`` (e.g.
      ``SubClassOf(Annotation(rdfs:label "x") A B)``) are skipped the same way,
      before its real arguments are parsed.

Rejected loudly, one :class:`OwlFunctionalUnsupportedError` per construct,
naming it by its OWL keyword (mirrors
:mod:`unicode_logic_kit.dl.owl_manchester`'s messages):
``ObjectInverseOf`` (inverse roles — ALCHQ has none; the ONE place it is read is
either side of a ``SubObjectPropertyOf``, where ``r ⊑ s⁻`` is a genuinely
different axiom from ``r ⊑ s`` that a ``TBox`` holds, ``rbox_to_fol`` renders and
the tableau then refuses BY NAME at query time), ``ObjectHasSelf``, ``ObjectOneOf`` (nominals), ``HasKey``, ``DisjointUnion``,
an OWL 2 BUILT-IN property name in any non-tautological position, anonymous
individuals (``_:nodeID``), and inside the data layer an out-of-scope facet
(``xsd:pattern``, the length facets, an ordering facet on a non-numeric base)
or an ill-typed literal -- each by name, from
:class:`~unicode_logic_kit.dl.datatypes.UnsupportedDatatypeError`. Also refused, by
name and with the wording :mod:`unicode_logic_kit.dl.owl_manchester` uses: a
BUILT-IN datatype name (``xsd:integer``, either namespace spelling) where a CLASS
is wanted, and ``owl:Thing``/``owl:Nothing`` where a DATA RANGE is wanted --
OWL 2 does not let one name be both a class and a datatype -- and a literal with
no first-order term (``xsd:float``/``xsd:double``, a decimal no ``Number`` holds
exactly), so that an axiom this reader ACCEPTS is one the FOL image can render.

CONSUMED without logical content (not refused: nothing is lost) -- reported by
:func:`parse_owl_functional_axioms` in ``OwlFunctionalResult.consumed``, one
:class:`ConsumedAxiom` each: ``SubAnnotationPropertyOf``,
``AnnotationPropertyDomain`` and ``AnnotationPropertyRange`` (annotation
properties carry no content under the OWL 2 direct semantics, so these are
exactly what ``AnnotationAssertion`` already was), and a TAUTOLOGICAL property
inclusion into ``owl:topObjectProperty``/``owl:topDataProperty`` or out of
``owl:bottomObjectProperty``/``owl:bottomDataProperty``.

The data layer
---------------
The data half of OWL 2 -- see :mod:`unicode_logic_kit.dl.datatypes` -- is stored
(``TBox.add_data_property_*``, ``ABox.assert_data``) and translated by the FOL
image, and REFUSED by the in-house tableau, which has no data domain. A parser
never refuses an axiom KIND, so all of it is read here. The reading of a
literal is OWL's own: ``"lexical"^^datatype`` (a full-IRI datatype is
canonicalised, so ``<http://www.w3.org/2001/XMLSchema#integer>`` and
``xsd:integer`` are one datatype), a plain ``"text"`` is an ``xsd:string``, and
``"text"@en`` a language-tagged string. A BARE numeral such as ``42`` is not a
literal in this syntax (it is in Manchester Syntax) and is a syntax error.

A whole ontology, with the refusals as data
--------------------------------------------
:func:`parse_owl_functional` is STRICT: it raises on the FIRST construct
outside the fragment, so a real ontology carrying one ``DataPropertyRange``
yields no TBox at all. :func:`parse_owl_functional_axioms` is the per-axiom
reader — one tokenization, one pass, recovering at AXIOM boundaries — and
returns an :class:`OwlFunctionalResult` holding the TBox/ABox it could build
plus one :class:`RefusedAxiom` per axiom it could not, each naming the
construct, its offset and its own source text. It recovers from
:class:`OwlFunctionalUnsupportedError` and from NOTHING else: malformed input
still raises, because recovering from an unbalanced paren could drop arbitrary
content. See that function for the contract.

IRIs and names
---------------
Exactly :mod:`unicode_logic_kit.dl.owl_manchester`'s convention (both readers store
one IRI as ONE Python string, the IRI WITHOUT its angle brackets, in every
position), adapted to two
concrete-syntax spellings instead of one: a **full IRI** token, ``<...>``, is
stored as the kit name with the angle brackets stripped (``<http://example.org/Person>``
-> ``Atomic("http://example.org/Person")``); a **prefixed (or otherwise bare)
name** token, e.g. ``ex:Person`` or a plain ``Person``, is stored VERBATIM, with
no prefix resolution at all — this module carries no ``Prefix(...)`` -> IRI
table, since (like Manchester's ``owl:Thing``/``owl:Nothing`` special case) the
kit's ``Atomic``/role/individual names are opaque strings, not resolved IRIs.
Rendering back (:func:`to_owl_functional_class_expression`, :func:`to_owl_functional`)
picks one of the two spellings DETERMINISTICALLY, by a single rule: a name
containing ``"://"`` (i.e., shaped like an absolute IRI with a network scheme) is
wrapped back in ``<...>``; every other name is written bare when the tokenizer
reads it as ONE plain word, and in ``<...>`` otherwise. The brackets are the
syntax's own escape and carry ANY name that has no ``>`` in it — whitespace, the
structural characters ``()=<>"``, the empty name, a name spelled like a keyword
the reader dispatches on (``ObjectUnionOf``, ``Annotation``, ...) and an
anonymous-individual label (``_:x``) alike — because the reader takes everything
up to the first ``>`` for one name. So
``parse_owl_functional_class_expression(to_owl_functional_class_expression(c))
== c`` holds for every concept ``c`` built from any name string that has a spelling
(see "Round-trip guarantee" below); the RENDERED spelling need not match the
ORIGINALLY PARSED spelling (a full-IRI ``owl:Thing`` reads as
:class:`~unicode_logic_kit.dl.concepts.Top` and always renders back as the bare
``"owl:Thing"``, for instance), only the resulting
:class:`~unicode_logic_kit.dl.concepts.Concept`/``TBox``/``ABox`` structure must
match, which is exactly the oracle the tests check.

A name with NO spelling is refused, by name, with a :class:`ValueError`: a name
holding ``>`` (which ends a full IRI, and a bare ``>`` is no part of a word); a
name that ALREADY carries its brackets (a hand-built ``"<http://x.org/A>"``),
since ``<...>`` reads back as the text between the brackets, which is another
name, and ``<<...>>`` is refused by the reader; and ``owl:Thing`` /
``owl:Nothing`` (in either spelling) as a CLASS, which the reader makes the top
and the bottom class however they are written (as a role or an individual they
are ordinary names). The same rule, over a different escape, is
:mod:`unicode_logic_kit.dl.owl_manchester`'s "Names with no spelling".

EquivalentClasses and DisjointClasses
---------------------------------------
Neither is a primitive of :class:`~unicode_logic_kit.dl.tableau.TBox` (which only
has ``add`` (⊑) and ``add_equivalence`` (⊑ both ways) — see its module
docstring), so both n-ary OWL axioms are DECOMPOSED at parse time:
``EquivalentClasses(C1 C2 ... Ck)`` becomes the chain ``add_equivalence(C1, C2)``,
``add_equivalence(C2, C3)``, ..., ``add_equivalence(C{k-1}, Ck)`` — sound
because pairwise-consecutive equivalence already entails the full mutual
equivalence of every pair by transitivity of ⊑, and it is what
:func:`to_owl_functional` can deterministically detect and re-fold on the way
out (see below). ``DisjointClasses(C1 ... Ck)`` becomes one
``add(C_i ⊓ C_j, ⊥)`` GCI per UNORDERED pair ``i < j`` (all C(k, 2) of them,
not a chain — disjointness has no transitive shortcut the way equivalence
does: knowing C1⊓C2⊑⊥ and C2⊓C3⊑⊥ says nothing about C1⊓C3), which is exactly
what "``DisjointClasses`` pairwise" means model-theoretically and is always
expressible in ALCHQ (conjunction and ⊥ are both primitive), hence
unconditionally reducible — there is no case where this module rejects
``DisjointClasses`` outright, unlike the several other axiom kinds it does
reject by name. :func:`to_owl_functional` does not attempt to re-detect and
re-fold a set of GCIs back into a single ``DisjointClasses(...)`` axiom (that
would require solving a covering problem over ``TBox.inclusions`` with no
guarantee of a unique answer) — it always renders each ``TBox.inclusions``
entry as its own axiom, using the ``EquivalentClasses`` re-fold ONLY where the
adjacent-pair shape ``add_equivalence`` itself produces is recognised (see
:func:`_render_axioms`); every other inclusion, including one that
happens to look like ``C ⊓ D ⊑ ⊥``, is rendered as a plain ``SubClassOf``.
This asymmetry (read supports both compact forms, write only re-folds one)
is deliberate and harmless: :class:`~unicode_logic_kit.dl.tableau.TBox` equality
(a plain ``@dataclass``) only ever compares the underlying ``inclusions``
list, never which OWL keyword produced it, so the round-trip oracle
``parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)`` holds
regardless of which axiom spelling is chosen on the way out.

DifferentIndividuals
----------------------
:class:`~unicode_logic_kit.dl.tableau.ABox` has no unique name assumption (see
"Qualified number restrictions" in :mod:`unicode_logic_kit.dl.tableau`'s module
docstring), so ``a ≠ b`` is a genuine semantic fact that must be asserted, not
inferred from two individuals merely having different names. OWL's
``DifferentIndividuals(a1 ... ak)`` asserts ALL of them pairwise distinct, so
reading it as anything less than every one of the C(k, 2) pairs — e.g. only a
consecutive chain, the way ``EquivalentClasses`` is decomposed above — would
be a silent WEAKENING of what the axiom actually states (equivalence has a
free transitive closure through ⊑; distinctness has no such closure: knowing
``a ≠ b`` and ``b ≠ c`` says nothing about whether ``a`` and ``c`` might still
be forced equal), which the kit's honesty convention forbids. So every pair is
asserted explicitly. :func:`to_owl_functional`, symmetrically, does not try to
re-cluster ``ABox.distinct_assertions`` back into one k-ary
``DifferentIndividuals(...)`` per clique (an unnecessary complication — see
the DisjointClasses note above for the identical reasoning): it renders each
``distinct_assertions`` entry as its own binary ``DifferentIndividuals(a b)``,
which is itself perfectly legal OWL 2 syntax (the W3C grammar's minimum arity
is two, not three) and round-trips to the identical single pair.

``SameIndividual(a1 ... ak)`` is the CONTRAST that makes the argument above
concrete: equality IS transitive, so the consecutive chain ``a1 = a2``,
``a2 = a3``, … already entails every pair, and reading it that way is not a
weakening. Its renderer is the same one-binary-line-per-pair shape, for the
same reason.

Qualified number restrictions
------------------------------
Identical semantics to :mod:`unicode_logic_kit.dl.owl_manchester`'s ``min``/
``max``/``exactly``: ``ObjectMinCardinality``/``ObjectMaxCardinality`` parse
into :class:`~unicode_logic_kit.dl.concepts.AtLeast`/:class:`~unicode_logic_kit.dl.concepts.AtMost`,
and ``ObjectExactCardinality(n OPE CE?)`` desugars AT PARSE TIME into
``AtLeast(n, role, CE) ⊓ AtMost(n, role, CE)`` (there is no separate "exactly"
AST node — see :mod:`unicode_logic_kit.dl.concepts`). Unlike
:func:`~unicode_logic_kit.dl.owl_manchester.to_manchester` (which omits the
qualifying-class text when it is ⊤, for terseness),
:func:`to_owl_functional_class_expression` always renders the explicit 3-arg
qualified form — S-expression syntax has no terseness pressure the way
Manchester's inline keyword notation does, and always emitting one shape
keeps the renderer simpler with no loss of round-trip fidelity (the 2-arg
unqualified form is still accepted on READ, defaulting to ``owl:Thing``,
exactly like Manchester's bare ``role min n``). See ``dl.tableau``'s
"Qualified number restrictions" section for the reasoning side, in particular
the SIMPLE ROLES restriction (a number restriction on a transitive role, or
one with a transitive sub-role, is rejected there — by
:class:`~unicode_logic_kit.dl.tableau.NonSimpleRoleError` — not by this module,
which only builds the AST).

No ambiguity, no precedence
-----------------------------
Unlike :mod:`unicode_logic_kit.dl.owl_manchester` (whose ``_PREC`` lattice and
``_paren`` helper resolve a genuinely ambiguous infix grammar), OWL 2
Functional-Style Syntax has NO precedence to resolve: every compound
expression is ``Keyword(arg arg ...)``, fully parenthesised by the keyword
itself. :func:`_render_ce` therefore needs no precedence table and never
omits or inserts a parenthesis conditionally — the keyword IS the
parenthesisation.

Round-trip guarantee
---------------------
``parse_owl_functional_class_expression(to_owl_functional_class_expression(c))
== c`` for every ALCHQ concept ``c``, and
``parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)`` for
every ALCHQ ``(tbox, abox)`` pair — see ``tests/test_owl_functional.py`` for
the hand-checked cases, including one per constructor, nested expressions, and
a full document with every supported axiom kind.

The one exception is a knowledge base the READER refuses on principle: a
hand-built ``Atomic`` named like a built-in datatype (``xsd:integer`` is a
datatype, never a class), a datatype named ``owl:Thing``/``owl:Nothing``, or a
literal with no first-order term (``xsd:float``/``xsd:double``, a decimal no
``Number`` holds exactly). :func:`to_owl_functional` writes such a knowledge base
as it was given, and :func:`parse_owl_functional` refuses the text by name on the
way back in — loudly, never as a different knowledge base.
"""

import functools
from dataclasses import dataclass
from dataclasses import fields as dataclass_fields
from typing import Dict, List, Optional, Sequence, Set, Tuple, Union

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DataExists, DataForAll, DataHasValue,
    DataAtLeast, DataAtMost, DATA_CONCEPTS,
)
from .datatypes import (
    DataRange, Datatype, DatatypeRestriction, DataOneOf, DataComplementOf,
    DataIntersectionOf, DataUnionOf, Literal, UnsupportedDatatypeError,
    is_builtin_datatype, render_datarange_fs, render_literal_fs,
)
from .tableau import (
    TBox, ABox, RESERVED_TOP_ROLES, is_tautological_role_inclusion,
    reserved_role, _reject_abox_roles, _reject_concept_roles_deep,
    _tbox_class_expressions, _validate_data_box, _validate_role_box,
)
from .translate import _collect_vocabulary

__all__ = [
    "parse_owl_functional", "parse_owl_functional_axioms", "to_owl_functional",
    "parse_owl_functional_class_expression", "to_owl_functional_class_expression",
    "OwlFunctionalResult", "RefusedAxiom", "ConsumedAxiom",
    "OwlFunctionalSyntaxError", "OwlFunctionalUnsupportedError",
]


class OwlFunctionalSyntaxError(ValueError):
    """Raised by this module's parser on malformed input *and* on syntax that is
    valid OWL 2 Functional-Style Syntax but falls outside ALCHQ (see the module
    docstring's "Rejected"). Always a :class:`ValueError` subclass with a
    message naming the specific offending construct and its position in the
    input, per the kit's honesty convention.

    :class:`OwlFunctionalUnsupportedError` is the SUBCLASS raised for the
    second case alone — "valid OWL 2, outside this fragment" — so a caller can
    tell it from genuinely malformed input. Catching this class still catches
    both, which is why adding the subclass broke no existing call site.
    """


class OwlFunctionalUnsupportedError(OwlFunctionalSyntaxError):
    """Raised for input that is valid OWL 2 Functional-Style Syntax but falls
    outside ALCHQ — as opposed to input that is malformed.

    A subclass of :class:`OwlFunctionalSyntaxError`, deliberately: every
    existing ``except OwlFunctionalSyntaxError`` and every ``pytest.raises`` in
    the suite keeps working unchanged.

    The distinction is what makes :func:`parse_owl_functional_axioms` possible
    and SAFE. That reader recovers from this class and from nothing else: a
    construct outside the fragment is a question about the FRAGMENT, and
    skipping it loses exactly the axiom it names, which the result reports. A
    tokenizer error, an unbalanced paren, a missing ``Ontology(`` or a bad name
    is a question about the DOCUMENT, and recovering from one of those could
    silently drop arbitrary content — so those still raise.

    Attributes:
        keyword: The offending construct's own OWL keyword (or name), e.g.
            ``"ObjectHasSelf"``. For a construct nested inside an axiom this is
            the INNER keyword, not the axiom's.
        position: Its 0-based character offset in the parsed text, or ``-1``
            when the raising site has no token to point at.
    """

    def __init__(self, message: str, keyword: str = "", position: int = -1):
        super().__init__(message)
        self.keyword = keyword
        self.position = position


# --------------------------------------------------------------------------- #
# Tokenizer: '(', ')', '=', '<full IRI>', '"string literal"', and WORD (a
# maximal run of everything else -- prefixed names, plain names, and every
# axiom/class-expression keyword alike; keywords are matched by exact string
# comparison in the parser, not pre-classified here, since the grammar is a
# flat prefix S-expression with no infix operators to disambiguate).
# --------------------------------------------------------------------------- #

_STRUCT_CHARS = set("()=<>\"")

# A Token is (type: str, value: str, pos: int).
_Token = Tuple[str, str, int]


def _tokenize(text: str) -> List[_Token]:
    """Split ``text`` into structural/IRI/string/word tokens plus a trailing
    EOF sentinel (whose ``pos`` is ``len(text)``, for error messages).
    """
    tokens: List[_Token] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "(":
            tokens.append(("LPAREN", ch, i))
            i += 1
            continue
        if ch == ")":
            tokens.append(("RPAREN", ch, i))
            i += 1
            continue
        if ch == "=":
            tokens.append(("EQUALS", ch, i))
            i += 1
            continue
        if ch == "<":
            start = i
            end = text.find(">", i + 1)
            if end == -1:
                raise OwlFunctionalSyntaxError(
                    f"parse_owl_functional: unterminated IRI ('<...>' never "
                    f"closed) starting at position {start} in {text!r}")
            tokens.append(("IRI", text[i + 1:end], start))
            i = end + 1
            continue
        if ch == '"':
            start = i
            j = i + 1
            buf = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    buf.append(text[j:j + 2])
                    j += 2
                else:
                    buf.append(text[j])
                    j += 1
            if j >= n:
                raise OwlFunctionalSyntaxError(
                    f"parse_owl_functional: unterminated string literal "
                    f"starting at position {start} in {text!r}")
            tokens.append(("STRING", "".join(buf), start))
            i = j + 1
            continue
        if ch == ">":
            raise OwlFunctionalSyntaxError(
                f"parse_owl_functional: unexpected '>' at position {i} in {text!r}")
        start = i
        while i < n and not text[i].isspace() and text[i] not in _STRUCT_CHARS:
            i += 1
        tokens.append(("WORD", text[start:i], start))
    tokens.append(("EOF", "", n))
    return tokens


# --------------------------------------------------------------------------- #
# Recursive-descent parser.
# --------------------------------------------------------------------------- #

_TOP_SPELLINGS = {"owl:Thing", "http://www.w3.org/2002/07/owl#Thing"}
_BOTTOM_SPELLINGS = {"owl:Nothing", "http://www.w3.org/2002/07/owl#Nothing"}

# Class-expression keywords rejected outright (outside ALCHQ), keyed by their
# OWL name -> a human-readable phrase naming the construct for the error message.
_REJECTED_CE = {
    "ObjectHasSelf": "Self restrictions (ObjectHasSelf)",
    "ObjectOneOf": "nominal concepts (ObjectOneOf)",
    "ObjectInverseOf": "inverse object properties (ObjectInverseOf)",
}

# The seven OWL 2 object-property CHARACTERISTIC axioms, each a one-role
# keyword, mapped to the TBox builder that stores it. One table rather than
# seven parse branches: they differ only in the method name, and the tableau's
# own decision about each (decide / internalise / refuse by name) is recorded
# in dl.tableau._AXIOM_KINDS, not here -- a PARSER never refuses a KIND.
_CHARACTERISTIC_AXIOMS = {
    "TransitiveObjectProperty": "add_transitive_role",
    "SymmetricObjectProperty": "add_symmetric_role",
    "AsymmetricObjectProperty": "add_asymmetric_role",
    "ReflexiveObjectProperty": "add_reflexive_role",
    "IrreflexiveObjectProperty": "add_irreflexive_role",
    "FunctionalObjectProperty": "add_functional_role",
    "InverseFunctionalObjectProperty": "add_inverse_functional_role",
}

# Axiom keywords rejected outright (outside ALCHQ), same convention.
_REJECTED_AXIOMS = {
    "HasKey": "keys (HasKey)",
    "DisjointUnion": "disjoint union class axioms (DisjointUnion)",
}

# The annotation-property axioms. Annotation properties carry no content under
# the OWL 2 direct semantics (annotations are explicitly non-logical), so these
# are exactly what AnnotationAssertion already was: read, consumed, and --
# unlike a Declaration -- REPORTED, as a ConsumedAxiom, so they do not vanish.
_ANNOTATION_PROPERTY_AXIOMS = frozenset({
    "SubAnnotationPropertyOf", "AnnotationPropertyDomain", "AnnotationPropertyRange",
})


#: The keywords that start a data range: a word like these in a position that
#: wants a datatype NAME is a mistake worth naming, not a datatype called that.
_DATA_RANGE_KEYWORDS = frozenset({
    "DataIntersectionOf", "DataUnionOf", "DataComplementOf", "DataOneOf",
    "DatatypeRestriction",
})

#: Every bare word the reader takes for a KEYWORD where a name could stand: the
#: class-expression keywords, the data-range keywords, ``ObjectInverseOf`` (an
#: object property expression) and ``Annotation`` (skipped in front of every
#: axiom's first argument). A name spelled like one of them is written in angle
#: brackets, which the reader takes for a name whatever it says.
_NAME_KEYWORDS = frozenset({
    "ObjectIntersectionOf", "ObjectUnionOf", "ObjectComplementOf",
    "ObjectSomeValuesFrom", "ObjectAllValuesFrom", "ObjectHasValue",
    "ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality",
    "DataSomeValuesFrom", "DataAllValuesFrom", "DataHasValue",
    "DataMinCardinality", "DataMaxCardinality", "DataExactCardinality",
    "Annotation",
}) | frozenset(_REJECTED_CE) | _DATA_RANGE_KEYWORDS


def _unescape_string(raw: str) -> str:
    """The text of a string-literal token with its two OWL 2 escapes undone
    (``\\"`` and ``\\\\``). The tokenizer keeps the escapes in the token's value so
    that the token's SOURCE length is recoverable."""
    out: List[str] = []
    i = 0
    while i < len(raw):
        if raw[i] == "\\" and i + 1 < len(raw) and raw[i + 1] in ('"', "\\"):
            out.append(raw[i + 1])
            i += 2
        else:
            out.append(raw[i])
            i += 1
    return "".join(out)


def _is_tautology_of(sub: str, sup: str, family: str) -> bool:
    """:func:`~unicode_logic_kit.dl.tableau.is_tautological_role_inclusion`,
    restricted to built-ins of ONE family (``"Object"`` or ``"Data"``).

    ``SubDataPropertyOf(P owl:topObjectProperty)`` mixes the families: it is
    ill-typed OWL 2, not a tautology, so it must be refused and not consumed.
    """
    if not is_tautological_role_inclusion(sub, sup):
        return False
    for name in (sub, sup):
        builtin = reserved_role(name)
        if builtin is not None and family not in builtin:
            return False
    return True


def _owl_role_text(role) -> str:
    """``role`` as OWL's functional syntax spells it: the name, or
    ``ObjectInverseOf(name)`` for an :class:`InverseRole`."""
    return f"ObjectInverseOf({role.role})" if isinstance(role, InverseRole) else role


def _tautology_reason(axiom: str, sub, sup) -> str:
    builtin = reserved_role(sup) if reserved_role(sup) in RESERVED_TOP_ROLES else reserved_role(sub)
    sub, sup = _owl_role_text(sub), _owl_role_text(sup)
    return (f"{axiom}({sub} {sup}) is a tautology -- it holds in every "
            f"interpretation because of the built-in property {builtin} -- so "
            f"it constrains nothing (consumed as a documented no-op, and "
            f"reported)")


class _Parser:
    """A single parse of one tokenized input; not re-used across calls."""

    def __init__(self, tokens: List[_Token], text: str):
        self._tokens = tokens
        self._text = text
        self._i = 0
        # The ``DatatypeDefinition`` entries of the axioms ALREADY read, when
        # each axiom is parsed into a scratch ``TBox`` of its own (the lenient
        # reader): a definition is checked against these as well as against the
        # scratch ``TBox``, which holds nothing earlier. Empty for the strict
        # reader, whose one ``TBox`` already holds everything read so far.
        self._earlier_definitions: Sequence[Tuple[str, DataRange]] = ()

    def _peek(self) -> _Token:
        return self._tokens[self._i]

    def _advance(self) -> _Token:
        tok = self._tokens[self._i]
        self._i += 1
        return tok

    def _error(self, message: str) -> OwlFunctionalSyntaxError:
        return OwlFunctionalSyntaxError(f"parse_owl_functional: {message} in {self._text!r}")

    def _expect(self, ttype: str, what: str) -> _Token:
        tok = self._peek()
        if tok[0] != ttype:
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(f"expected {what} but found {found} at position {tok[2]}")
        return self._advance()

    def _expect_word(self, word: str) -> _Token:
        tok = self._peek()
        if tok[0] != "WORD" or tok[1] != word:
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(f"expected {word!r} but found {found} at position {tok[2]}")
        return self._advance()

    def _expect_eof(self) -> None:
        tok = self._peek()
        if tok[0] != "EOF":
            raise self._error(f"unexpected trailing input {tok[1]!r} at position {tok[2]}")

    def _unsupported(self, message: str, keyword: str,
                     position: int) -> OwlFunctionalUnsupportedError:
        """The "valid OWL 2, outside this fragment" error, carrying the
        offending construct and its offset as DATA — see
        :class:`OwlFunctionalUnsupportedError` and
        :func:`parse_owl_functional_axioms`.
        """
        return OwlFunctionalUnsupportedError(
            f"parse_owl_functional: {message} in {self._text!r}",
            keyword=keyword, position=position)

    def _reject(self, what: str, tok: _Token) -> None:
        raise self._unsupported(
            f"{what} is not supported — outside ALCHQ (this kit's DL fragment), "
            f"found {tok[1]!r} at position {tok[2]}", tok[1], tok[2])

    # -- names: full IRIs ('<...>') and prefixed/plain names, taken verbatim -- #

    def _parse_name(self) -> str:
        tok = self._peek()
        if tok[0] == "IRI":
            self._advance()
            return tok[1]
        if tok[0] == "WORD":
            if tok[1].startswith("_:"):
                self._reject("anonymous individuals ('_:nodeID')", tok)
            self._advance()
            return tok[1]
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"expected a name (a full IRI '<...>' or a prefixed/plain name) "
            f"but found {found} at position {tok[2]}")

    def _parse_inclusion_role(self) -> Union[str, InverseRole]:
        """One side of a ``SubObjectPropertyOf``: a role name, or
        ``ObjectInverseOf(name)`` as an :class:`InverseRole`.

        The one position this grammar reads an inverse role in. ``TBox``
        accepts one on either side of a role inclusion (``r ⊑ s⁻`` is a
        different axiom from ``r ⊑ s``) and the writers print it —
        ``dl.to_owl_functional``, the Hets renderer — so a reader that refused
        what the writer wrote would break the round trip. Everywhere else it is
        still refused by name (a characteristic of ``r⁻`` is not, in general,
        the characteristic of ``r``; see ``dl.tableau``'s ``_inverse_advice``).
        The name INSIDE an inverse is an ordinary role name: a built-in is
        refused there, and so is a nested ``ObjectInverseOf``.
        """
        tok = self._peek()
        if tok[0] == "WORD" and tok[1] == "ObjectInverseOf":
            self._advance()
            self._expect("LPAREN", "'('")
            inner = self._parse_object_property_expression()
            self._expect("RPAREN", "')'")
            return InverseRole(inner)
        return self._parse_object_property_expression(allow_reserved=True)

    def _parse_object_property_expression(self, *,
                                          allow_reserved: bool = False) -> str:
        """One ``ObjectPropertyExpression``: a plain role name.

        An OWL 2 BUILT-IN property name is refused here, so EVERY role position
        in the grammar — a restriction's role, an ``ObjectPropertyAssertion``,
        a characteristic's subject — is covered by this one guard rather than
        by each branch remembering to ask. ``allow_reserved=True`` is passed by
        the ``SubObjectPropertyOf`` branch alone, which must read both sides
        before it can tell whether the inclusion is the TAUTOLOGY it consumes
        as a no-op.
        """
        tok = self._peek()
        if tok[0] == "WORD" and tok[1] == "ObjectInverseOf":
            self._reject(_REJECTED_CE["ObjectInverseOf"], tok)
        name = self._parse_name()
        if not allow_reserved:
            self._check_role_name(name, "a role position", tok[2])
        return name

    def _check_role_name(self, role: str, axiom: str, position: int = -1) -> None:
        """Refuse an OWL 2 BUILT-IN property name by name.

        ALCHQ has neither the universal nor the empty role, so a built-in
        cannot be carried as an ordinary role (which is what this parser did
        until 0.30.0: 31 of the OEO axioms translated with a bogus
        uninterpreted ``TopObjectProperty`` predicate). The ONE exception is a
        TAUTOLOGICAL inclusion, consumed as a no-op by the
        ``SubObjectPropertyOf`` branch before this is reached — see
        :func:`~unicode_logic_kit.dl.tableau.is_tautological_role_inclusion` and
        "The OWL 2 built-in roles" in ``dl.tableau``'s module docstring.

        Raises :class:`OwlFunctionalUnsupportedError`, not the plain error: a
        built-in property name is valid OWL 2 that this fragment has no reading
        for, which is exactly the class
        :func:`parse_owl_functional_axioms` recovers from. Without that, one
        such axiom would abort a whole-document read.
        """
        builtin = reserved_role(role)
        if builtin is None:
            return
        builtin_is_data = "Data" in builtin
        axiom_is_data = "data" in axiom.lower()
        if builtin_is_data != axiom_is_data:
            # A DATA built-in in an OBJECT position (or the other way round):
            # ill-typed OWL 2, not the tautology the same inclusion would be
            # between two properties of ONE family -- so it is refused by name
            # and not consumed.
            what = ("the universal property (it relates every pair)"
                    if builtin in RESERVED_TOP_ROLES else
                    "the empty property (it relates no pair at all)")
            remedy = (f"It is also ILL-TYPED OWL 2: {builtin} is "
                      f"{'a data' if builtin_is_data else 'an object'} property "
                      f"and {axiom} takes "
                      f"{'a data' if axiom_is_data else 'an object'} property, "
                      f"so this is refused rather than consumed as the "
                      f"tautology the same inclusion between two "
                      f"{'data' if axiom_is_data else 'object'} properties "
                      f"would be")
        elif builtin in RESERVED_TOP_ROLES:
            what = "the universal property (it relates every pair)"
            remedy = ("An inclusion INTO it is a tautology and IS accepted, as "
                      "a no-op; 'P is universal' is the universal role of "
                      "SROIQ, which breaks the tree-model property and this "
                      "kit does not have it")
        else:
            what = "the empty property (it relates no pair at all)"
            remedy = ("An inclusion OUT OF it is a tautology and IS accepted, "
                      "as a no-op; 'P is empty' is the concept inclusion "
                      "SubClassOf(owl:Thing ObjectAllValuesFrom(P owl:Nothing))")
        raise self._unsupported(
            f"the OWL 2 BUILT-IN property {role!r} ({builtin} — {what}) in "
            f"{axiom} is not supported — outside ALCHQ (this kit's DL "
            f"fragment), which has neither the universal nor the empty role. "
            f"{remedy}", role, position)

    # -- the data layer: data properties, literals, data ranges -------------- #

    def _parse_data_property_expression(self, *,
                                        allow_reserved: bool = False) -> str:
        """One ``DataPropertyExpression``: a plain data property name.

        A data property has no inverse and no expression syntax, so this is a
        name; the OWL 2 BUILT-IN property names are refused in every position
        but the tautological ``SubDataPropertyOf`` one (``allow_reserved``), by
        the same guard the object side uses.
        """
        tok = self._peek()
        name = self._parse_name()
        if not allow_reserved:
            self._check_role_name(name, "a data property position", tok[2])
        return name

    def _parse_data_property_name(self, axiom: str) -> str:
        """One data property that must be an ordinary name, ``axiom`` naming the
        construct in the refusal message."""
        position = self._peek()[2]
        prop = self._parse_data_property_expression(allow_reserved=True)
        self._check_role_name(prop, axiom, position)
        return prop

    def _parse_datatype_name(self) -> str:
        tok = self._peek()
        if tok[0] == "WORD" and tok[1] in _DATA_RANGE_KEYWORDS:
            raise self._error(
                f"expected a datatype name but found the data range "
                f"{tok[1]!r} at position {tok[2]}")
        return self._check_not_a_class_name(self._parse_name(), tok[2])

    def _datatype_construct(self, build, keyword: str, position: int):
        """``build()``, with a data-layer refusal turned into the RECOVERABLE
        :class:`OwlFunctionalUnsupportedError` carrying the offending construct
        as data (an out-of-scope facet is valid OWL 2 this fragment cannot
        translate, not malformed input)."""
        try:
            return build()
        except UnsupportedDatatypeError as exc:
            raise self._unsupported(str(exc), keyword, position) from exc

    def _add_datatype_definition(self, tbox: TBox, name: str,
                                 datarange: DataRange) -> None:
        """Store ``DatatypeDefinition(name datarange)`` in ``tbox``, after the
        three rules of :meth:`~unicode_logic_kit.dl.tableau.TBox.add_datatype_definition`
        (not a built-in name, one definition per name, no cycle) have been run
        against the definitions read EARLIER in the document as well.

        ``tbox`` is the scratch ``TBox`` of one axiom when the lenient reader
        drives this, so it knows no earlier definition: a definition that closes
        a cycle with one, or gives a name a second and different definition,
        would be stored and refused only when the knowledge base is rendered.
        The probe below holds the earlier ones, so the refusal is the one the
        strict reader raises, at the axiom that causes it.
        """
        if self._earlier_definitions:
            probe = TBox(datatype_definitions=list(self._earlier_definitions))
            probe.add_datatype_definition(name, datarange)
        tbox.add_datatype_definition(name, datarange)

    def _parse_literal(self) -> Literal:
        """``"lexical"``, ``"lexical"^^datatype`` or ``"lexical"@lang``.

        The ``^^`` and ``@`` suffixes must be ADJACENT to the closing quote, as
        in the W3C grammar's one token; a datatype may be a prefixed name or a
        full ``<IRI>``. A plain string is an ``xsd:string``.
        """
        tok = self._peek()
        if tok[0] != "STRING":
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(
                f"expected a literal (\"lexical\"^^datatype) but found {found} "
                f"at position {tok[2]}")
        self._advance()
        lexical = _unescape_string(tok[1])
        end = tok[2] + len(tok[1]) + 2          # past the closing quote
        datatype, language = "xsd:string", None
        nxt = self._peek()
        if nxt[0] == "WORD" and nxt[2] == end and nxt[1].startswith("^^"):
            self._advance()
            rest = nxt[1][2:]
            if rest:
                datatype = rest
            else:
                iri = self._peek()
                if iri[0] != "IRI" or iri[2] != nxt[2] + 2:
                    raise self._error(
                        f"expected a datatype after '^^' at position {nxt[2]}")
                self._advance()
                datatype = iri[1]
        elif nxt[0] == "WORD" and nxt[2] == end and nxt[1].startswith("@"):
            self._advance()
            language = nxt[1][1:]
            if not language:
                raise self._error(f"empty language tag at position {nxt[2]}")
        if language is None:
            # owl:Thing / owl:Nothing are CLASSES: as the datatype of a literal
            # they are refused exactly as they are in a data range, in either
            # spelling of the name (the same check, so one policy)
            self._check_not_a_class_name(datatype, tok[2])
        literal = self._datatype_construct(
            lambda: Literal(lexical, datatype, language), "IllTypedLiteral", tok[2])
        # A literal the first-order image cannot hold (xsd:double/xsd:float, a
        # decimal no Number holds exactly) is refused HERE, by its datatype, so
        # that an axiom reported as ACCEPTED is one result.to_kb() can
        # translate -- not one that reads fine and then fails at the image.
        self._datatype_construct(literal.to_term, literal.datatype, tok[2])
        return literal

    def _parse_data_range(self) -> DataRange:
        """One ``DataRange``: a datatype name, ``DataIntersectionOf(DR DR+)``,
        ``DataUnionOf(DR DR+)``, ``DataComplementOf(DR)``, ``DataOneOf(lt+)`` or
        ``DatatypeRestriction(Datatype (facet lt)+)``."""
        tok = self._peek()
        if tok[0] == "IRI":
            self._advance()
            return Datatype(self._check_not_a_class_name(tok[1], tok[2]))
        if tok[0] != "WORD":
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(
                f"expected a data range but found {found} at position {tok[2]}")
        word = tok[1]
        if word in ("DataIntersectionOf", "DataUnionOf"):
            self._advance()
            self._expect("LPAREN", "'('")
            ranges: List[DataRange] = []
            while self._peek()[0] != "RPAREN":
                ranges.append(self._parse_data_range())
            self._expect("RPAREN", "')'")
            if len(ranges) < 2:
                raise self._error(f"{word} expects at least 2 data ranges, "
                                  f"found {len(ranges)}")
            return (DataIntersectionOf if word == "DataIntersectionOf"
                    else DataUnionOf)(tuple(ranges))
        if word == "DataComplementOf":
            self._advance()
            self._expect("LPAREN", "'('")
            inner = self._parse_data_range()
            self._expect("RPAREN", "')'")
            return DataComplementOf(inner)
        if word == "DataOneOf":
            self._advance()
            self._expect("LPAREN", "'('")
            values: List[Literal] = []
            while self._peek()[0] != "RPAREN":
                values.append(self._parse_literal())
            self._expect("RPAREN", "')'")
            if not values:
                raise self._error("DataOneOf expects at least 1 literal, found 0")
            return DataOneOf(tuple(values))
        if word == "DatatypeRestriction":
            self._advance()
            self._expect("LPAREN", "'('")
            base = self._parse_datatype_name()
            facets: List[Tuple[str, Literal]] = []
            while self._peek()[0] != "RPAREN":
                facet = self._parse_name()
                facets.append((facet, self._parse_literal()))
            self._expect("RPAREN", "')'")
            if not facets:
                raise self._error("DatatypeRestriction expects at least one "
                                  "(facet literal) pair, found none")
            first_facet = facets[0][0]
            return self._datatype_construct(
                lambda: DatatypeRestriction(Datatype(base), tuple(facets)),
                first_facet, tok[2])
        self._advance()
        if self._peek()[0] == "LPAREN":
            raise self._unsupported(
                f"unsupported or unknown OWL 2 data range {word!r}", word, tok[2])
        return Datatype(self._check_not_a_class_name(word, tok[2]))

    def _parse_role_name(self, axiom: str) -> str:
        """One object property expression that must be an ordinary role name,
        with ``axiom`` naming the construct in the refusal message."""
        position = self._peek()[2]
        role = self._parse_object_property_expression(allow_reserved=True)
        self._check_role_name(role, axiom, position)
        return role

    def _parse_role_list(self, axiom: str, minimum: int = 2) -> List[str]:
        """Parse ``OPE+ ')'`` (the ``'('`` already consumed) as ordinary role
        names, consume the ``')'``, and require at least ``minimum`` of them.
        """
        roles: List[str] = []
        while self._peek()[0] != "RPAREN":
            roles.append(self._parse_role_name(axiom))
        self._expect("RPAREN", "')'")
        if len(roles) < minimum:
            raise self._error(
                f"{axiom} expects at least {minimum} object properties, "
                f"found {len(roles)}")
        return roles

    def _parse_data_property_list(self, axiom: str, minimum: int = 2) -> List[str]:
        """Parse ``DPE+ ')'`` (the ``'('`` already consumed) as ordinary data
        property names, consume the ``')'``, and require at least ``minimum``."""
        props: List[str] = []
        while self._peek()[0] != "RPAREN":
            props.append(self._parse_data_property_name(axiom))
        self._expect("RPAREN", "')'")
        if len(props) < minimum:
            raise self._error(
                f"{axiom} expects at least {minimum} data properties, "
                f"found {len(props)}")
        return props

    def _parse_individual_list(self, axiom: str, minimum: int = 2) -> List[str]:
        """Parse ``Individual+ ')'`` (the ``'('`` already consumed), consume the
        ``')'``, and require at least ``minimum`` of them.

        One function for ``SameIndividual`` and ``DifferentIndividuals``: the
        two differ only in how the list is EXPANDED (a consecutive chain versus
        all pairs — see each branch), never in how it is read, and the arity
        message should read the same for both.
        """
        individuals: List[str] = []
        while self._peek()[0] != "RPAREN":
            individuals.append(self._parse_name())
        self._expect("RPAREN", "')'")
        if len(individuals) < minimum:
            raise self._error(
                f"{axiom} expects at least {minimum} individuals, "
                f"found {len(individuals)}")
        return individuals

    def _name_to_class_expression(self, name: str, position: int = -1) -> Concept:
        if name in _TOP_SPELLINGS:
            return Top()
        if name in _BOTTOM_SPELLINGS:
            return Bottom()
        if is_builtin_datatype(name):
            # One reading policy for both OWL readers: Manchester refuses this
            # by name ("is a DATATYPE, not a class"); reading it here as an
            # ordinary class called xsd:integer put the datatype's own
            # predicate in a class position, and the verdict changed.
            raise self._unsupported(
                f"{name!r} (at position {position}) is a DATATYPE, not a class "
                f"— OWL 2 does not let one name be both. Use it as the "
                f"filler of a data restriction (DataSomeValuesFrom(d {name})) "
                f"or as a data range", name, position)
        return Atomic(name)

    def _check_not_a_class_name(self, name: str, position: int) -> str:
        """``name``, unless it is one of the two CLASS names ``owl:Thing`` /
        ``owl:Nothing`` (either spelling) -- the mirror of the refusal above: a
        class is not a data range, and a datatype of that name would be the
        class's own predicate."""
        if name in _TOP_SPELLINGS or name in _BOTTOM_SPELLINGS:
            raise self._unsupported(
                f"{name!r} (at position {position}) is a CLASS, not a data range "
                f"— OWL 2 does not let one name be both. The data domain's own "
                f"'everything' is rdfs:Literal; use a datatype name here",
                name, position)
        return name

    # -- balanced-parenthesis skipping, for Declaration/Annotation bodies and
    # an axiom's own leading axiomAnnotations (their content is discarded, so
    # it is skipped structurally rather than parsed field-by-field) -------- #

    def _skip_balanced_parens(self) -> None:
        self._expect("LPAREN", "'('")
        depth = 1
        while depth > 0:
            tok = self._advance()
            if tok[0] == "LPAREN":
                depth += 1
            elif tok[0] == "RPAREN":
                depth -= 1
            elif tok[0] == "EOF":
                raise self._error(
                    "unexpected end of input while skipping a parenthesised group")

    def _skip_leading_annotations(self) -> None:
        while self._peek()[0] == "WORD" and self._peek()[1] == "Annotation":
            self._advance()
            self._skip_balanced_parens()

    # -- class expressions -------------------------------------------------- #

    def _parse_ce_list(self, minimum: int, what: str) -> List[Concept]:
        """Parse ``'(' CE+ ')'`` (the '(' already consumed by the caller)."""
        ces: List[Concept] = []
        while self._peek()[0] != "RPAREN":
            ces.append(self.parse_class_expression())
        self._expect("RPAREN", "')'")
        if len(ces) < minimum:
            raise self._error(f"{what} expects at least {minimum} arguments, found {len(ces)}")
        return ces

    def parse_class_expression(self) -> Concept:
        tok = self._peek()
        if tok[0] == "IRI":
            self._advance()
            return self._name_to_class_expression(tok[1], tok[2])
        if tok[0] == "WORD":
            word = tok[1]
            if word in _REJECTED_CE:
                self._reject(_REJECTED_CE[word], tok)
            if word == "ObjectIntersectionOf":
                self._advance()
                self._expect("LPAREN", "'('")
                ces = self._parse_ce_list(2, "ObjectIntersectionOf")
                return _fold_left(And, ces)
            if word == "ObjectUnionOf":
                self._advance()
                self._expect("LPAREN", "'('")
                ces = self._parse_ce_list(2, "ObjectUnionOf")
                return _fold_left(Or, ces)
            if word == "ObjectComplementOf":
                self._advance()
                self._expect("LPAREN", "'('")
                ce = self.parse_class_expression()
                self._expect("RPAREN", "')'")
                return Not(ce)
            if word == "ObjectSomeValuesFrom":
                self._advance()
                self._expect("LPAREN", "'('")
                role = self._parse_object_property_expression()
                ce = self.parse_class_expression()
                self._expect("RPAREN", "')'")
                return Exists(role, ce)
            if word == "ObjectAllValuesFrom":
                self._advance()
                self._expect("LPAREN", "'('")
                role = self._parse_object_property_expression()
                ce = self.parse_class_expression()
                self._expect("RPAREN", "')'")
                return ForAll(role, ce)
            if word == "ObjectHasValue":
                # ObjectHasValue(OPE Individual) -- its own concept kind, NOT
                # Exists(role, Nominal(individual)): the two are distinct OWL 2
                # structural objects (ObjectSomeValuesFrom(r ObjectOneOf(a)) is
                # the other one, and still refused), and folding them together
                # would break the round-trip guarantee for whichever lost. See
                # dl.concepts.HasValue.
                self._advance()
                self._expect("LPAREN", "'('")
                role = self._parse_object_property_expression()
                individual = self._parse_name()
                self._expect("RPAREN", "')'")
                return HasValue(role, individual)
            if word in ("DataSomeValuesFrom", "DataAllValuesFrom"):
                self._advance()
                self._expect("LPAREN", "'('")
                prop = self._parse_data_property_expression()
                datarange = self._parse_data_range()
                self._expect("RPAREN", "')'")
                return (DataExists if word == "DataSomeValuesFrom"
                        else DataForAll)(prop, datarange)
            if word == "DataHasValue":
                self._advance()
                self._expect("LPAREN", "'('")
                prop = self._parse_data_property_expression()
                value = self._parse_literal()
                self._expect("RPAREN", "')'")
                return DataHasValue(prop, value)
            if word in ("DataMinCardinality", "DataMaxCardinality", "DataExactCardinality"):
                self._advance()
                self._expect("LPAREN", "'('")
                n = self._expect_nonneg_int()
                prop = self._parse_data_property_expression()
                # the data range is OPTIONAL, defaulting to rdfs:Literal -- the
                # data twin of the object cardinalities' owl:Thing default
                datarange = (self._parse_data_range() if self._peek()[0] != "RPAREN"
                             else Datatype("rdfs:Literal"))
                self._expect("RPAREN", "')'")
                if word == "DataMinCardinality":
                    return DataAtLeast(n, prop, datarange)
                if word == "DataMaxCardinality":
                    return DataAtMost(n, prop, datarange)
                return And(DataAtLeast(n, prop, datarange),
                           DataAtMost(n, prop, datarange))      # ExactCardinality
            if word in ("ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality"):
                self._advance()
                self._expect("LPAREN", "'('")
                n = self._expect_nonneg_int()
                role = self._parse_object_property_expression()
                filler = self.parse_class_expression() if self._peek()[0] != "RPAREN" else Top()
                self._expect("RPAREN", "')'")
                if word == "ObjectMinCardinality":
                    return AtLeast(n, role, filler)
                if word == "ObjectMaxCardinality":
                    return AtMost(n, role, filler)
                return And(AtLeast(n, role, filler), AtMost(n, role, filler))   # ExactCardinality
            # Not a recognised class-expression keyword: an atomic name, UNLESS
            # it is immediately followed by '(' -- an unknown/unsupported
            # construct, not a bare name that merely happens to precede one.
            self._advance()
            if self._peek()[0] == "LPAREN":
                raise self._unsupported(
                    f"unsupported or unknown OWL 2 class expression {word!r}",
                    word, tok[2])
            return self._name_to_class_expression(word, tok[2])
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"expected a class expression but found {found} at position {tok[2]}; "
            "expected a class name, 'owl:Thing', 'owl:Nothing', or an "
            "ObjectIntersectionOf/ObjectUnionOf/ObjectComplementOf/"
            "ObjectSomeValuesFrom/ObjectAllValuesFrom/ObjectHasValue/"
            "ObjectMinCardinality/"
            "ObjectMaxCardinality/ObjectExactCardinality or "
            "DataSomeValuesFrom/DataAllValuesFrom/DataHasValue/"
            "DataMin/Max/ExactCardinality expression")

    def _expect_nonneg_int(self) -> int:
        tok = self._peek()
        if tok[0] == "WORD" and tok[1].isdigit():
            self._advance()
            return int(tok[1])
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"expected a non-negative integer but found {found} at position {tok[2]}")

    # -- axioms --------------------------------------------------------------- #

    def _parse_axiom(self, tbox: TBox, abox: ABox) -> Optional[str]:
        """Parse ONE axiom into ``tbox``/``abox``.

        Returns ``None`` for an axiom that was read (or a Declaration/
        Annotation/AnnotationAssertion, which :meth:`parse_document_lenient`
        counts as skipped), and a REASON string for an axiom that was CONSUMED
        without logical content -- a tautological property inclusion or an
        annotation-property axiom -- so the caller can report it instead of
        letting it vanish.
        """
        tok = self._peek()
        if tok[0] != "WORD":
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(f"expected an axiom keyword but found {found} at position {tok[2]}")
        word = tok[1]

        if word == "Declaration" or word in ("Annotation", "AnnotationAssertion"):
            self._advance()
            self._skip_balanced_parens()
            return None

        if word in _ANNOTATION_PROPERTY_AXIOMS:
            self._advance()
            self._skip_balanced_parens()
            return (f"{word} is an annotation-property axiom: annotation "
                    f"properties carry no content under the OWL 2 direct "
                    f"semantics, so it constrains nothing (consumed, like "
                    f"AnnotationAssertion, but reported)")

        if word in _REJECTED_AXIOMS:
            self._advance()
            self._reject(_REJECTED_AXIOMS[word], tok)
            return None

        if word == "SubClassOf":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            sub = self.parse_class_expression()
            sup = self.parse_class_expression()
            self._expect("RPAREN", "')'")
            tbox.add(sub, sup)
            return None

        if word == "EquivalentClasses":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ces = self._parse_ce_list(2, "EquivalentClasses")
            for left, right in zip(ces, ces[1:]):
                tbox.add_equivalence(left, right)
            return None

        if word == "DisjointClasses":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ces = self._parse_ce_list(2, "DisjointClasses")
            for i in range(len(ces)):
                for j in range(i + 1, len(ces)):
                    tbox.add(And(ces[i], ces[j]), Bottom())
            return None

        if word == "SubObjectPropertyOf":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            chain_tok = self._peek()
            if chain_tok[0] == "WORD" and chain_tok[1] == "ObjectPropertyChain":
                self._advance()
                self._expect("LPAREN", "'('")
                chain: List[str] = []
                while self._peek()[0] != "RPAREN":
                    chain.append(self._parse_role_name("SubObjectPropertyOf"))
                self._expect("RPAREN", "')'")
                if len(chain) < 2:
                    raise self._error(
                        f"ObjectPropertyChain expects at least 2 object "
                        f"properties, found {len(chain)} (OWL 2's grammar is "
                        f"ObjectPropertyChain(OPE OPE+); a single role on the "
                        f"left is an ordinary SubObjectPropertyOf axiom)")
                chain_super_role = self._parse_role_name("SubObjectPropertyOf")
                self._expect("RPAREN", "')'")
                tbox.add_role_chain(tuple(chain), chain_super_role)
                return None
            sub_position = self._peek()[2]
            sub_role = self._parse_inclusion_role()
            sup_position = self._peek()[2]
            sup_role = self._parse_inclusion_role()
            self._expect("RPAREN", "')'")
            # A9: an inclusion that is a TAUTOLOGY because of a built-in role
            # name is consumed as a no-op. Not the "silent dropping" this kit
            # forbids: a tautology carries no truth to lose, and it is the same
            # precedent Declaration(...)/Annotation(...) already set above.
            # EVERY other use of a built-in name is refused by name, below.
            if _is_tautology_of(sub_role, sup_role, "Object"):
                return _tautology_reason("SubObjectPropertyOf", sub_role, sup_role)
            # A side that is an inverse role was already read through the
            # plain-name reader (built-ins refused there); only a PLAIN side
            # can still be a built-in that is not part of a tautology.
            if isinstance(sub_role, str):
                self._check_role_name(sub_role, "SubObjectPropertyOf", sub_position)
            if isinstance(sup_role, str):
                self._check_role_name(sup_role, "SubObjectPropertyOf", sup_position)
            tbox.add_role_inclusion(sub_role, sup_role)
            return None

        if word == "ObjectPropertyChain":
            # Legal OWL 2 only INSIDE SubObjectPropertyOf (handled above);
            # on its own it is not an axiom at all.
            self._advance()
            raise self._error(
                f"ObjectPropertyChain is not an axiom on its own — it is the "
                f"left-hand side of SubObjectPropertyOf(ObjectPropertyChain(P1 "
                f"… Pn) Q), found {tok[1]!r} at position {tok[2]}")

        if word == "EquivalentObjectProperties":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            roles = self._parse_role_list("EquivalentObjectProperties")
            # Stored as the role inclusions it abbreviates, CONSECUTIVE pairs
            # only: ⊑ is transitive, so P1 ≡ P2 ≡ P3 already entails P1 ≡ P3.
            # Contrast DisjointObjectProperties below, where disjointness has
            # no such closure and ALL pairs are needed -- the same argument
            # this module's docstring makes for EquivalentClasses.
            tbox.add_equivalent_roles(*roles)
            return None

        if word == "DisjointObjectProperties":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            roles = self._parse_role_list("DisjointObjectProperties")
            tbox.add_disjoint_roles(*roles)
            return None

        if word == "InverseObjectProperties":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            roles = self._parse_role_list("InverseObjectProperties")
            if len(roles) != 2:
                raise self._error(
                    f"InverseObjectProperties expects exactly 2 object "
                    f"properties, found {len(roles)}")
            tbox.add_inverse_roles(roles[0], roles[1])
            return None

        if word in _CHARACTERISTIC_AXIOMS:
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_role_name(word)
            self._expect("RPAREN", "')'")
            getattr(tbox, _CHARACTERISTIC_AXIOMS[word])(role)
            return None

        if word in ("ObjectPropertyDomain", "ObjectPropertyRange"):
            # Stored NATIVELY in the role box, not desugared into the
            # equivalent GCI -- see dl.TBox.add_role_domain for the three
            # reasons, the FOL image being the first of them.
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_role_name(word)
            filler = self.parse_class_expression()
            self._expect("RPAREN", "')'")
            builder = ("add_role_domain" if word == "ObjectPropertyDomain"
                       else "add_role_range")
            getattr(tbox, builder)(role, filler)
            return None

        if word == "SameIndividual":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            individuals = self._parse_individual_list("SameIndividual")
            # CONSECUTIVE pairs only: equality is transitive, so a1 = a2 and
            # a2 = a3 already entail a1 = a3. Deliberately NOT the all-pairs
            # expansion DifferentIndividuals needs below -- distinctness has no
            # transitive closure. (Same argument this module's docstring makes
            # for EquivalentClasses versus DisjointClasses.)
            for first, second in zip(individuals, individuals[1:]):
                abox.assert_same(first, second)
            return None

        if word == "NegativeObjectPropertyAssertion":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_object_property_expression()
            a = self._parse_name()
            b = self._parse_name()
            self._expect("RPAREN", "')'")
            abox.assert_negative_role(a, b, role)
            return None

        if word == "ClassAssertion":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ce = self.parse_class_expression()
            individual = self._parse_name()
            self._expect("RPAREN", "')'")
            abox.assert_concept(individual, ce)
            return None

        if word == "ObjectPropertyAssertion":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_object_property_expression()
            a = self._parse_name()
            b = self._parse_name()
            self._expect("RPAREN", "')'")
            abox.assert_role(a, b, role)
            return None

        if word == "DifferentIndividuals":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            individuals = self._parse_individual_list("DifferentIndividuals")
            for i in range(len(individuals)):
                for j in range(i + 1, len(individuals)):
                    abox.assert_distinct(individuals[i], individuals[j])
            return None

        if word == "SubDataPropertyOf":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            sub_position = self._peek()[2]
            sub_prop = self._parse_data_property_expression(allow_reserved=True)
            sup_position = self._peek()[2]
            sup_prop = self._parse_data_property_expression(allow_reserved=True)
            self._expect("RPAREN", "')'")
            # The data twin of the tautological object inclusion: P ⊑ topDataProperty
            # and bottomDataProperty ⊑ P hold in every interpretation.
            if _is_tautology_of(sub_prop, sup_prop, "Data"):
                return _tautology_reason("SubDataPropertyOf", sub_prop, sup_prop)
            self._check_role_name(sub_prop, "SubDataPropertyOf", sub_position)
            self._check_role_name(sup_prop, "SubDataPropertyOf", sup_position)
            tbox.add_data_property_inclusion(sub_prop, sup_prop)
            return None

        if word == "EquivalentDataProperties":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            props = self._parse_data_property_list(word)
            tbox.add_equivalent_data_properties(*props)
            return None

        if word == "DisjointDataProperties":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            props = self._parse_data_property_list(word)
            tbox.add_disjoint_data_properties(*props)
            return None

        if word == "FunctionalDataProperty":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            prop = self._parse_data_property_name(word)
            self._expect("RPAREN", "')'")
            tbox.add_functional_data_property(prop)
            return None

        if word == "DataPropertyDomain":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            prop = self._parse_data_property_name(word)
            filler = self.parse_class_expression()
            self._expect("RPAREN", "')'")
            tbox.add_data_property_domain(prop, filler)
            return None

        if word == "DataPropertyRange":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            prop = self._parse_data_property_name(word)
            datarange = self._parse_data_range()
            self._expect("RPAREN", "')'")
            tbox.add_data_property_range(prop, datarange)
            return None

        if word == "DatatypeDefinition":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            name_position = self._peek()[2]
            name = self._parse_datatype_name()
            datarange = self._parse_data_range()
            self._expect("RPAREN", "')'")
            self._datatype_construct(
                lambda: self._add_datatype_definition(tbox, name, datarange),
                "DatatypeDefinition", name_position)
            return None

        if word in ("DataPropertyAssertion", "NegativeDataPropertyAssertion"):
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            prop = self._parse_data_property_name(word)
            individual = self._parse_name()
            value = self._parse_literal()
            self._expect("RPAREN", "')'")
            (abox.assert_data if word == "DataPropertyAssertion"
             else abox.assert_negative_data)(individual, prop, value)
            return None

        raise self._unsupported(
            f"unknown or unsupported OWL 2 axiom {word!r}", word, tok[2])

    # -- document shell: Prefix(...)* Ontology(iri? version-iri? axiom*) ---- #

    def _parse_prefix(self) -> None:
        self._advance()   # 'Prefix'
        self._expect("LPAREN", "'('")
        self._expect("WORD", "a prefix name (e.g. 'owl:' or ':')")
        self._expect("EQUALS", "'='")
        self._expect("IRI", "a full IRI ('<...>')")
        self._expect("RPAREN", "')'")

    def parse_document(self) -> Tuple[TBox, ABox]:
        self._parse_document_shell()
        tbox, abox = TBox(), ABox()
        while self._peek()[0] != "RPAREN":
            self._parse_axiom(tbox, abox)
        self._expect("RPAREN", "')'")
        self._expect_eof()
        return tbox, abox

    def _parse_document_shell(self) -> None:
        """Consume ``Prefix(...)* Ontology( <iri>? <version-iri>?`` — the part
        of the document shell both :meth:`parse_document` and
        :meth:`parse_document_lenient` read identically.
        """
        while self._peek()[0] == "WORD" and self._peek()[1] == "Prefix":
            self._parse_prefix()
        self._expect_word("Ontology")
        self._expect("LPAREN", "'('")
        if self._peek()[0] == "IRI":
            self._advance()               # ontology IRI, discarded
            if self._peek()[0] == "IRI":
                self._advance()           # version IRI, discarded

    def _consume_axiom_text(self) -> str:
        """Consume one whole ``Keyword(...)`` group from the axiom keyword the
        cursor is on, and return that axiom's OWN source slice.

        The recovery step of :meth:`parse_document_lenient`: it skips the
        keyword WORD plus its balanced parens with the existing
        :meth:`_skip_balanced_parens`, so a refused axiom costs exactly its own
        text and the next axiom starts where it should. An unbalanced paren
        inside it still raises, which is the right answer — that is malformed
        input, not a fragment question.
        """
        keyword = self._advance()
        if self._peek()[0] == "LPAREN":
            self._skip_balanced_parens()
        last = self._tokens[self._i - 1]
        return self._text[keyword[2]:last[2] + len(last[1])]

    def parse_document_lenient(self) -> "OwlFunctionalResult":
        """:meth:`parse_document`, but recovering at AXIOM boundaries from every
        construct that is valid OWL 2 outside this fragment — see
        :func:`parse_owl_functional_axioms`, which is the public entry point and
        carries the contract.

        Each axiom is parsed into a FRESH scratch ``TBox``/``ABox`` pair and
        merged on success. That makes "a refused axiom leaves nothing behind"
        STRUCTURAL rather than a reading of :meth:`_parse_axiom`'s code: if a
        future axiom branch ever mutated its TBox before finishing its
        arguments, recovery would otherwise leave half an axiom in the result.
        """
        self._parse_document_shell()
        tbox, abox = TBox(), ABox()
        # The live list: ``_merge_axiom_holder`` extends it in place, so what
        # the parser checks a definition against is what has been merged so far.
        self._earlier_definitions = tbox.datatype_definitions
        refused: List[RefusedAxiom] = []
        consumed: List[ConsumedAxiom] = []
        accepted = 0
        skipped = 0
        while self._peek()[0] != "RPAREN":
            start = self._i
            head = self._peek()
            is_noop = (head[0] == "WORD"
                       and head[1] in ("Declaration", "Annotation",
                                       "AnnotationAssertion"))
            scratch_tbox, scratch_abox = TBox(), ABox()
            try:
                reason = self._parse_axiom(scratch_tbox, scratch_abox)
            except OwlFunctionalUnsupportedError as exc:
                self._i = start
                refused.append(RefusedAxiom(
                    keyword=exc.keyword or head[1],
                    position=exc.position if exc.position >= 0 else head[2],
                    text=self._consume_axiom_text(),
                    reason=str(exc)))
                continue
            _merge_axiom_holder(tbox, scratch_tbox)
            _merge_axiom_holder(abox, scratch_abox)
            if is_noop:
                skipped += 1
            elif reason is not None:
                last = self._tokens[self._i - 1]
                consumed.append(ConsumedAxiom(
                    keyword=head[1], position=head[2],
                    text=self._text[head[2]:last[2] + len(last[1])],
                    reason=reason))
            else:
                accepted += 1
        self._expect("RPAREN", "')'")
        self._expect_eof()
        return OwlFunctionalResult(tbox=tbox, abox=abox, refused=tuple(refused),
                                   accepted=accepted, skipped=skipped,
                                   consumed=tuple(consumed))


def _merge_axiom_holder(target, source) -> None:
    """Merge every axiom ``source`` holds into ``target`` (both a ``TBox`` or
    both an ``ABox``), generically over the dataclass fields.

    Generic on purpose: a field added to ``TBox``/``ABox`` is merged here with
    no edit, and :data:`~unicode_logic_kit.dl.tableau._AXIOM_KINDS`' own meta-test
    is what stops a field existing without anyone having thought about it.
    """
    for declared in dataclass_fields(type(source)):
        value = getattr(source, declared.name)
        current = getattr(target, declared.name)
        if isinstance(current, set):
            current.update(value)
        else:
            current.extend(value)


@dataclass(frozen=True)
class RefusedAxiom:
    """One axiom :func:`parse_owl_functional_axioms` did not read, as DATA.

    Structured rather than an exception message, because the useful questions
    about a real ontology are "how many, of which kinds, and where" — and the
    requesting OEO project answered them by regexing 4041 caught exception
    strings.

    Fields:

    * ``keyword`` — the OWL keyword that was refused. For a construct nested
      inside an otherwise-supported axiom this is the INNER one
      (``SubClassOf(A DataHasValue(d "1"))`` refuses as ``"DataHasValue"``),
      because that is the construct a caller would have to add support for.
    * ``position`` — its 0-based character offset in the input text.
    * ``text`` — the refused AXIOM's own source slice, keyword through its
      closing paren. The axiom, not the inner construct: that is the unit that
      was skipped.
    * ``reason`` — the full refusal message, which names the construct and says
      what to use instead.
    """

    keyword: str
    position: int
    text: str
    reason: str


@dataclass(frozen=True)
class ConsumedAxiom:
    """One axiom :func:`parse_owl_functional_axioms` READ and found to carry no
    logical content -- as DATA, so it is reported and does not vanish.

    Not a refusal: nothing is lost by consuming it. Two kinds exist, both
    valid OWL 2: an ANNOTATION-PROPERTY axiom (``SubAnnotationPropertyOf``,
    ``AnnotationPropertyDomain``, ``AnnotationPropertyRange`` -- annotation
    properties carry no content under the OWL 2 direct semantics), and a
    TAUTOLOGICAL property inclusion (``SubObjectPropertyOf(P
    owl:topObjectProperty)`` and its data and bottom-property twins, which hold
    in every interpretation).

    Fields: ``keyword`` (the axiom's own OWL keyword), ``position`` (its
    0-based offset), ``text`` (its source slice) and ``reason`` (why it carries
    no content).
    """

    keyword: str
    position: int
    text: str
    reason: str


@dataclass(frozen=True)
class OwlFunctionalResult:
    """What :func:`parse_owl_functional_axioms` read from a document, and what
    it did not.

    Fields:

    * ``tbox`` / ``abox`` — built from every axiom that WAS read. Ordinary
      :class:`~unicode_logic_kit.dl.tableau.TBox`/
      :class:`~unicode_logic_kit.dl.tableau.ABox` objects, so every ``dl``
      function takes them unchanged.
    * ``refused`` — one :class:`RefusedAxiom` per axiom skipped, in document
      order.
    * ``accepted`` — how many axioms were read into ``tbox``/``abox``.
    * ``skipped`` — how many ``Declaration``/``Annotation``/
      ``AnnotationAssertion`` no-ops were consumed. Counted separately from
      ``accepted`` because they carry no logical content.
    * ``consumed`` — one :class:`ConsumedAxiom` per axiom that WAS read but
      carries no logical content (an annotation-property axiom, a tautological
      property inclusion), in document order. Reported rather than counted
      with ``skipped``, because these LOOK logical: a caller auditing a
      census against the document needs to be told. ``accepted + skipped +
      len(consumed) + len(refused)`` is the document's axiom count.

    ``accepted`` counts AXIOMS, not stored entries: one
    ``EquivalentClasses(C D)`` is one accepted axiom and two
    ``tbox.inclusions``, and one ``DisjointObjectProperties(P Q R)`` is one
    accepted axiom and three stored pairs.
    """

    tbox: TBox
    abox: ABox
    refused: Tuple[RefusedAxiom, ...] = ()
    accepted: int = 0
    skipped: int = 0
    consumed: Tuple[ConsumedAxiom, ...] = ()

    @property
    def ok(self) -> bool:
        """True iff nothing was refused — the same convention
        :class:`unicode_logic_kit.api.ParseResult` uses.

        ``False`` does NOT mean the result is unusable: ``tbox``/``abox`` hold
        every axiom that WAS read. It means the knowledge base they describe is
        WEAKER than the document, by exactly the axioms ``refused`` names.
        """
        return not self.refused

    @property
    def refused_keywords(self) -> Dict[str, int]:
        """``keyword -> how many axioms were refused for it``, so a census of an
        ontology's unsupported fragment needs no regex over messages.
        """
        counts: Dict[str, int] = {}
        for axiom in self.refused:
            counts[axiom.keyword] = counts.get(axiom.keyword, 0) + 1
        return counts

    def to_kb(self) -> "object":
        """``dl.kb_to_fol(self.tbox, self.abox)`` — the FOL image, with the role
        box as SEPARATE premises.

        The obvious next call, and the reason it is a method: handing the TBox
        to :func:`~unicode_logic_kit.dl.translate.tbox_to_fol` instead would drop
        every role-box axiom the document carried (218 of them on the OEO
        ontology), which is the trap
        :class:`~unicode_logic_kit.dl.translate.RoleBoxOmittedError` exists for
        and the one the requesting project's own translator fell into.

        The import is local: ``dl.translate`` imports THIS module's siblings
        (``tableau``, ``concepts``) but not this module, so a module-level
        import here would add an edge to the package's layering for one
        convenience method.
        """
        from .translate import kb_to_fol

        return kb_to_fol(self.tbox, self.abox)

    def to_dict(self) -> dict:
        """JSON-compatible form: the counts and the refusals.

        The TBox/ABox are NOT in it — they are object graphs, and the FOL image
        (``to_kb().to_dict()``) is the serialisable form of their content.
        """
        return {
            "ok": self.ok,
            "accepted": self.accepted,
            "skipped": self.skipped,
            "consumed": [{"keyword": a.keyword, "position": a.position,
                          "text": a.text, "reason": a.reason}
                         for a in self.consumed],
            "refused": [{"keyword": a.keyword, "position": a.position,
                         "text": a.text, "reason": a.reason}
                        for a in self.refused],
            "refused_keywords": self.refused_keywords,
        }


def _fold_left(ctor, items: List[Concept]) -> Concept:
    """Fold ``items`` into ``ctor`` left-associatively (see the module
    docstring's "Supported fragment" note on ``ObjectIntersectionOf``/``ObjectUnionOf``).
    """
    acc = items[0]
    for item in items[1:]:
        acc = ctor(acc, item)
    return acc


# --------------------------------------------------------------------------- #
# Public parsing API.
# --------------------------------------------------------------------------- #

def parse_owl_functional(text: str) -> Tuple[TBox, ABox]:
    """Parse a whole OWL 2 Functional-Style Syntax ontology document.

    Round-trips against :func:`to_owl_functional`: ``parse_owl_functional(
    to_owl_functional(tbox, abox)) == (tbox, abox)`` for every ALCHQ ``(tbox,
    abox)`` pair (see the module docstring's "Round-trip guarantee").

    Args:
        text: A document of the shape ``Prefix(...)* Ontology(<iri>? axiom*)``
            (see the module docstring's "Supported fragment").

    Returns:
        ``(tbox, abox)``, the :class:`~unicode_logic_kit.dl.tableau.TBox`/
        :class:`~unicode_logic_kit.dl.tableau.ABox` built from every supported
        axiom in the document (``Declaration``/``Annotation``/
        ``AnnotationAssertion`` axioms are no-ops — see the module docstring).

    Raises:
        OwlFunctionalSyntaxError: On malformed input, or on syntax that is
            valid OWL 2 Functional-Style Syntax but falls outside ALCHQ (see
            the module docstring's "Rejected").

    STRICT, and deliberately kept so: it raises on the FIRST axiom outside the
    fragment and returns nothing, which for a real ontology means no TBox at
    all. :func:`parse_owl_functional_axioms` is the per-axiom reader that
    reports the refusals instead.

    Consumed without a report: besides the ``Declaration``/``Annotation``/
    ``AnnotationAssertion`` no-ops, this function reads and DROPS the
    annotation-property axioms (``SubAnnotationPropertyOf``,
    ``AnnotationPropertyDomain``, ``AnnotationPropertyRange``) and a
    TAUTOLOGICAL property inclusion (into ``owl:topObjectProperty``/
    ``owl:topDataProperty``, or out of ``owl:bottomObjectProperty``/
    ``owl:bottomDataProperty``). They carry no logical content, so nothing is
    lost -- but they vanish without a report here. Use
    :func:`parse_owl_functional_axioms`, whose ``consumed`` lists each one, when
    the document's axiom count has to add up.

    A literal with no first-order term (``xsd:float``/``xsd:double``, a decimal
    beyond float precision) and a built-in datatype name in class position are
    refused here as well (see the module docstring). A class expression nested
    about a thousand levels deep raises :class:`RecursionError` (the reader is
    recursive descent; the nesting is not rewritten).
    """
    return _Parser(_tokenize(text), text).parse_document()


def parse_owl_functional_axioms(text: str) -> OwlFunctionalResult:
    """Read a whole OWL 2 Functional-Style Syntax document, REPORTING the axioms
    outside this fragment instead of raising on the first one.

    The entry point for a real ontology. :func:`parse_owl_functional` raises as
    soon as it meets a construct it has no reading for, so a document with one
    ``DataPropertyRange`` yields nothing at all; this returns everything it
    could read plus a :class:`RefusedAxiom` per axiom it could not, each naming
    the construct, its offset and its own source text. House rule: an
    unsupported fragment is refused LOUDLY, by name — never approximated and
    never silently dropped — so the refusals are part of the RESULT, and a
    caller who ignores them is choosing to, in writing.

    One tokenization and ONE pass over the document, recovering at axiom
    boundaries. Each axiom is parsed into a scratch ``TBox``/``ABox`` and
    merged only on success, so a refused axiom leaves nothing behind
    structurally rather than by anyone's reading of the parser.

    Args:
        text: A document of the shape ``Prefix(...)* Ontology(<iri>? axiom*)``
            (see the module docstring's "Supported fragment").

    Returns:
        An :class:`OwlFunctionalResult`. ``doc.to_kb()`` is the FOL image (==
        ``dl.kb_to_fol(doc.tbox, doc.abox)``), whose ``premises`` /
        ``tbox_premises`` are what ``api.prove`` wants;
        ``dl.abox_consistent(doc.tbox and doc.abox)`` is the in-house tableau
        over the SAME object, and the two must agree.

    Raises:
        OwlFunctionalSyntaxError: on MALFORMED input only — an unterminated
            IRI or string literal, an unbalanced paren, a missing
            ``Ontology(``, a bad name, trailing input. Those are questions
            about the document rather than about the fragment, and recovering
            from one could silently drop arbitrary content. Never
            :class:`OwlFunctionalUnsupportedError`: that class is precisely
            what this function recovers from, and it is a SUBCLASS, so a
            caller catching ``OwlFunctionalSyntaxError`` around this call is
            catching malformed input alone.
        RecursionError: a class expression nested about a thousand levels deep
            (Python's default recursion limit). The reader is recursive descent
            and the recursion is not rewritten; the call fails, it never
            truncates. Nothing short of a machine-generated document nests that
            deeply.

    ``accepted`` counts axioms READ. Each literal an accepted axiom carries has
    a first-order term (``xsd:float``/``xsd:double`` literals and decimals no
    ``Number`` holds exactly are refused HERE, by their datatype, instead of
    failing later), so ``to_kb()`` can render every accepted axiom. So is a
    ``DatatypeDefinition`` that OWL 2 (Structural Specification §9.4) does not
    allow given the definitions read before it: one that closes a cycle with
    them, or gives a datatype a second and different definition, is a
    :class:`RefusedAxiom` with ``keyword == "DatatypeDefinition"`` and the same
    reason :func:`parse_owl_functional` raises with, and it is not stored (the
    definitions before it are). An identical repeat of a definition is the same
    axiom and is accepted. ``to_kb()`` may still refuse the knowledge base as a
    WHOLE, for what no single axiom shows: one name used both as an object
    property and a data property or both as a class and a datatype (OWL 2 DL
    forbids it, and the image has one predicate per name), or
    ``OwlThing``/``OwlData`` used as a name.
    """
    return _Parser(_tokenize(text), text).parse_document_lenient()


def parse_owl_functional_class_expression(text: str) -> Concept:
    """Parse a single OWL 2 Functional-Style Syntax class expression.

    Round-trips against :func:`to_owl_functional_class_expression` (see the
    module docstring's "Round-trip guarantee").

    Args:
        text: A class expression, e.g. ``"ObjectIntersectionOf(Person
            ObjectSomeValuesFrom(hasChild Doctor))"``.

    Returns:
        The parsed :class:`~unicode_logic_kit.dl.concepts.Concept`.

    Raises:
        OwlFunctionalSyntaxError: On malformed input, or on syntax outside
            ALCHQ (see the module docstring's "Rejected").
    """
    parser = _Parser(_tokenize(text), text)
    ce = parser.parse_class_expression()
    parser._expect_eof()
    return ce


# --------------------------------------------------------------------------- #
# Renderer: no precedence table needed (see the module docstring's "No
# ambiguity, no precedence") -- every compound is 'Keyword(args)'.
# --------------------------------------------------------------------------- #

def _is_one_word(name: str) -> bool:
    """True iff the tokenizer reads ``name`` as ONE bare WORD that is no keyword
    and no anonymous-individual label."""
    try:
        tokens = _tokenize(name)
    except OwlFunctionalSyntaxError:
        return False
    return (len(tokens) == 2 and tokens[0][0] == "WORD" and tokens[0][1] == name
            and name not in _NAME_KEYWORDS and not name.startswith("_:"))


@functools.lru_cache(maxsize=8192)
def _name_spelling(name: str, kind: str) -> Tuple[Optional[str], str]:
    """``(spelling, "")`` for the one-token spelling of ``name`` that the reader
    reads back as exactly that name, or ``(None, reason)`` when there is none.

    A name holding ``://`` is written in angle brackets, as it always was. Any
    other name is written bare when the tokenizer reads it as one plain word, and
    in angle brackets otherwise, which carries whitespace, structural characters,
    keywords and the empty name alike: the reader takes everything up to the
    first ``>`` for one IRI. That leaves a name with a ``>`` in it with no
    spelling, and a name that already holds the brackets of a full IRI, since
    ``<...>`` reads back as the text between them. For a ``kind`` of ``"class"``
    ``owl:Thing`` and ``owl:Nothing`` read as the top and the bottom class in
    every spelling, so they have none either. (A class named like a built-in
    datatype is a different case: the reader REFUSES it, loudly, and it is
    written as given — see the module docstring's "Round-trip guarantee".)
    """
    if kind == "class":
        try:
            back = _Parser([], "")._name_to_class_expression(name)
        except OwlFunctionalSyntaxError:
            back = Atomic(name)            # refused on reading, not another reading
        if back != Atomic(name):
            return None, (f"read as a class it is {back!r} in every spelling "
                          f"(owl:Thing and owl:Nothing are the top and the bottom class)")
    if name[:1] == "<" and name[-1:] == ">" and ">" not in name[1:-1]:
        return None, ("it already holds the angle brackets of a full IRI, and the "
                      "reader reads <...> as the text between them, which is "
                      "another name")
    bracketable = ">" not in name
    if "://" in name and bracketable:
        return f"<{name}>", ""
    if _is_one_word(name):
        return name, ""
    if bracketable:
        return f"<{name}>", ""
    return None, "it holds '>', which ends a full IRI, and a bare name cannot carry it"


def _render_name(name: str, kind: str = "name") -> str:
    """Render a kit name back as a Functional-Syntax token that reads back as that
    name: ``<...>`` when it looks like an absolute IRI (contains ``"://"``) or
    when a bare name would not read back as ONE name (whitespace, a structural
    character, a keyword, the empty name), bare otherwise -- see the module
    docstring's "IRIs and names". ``kind`` is ``"class"`` where the reader gives
    ``owl:Thing`` and ``owl:Nothing`` a meaning of their own, ``"name"`` elsewhere.

    Raises:
        ValueError: no spelling reads back as ``name`` (it holds ``>``, already
            holds the brackets of a full IRI, or is ``owl:Thing`` /
            ``owl:Nothing`` as a class name). The text is never written as
            something that reads back as another name or expression.
    """
    spelling, reason = _name_spelling(name, kind)
    if spelling is None:
        raise ValueError(
            f"to_owl_functional: the name {name!r} cannot be written so that "
            f"parse_owl_functional reads it back as that name: {reason}. Rename it.")
    return spelling


# The message shared by both I/O rejections below: unlike parse_owl_functional's
# _reject (which points at a byte position in some INPUT TEXT), there is no text
# position here -- we are rendering a Concept object tree that was built directly
# via dl.InverseRole/dl.Nominal (never round-tripped through this module's own
# parser, which already refuses ObjectInverseOf/ObjectOneOf on the way in -- see
# _REJECTED_CE). Mirrors the wording of dl.translate.concept_to_modal's own I/O
# refusal (_IO_MODAL_MSG) and points the caller at the two things that DO support
# I/O: dl.to_manchester (rendering only) and dl.owl_reasoner (deciding).
_IO_RENDER_MSG = (
    "{fn}: {what} is outside ALCHQ (this kit's DL fragment) -- OWL 2 "
    "Functional-Style Syntax rendering only covers ALCHQ, the same fragment "
    "this module's parser accepts. Use dl.to_manchester for a diagnostic-only "
    "rendering that does support inverse roles (I) and nominals (O), or "
    "dl.owl_reasoner to actually decide a concept that needs them."
)


def _plain_role_name(role: Union[str, InverseRole], fn: str) -> str:
    """``role`` as a plain role NAME, or a loud ``TypeError`` naming ``fn`` if it
    is an :class:`InverseRole` -- outside ALCHQ, refused by name (see
    :data:`_IO_RENDER_MSG`).

    The one place the ``str | InverseRole`` union a role field may carry is
    narrowed for the renderer, so no call site hands :func:`_render_name` (which
    expects a ``str``) an object it would turn into a low-level, unnamed
    ``TypeError`` (``InverseRole`` is not iterable) or, worse, a set member
    ``sorted()`` then chokes on.
    """
    if isinstance(role, InverseRole):
        raise TypeError(_IO_RENDER_MSG.format(
            fn=fn, what=f"the inverse role {role.role}⁻ (InverseRole)"))
    return role


def _render_role(role: Union[str, InverseRole],
                 fn: str = "to_owl_functional_class_expression") -> str:
    """Render a ``role`` field (the ``role`` of :class:`Exists`/:class:`ForAll`/
    :class:`AtLeast`/:class:`AtMost`, or either side of a role inclusion), which
    may be a plain role name (``str``) or an :class:`InverseRole` -- outside
    ALCHQ, refused by name (see :func:`_plain_role_name`).
    """
    return _render_name(_plain_role_name(role, fn))


def _render_ce(c: Concept) -> str:
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return _render_name(c.name, "class")
    if isinstance(c, Nominal):
        raise TypeError(_IO_RENDER_MSG.format(
            fn="to_owl_functional_class_expression",
            what=f"the nominal {{{c.individual}}} (Nominal)"))
    if isinstance(c, Not):
        return f"ObjectComplementOf({_render_ce(c.concept)})"
    if isinstance(c, And):
        return f"ObjectIntersectionOf({_render_ce(c.left)} {_render_ce(c.right)})"
    if isinstance(c, Or):
        return f"ObjectUnionOf({_render_ce(c.left)} {_render_ce(c.right)})"
    if isinstance(c, Exists):
        return f"ObjectSomeValuesFrom({_render_role(c.role)} {_render_ce(c.concept)})"
    if isinstance(c, ForAll):
        return f"ObjectAllValuesFrom({_render_role(c.role)} {_render_ce(c.concept)})"
    if isinstance(c, HasValue):
        return f"ObjectHasValue({_render_role(c.role)} {_render_name(c.individual)})"
    if isinstance(c, AtLeast):
        return f"ObjectMinCardinality({c.n} {_render_role(c.role)} {_render_ce(c.concept)})"
    if isinstance(c, AtMost):
        return f"ObjectMaxCardinality({c.n} {_render_role(c.role)} {_render_ce(c.concept)})"
    if isinstance(c, DataExists):
        return (f"DataSomeValuesFrom({_render_name(c.prop)} "
                f"{render_datarange_fs(c.datarange, _render_name)})")
    if isinstance(c, DataForAll):
        return (f"DataAllValuesFrom({_render_name(c.prop)} "
                f"{render_datarange_fs(c.datarange, _render_name)})")
    if isinstance(c, DataHasValue):
        return (f"DataHasValue({_render_name(c.prop)} "
                f"{render_literal_fs(c.value, _render_name)})")
    if isinstance(c, DataAtLeast):
        return (f"DataMinCardinality({c.n} {_render_name(c.prop)} "
                f"{render_datarange_fs(c.datarange, _render_name)})")
    if isinstance(c, DataAtMost):
        return (f"DataMaxCardinality({c.n} {_render_name(c.prop)} "
                f"{render_datarange_fs(c.datarange, _render_name)})")
    raise TypeError(f"to_owl_functional_class_expression: unsupported concept {type(c).__name__}")


def to_owl_functional_class_expression(concept: Concept) -> str:
    """Render ``concept`` in OWL 2 Functional-Style Syntax, dual to
    :func:`parse_owl_functional_class_expression`.

    Args:
        concept: Any ALCHQ :class:`~unicode_logic_kit.dl.concepts.Concept`.

    Returns:
        The Functional-Syntax rendering, e.g.
        ``"ObjectSomeValuesFrom(r ObjectIntersectionOf(A B))"``.

    Raises:
        ~unicode_logic_kit.dl.tableau.RoleExpressionError:
            a restriction's role is an OWL 2 built-in
            property name or ``=``/``≠`` — see :func:`to_owl_functional`.
        ValueError: a name has no spelling that the reader reads back as that
            name (see "IRIs and names" in the module docstring).
    """
    _reject_concept_roles_deep(concept, where="to_owl_functional_class_expression")
    return _render_ce(concept)


def _render_inclusion_role(role: Union[str, InverseRole]) -> str:
    """One side of a ``SubObjectPropertyOf`` line: the name, or
    ``ObjectInverseOf(name)`` — the only position the grammar reads an inverse
    role in (see ``_Parser._parse_inclusion_role``)."""
    if isinstance(role, InverseRole):
        return f"ObjectInverseOf({_render_name(role.role)})"
    return _render_name(role)


def _render_role_box(tbox: TBox) -> List[str]:
    """Render ``tbox``'s role box as Functional-Syntax axiom lines.

    Every field of the role box, in the order
    :data:`~unicode_logic_kit.dl.tableau._AXIOM_KINDS` lists them: a kind the
    parser reads and this drops is a round-trip bug (see "The axiom-kind table"
    in :mod:`unicode_logic_kit.dl.tableau`), which is why
    ``tests/test_dl_route_agreement.py`` checks the round trip per kind.

    Two deliberate read-both/write-one asymmetries, both of which still
    round-trip to the identical ``TBox``:

    * ``EquivalentObjectProperties`` is NOT re-folded out of the role
      inclusions it was stored as — two ``SubObjectPropertyOf`` lines come
      back out, exactly as ``DisjointClasses`` comes back out as ``SubClassOf``
      lines;
    * ``DisjointObjectProperties`` is written as one BINARY line per stored
      pair (legal OWL 2 — the grammar's minimum is two) rather than re-folded
      into one k-ary line, because the pairs are what the ``TBox`` holds and
      re-folding could only reconstruct a different-but-equivalent grouping.
    """
    lines: List[str] = []
    for sub_role, super_role in tbox.role_inclusions:
        # An inverse role is written as OWL 2 spells it, ObjectInverseOf(P) --
        # the TBox holds `r ⊑ s⁻`, rbox_to_fol renders it, the Hets renderer
        # writes it, and parse_owl_functional reads it on exactly this
        # position, so refusing it here broke the round trip with a TypeError.
        lines.append(f"SubObjectPropertyOf({_render_inclusion_role(sub_role)} "
                     f"{_render_inclusion_role(super_role)})")
    for role in sorted(tbox.transitive_roles):
        lines.append(f"TransitiveObjectProperty({_render_name(role)})")
    for left, right in tbox.disjoint_role_pairs:
        lines.append(f"DisjointObjectProperties({_render_name(left)} "
                     f"{_render_name(right)})")
    for role in sorted(tbox.asymmetric_roles):
        lines.append(f"AsymmetricObjectProperty({_render_name(role)})")
    for role in sorted(tbox.irreflexive_roles):
        lines.append(f"IrreflexiveObjectProperty({_render_name(role)})")
    for role in sorted(tbox.functional_roles):
        lines.append(f"FunctionalObjectProperty({_render_name(role)})")
    for p, q in tbox.inverse_role_pairs:
        lines.append(f"InverseObjectProperties({_render_name(p)} {_render_name(q)})")
    for role in sorted(tbox.symmetric_roles):
        lines.append(f"SymmetricObjectProperty({_render_name(role)})")
    for role in sorted(tbox.reflexive_roles):
        lines.append(f"ReflexiveObjectProperty({_render_name(role)})")
    for role in sorted(tbox.inverse_functional_roles):
        lines.append(f"InverseFunctionalObjectProperty({_render_name(role)})")
    for chain, super_role in tbox.role_chains:
        body = " ".join(_render_name(role) for role in chain)
        lines.append(f"SubObjectPropertyOf(ObjectPropertyChain({body}) "
                     f"{_render_name(super_role)})")
    for role, filler in tbox.role_domains:
        lines.append(f"ObjectPropertyDomain({_render_name(role)} "
                     f"{_render_ce(filler)})")
    for role, filler in tbox.role_ranges:
        lines.append(f"ObjectPropertyRange({_render_name(role)} "
                     f"{_render_ce(filler)})")
    return lines


def _render_data_box(tbox: TBox) -> List[str]:
    """Render ``tbox``'s data box as Functional-Syntax axiom lines, in the order
    :data:`~unicode_logic_kit.dl.tableau._AXIOM_KINDS` lists the kinds. Same two
    read-both/write-one asymmetries as :func:`_render_role_box`:
    ``EquivalentDataProperties`` comes back out as the two inclusions it was
    stored as, and ``DisjointDataProperties`` as one binary line per stored pair.
    """
    lines: List[str] = []
    for sub_prop, super_prop in tbox.data_property_inclusions:
        lines.append(f"SubDataPropertyOf({_render_name(sub_prop)} "
                     f"{_render_name(super_prop)})")
    for left, right in tbox.disjoint_data_property_pairs:
        lines.append(f"DisjointDataProperties({_render_name(left)} "
                     f"{_render_name(right)})")
    for prop in sorted(tbox.functional_data_properties):
        lines.append(f"FunctionalDataProperty({_render_name(prop)})")
    for prop, filler in tbox.data_property_domains:
        lines.append(f"DataPropertyDomain({_render_name(prop)} {_render_ce(filler)})")
    for prop, datarange in tbox.data_property_ranges:
        lines.append(f"DataPropertyRange({_render_name(prop)} "
                     f"{render_datarange_fs(datarange, _render_name)})")
    for name, datarange in tbox.datatype_definitions:
        lines.append(f"DatatypeDefinition({_render_name(name)} "
                     f"{render_datarange_fs(datarange, _render_name)})")
    return lines


def _role_box_role_names(tbox: TBox) -> Set[str]:
    """Every role name ``tbox``'s role box mentions (for the
    ``Declaration(...)`` block — see :func:`_collect_names`).

    Driven field by field over the SAME fields :func:`_render_role_box` writes,
    so a role that appears only in, say, a property chain is still declared.
    """
    roles: Set[str] = set()
    for sub_role, super_role in tbox.role_inclusions:
        for role in (sub_role, super_role):
            roles.add(role.role if isinstance(role, InverseRole) else role)
    for pair in tbox.inverse_role_pairs + tbox.disjoint_role_pairs:
        roles.update(pair)
    for chain, super_role in tbox.role_chains:
        roles.update(chain)
        roles.add(super_role)
    for role, _filler in tbox.role_domains + tbox.role_ranges:
        roles.add(role)                 # the FILLER's names are walked by
                                        # _collect_names, which has the
                                        # classes/individuals sets too
    for names in (tbox.transitive_roles, tbox.symmetric_roles,
                  tbox.asymmetric_roles, tbox.reflexive_roles,
                  tbox.irreflexive_roles, tbox.functional_roles,
                  tbox.inverse_functional_roles):
        roles.update(names)
    return roles


def _render_axioms(tbox: TBox) -> List[str]:
    """Render ``tbox``'s concept-level axioms as ``SubClassOf``/
    ``EquivalentClasses`` lines.

    Named for the TBox, not for ``tbox.inclusions``: every axiom kind the
    parser reads, the writer must write, or the round-trip guarantee is a lie
    (see "The axiom-kind table" in :mod:`unicode_logic_kit.dl.tableau`), so this
    is where a TBox axiom kind other than the two below is rendered as well.

    Recognises the exact adjacent-pair shape ``TBox.add_equivalence`` produces
    (``(c, d)`` immediately followed by ``(d, c)``) and re-folds it into one
    ``EquivalentClasses(c d)`` line; every other inclusion is a plain
    ``SubClassOf`` (see the module docstring's "EquivalentClasses and
    DisjointClasses").
    """
    lines: List[str] = []
    incs = tbox.inclusions
    i, n = 0, len(incs)
    while i < n:
        c, d = incs[i]
        if i + 1 < n and incs[i + 1] == (d, c) and c != d:
            lines.append(f"EquivalentClasses({_render_ce(c)} {_render_ce(d)})")
            i += 2
        else:
            lines.append(f"SubClassOf({_render_ce(c)} {_render_ce(d)})")
            i += 1
    return lines


def _walk_class_expression_names(c: Concept, classes: Set[str], roles: Set[str],
                                 individuals: Set[str]) -> None:
    """Collect every ``Atomic`` name into ``classes``, every role name into
    ``roles`` and every INDIVIDUAL name into ``individuals``, recursively (used
    by :func:`_collect_names` for the ``Declaration(...)`` block -- see
    :func:`to_owl_functional`).

    ``individuals`` is an out-parameter because a class expression CAN name one:
    a HasValue's filler. Without it, an individual that occurs ONLY inside a
    TBox class expression -- which is every ObjectHasValue filler, 95 axioms'
    worth on the OEO ontology -- would get no
    ``Declaration(NamedIndividual(...))`` line.
    """
    if isinstance(c, Atomic):
        classes.add(c.name)
    elif isinstance(c, (Top, Bottom)):
        pass
    elif isinstance(c, Nominal):
        raise TypeError(_IO_RENDER_MSG.format(
            fn="to_owl_functional", what=f"the nominal {{{c.individual}}} (Nominal)"))
    elif isinstance(c, HasValue):
        if isinstance(c.role, InverseRole):
            raise TypeError(_IO_RENDER_MSG.format(
                fn="to_owl_functional",
                what=f"the inverse role {c.role.role}⁻ (InverseRole)"))
        roles.add(c.role)
        individuals.add(c.individual)
    elif isinstance(c, Not):
        _walk_class_expression_names(c.concept, classes, roles, individuals)
    elif isinstance(c, (And, Or)):
        _walk_class_expression_names(c.left, classes, roles, individuals)
        _walk_class_expression_names(c.right, classes, roles, individuals)
    elif isinstance(c, DATA_CONCEPTS):
        # A data restriction names a DATA property and a data range, neither of
        # which is a class, an object role or an individual; they are collected
        # from the knowledge base's whole vocabulary by to_owl_functional.
        pass
    elif isinstance(c, (Exists, ForAll, AtLeast, AtMost)):
        # c.role may be an InverseRole (see _render_role's docstring) -- caught
        # HERE, before it is ever added to the `roles: Set[str]` collected for
        # the Declaration(...) block, so a mixed/singleton set of roles never
        # reaches _collect_names's sorted(roles) with a non-str member (which
        # would otherwise raise its own low-level, unnamed TypeError there).
        if isinstance(c.role, InverseRole):
            raise TypeError(_IO_RENDER_MSG.format(
                fn="to_owl_functional",
                what=f"the inverse role {c.role.role}⁻ (InverseRole)"))
        roles.add(c.role)
        _walk_class_expression_names(c.concept, classes, roles, individuals)
    else:
        raise TypeError(f"to_owl_functional: unsupported concept {type(c).__name__}")


def _collect_names(tbox: TBox, abox: ABox) -> Tuple[List[str], List[str], List[str]]:
    """Every atomic-class, role, and individual name referenced anywhere in
    ``tbox``/``abox``, each as a sorted, de-duplicated list (sorted for
    deterministic output -- see :func:`to_owl_functional`).
    """
    classes: Set[str] = set()
    roles: Set[str] = set()
    individuals: Set[str] = set()

    for sub, sup in tbox.inclusions:
        _walk_class_expression_names(sub, classes, roles, individuals)
        _walk_class_expression_names(sup, classes, roles, individuals)
    roles.update(_role_box_role_names(tbox))
    for _role, filler in tbox.role_domains + tbox.role_ranges:
        _walk_class_expression_names(filler, classes, roles, individuals)
    for _prop, filler in tbox.data_property_domains:
        _walk_class_expression_names(filler, classes, roles, individuals)
    for individual, concept in abox.concept_assertions:
        individuals.add(individual)
        _walk_class_expression_names(concept, classes, roles, individuals)
    for a, b, role in abox.role_assertions:
        individuals.add(a)
        individuals.add(b)
        roles.add(role)
    for a, b in abox.distinct_assertions + abox.same_assertions:
        individuals.add(a)
        individuals.add(b)
    for a, b, role in abox.negative_role_assertions:
        individuals.add(a)
        individuals.add(b)
        roles.add(role)
    for individual, _prop, _value in abox.data_assertions + abox.negative_data_assertions:
        individuals.add(individual)

    return sorted(classes), sorted(roles), sorted(individuals)


def _reject_unwritable_roles(tbox: TBox, abox: ABox, fn: str) -> None:
    """The roles ``fn`` could not write back to a document the reader accepts:
    the stored role box and data box must be well-formed (the validation the
    tableau and the FOL image run), and no assertion or class expression may
    carry an OWL 2 built-in property name, ``=`` or ``≠``."""
    _validate_role_box(tbox, where=fn)
    _validate_data_box(tbox, where=fn)
    _reject_abox_roles(abox, where=fn)
    fillers = _tbox_class_expressions(tbox) + [c for _, c in tbox.data_property_domains]
    for _individual, concept in abox.concept_assertions:
        fillers.append(concept)
    for concept in fillers:
        _reject_concept_roles_deep(concept, where=fn)


def to_owl_functional(tbox: TBox, abox: ABox, ontology_iri: str = "") -> str:
    """Render ``(tbox, abox)`` as one OWL 2 Functional-Style Syntax ``Ontology(...)``
    document, dual to :func:`parse_owl_functional`.

    Writes a ``Declaration(Class(...)/ObjectProperty(.../NamedIndividual(...))``
    block for every atomic-class/role/individual name referenced anywhere in
    ``tbox``/``abox`` (see :func:`_collect_names`), then the whole role box
    (see :func:`_render_role_box`), then the TBox's concept inclusions (as
    ``SubClassOf``/``EquivalentClasses`` — see :func:`_render_axioms`), then
    the ABox's assertions (``ClassAssertion``, ``ObjectPropertyAssertion``,
    ``DifferentIndividuals``).

    Args:
        tbox: The TBox to render.
        abox: The ABox to render.
        ontology_iri: An optional ontology IRI for the ``Ontology(<iri> ...)``
            header; omitted entirely (``Ontology(...)``, no IRI argument) when
            empty (the default). Discarded on the way back in by
            :func:`parse_owl_functional`, exactly like a ``Prefix(...)`` line
            — this module carries no ontology-metadata state (see the module
            docstring's "Document shell").

    Returns:
        The Functional-Syntax document text.

    Raises:
        ~unicode_logic_kit.dl.tableau.RoleExpressionError:
            a stored role is no usable name, or an OWL 2
            built-in property name (``owl:topObjectProperty`` …) or ``=``/``≠``
            is the role of a restriction or an assertion — written as an
            ordinary role it would read back as a refusal
            (:func:`parse_owl_functional` refuses the name in every such
            position), and a document this module wrote must be one it reads.
        TypeError: an inverse role anywhere BUT either side of a role inclusion,
            or a nominal (outside ALCHQ).
        ValueError: a class, role, property, datatype or individual name has no
            spelling that :func:`parse_owl_functional` reads back as that name
            (see "IRIs and names" in the module docstring).
    """
    _reject_unwritable_roles(tbox, abox, "to_owl_functional")
    class_names, role_names, individual_names = _collect_names(tbox, abox)
    vocabulary = _collect_vocabulary(tbox, abox)
    lines: List[str] = []
    for name in class_names:
        lines.append(f"Declaration(Class({_render_name(name, 'class')}))")
    for name in role_names:
        lines.append(f"Declaration(ObjectProperty({_render_name(name)}))")
    for name in sorted(vocabulary.data_properties):
        lines.append(f"Declaration(DataProperty({_render_name(name)}))")
    # Only the datatypes OWL 2 does not already know: declaring xsd:integer is
    # not wrong, but a declaration for every built-in a document mentions would
    # bury the ones that matter (the user-defined datatypes).
    for name in sorted(vocabulary.datatypes):
        if not is_builtin_datatype(name):
            lines.append(f"Declaration(Datatype({_render_name(name)}))")
    for name in individual_names:
        lines.append(f"Declaration(NamedIndividual({_render_name(name)}))")
    lines.extend(_render_role_box(tbox))
    lines.extend(_render_data_box(tbox))
    lines.extend(_render_axioms(tbox))
    for individual, concept in abox.concept_assertions:
        lines.append(f"ClassAssertion({_render_ce(concept)} {_render_name(individual)})")
    for a, b, role in abox.role_assertions:
        lines.append(f"ObjectPropertyAssertion({_render_name(role)} {_render_name(a)} {_render_name(b)})")
    for a, b in abox.distinct_assertions:
        lines.append(f"DifferentIndividuals({_render_name(a)} {_render_name(b)})")
    # One BINARY line per stored pair, for both identity kinds: binary is legal
    # OWL 2 (the grammar's minimum arity is two), the pairs are what the ABox
    # holds, and re-folding them into a k-ary line could only reconstruct a
    # different-but-equivalent grouping -- the same read-many/write-binary
    # asymmetry DisjointObjectProperties has in _render_role_box.
    for a, b in abox.same_assertions:
        lines.append(f"SameIndividual({_render_name(a)} {_render_name(b)})")
    for a, b, role in abox.negative_role_assertions:
        lines.append(f"NegativeObjectPropertyAssertion({_render_name(role)} "
                     f"{_render_name(a)} {_render_name(b)})")
    for individual, prop, value in abox.data_assertions:
        lines.append(f"DataPropertyAssertion({_render_name(prop)} "
                     f"{_render_name(individual)} "
                     f"{render_literal_fs(value, _render_name)})")
    for individual, prop, value in abox.negative_data_assertions:
        lines.append(f"NegativeDataPropertyAssertion({_render_name(prop)} "
                     f"{_render_name(individual)} "
                     f"{render_literal_fs(value, _render_name)})")

    head =f"Ontology(<{ontology_iri}>" if ontology_iri else "Ontology("
    if not lines:
        return head + ")"
    body = "\n".join(f"  {line}" for line in lines)
    return f"{head}\n{body}\n)"
