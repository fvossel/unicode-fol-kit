"""A parser/renderer for the **OWL 2 Functional-Style Syntax**, restricted to ALCHQ.

`OWL 2 Functional-Style Syntax <https://www.w3.org/TR/owl2-syntax/#Functional-Style_Syntax>`_
is the W3C-standardised, S-expression-shaped ``Keyword(arg arg ...)`` concrete
syntax for a whole OWL 2 *ontology document* — Declarations, an ``Ontology(...)``
wrapper, and a flat list of axioms — as opposed to
:mod:`unicode_fol_kit.dl.owl_manchester`'s frame-based, keyword-infix Manchester
Syntax, which this module otherwise mirrors closely: same recursive-descent
style, same "refuse loudly, name the construct" convention, and the same
treatment of prefixed/full-IRI names as opaque :class:`~unicode_fol_kit.dl.concepts.Atomic`/
role/individual strings, with no RDF-graph or IRI-resolution machinery. This is
the *OWL bridge, part 2*: it reads/writes exactly the ALCHQ-expressible fragment
of a Functional-Style ontology document into/from :class:`~unicode_fol_kit.dl.tableau.TBox`/
:class:`~unicode_fol_kit.dl.tableau.ABox`, plus a standalone class-expression
entry point analogous to :func:`~unicode_fol_kit.dl.owl_manchester.parse_manchester`.

Supported fragment (ALCHQ — this kit's DL fragment, see
:mod:`unicode_fol_kit.dl.tableau`'s module docstring for the RBox/counting
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
      folding **left** into the binary :class:`~unicode_fol_kit.dl.concepts.And`/
      :class:`~unicode_fol_kit.dl.concepts.Or` AST, matching
      :mod:`unicode_fol_kit.dl.owl_manchester`'s documented left-fold for
      ``and``/``or`` chains); ``ObjectComplementOf(CE)``;
      ``ObjectSomeValuesFrom(OPE CE)``, ``ObjectAllValuesFrom(OPE CE)``;
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
      ``TBox.add_transitive_role``; ``ClassAssertion(CE a)`` ->
      ``ABox.assert_concept``; ``ObjectPropertyAssertion(OPE a b)`` ->
      ``ABox.assert_role``; ``DifferentIndividuals(a1 a2+)`` -> **every**
      pairwise ``ABox.assert_distinct`` (all C(k, 2) pairs, not just a
      consecutive chain — see "DifferentIndividuals" below, this is a
      completeness requirement, not a style choice); ``Declaration(Class(...)
      / ObjectProperty(...) / NamedIndividual(...))`` parsed and discarded
      (declarations carry no ALCHQ-relevant content, since
      :mod:`unicode_fol_kit.dl.concepts`'s ``Atomic``/role/individual names are
      already untyped strings — this is not a silent weakening, just a no-op
      the W3C spec itself defines as non-restrictive); axiom-level and
      standalone ``Annotation(...)``/``AnnotationAssertion(...)`` parsed and
      discarded (annotations are explicitly non-logical in OWL 2, so dropping
      them is not a "weaker than requested" translation of truth-bearing
      content) — an axiom's own leading ``axiomAnnotations`` (e.g.
      ``SubClassOf(Annotation(rdfs:label "x") A B)``) are skipped the same way,
      before its real arguments are parsed.

Rejected loudly, one :class:`OwlFunctionalSyntaxError` per construct, naming it
by its OWL keyword (mirrors :mod:`unicode_fol_kit.dl.owl_manchester`'s
messages): ``ObjectInverseOf`` (inverse roles — ALCHQ has none), ``ObjectHasValue``,
``ObjectHasSelf``, ``ObjectOneOf`` (nominals), every ``Data*`` construct
(``DataSomeValuesFrom``, ``DataPropertyAssertion``, …), ``ObjectPropertyChain``
(role chains inside ``SubObjectPropertyOf`` — this kit's RBox has plain role
inclusion only, not SROIQ-style chains), every OTHER object-property
characteristic axiom (``FunctionalObjectProperty``, ``InverseFunctionalObjectProperty``,
``SymmetricObjectProperty``, ``AsymmetricObjectProperty``, ``ReflexiveObjectProperty``,
``IrreflexiveObjectProperty``), ``ObjectPropertyDomain``/``Range``,
``DisjointObjectProperties``, ``EquivalentObjectProperties``,
``InverseObjectProperties``, ``HasKey``, ``SameIndividual`` (same-individual
merging is outside the fragment this module writes back — only distinctness
round-trips, via ``ABox.assert_distinct``), ``SubAnnotationPropertyOf`` and the
other annotation-property axioms, ``DatatypeDefinition``, ``DisjointUnion``,
and anonymous individuals (``_:nodeID``).

IRIs and names
---------------
Exactly :mod:`unicode_fol_kit.dl.owl_manchester`'s convention, adapted to two
concrete-syntax spellings instead of one: a **full IRI** token, ``<...>``, is
stored as the kit name with the angle brackets stripped (``<http://example.org/Person>``
-> ``Atomic("http://example.org/Person")``); a **prefixed (or otherwise bare)
name** token, e.g. ``ex:Person`` or a plain ``Person``, is stored VERBATIM, with
no prefix resolution at all — this module carries no ``Prefix(...)`` -> IRI
table, since (like Manchester's ``owl:Thing``/``owl:Nothing`` special case) the
kit's ``Atomic``/role/individual names are opaque strings, not resolved IRIs.
Rendering back (:func:`to_owl_functional_class_expression`, :func:`to_owl_functional`)
picks one of the two spellings DETERMINISTICALLY, by a single, simple rule: a
name containing ``"://"`` (i.e., shaped like an absolute IRI with a network
scheme) is wrapped back in ``<...>``; every other name is written bare. This
is a heuristic, not IRI validation, but it is total and deterministic, so
``parse_owl_functional_class_expression(to_owl_functional_class_expression(c))
== c`` holds for every concept ``c`` built from any name string (see "Round-trip
guarantee" below) — the RENDERED spelling need not match the ORIGINALLY PARSED
spelling (a full-IRI ``owl:Thing`` reads as :class:`~unicode_fol_kit.dl.concepts.Top`
and always renders back as the bare ``"owl:Thing"``, for instance), only the
resulting :class:`~unicode_fol_kit.dl.concepts.Concept`/``TBox``/``ABox``
structure must match, which is exactly the oracle the tests check. This "any
name string" is not unconditional, though: the round-trip guarantee holds only
for names the TOKENIZER can read back as one WORD token, i.e. names containing
no whitespace and none of ``_STRUCT_CHARS`` (``()=<>"``, see "Tokenizer"
below) outside a bare-name's own ``://``-less body — a kit name built with
such a character (e.g. ``Atomic("Has Value")``) still renders (there is no
escaping mechanism, unlike a full IRI's ``<...>`` bracketing, which only
protects the CONTENTS from re-tokenization, not from containing ``>``
itself), but the rendered text then fails to re-parse as that single name.
This is the same pre-existing convention :mod:`unicode_fol_kit.dl.owl_manchester`
already has for the identical reason (its tokenizer also splits on whitespace
and structural characters), and the failure is always loud (an
:class:`OwlFunctionalSyntaxError` at re-parse), never a silent corruption.

EquivalentClasses and DisjointClasses
---------------------------------------
Neither is a primitive of :class:`~unicode_fol_kit.dl.tableau.TBox` (which only
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
:func:`_render_tbox_axioms`); every other inclusion, including one that
happens to look like ``C ⊓ D ⊑ ⊥``, is rendered as a plain ``SubClassOf``.
This asymmetry (read supports both compact forms, write only re-folds one)
is deliberate and harmless: :class:`~unicode_fol_kit.dl.tableau.TBox` equality
(a plain ``@dataclass``) only ever compares the underlying ``inclusions``
list, never which OWL keyword produced it, so the round-trip oracle
``parse_owl_functional(to_owl_functional(tbox, abox)) == (tbox, abox)`` holds
regardless of which axiom spelling is chosen on the way out.

DifferentIndividuals
----------------------
:class:`~unicode_fol_kit.dl.tableau.ABox` has no unique name assumption (see
"Qualified number restrictions" in :mod:`unicode_fol_kit.dl.tableau`'s module
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

Qualified number restrictions
------------------------------
Identical semantics to :mod:`unicode_fol_kit.dl.owl_manchester`'s ``min``/
``max``/``exactly``: ``ObjectMinCardinality``/``ObjectMaxCardinality`` parse
into :class:`~unicode_fol_kit.dl.concepts.AtLeast`/:class:`~unicode_fol_kit.dl.concepts.AtMost`,
and ``ObjectExactCardinality(n OPE CE?)`` desugars AT PARSE TIME into
``AtLeast(n, role, CE) ⊓ AtMost(n, role, CE)`` (there is no separate "exactly"
AST node — see :mod:`unicode_fol_kit.dl.concepts`). Unlike
:func:`~unicode_fol_kit.dl.owl_manchester.to_manchester` (which omits the
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
:class:`~unicode_fol_kit.dl.tableau.NonSimpleRoleError` — not by this module,
which only builds the AST).

No ambiguity, no precedence
-----------------------------
Unlike :mod:`unicode_fol_kit.dl.owl_manchester` (whose ``_PREC`` lattice and
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
"""

from typing import List, Set, Tuple

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal,
)
from .tableau import TBox, ABox

__all__ = [
    "parse_owl_functional", "to_owl_functional",
    "parse_owl_functional_class_expression", "to_owl_functional_class_expression",
    "OwlFunctionalSyntaxError",
]


class OwlFunctionalSyntaxError(ValueError):
    """Raised by this module's parser on malformed input *and* on syntax that is
    valid OWL 2 Functional-Style Syntax but falls outside ALCHQ (see the module
    docstring's "Rejected"). Always a :class:`ValueError` subclass with a
    message naming the specific offending construct and its position in the
    input, per the kit's honesty convention.
    """


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
    "ObjectHasValue": "value restrictions (ObjectHasValue)",
    "ObjectHasSelf": "Self restrictions (ObjectHasSelf)",
    "ObjectOneOf": "nominal concepts (ObjectOneOf)",
    "ObjectInverseOf": "inverse object properties (ObjectInverseOf)",
    "DataSomeValuesFrom": "datatype restrictions (DataSomeValuesFrom)",
    "DataAllValuesFrom": "datatype restrictions (DataAllValuesFrom)",
    "DataHasValue": "datatype restrictions (DataHasValue)",
    "DataMinCardinality": "datatype cardinality restrictions (DataMinCardinality)",
    "DataMaxCardinality": "datatype cardinality restrictions (DataMaxCardinality)",
    "DataExactCardinality": "datatype cardinality restrictions (DataExactCardinality)",
}

# Axiom keywords rejected outright (outside ALCHQ), same convention.
_REJECTED_AXIOMS = {
    "ObjectPropertyDomain": "object property domain axioms (ObjectPropertyDomain)",
    "ObjectPropertyRange": "object property range axioms (ObjectPropertyRange)",
    "FunctionalObjectProperty": "the Functional object property characteristic (FunctionalObjectProperty)",
    "InverseFunctionalObjectProperty": (
        "the InverseFunctional object property characteristic "
        "(InverseFunctionalObjectProperty) — ALCHQ has no inverse roles"),
    "SymmetricObjectProperty": "the Symmetric object property characteristic (SymmetricObjectProperty)",
    "AsymmetricObjectProperty": "the Asymmetric object property characteristic (AsymmetricObjectProperty)",
    "ReflexiveObjectProperty": "the Reflexive object property characteristic (ReflexiveObjectProperty)",
    "IrreflexiveObjectProperty": "the Irreflexive object property characteristic (IrreflexiveObjectProperty)",
    "DisjointObjectProperties": "disjoint object properties (DisjointObjectProperties)",
    "EquivalentObjectProperties": "equivalent object properties (EquivalentObjectProperties)",
    "InverseObjectProperties": "inverse object property pairs (InverseObjectProperties)",
    "SubDataPropertyOf": "data properties (SubDataPropertyOf)",
    "EquivalentDataProperties": "data properties (EquivalentDataProperties)",
    "DisjointDataProperties": "data properties (DisjointDataProperties)",
    "DataPropertyDomain": "data properties (DataPropertyDomain)",
    "DataPropertyRange": "data properties (DataPropertyRange)",
    "FunctionalDataProperty": "data properties (FunctionalDataProperty)",
    "DataPropertyAssertion": "data property assertions (DataPropertyAssertion)",
    "NegativeDataPropertyAssertion": "negative data property assertions (NegativeDataPropertyAssertion)",
    "NegativeObjectPropertyAssertion": "negative object property assertions (NegativeObjectPropertyAssertion)",
    "HasKey": "keys (HasKey)",
    "SubAnnotationPropertyOf": "annotation property axioms (SubAnnotationPropertyOf)",
    "AnnotationPropertyDomain": "annotation property axioms (AnnotationPropertyDomain)",
    "AnnotationPropertyRange": "annotation property axioms (AnnotationPropertyRange)",
    "DatatypeDefinition": "datatype definitions (DatatypeDefinition)",
    "SameIndividual": "same-individual assertions (SameIndividual)",
    "DisjointUnion": "disjoint union class axioms (DisjointUnion)",
}


class _Parser:
    """A single parse of one tokenized input; not re-used across calls."""

    def __init__(self, tokens: List[_Token], text: str):
        self._tokens = tokens
        self._text = text
        self._i = 0

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

    def _reject(self, what: str, tok: _Token) -> None:
        raise self._error(
            f"{what} is not supported — outside ALCHQ (this kit's DL fragment), "
            f"found {tok[1]!r} at position {tok[2]}")

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

    def _parse_object_property_expression(self) -> str:
        tok = self._peek()
        if tok[0] == "WORD" and tok[1] == "ObjectInverseOf":
            self._reject(_REJECTED_CE["ObjectInverseOf"], tok)
        return self._parse_name()

    def _name_to_class_expression(self, name: str) -> Concept:
        if name in _TOP_SPELLINGS:
            return Top()
        if name in _BOTTOM_SPELLINGS:
            return Bottom()
        return Atomic(name)

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
            return self._name_to_class_expression(tok[1])
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
                raise self._error(f"unsupported or unknown OWL 2 class expression {word!r}")
            return self._name_to_class_expression(word)
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"expected a class expression but found {found} at position {tok[2]}; "
            "expected a class name, 'owl:Thing', 'owl:Nothing', or an "
            "ObjectIntersectionOf/ObjectUnionOf/ObjectComplementOf/"
            "ObjectSomeValuesFrom/ObjectAllValuesFrom/ObjectMinCardinality/"
            "ObjectMaxCardinality/ObjectExactCardinality expression")

    def _expect_nonneg_int(self) -> int:
        tok = self._peek()
        if tok[0] == "WORD" and tok[1].isdigit():
            self._advance()
            return int(tok[1])
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"expected a non-negative integer but found {found} at position {tok[2]}")

    # -- axioms --------------------------------------------------------------- #

    def _parse_axiom(self, tbox: TBox, abox: ABox) -> None:
        tok = self._peek()
        if tok[0] != "WORD":
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(f"expected an axiom keyword but found {found} at position {tok[2]}")
        word = tok[1]

        if word == "Declaration" or word in ("Annotation", "AnnotationAssertion"):
            self._advance()
            self._skip_balanced_parens()
            return

        if word in _REJECTED_AXIOMS:
            self._advance()
            self._reject(_REJECTED_AXIOMS[word], tok)
            return

        if word == "SubClassOf":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            sub = self.parse_class_expression()
            sup = self.parse_class_expression()
            self._expect("RPAREN", "')'")
            tbox.add(sub, sup)
            return

        if word == "EquivalentClasses":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ces = self._parse_ce_list(2, "EquivalentClasses")
            for left, right in zip(ces, ces[1:]):
                tbox.add_equivalence(left, right)
            return

        if word == "DisjointClasses":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ces = self._parse_ce_list(2, "DisjointClasses")
            for i in range(len(ces)):
                for j in range(i + 1, len(ces)):
                    tbox.add(And(ces[i], ces[j]), Bottom())
            return

        if word == "SubObjectPropertyOf":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            chain_tok = self._peek()
            if chain_tok[0] == "WORD" and chain_tok[1] == "ObjectPropertyChain":
                self._reject(
                    "property chains (ObjectPropertyChain) in SubObjectPropertyOf",
                    chain_tok)
            sub = self._parse_object_property_expression()
            sup = self._parse_object_property_expression()
            self._expect("RPAREN", "')'")
            tbox.add_role_inclusion(sub, sup)
            return

        if word == "TransitiveObjectProperty":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_object_property_expression()
            self._expect("RPAREN", "')'")
            tbox.add_transitive_role(role)
            return

        if word == "ClassAssertion":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            ce = self.parse_class_expression()
            individual = self._parse_name()
            self._expect("RPAREN", "')'")
            abox.assert_concept(individual, ce)
            return

        if word == "ObjectPropertyAssertion":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            role = self._parse_object_property_expression()
            a = self._parse_name()
            b = self._parse_name()
            self._expect("RPAREN", "')'")
            abox.assert_role(a, b, role)
            return

        if word == "DifferentIndividuals":
            self._advance()
            self._expect("LPAREN", "'('")
            self._skip_leading_annotations()
            individuals: List[str] = []
            while self._peek()[0] != "RPAREN":
                individuals.append(self._parse_name())
            self._expect("RPAREN", "')'")
            if len(individuals) < 2:
                raise self._error(
                    f"DifferentIndividuals expects at least 2 individuals, "
                    f"found {len(individuals)}")
            for i in range(len(individuals)):
                for j in range(i + 1, len(individuals)):
                    abox.assert_distinct(individuals[i], individuals[j])
            return

        raise self._error(f"unknown or unsupported OWL 2 axiom {word!r}")

    # -- document shell: Prefix(...)* Ontology(iri? version-iri? axiom*) ---- #

    def _parse_prefix(self) -> None:
        self._advance()   # 'Prefix'
        self._expect("LPAREN", "'('")
        self._expect("WORD", "a prefix name (e.g. 'owl:' or ':')")
        self._expect("EQUALS", "'='")
        self._expect("IRI", "a full IRI ('<...>')")
        self._expect("RPAREN", "')'")

    def parse_document(self) -> Tuple[TBox, ABox]:
        while self._peek()[0] == "WORD" and self._peek()[1] == "Prefix":
            self._parse_prefix()
        self._expect_word("Ontology")
        self._expect("LPAREN", "'('")
        if self._peek()[0] == "IRI":
            self._advance()               # ontology IRI, discarded
            if self._peek()[0] == "IRI":
                self._advance()           # version IRI, discarded
        tbox, abox = TBox(), ABox()
        while self._peek()[0] != "RPAREN":
            self._parse_axiom(tbox, abox)
        self._expect("RPAREN", "')'")
        self._expect_eof()
        return tbox, abox


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
        ``(tbox, abox)``, the :class:`~unicode_fol_kit.dl.tableau.TBox`/
        :class:`~unicode_fol_kit.dl.tableau.ABox` built from every supported
        axiom in the document (``Declaration``/``Annotation``/
        ``AnnotationAssertion`` axioms are no-ops — see the module docstring).

    Raises:
        OwlFunctionalSyntaxError: On malformed input, or on syntax that is
            valid OWL 2 Functional-Style Syntax but falls outside ALCHQ (see
            the module docstring's "Rejected").
    """
    return _Parser(_tokenize(text), text).parse_document()


def parse_owl_functional_class_expression(text: str) -> Concept:
    """Parse a single OWL 2 Functional-Style Syntax class expression.

    Round-trips against :func:`to_owl_functional_class_expression` (see the
    module docstring's "Round-trip guarantee").

    Args:
        text: A class expression, e.g. ``"ObjectIntersectionOf(Person
            ObjectSomeValuesFrom(hasChild Doctor))"``.

    Returns:
        The parsed :class:`~unicode_fol_kit.dl.concepts.Concept`.

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

def _render_name(name: str) -> str:
    """Render a kit name back as a Functional-Syntax token: ``<...>`` when it
    looks like an absolute IRI (contains ``"://"``), bare otherwise -- see the
    module docstring's "IRIs and names".
    """
    if "://" in name:
        return f"<{name}>"
    return name


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


def _render_role(role) -> str:
    """Render a ``role`` field (the ``role`` of :class:`Exists`/:class:`ForAll`/
    :class:`AtLeast`/:class:`AtMost`), which may be a plain role name (``str``)
    or an :class:`InverseRole` -- outside ALCHQ, refused by name (see
    :data:`_IO_RENDER_MSG`) rather than passed through to :func:`_render_name`,
    which expects a ``str`` and would otherwise crash with a low-level,
    unnamed ``TypeError`` (``InverseRole`` is not iterable).
    """
    if isinstance(role, InverseRole):
        raise TypeError(_IO_RENDER_MSG.format(
            fn="to_owl_functional_class_expression",
            what=f"the inverse role {role.role}⁻ (InverseRole)"))
    return _render_name(role)


def _render_ce(c: Concept) -> str:
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return _render_name(c.name)
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
    if isinstance(c, AtLeast):
        return f"ObjectMinCardinality({c.n} {_render_role(c.role)} {_render_ce(c.concept)})"
    if isinstance(c, AtMost):
        return f"ObjectMaxCardinality({c.n} {_render_role(c.role)} {_render_ce(c.concept)})"
    raise TypeError(f"to_owl_functional_class_expression: unsupported concept {type(c).__name__}")


def to_owl_functional_class_expression(concept: Concept) -> str:
    """Render ``concept`` in OWL 2 Functional-Style Syntax, dual to
    :func:`parse_owl_functional_class_expression`.

    Args:
        concept: Any ALCHQ :class:`~unicode_fol_kit.dl.concepts.Concept`.

    Returns:
        The Functional-Syntax rendering, e.g.
        ``"ObjectSomeValuesFrom(r ObjectIntersectionOf(A B))"``.
    """
    return _render_ce(concept)


def _render_tbox_axioms(tbox: TBox) -> List[str]:
    """Render ``tbox.inclusions`` as ``SubClassOf``/``EquivalentClasses`` lines.

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


def _walk_class_expression_names(c: Concept, classes: Set[str], roles: Set[str]) -> None:
    """Collect every ``Atomic`` name into ``classes`` and every role name into
    ``roles``, recursively (used by :func:`_collect_names` for the
    ``Declaration(...)`` block -- see :func:`to_owl_functional`).
    """
    if isinstance(c, Atomic):
        classes.add(c.name)
    elif isinstance(c, (Top, Bottom)):
        pass
    elif isinstance(c, Nominal):
        raise TypeError(_IO_RENDER_MSG.format(
            fn="to_owl_functional", what=f"the nominal {{{c.individual}}} (Nominal)"))
    elif isinstance(c, Not):
        _walk_class_expression_names(c.concept, classes, roles)
    elif isinstance(c, (And, Or)):
        _walk_class_expression_names(c.left, classes, roles)
        _walk_class_expression_names(c.right, classes, roles)
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
        _walk_class_expression_names(c.concept, classes, roles)
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
        _walk_class_expression_names(sub, classes, roles)
        _walk_class_expression_names(sup, classes, roles)
    for sub_role, super_role in tbox.role_inclusions:
        roles.add(sub_role)
        roles.add(super_role)
    roles.update(tbox.transitive_roles)
    for individual, concept in abox.concept_assertions:
        individuals.add(individual)
        _walk_class_expression_names(concept, classes, roles)
    for a, b, role in abox.role_assertions:
        individuals.add(a)
        individuals.add(b)
        roles.add(role)
    for a, b in abox.distinct_assertions:
        individuals.add(a)
        individuals.add(b)

    return sorted(classes), sorted(roles), sorted(individuals)


def to_owl_functional(tbox: TBox, abox: ABox, ontology_iri: str = "") -> str:
    """Render ``(tbox, abox)`` as one OWL 2 Functional-Style Syntax ``Ontology(...)``
    document, dual to :func:`parse_owl_functional`.

    Writes a ``Declaration(Class(...)/ObjectProperty(.../NamedIndividual(...))``
    block for every atomic-class/role/individual name referenced anywhere in
    ``tbox``/``abox`` (see :func:`_collect_names`), then the RBox axioms
    (``SubObjectPropertyOf``, ``TransitiveObjectProperty``), then the TBox's
    concept inclusions (as ``SubClassOf``/``EquivalentClasses`` — see
    :func:`_render_tbox_axioms`), then the ABox's assertions
    (``ClassAssertion``, ``ObjectPropertyAssertion``, ``DifferentIndividuals``).

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
    """
    class_names, role_names, individual_names = _collect_names(tbox, abox)
    lines: List[str] = []
    for name in class_names:
        lines.append(f"Declaration(Class({_render_name(name)}))")
    for name in role_names:
        lines.append(f"Declaration(ObjectProperty({_render_name(name)}))")
    for name in individual_names:
        lines.append(f"Declaration(NamedIndividual({_render_name(name)}))")
    for sub_role, super_role in tbox.role_inclusions:
        lines.append(f"SubObjectPropertyOf({_render_name(sub_role)} {_render_name(super_role)})")
    for role in sorted(tbox.transitive_roles):
        lines.append(f"TransitiveObjectProperty({_render_name(role)})")
    lines.extend(_render_tbox_axioms(tbox))
    for individual, concept in abox.concept_assertions:
        lines.append(f"ClassAssertion({_render_ce(concept)} {_render_name(individual)})")
    for a, b, role in abox.role_assertions:
        lines.append(f"ObjectPropertyAssertion({_render_name(role)} {_render_name(a)} {_render_name(b)})")
    for a, b in abox.distinct_assertions:
        lines.append(f"DifferentIndividuals({_render_name(a)} {_render_name(b)})")

    head = f"Ontology(<{ontology_iri}>" if ontology_iri else "Ontology("
    if not lines:
        return head + ")"
    body = "\n".join(f"  {line}" for line in lines)
    return f"{head}\n{body}\n)"
