"""A parser/renderer for the **OWL 2 Manchester Syntax**, restricted to ALCHQ.

`OWL 2 Manchester Syntax <https://www.w3.org/TR/owl2-manchester-syntax/>`_ is
the W3C-standardised, keyword-based (as opposed to :mod:`unicode_fol_kit.dl.parser`'s
glyph-based) concrete syntax for OWL 2 class expressions — the notation Protégé
and most OWL tooling show by default (``Person and hasChild some Doctor``
rather than ``Person ⊓ ∃hasChild.Doctor``). This module is the *OWL bridge,
part 1*: it parses (and renders) exactly the ALCHQ-expressible fragment of that
syntax into/from the kit's existing :class:`~unicode_fol_kit.dl.concepts.Concept`
AST, so any Manchester-syntax ALCHQ expression becomes reachable by every kit
reasoner and export (:mod:`unicode_fol_kit.dl.tableau`,
:mod:`unicode_fol_kit.dl.translate`, …) with no separate code path.

Supported fragment (ALCHQ, matching :mod:`unicode_fol_kit.dl.concepts` plus the
role-hierarchy/transitivity RBox axioms below):

    - class names (``Person``, ``hasChild`` as a role name);
    - ``C and D``, ``C or D``, ``not C``;
    - ``r some C`` (∃r.C), ``r only C`` (∀r.C);
    - ``r value a`` (∃r.{a}) — a value restriction, mapping onto
      :class:`~unicode_fol_kit.dl.concepts.HasValue`, a concept kind of its
      own and NOT ``r some {a}``, which stays refused (see that class's
      docstring for why the two must not collapse into one AST shape);
    - ``r min n C`` / ``r max n C`` / ``r exactly n C`` (≥n r.C / ≤n r.C /
      ≥n r.C ⊓ ≤n r.C) — the qualifying class ``C`` is OPTIONAL per the W3C
      grammar and defaults to ``owl:Thing`` when omitted (``r min n`` alone);
      see "Qualified number restrictions" below;
    - parentheses;
    - ``owl:Thing`` / ``owl:Nothing`` for ⊤ / ⊥ (the W3C grammar treats these
      as ordinary ``owl:``-prefixed class names, not keywords — see "Top and
      Bottom" below — and this module maps exactly those two spellings onto
      :class:`~unicode_fol_kit.dl.concepts.Top` / :class:`~unicode_fol_kit.dl.concepts.Bottom`).

Rejected (real Manchester/OWL 2 syntax, but outside ALCHQ — see "Rejected
constructs" below): ``Self`` restrictions, inverse
roles (``inverse r``), nominal ("one-of") concepts (``{a, b}``), and the facets
of a datatype restriction that have no first-order image
(``xsd:pattern``, the length facets, an ordering facet on a non-numeric base).
Each is rejected with a
:class:`ManchesterSyntaxError` naming the specific construct, per the kit's
honesty convention (an unsupported construct is a loud, precise error —
never a silent mistranslation or a weaker-than-requested result).

Data restrictions
------------------
A restriction whose filler is a DATA RANGE is read as a data restriction
(:class:`~unicode_fol_kit.dl.concepts.DataExists` and friends), not as an
object restriction with a class that happens to be called ``xsd:integer``:

* ``d some xsd:integer``, ``d only DR`` -> ``DataExists`` / ``DataForAll``;
* ``d min 2 DR`` / ``d max 2 DR`` / ``d exactly 2 DR`` -> ``DataAtLeast`` /
  ``DataAtMost`` (``exactly`` as their conjunction, as for objects);
* ``d value "1"^^xsd:integer`` (or a bare numeral, ``d value 1``) ->
  ``DataHasValue``. The BARE numerals read are the W3C grammar's three
  unquoted literal forms: an integer (``1``, ``-3``, an ``xsd:integer``), a
  decimal (``1.5``, an ``xsd:decimal``) and a floating-point literal, which is
  an ``xsd:float`` and ends in ``f`` or ``F`` (``1.5f``, ``2F``, ``-.5f``,
  ``1.0e+2f``). The data layer has no first-order image of ``xsd:float`` (its
  value space has ``NaN`` and a signed zero), so ``d value 1.5f`` is the same
  ``DataHasValue`` as ``d value "1.5"^^xsd:float`` and is refused BY NAME at
  translation, exactly as that quoted spelling and the Functional-Style
  ``"1.5"^^xsd:float`` are; it is never read as an individual called ``1.5f``.
  What is not a literal form stays an individual name: ``1e5`` (no ``f``),
  ``1.5d``, ``1.5fx``;
* the data ranges: a datatype name, ``DR and DR``, ``DR or DR``, ``not DR``,
  ``{lit, lit}`` and the facet bracket ``xsd:decimal[>= 10000, <= 30000]``
  (``>=``/``<=``/``>``/``<`` for the four ordering facets, with a bare numeral
  typed as the base datatype). Read on its own by
  :func:`parse_manchester_data_range`.

Manchester Syntax has no declaration table, so a restriction's property is not
known to be a data property. The parser needs ONE signal, and the FILLER gives
it, because OWL 2 forbids a name being both a class and a datatype: a filler is
a data range when it names a built-in datatype of the OWL 2 datatype map
(``xsd:integer``, ``rdfs:Literal``, …, either spelling), when it is followed by
a facet bracket, when it is a brace-enclosed list of literals, or when its name
is one of the ``datatypes=`` the caller passes. A datatype DEFINED by the
ontology (``OboRoIdrange1``) has no marker a context-free parse could see:
``d some OboRoIdrange1`` reads as an object restriction over a class of that
name unless ``datatypes=("OboRoIdrange1",)`` says otherwise. ``hasPet some Dog``
is unchanged. A built-in datatype name in CLASS position is refused by name
(it cannot be a class), and an unqualified ``d min 2`` has no filler to tell
by and stays an object restriction.

Qualified number restrictions
------------------------------
``min``/``max``/``exactly`` parse into
:class:`~unicode_fol_kit.dl.concepts.AtLeast` /
:class:`~unicode_fol_kit.dl.concepts.AtMost` / their conjunction, per the W3C
grammar's ``objectPropertyExpression ('min'|'max'|'exactly') nonNegativeInteger
primary?`` production (`§2.2 <https://www.w3.org/TR/owl2-manchester-syntax/#Class_Expressions>`_):
the qualifying class is a ``primary`` slot exactly like ``some``/``only``'s
operand (so it parenthesises/binds by the same precedence rule — see "Grammar
and precedence" below), but it is OPTIONAL, defaulting to ``owl:Thing`` (⊤)
when the token right after the integer cannot start one (i.e. is not ``not``,
``inverse``, ``{``, ``(``, or a NAME). ``exactly n`` desugars to
``AtLeast(n, role, C) ⊓ AtMost(n, role, C)`` at PARSE time (there is no
separate "exactly" AST node — see :mod:`unicode_fol_kit.dl.concepts`), and
:func:`to_manchester` renders the two restrictions back out separately (as
``role min n ... and role max n ...``), which still round-trips to the exact
same conjunction rather than needing to be recognised and re-folded into
``exactly``. :func:`to_manchester` likewise omits the qualifying-class text
entirely when it is ⊤ (``role min n``, not ``role min n owl:Thing``), the
same "unqualified restriction" shorthand real OWL tooling uses; both
spellings parse back to the identical ``AtLeast``/``AtMost`` with ``Top()``
as the filler. See :mod:`unicode_fol_kit.dl.tableau`'s "Qualified number
restrictions" section for the reasoning side (the *simple roles* restriction
in particular: a number restriction is rejected outright, by role name, if
the role is transitive or has a transitive sub-role).

Grammar and precedence
-----------------------
The W3C grammar (`§2.2 <https://www.w3.org/TR/owl2-manchester-syntax/#Class_Expressions>`_)
is, in its own words, ambiguous "as stated" and resolved by later productions
binding *more tightly*::

    description  ::= conjunction ('or' conjunction)*        -- loosest
    conjunction  ::= primary ('and' primary)*
    primary      ::= 'not' primary | restriction | atomic
    restriction  ::= NAME 'some' primary | NAME 'only' primary | ...
    atomic       ::= NAME | '(' description ')'              -- tightest

i.e. restrictions (``some``/``only``) bind tightest, then ``not``, then
``and``, then ``or`` loosest — precisely the precedence lattice
:mod:`unicode_fol_kit.dl.concepts` already uses for the glyph syntax
(``_PREC``: ``Or=1 < And=2 < Not=Exists=ForAll=3 < Atomic=4``), so
:func:`to_manchester` reuses that exact lattice, just spelling the operators
as keywords instead of glyphs. Two consequences worth spelling out because
they are easy to get backwards:

- ``not`` binds *weaker* than ``some``/``only``: ``not r some A`` parses as
  ``not (r some A)`` (¬∃r.A) — ``primary``'s ``'not' primary`` production
  recurses into a ``primary`` that can itself *be* the whole restriction, so
  ``not`` scopes over it, not over the role name alone (a bare role has no
  negation in ALC in the first place).
- ``and`` binds tighter than ``or``: ``A and r some B or C`` parses as
  ``(A and (r some B)) or C`` — first ``and`` groups ``A`` with the
  restriction ``r some B`` (restrictions bind tighter than ``and``), then
  the result is ``or``-ed with ``C`` at the loosest level.
- ``and``/``or`` chains are flat in the grammar (``primary ('and' primary)*``)
  but the AST is binary, so a chain of three or more folds **left**:
  ``A and B and C`` is ``(A and B) and C``, matching
  :mod:`unicode_fol_kit.dl.parser`'s glyph parser exactly. So :func:`to_manchester`
  writes a nested operand of the SAME connective without parentheses on the
  left only: ``And(A, And(B, C))`` is ``A and (B and C)``, never ``A and B and
  C``, which reads back as the other tree.

``and``/``or``/``not``/``some``/``only``/``min``/``max``/``exactly``/
``value``/``inverse`` are case-sensitively lowercase keywords; ``Self`` is
capitalised; ``SubClassOf``/``EquivalentTo`` (used only by
:func:`parse_manchester_axiom`) are capitalised, with or without a trailing
colon (``SubClassOf`` and ``SubClassOf:`` are accepted identically — the W3C
grammar's frame header is colon-terminated, ``SubClassOf:``, but the
colon-free spelling is the common informal form for a standalone axiom and
is what callers of this module are expected to write). Per the W3C grammar
("Prefixes in abbreviated IRIs must not match any of the keywords of this
syntax"), none of these words may be used as a bare class or role name.

Top and Bottom
--------------
The Manchester grammar has no dedicated ⊤/⊥ keyword: ``owl:Thing`` and
``owl:Nothing`` are ordinary ``classIRI``s (the prefix ``owl:`` abbreviating
``http://www.w3.org/2002/07/owl#``) that merely happen to name the universal
and empty OWL classes. Since :mod:`unicode_fol_kit.dl.concepts` *does* carry
first-class :class:`~unicode_fol_kit.dl.concepts.Top`/:class:`~unicode_fol_kit.dl.concepts.Bottom`
constructors, this module special-cases exactly those two names, in either
spelling (``owl:Thing`` or the full IRI, bracketed or not; nothing else under the
``owl:`` prefix is recognised) rather than leaving them as
opaque :class:`~unicode_fol_kit.dl.concepts.Atomic` names, so
``owl:Thing and C`` reasons exactly like ``⊤ ⊓ C`` under
:func:`unicode_fol_kit.dl.tableau.concept_satisfiable` and friends.

Full IRIs are one name
----------------------
A name in angle brackets with a scheme, ``<http://x.org/a,b>``, is ONE atomic
name whatever it contains: ``,``, parentheses and square brackets are legal
inside an IRI, so the tokenizer reads the whole ``<...>`` (and a ``"..."^^<IRI>``
literal's datatype) before it looks for structural characters. The name is
STORED WITHOUT its brackets (``Atomic("http://x.org/a,b")``), in every position
-- a class, a datatype, an object or data property, an individual, a literal's
datatype, a facet's base -- which is what
:func:`~unicode_fol_kit.dl.owl_functional.parse_owl_functional` stores too, so
one IRI is ONE Python string whichever reader produced it: a datatype read here
matches the literals of that datatype, and ``owl:Thing`` is ``owl:Thing``
whether it is written ``owl:Thing`` or ``<http://www.w3.org/2002/07/owl#Thing>``
(the reserved names are compared in their canonical spelling, in every position
where one of them is special or refused -- a class, a data range, and the
datatype of a literal). The writers bracket on the way out, and only there:
:func:`to_manchester` writes a name that is a full IRI (it holds ``://``), or
that holds a structural character a bare name could not carry, as ``<name>``,
which reads back as the same string. What tells an IRI from the facet symbols
``<`` and ``<=`` is its scheme letter: a facet bound starts with a digit, a sign,
``=``, a dot or a quote, never a letter.

Names with no spelling
-----------------------
A name is written so that the reader reads back THAT name, or it is refused: the
writer asks the reader's own tokenizer (and, for a class and an individual, its
parser) whether the spelling reads back as exactly that name, and raises
:class:`ValueError` naming the name and the reason when no spelling does. The
bracketed form is the only escape the syntax has, and it needs a scheme and no
whitespace, so these have none:

* a keyword (``and``, ``some``, ``Domain``, ``SubClassOf:``, ...): ``<and>`` has
  no scheme and reads as the name ``<and>``;
* a name with whitespace, and the empty name (``A and B`` is a conjunction);
* a name with a structural character ``( ) { } [ ] ,`` and no scheme;
* a name that already holds the brackets of a full IRI (``<http://x.org/a>``):
  the reader stores an IRI without them, so the text reads back as another name;
* ``owl:Thing`` and ``owl:Nothing`` as a CLASS, bracketed or not, in either
  spelling: they are the top and the bottom class (as a role or an individual they
  are ordinary names);
* a built-in datatype (``xsd:integer``, ``rdfs:Literal``, ``owl:real``, ..., in
  either spelling of its namespace, bracketed or not) as a CLASS: the reader
  tells a data restriction from an object restriction by its filler, so
  ``r some xsd:integer`` is a DATA restriction whatever the writer meant, and
  the angle brackets of a full IRI change nothing. As a role, an individual or a
  datatype the name is an ordinary one.

A text the reader refuses, as opposed to reads as something else, is not a
reason to refuse the name.

Export-only asymmetry: inverse roles and nominals
-----------------------------------------------------
:func:`to_manchester` also RENDERS :class:`~unicode_fol_kit.dl.concepts.InverseRole`
(as ``inverse r``, in the ``role`` slot of ``some``/``only``/``min``/``max``)
and :class:`~unicode_fol_kit.dl.concepts.Nominal` (as ``{a}``) — real,
W3C-legal Manchester syntax the grammar always had room for (see "Rejected
constructs" above). :func:`parse_manchester` does NOT gain the matching
read side: ``INVERSE``/``LBRACE`` still hit the same ``_reject`` calls they
always did, unchanged. This is deliberate, not an oversight: rendering has
no soundness consequence, so it costs nothing to let a concept built with
either construct (e.g. from :mod:`unicode_fol_kit.dl.owl_reasoner`'s ALCHQ +
I/O fragment) still be printed/diffed/logged in this syntax, while parsing it
back in would re-admit exactly the constructs this module's ALC(HQ)-only
fragment exists to keep out. ``to_manchester(c)`` followed by
``parse_manchester`` on the result therefore round-trips for an
:class:`~unicode_fol_kit.dl.concepts.InverseRole`/:class:`~unicode_fol_kit.dl.concepts.Nominal`-free
``c`` exactly as before, and raises :class:`ManchesterSyntaxError` — naming
the construct, as always — for one that uses either.

Round-trip guarantee
---------------------
``parse_manchester(to_manchester(c)) == c`` for every concept ``c`` the reader
reads — every constructor but :class:`~unicode_fol_kit.dl.concepts.Nominal` and
an :class:`~unicode_fol_kit.dl.concepts.InverseRole` role, which are printed and
refused by name on the way back — see ``tests/test_owl_manchester.py`` for the
hand-checked precedence cases and ``tests/test_owl_manchester_roundtrip.py`` for
every constructor in every child slot and for random nestings. The
grammar/lattice argument above is why this holds structurally, not just on the
tested examples: :func:`to_manchester` parenthesises a child exactly when its
precedence is below the parent slot's threshold — the right operand of ``and``
(``or``) counting a nested ``and`` (``or``) as below it, because the reader folds
a flat chain to the left — the same rule :func:`parse_manchester` uses to
*resolve* precedence when reading text back in.

Role axioms: the one-line role-box frames
--------------------------------------------
:func:`parse_manchester_role_axiom` reads the role-box axiom shapes
:class:`~unicode_fol_kit.dl.tableau.TBox` holds — see "Role hierarchies and
transitive roles (RBox)" and "The rest of the OWL 2 role box" in
:mod:`unicode_fol_kit.dl.tableau`'s module docstring — each as the one-line
spelling this module already uses for :func:`parse_manchester_axiom`, rather
than the full multi-line W3C ``ObjectProperty:`` frame (whose annotation
slots this kit's role box does not represent). Seven shapes, every frame
keyword accepted with or without its W3C-grammar trailing colon exactly
like ``SubClassOf``/``SubClassOf:`` above:

* ``"r SubPropertyOf s"``        -> ``("subproperty", "r", "s")``
* ``"r EquivalentTo s"``         -> ``("equivalentproperty", "r", "s")``
* ``"r InverseOf s"``            -> ``("inverse", "r", "s")``
* ``"r DisjointWith s"``         -> ``("disjoint", "r", "s")``
* ``"r Domain: C"``              -> ``("domain", "r", Concept)``
* ``"r Range: C"``               -> ``("range", "r", Concept)``
* ``"r Characteristics: X"``     -> ``("transitive"/"symmetric"/…, "r")``, for
  all SEVEN of OWL 2's object-property characteristics (``Transitive``,
  ``Symmetric``, ``Asymmetric``, ``Reflexive``, ``Irreflexive``,
  ``Functional``, ``InverseFunctional``).

``Domain:``/``Range:`` are the two whose right-hand side is a CLASS
EXPRESSION rather than a role name, parsed by the same ``_description()``
every other class-expression position uses (so ``"r Domain: A and B"``
reads), which is why :func:`parse_manchester_role_axiom`'s return type is
``Tuple[object, ...]`` and not ``Tuple[str, ...]``.

A PARSER never refuses an axiom KIND — a ``TBox`` is what a parser fills from
a file, and which kinds the in-house tableau decides is recorded in
``dl.tableau._AXIOM_KINDS`` and enforced at query time (see "The axiom-kind
table" there). So all seven characteristics are read here, and three of them
(``Symmetric``, ``Reflexive``, ``InverseFunctional``) then make the TABLEAU
refuse the knowledge base by name while the FOL image still renders them. An
UNKNOWN characteristic word is still a syntax error naming itself.

Two shapes stay refused by name, and the refusal names
:func:`~unicode_fol_kit.dl.owl_functional.parse_owl_functional` as the entry
point that does read them:

* a PROPERTY CHAIN (``"r o s SubPropertyOf t"``). The bare name ``o`` is
  deliberately NOT promoted to a keyword, so a class or role literally named
  ``o`` keeps working in :func:`parse_manchester`;
* the comma-separated n-ary ``DisjointWith``/``EquivalentTo`` frame slot.
  ``DisjointWith`` in particular needs ALL pairs, and a one-axiom parser
  returning one pair would quietly produce a weaker theory.

One deliberate asymmetry with ``parse_owl_functional``, documented in both: an
OWL 2 built-in property name (``owl:topObjectProperty`` and the other three)
is refused here in EVERY position, including the tautological super-role case
that ``parse_owl_functional`` consumes as a no-op — a single-axiom parser has
no return shape for "this axiom is nothing", so it names the entry point that
does. :func:`role_axiom_to_manchester` is the dual renderer for every shape
above.
"""

import functools
import re
from typing import FrozenSet, Iterable, List, Optional, Tuple

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DataExists, DataForAll, DataHasValue,
    DataAtLeast, DataAtMost,
)
from .datatypes import (
    BUILTIN_DATATYPES, DataRange, Datatype, DatatypeRestriction, DataOneOf,
    DataComplementOf, DataIntersectionOf, DataUnionOf, Literal,
    UnsupportedDatatypeError, canonical_datatype_name, render_literal_fs,
    EXACT_NUMBER_DATATYPES as _EXACT_BASES,
)
from .tableau import (
    RESERVED_TOP_ROLES, RoleExpressionError, _reject_concept_role,
    _reject_concept_roles_deep, reserved_role,
)

__all__ = [
    "parse_manchester", "to_manchester", "parse_manchester_axiom",
    "parse_manchester_role_axiom", "role_axiom_to_manchester",
    "parse_manchester_data_range", "to_manchester_data_range",
    "parse_manchester_literal", "ManchesterSyntaxError",
]


class ManchesterSyntaxError(ValueError):
    """Raised by this module's parsers on malformed input *and* on syntax
    that is valid Manchester/OWL 2 but falls outside the ALC fragment (see
    the module docstring's "Rejected constructs"). Always a :class:`ValueError`
    subclass with a message naming the specific offending construct and its
    position in the input, per the kit's honesty convention.
    """


# --------------------------------------------------------------------------- #
# Tokenizer.
# --------------------------------------------------------------------------- #

# Lowercase connective/restriction keywords (case-sensitive, per the W3C grammar).
_KEYWORDS = {
    "and": "AND", "or": "OR", "not": "NOT", "some": "SOME", "only": "ONLY",
    "min": "MIN", "max": "MAX", "exactly": "EXACTLY", "value": "VALUE",
    "Self": "SELF", "inverse": "INVERSE",
}

# Axiom-frame keywords, accepted with or without a trailing colon (see module docstring).
_AXIOM_KEYWORDS = {"SubClassOf": "SUBCLASSOF", "EquivalentTo": "EQUIVALENTTO"}

# Role-axiom-frame keywords (see "Role axioms" in the module docstring), same
# colon-optional convention as _AXIOM_KEYWORDS above. `EquivalentTo` is NOT
# here: it is already an _AXIOM_KEYWORDS entry (shared with the class-axiom
# frame) and _classify_word checks that table first, so the role-axiom parser
# accepts its EQUIVALENTTO token directly.
_ROLE_AXIOM_KEYWORDS = {
    "SubPropertyOf": "SUBPROPERTYOF",
    "Characteristics": "CHARACTERISTICS",
    "InverseOf": "INVERSEOF",
    "DisjointWith": "DISJOINTWITH",
    "Domain": "DOMAIN",
    "Range": "RANGE",
}

_STRUCT_TOKENS = {
    "(": "LPAREN", ")": "RPAREN",
    "{": "LBRACE", "}": "RBRACE",
    "[": "LBRACKET", "]": "RBRACKET",
    ",": "COMMA",
}

# A Token is (type: str, value: str, pos: int).
_Token = Tuple[str, str, int]

#: A full IRI in angle brackets -- ``<http://x.org/a,b>`` -- which is ONE atomic
#: name whatever it contains (``,``, parentheses and brackets are all legal inside
#: an IRI), so the tokenizer reads it before it looks for structural characters.
#: It must open with a scheme (``letter (letter|digit|+|.|-)* ':'``) and contain
#: no whitespace; that is what tells it from the facet symbols ``<`` and ``<=``
#: (``xsd:integer[<5,>=3]``), whose next character is a digit, ``=``, a sign, a
#: dot or a quote -- never a letter.
_FULL_IRI = re.compile(r"<[A-Za-z][A-Za-z0-9+.\-]*:[^\s>]*>")


def _unbracket(name: str) -> str:
    """``name`` without the angle brackets of a full IRI: the ONE stored spelling
    of an IRI (see "Full IRIs are one name" in the module docstring). Any other
    name is returned unchanged."""
    return name[1:-1] if _FULL_IRI.fullmatch(name) else name


def _classify_word(word: str) -> str:
    """Classify a maximal non-structural, non-whitespace run as a keyword or NAME."""
    if word in _KEYWORDS:
        return _KEYWORDS[word]
    bare = word[:-1] if word.endswith(":") else word
    if bare in _AXIOM_KEYWORDS:
        return _AXIOM_KEYWORDS[bare]
    if bare in _ROLE_AXIOM_KEYWORDS:
        return _ROLE_AXIOM_KEYWORDS[bare]
    return "NAME"


def _tokenize(text: str) -> List[_Token]:
    """Split ``text`` into structural/keyword/NAME tokens plus a trailing EOF
    sentinel (whose ``pos`` is ``len(text)``, for error messages).
    """
    tokens: List[_Token] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch in _STRUCT_TOKENS:
            tokens.append((_STRUCT_TOKENS[ch], ch, i))
            i += 1
            continue
        if ch == "<":
            iri = _FULL_IRI.match(text, i)
            # ... and it must END there: `<http://x.org/a>b` is one odd word, as
            # it always was, not an IRI followed by a name.
            if iri is not None and (iri.end() == n or text[iri.end()].isspace()
                                    or text[iri.end()] in _STRUCT_TOKENS):
                tokens.append(("NAME", iri.group(0)[1:-1], i))   # stored WITHOUT brackets
                i = iri.end()
                continue
        if ch == '"':
            # A quoted literal is ONE token, with its ^^datatype or @language
            # suffix: its text may hold whitespace and structural characters
            # (the lexical form of a string), which nothing else here may.
            start = i
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" and i + 1 < n else 1
            if i >= n:
                raise ManchesterSyntaxError(
                    f"parse_manchester: unterminated string literal starting "
                    f"at position {start} in {text!r}")
            i += 1
            iri = _FULL_IRI.match(text, i + 2) if text.startswith("^^", i) else None
            if iri is not None:
                i = iri.end()           # "..."^^<IRI>: the datatype IRI is one name
            while i < n and not text[i].isspace() and text[i] not in _STRUCT_TOKENS:
                i += 1
            tokens.append(("LITERAL", text[start:i], start))
            continue
        start = i
        while i < n and not text[i].isspace() and text[i] not in _STRUCT_TOKENS:
            i += 1
        word = text[start:i]
        tokens.append((_classify_word(word), word, start))
    tokens.append(("EOF", "", n))
    return tokens


# --------------------------------------------------------------------------- #
# Recursive-descent parser (description expressions only; parse_manchester_axiom
# splits an axiom into two token slices and runs one of these per side).
# --------------------------------------------------------------------------- #

class _Parser:
    """A single parse of one token slice; not re-used across calls."""

    def __init__(self, tokens: List[_Token], text: str,
                 datatypes: Iterable[str] = ()):
        self._tokens = tokens
        self._text = text
        self._i = 0
        self._datatypes: FrozenSet[str] = frozenset(
            canonical_datatype_name(_unbracket(name)) for name in datatypes)

    def _peek(self) -> _Token:
        return self._tokens[self._i]

    def _advance(self) -> _Token:
        tok = self._tokens[self._i]
        self._i += 1
        return tok

    def _error(self, message: str) -> ManchesterSyntaxError:
        return ManchesterSyntaxError(f"{message} in {self._text!r}")

    def _expect(self, ttype: str, what: str) -> _Token:
        tok = self._peek()
        if tok[0] != ttype:
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(
                f"parse_manchester: expected {what} but found {found} "
                f"at position {tok[2]}")
        return self._advance()

    def _expect_eof(self) -> None:
        tok = self._peek()
        if tok[0] != "EOF":
            raise self._error(
                f"parse_manchester: unexpected trailing input {tok[1]!r} "
                f"at position {tok[2]}")

    def _reject(self, what: str, tok: _Token) -> None:
        raise self._error(
            f"parse_manchester: {what} — not supported outside ALC "
            f"(found {tok[1]!r} at position {tok[2]})")

    def _checked(self, concept: Concept, pos: int) -> Concept:
        """``concept``, unless its role is an OWL 2 built-in property name (or
        ``=``/``≠``) — refused BY NAME, as :func:`parse_manchester_role_axiom`
        and ``dl.parse_owl_functional`` refuse the same name. ``owl:topObject
        Property some A`` used to read as an ordinary role of that name, whose
        verdict is not the universal property's. ``exactly`` is the ``And`` of
        two restrictions over ONE role, so the left one stands for both."""
        try:
            _reject_concept_role(
                concept.left if isinstance(concept, And) else concept,
                where="parse_manchester")
        except RoleExpressionError as exc:
            raise self._error(f"{exc} (at position {pos})") from exc
        return concept

    # -- grammar levels, loosest first (mirrors the W3C production order) -- #

    def _description(self) -> Concept:
        left = self._conjunction()
        while self._peek()[0] == "OR":
            self._advance()
            left = Or(left, self._conjunction())
        return left

    def _conjunction(self) -> Concept:
        left = self._primary()
        while self._peek()[0] == "AND":
            self._advance()
            left = And(left, self._primary())
        return left

    def _primary(self) -> Concept:
        ttype, value, pos = self._peek()
        if ttype == "NOT":
            self._advance()
            return Not(self._primary())
        if ttype == "INVERSE":
            self._reject("inverse roles ('inverse r')", self._peek())
        if ttype == "LBRACE":
            self._reject("nominal concepts ('{a, b}')", self._peek())
        if ttype == "LPAREN":
            self._advance()
            inner = self._description()
            self._expect("RPAREN", "')'")
            return inner
        if ttype == "NAME":
            self._advance()
            if self._peek()[0] == "LBRACKET":
                raise self._error(
                    f"parse_manchester: the facet bracket after {value!r} (at "
                    f"position {self._peek()[2]}) makes it a DATA RANGE, which is "
                    f"not a class expression. Use it as the filler of a data "
                    f"restriction ('d some {value}[...]') or read it on its own "
                    f"with parse_manchester_data_range")
            nxt = self._peek()
            if nxt[0] == "SOME":
                self._advance()
                if self._filler_is_data_range():
                    return self._checked(DataExists(value, self._data_primary()), pos)
                return self._checked(Exists(value, self._primary()), pos)
            if nxt[0] == "ONLY":
                self._advance()
                if self._filler_is_data_range():
                    return self._checked(DataForAll(value, self._data_primary()), pos)
                return self._checked(ForAll(value, self._primary()), pos)
            if nxt[0] in ("MIN", "MAX", "EXACTLY"):
                self._advance()
                return self._checked(self._number_restriction(nxt[0], value), pos)
            if nxt[0] == "VALUE":
                # `r value a` -> HasValue(r, a); `d value "1"^^xsd:integer` (or a
                # bare numeral) -> DataHasValue(d, lit). The keyword was always
                # tokenised (see _KEYWORDS). NOT Exists(value, Nominal(...)):
                # `r some {a}` is the other spelling and stays refused, so the
                # two round-trip apart -- see dl.concepts.HasValue.
                self._advance()
                literal = self._literal_or_none()
                if literal is not None:
                    return self._checked(DataHasValue(value, literal), pos)
                return self._checked(HasValue(
                    value, self._expect("NAME", "an individual name or a literal")[1]), pos)
            if nxt[0] == "SELF":
                self._reject("Self restrictions ('Self')", nxt)
            canonical = canonical_datatype_name(value)
            if canonical == "owl:Thing":
                return Top()
            if canonical == "owl:Nothing":
                return Bottom()
            if self._is_datatype(value):
                raise self._error(
                    f"parse_manchester: {value!r} (at position {pos}) is a "
                    f"DATATYPE, not a class — OWL 2 does not let one name be "
                    f"both. Use it as the filler of a data restriction "
                    f"('d some {value}') or read it with parse_manchester_data_range")
            return Atomic(value)
        found = "end of input" if ttype == "EOF" else f"{value!r}"
        raise self._error(
            f"parse_manchester: unexpected {found} at position {pos}; "
            "expected a class name, 'not', 'owl:Thing', 'owl:Nothing', or '('")

    # -- qualified number restrictions ('min'/'max'/'exactly') ---------- #

    _PRIMARY_START = {"NOT", "INVERSE", "LBRACE", "LPAREN", "NAME"}

    def _number_restriction(self, kind: str, role: str) -> Concept:
        """Parse the ``n primary?`` tail of ``role (min|max|exactly) n primary?``,
        having already consumed ``role`` and the ``kind`` keyword (see the module
        docstring's "Qualified number restrictions"). The qualifying class defaults
        to ``owl:Thing`` (⊤) when the next token cannot start a ``primary``.
        """
        n = self._expect_nonneg_int()
        if self._peek()[0] in self._PRIMARY_START and self._filler_is_data_range():
            datarange = self._data_primary()
            if kind == "MIN":
                return DataAtLeast(n, role, datarange)
            if kind == "MAX":
                return DataAtMost(n, role, datarange)
            return And(DataAtLeast(n, role, datarange), DataAtMost(n, role, datarange))
        filler = self._primary() if self._peek()[0] in self._PRIMARY_START else Top()
        if kind == "MIN":
            return AtLeast(n, role, filler)
        if kind == "MAX":
            return AtMost(n, role, filler)
        return And(AtLeast(n, role, filler), AtMost(n, role, filler))     # 'exactly'

    def _expect_nonneg_int(self) -> int:
        tok = self._peek()
        if tok[0] == "NAME" and tok[1].isdigit():
            self._advance()
            return int(tok[1])
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"parse_manchester: expected a non-negative integer but found {found} "
            f"at position {tok[2]}")

    def parse_description(self) -> Concept:
        c = self._description()
        self._expect_eof()
        return c

    # -- data ranges and literals ---------------------------------------- #

    def _is_datatype(self, name: str) -> bool:
        """True iff ``name`` is a datatype for this parse: one of the OWL 2
        datatype map's (either spelling of its namespace) or one the caller
        declared with ``datatypes=``."""
        canonical = canonical_datatype_name(name)
        return canonical in BUILTIN_DATATYPES or canonical in self._datatypes

    def _filler_is_data_range(self) -> bool:
        """Does the filler that starts at the cursor read as a DATA range?

        Looks only at the filler's HEAD, skipping any ``not`` and ``(`` in front
        of it: a name that is a datatype or is followed by a facet bracket, or a
        brace-enclosed list that starts with a literal. This is the one signal a
        context-free Manchester parse has (see the module docstring's "Data
        restrictions"); it never consumes anything.
        """
        tokens, i = self._tokens, self._i
        while tokens[i][0] in ("NOT", "LPAREN"):
            i += 1
        ttype, value, _pos = tokens[i]
        if ttype == "NAME":
            return tokens[i + 1][0] == "LBRACKET" or self._is_datatype(value)
        if ttype == "LBRACE":
            head = tokens[i + 1]
            return head[0] == "LITERAL" or (head[0] == "NAME" and _bare_numeral(head[1]))
        return False

    def _literal_or_none(self) -> Optional[Literal]:
        """Consume a literal if one is at the cursor: a quoted literal token or
        a bare numeral (``1``, ``-3``, ``1.5``, or the floating-point ``1.5f``);
        else ``None``."""
        ttype, value, pos = self._peek()
        if ttype == "LITERAL":
            self._advance()
            return self._build(lambda: _literal_from_token(value, pos), value, pos)
        if ttype == "NAME" and _bare_numeral(value):
            self._advance()
            return self._build(lambda: _bare_literal(value, None), value, pos)
        return None

    def _build(self, make, what: str, pos: int):
        """``make()``, a data-layer refusal re-raised as the parser's own error
        naming ``what`` and where."""
        try:
            return make()
        except UnsupportedDatatypeError as exc:
            raise self._error(f"parse_manchester: {exc} (at position {pos}, {what!r})") from exc

    def _data_description(self) -> DataRange:
        """``dataConjunction ('or' dataConjunction)*`` -- an N-ARY union, so a
        chain is one :class:`DataUnionOf`; a parenthesised group stays nested."""
        parts = [self._data_conjunction()]
        while self._peek()[0] == "OR":
            self._advance()
            parts.append(self._data_conjunction())
        return parts[0] if len(parts) == 1 else DataUnionOf(tuple(parts))

    def _data_conjunction(self) -> DataRange:
        parts = [self._data_primary()]
        while self._peek()[0] == "AND":
            self._advance()
            parts.append(self._data_primary())
        return parts[0] if len(parts) == 1 else DataIntersectionOf(tuple(parts))

    def _data_primary(self) -> DataRange:
        """``'not'? dataAtomic`` with ``dataAtomic`` a datatype, a facet
        restriction ``dt[facet lit, …]``, a literal set ``{lit, …}`` or a
        parenthesised data range."""
        ttype, value, pos = self._peek()
        if ttype == "NOT":
            self._advance()
            return DataComplementOf(self._data_primary())
        if ttype == "LPAREN":
            self._advance()
            inner = self._data_description()
            self._expect("RPAREN", "')'")
            return inner
        if ttype == "LBRACE":
            self._advance()
            values = [self._expect_literal()]
            while self._peek()[0] == "COMMA":
                self._advance()
                values.append(self._expect_literal())
            self._expect("RBRACE", "'}'")
            return DataOneOf(tuple(values))
        if ttype == "NAME":
            if canonical_datatype_name(value) in ("owl:Thing", "owl:Nothing"):
                # The mirror of the "is a DATATYPE, not a class" refusal in
                # _primary, and the same policy dl.parse_owl_functional has: a
                # class is not a data range, and a datatype called owl:Thing
                # would be an uninterpreted predicate of that name.
                raise self._error(
                    f"parse_manchester: {value!r} (at position {pos}) is a CLASS, "
                    f"not a data range — OWL 2 does not let one name be both. "
                    f"The data domain's own 'everything' is rdfs:Literal; use a "
                    f"datatype name here")
            self._advance()
            if self._peek()[0] == "LBRACKET":
                return self._facet_restriction(value, pos)
            return Datatype(value)
        found = "end of input" if ttype == "EOF" else f"{value!r}"
        raise self._error(
            f"parse_manchester: expected a data range but found {found} at "
            f"position {pos}; expected a datatype name, 'not', '{{', or '('")

    def _expect_literal(self) -> Literal:
        literal = self._literal_or_none()
        if literal is None:
            found = "end of input" if self._peek()[0] == "EOF" else f"{self._peek()[1]!r}"
            raise self._error(
                f"parse_manchester: expected a literal but found {found} at "
                f"position {self._peek()[2]}")
        return literal

    def _facet_restriction(self, base: str, pos: int) -> DataRange:
        """``dt '[' facet literal (',' facet literal)* ']'`` (the name already
        consumed, the cursor on ``[``)."""
        self._expect("LBRACKET", "'['")
        facets: List[Tuple[str, Literal]] = []
        while True:
            ftype, fvalue, fpos = self._peek()
            if ftype != "NAME":
                found = "end of input" if ftype == "EOF" else f"{fvalue!r}"
                raise self._error(
                    f"parse_manchester: expected a facet ({', '.join(_FACET_SYMBOLS)}, "
                    f"…) but found {found} at position {fpos}")
            self._advance()
            symbol, glued = fvalue, None
            # `>=5` with no space after the symbol: the symbol is the longest
            # ordering prefix, the rest the bound.
            if fvalue not in _FACET_SYMBOLS:
                for candidate in (">=", "<=", ">", "<"):
                    if fvalue.startswith(candidate):
                        symbol, glued = candidate, fvalue[len(candidate):]
                        break
            if symbol not in _FACET_SYMBOLS:
                raise self._error(
                    f"parse_manchester: unknown facet {symbol!r} at position "
                    f"{fpos}; the facets are {', '.join(_FACET_SYMBOLS)}")
            if glued is not None:
                bound = self._build(lambda: _bare_literal(glued, base), glued, fpos)
            else:
                btype, bvalue, bpos = self._peek()
                if btype == "LITERAL":
                    self._advance()
                    bound = self._build(lambda: _literal_from_token(bvalue, bpos), bvalue, bpos)
                elif btype == "NAME" and _bare_numeral(bvalue):
                    self._advance()
                    bound = self._build(lambda: _bare_literal(bvalue, base), bvalue, bpos)
                else:
                    found = "end of input" if btype == "EOF" else f"{bvalue!r}"
                    raise self._error(
                        f"parse_manchester: expected the facet {symbol!r}'s "
                        f"literal but found {found} at position {bpos}")
            facets.append((_FACET_SYMBOLS[symbol], bound))
            if self._peek()[0] == "COMMA":
                self._advance()
                continue
            break
        self._expect("RBRACKET", "']'")
        return self._build(
            lambda: DatatypeRestriction(Datatype(base), tuple(facets)), base, pos)

    def parse_data_range(self) -> DataRange:
        datarange = self._data_description()
        self._expect_eof()
        return datarange


# --------------------------------------------------------------------------- #
# Literals and facets.
# --------------------------------------------------------------------------- #

#: Manchester Syntax's facet spellings, mapped to the canonical facet names the
#: data layer uses. The four ordering symbols are the ones this kit translates;
#: the keyword facets are read so that the REFUSAL can name them.
_FACET_SYMBOLS = {
    ">=": "xsd:minInclusive", "<=": "xsd:maxInclusive",
    ">": "xsd:minExclusive", "<": "xsd:maxExclusive",
    "length": "xsd:length", "minLength": "xsd:minLength", "maxLength": "xsd:maxLength",
    "pattern": "xsd:pattern", "langRange": "rdf:langRange",
    "totalDigits": "xsd:totalDigits", "fractionDigits": "xsd:fractionDigits",
}
_SYMBOL_OF_FACET = {facet: symbol for symbol, facet in _FACET_SYMBOLS.items()}

_BARE_NUMERAL = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)\Z")
#: The W3C grammar's ``floatingPointLiteral``: a sign, ``digits ['.' digits]`` or
#: ``'.' digits``, an optional exponent, and the ``f``/``F`` that makes it a
#: float. Group 1 is the lexical form WITHOUT the suffix (``1.0e+2f`` is the
#: ``xsd:float`` ``"1.0e+2"``).
_FLOATING_POINT = re.compile(
    r"([+-]?(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)[fF]\Z")
_TYPED_LITERAL = re.compile(r'"((?:[^"\\]|\\.)*)"(?:\^\^(\S+)|@(\S+))?\Z', re.DOTALL)


def _bare_numeral(name: str) -> bool:
    """Is ``name`` a bare Manchester numeral: an integer (``1``, ``-3``), a
    decimal (``1.5``) or a floating-point literal (``1.5f``, ``1.0e+2F``)?"""
    return (_BARE_NUMERAL.match(name) is not None
            or _FLOATING_POINT.match(name) is not None)


def _bare_literal(text: str, base: Optional[str]) -> Literal:
    """The literal a BARE numeral stands for: a floating-point literal is an
    ``xsd:float`` whatever the facet's base (the ``f`` says so, as the quoted
    ``"1.5"^^xsd:float`` does); otherwise typed as the facet's base datatype
    when that is an exact-number datatype (``xsd:decimal[>= 10000]`` bounds are
    decimals), else by its shape — an integer, or a decimal if it has a point."""
    floating = _FLOATING_POINT.match(text)
    if floating is not None:
        return Literal(floating.group(1), "xsd:float")
    canonical = canonical_datatype_name(base) if base is not None else None
    if canonical is not None and canonical in _EXACT_BASES:
        return Literal(text, canonical)
    return Literal(text, "xsd:decimal" if "." in text else "xsd:integer")


def _literal_from_token(token: str, pos: int = 0) -> Literal:
    match = _TYPED_LITERAL.match(token)
    if match is None:
        raise UnsupportedDatatypeError(f"{token!r} is not a literal")
    lexical = re.sub(r'\\(["\\])', r"\1", match.group(1))
    if match.group(3) is not None:
        return Literal(lexical, "xsd:string", match.group(3))
    datatype = match.group(2) or "xsd:string"
    if datatype.startswith("<") and datatype.endswith(">"):
        datatype = datatype[1:-1]
    if canonical_datatype_name(datatype) in ("owl:Thing", "owl:Nothing"):
        # the same refusal a data range gets (see _Parser._data_primary), for the
        # datatype of a literal, in either spelling of the name
        raise UnsupportedDatatypeError(
            f"{datatype!r} is a CLASS, not a data range — OWL 2 does not let "
            f"one name be both, so it cannot be the datatype of a literal. "
            f"The data domain's own 'everything' is rdfs:Literal; use a "
            f"datatype name here")
    return Literal(lexical, datatype)



# --------------------------------------------------------------------------- #
# Public API.
# --------------------------------------------------------------------------- #

def parse_manchester_literal(text: str) -> Literal:
    """Parse one Manchester-syntax literal: ``"400"^^xsd:integer``, ``"abc"``
    (an ``xsd:string``), ``"abc"@en``, or a bare numeral (``400`` an
    ``xsd:integer``, ``1.5`` an ``xsd:decimal``, ``1.5f`` an ``xsd:float``).

    Raises:
        ManchesterSyntaxError: malformed text, an ill-typed literal.
    """
    text = text.strip()
    try:
        if _bare_numeral(text):
            return _bare_literal(text, None)
        return _literal_from_token(text)
    except UnsupportedDatatypeError as exc:
        raise ManchesterSyntaxError(
            f"parse_manchester_literal: {exc} in {text!r}") from exc


def parse_manchester_data_range(text: str, *, datatypes: Iterable[str] = ()) -> DataRange:
    """Parse ``text`` as a Manchester-syntax DATA RANGE: a datatype name,
    ``xsd:decimal[>= 10000, <= 30000]``, ``{1, 2}``, ``not DR``, ``DR and DR``,
    ``DR or DR`` and parentheses (precedence as for class expressions: ``not``
    over ``and`` over ``or``).

    Args:
        text: The data range.
        datatypes: Extra datatype names, for symmetry with
            :func:`parse_manchester`; a name in a data-range position is a
            datatype whether or not it is listed, so this only matters there.

    Raises:
        ManchesterSyntaxError: malformed text, or an out-of-scope facet
            (``xsd:pattern``, the length facets, an ordering facet on a
            non-numeric base) -- refused by name.
    """
    return _Parser(_tokenize(text), text, datatypes).parse_data_range()


def to_manchester_data_range(datarange: DataRange) -> str:
    """Render ``datarange`` in Manchester Syntax, dual to
    :func:`parse_manchester_data_range`: ``parse_manchester_data_range(
    to_manchester_data_range(dr)) == dr`` for every data range. A facet bound is
    written as a bare numeral exactly when reading that numeral back gives the
    same literal; otherwise as a typed literal."""
    return _render_datarange(datarange)


def parse_manchester(text: str, *, datatypes: Iterable[str] = ()) -> Concept:
    """Parse ``text`` (OWL 2 Manchester Syntax, ALC fragment) into a :class:`Concept`.

    Round-trips against :func:`to_manchester`: ``parse_manchester(to_manchester(c))
    == c`` for every ALC concept ``c`` (see the module docstring's "Round-trip
    guarantee").

    Args:
        text: A Manchester-syntax class expression, e.g.
            ``"Person and hasChild some (Doctor and not Rich)"``.
        datatypes: Extra datatype names to treat as data ranges, beyond the
            OWL 2 datatype map's own. A restriction whose filler names one is a
            DATA restriction (``HasNumber some OboRoIdrange1``); without the
            declaration it reads as an object restriction over a class of that
            name, because Manchester Syntax has no declaration table.

    Returns:
        The parsed :class:`Concept`.

    Raises:
        ManchesterSyntaxError: On malformed input (unbalanced parentheses, a
            stray keyword, trailing garbage, …) or on syntax that is valid
            Manchester/OWL 2 but outside ALC (cardinalities, ``value``,
            ``Self``, ``inverse``, nominals, datatype facets — see the module
            docstring's "Rejected constructs").
    """
    return _Parser(_tokenize(text), text, datatypes).parse_description()


def to_manchester(concept: Concept) -> str:
    """Render ``concept`` in OWL 2 Manchester Syntax, dual to :func:`parse_manchester`.

    Parenthesises a child expression exactly when its precedence is below the
    threshold of the slot it sits in (see the module docstring's "Grammar and
    precedence"; the right operand of ``and`` / ``or`` is parenthesised when it
    is itself an ``and`` / ``or``, since a flat chain reads to the left), so the
    output is minimally parenthesised and re-parses to an identical AST.

    Args:
        concept: Any ALC :class:`Concept` (as built by
            :mod:`unicode_fol_kit.dl.concepts`'s constructors).

    Returns:
        The Manchester-syntax rendering, e.g. ``"r some (A and B)"``.

    Raises:
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            a restriction's role (at any depth) is an OWL 2
            built-in property name or ``=`` / ``≠``. :func:`parse_manchester`
            refuses that text, and
            :func:`~unicode_fol_kit.dl.owl_functional.to_owl_functional_class_expression`
            refuses the same concept, with the same function — a writer never
            prints text its own reader refuses.
        ValueError: a class, role, property or individual name has no spelling
            that :func:`parse_manchester` reads back as that name (see "Names
            with no spelling" in the module docstring), or an individual is
            spelled like a numeral.
    """
    _reject_concept_roles_deep(concept, where="to_manchester")
    return _render(concept)


def parse_manchester_axiom(text: str, *,
                           datatypes: Iterable[str] = ()) -> Tuple[str, Concept, Concept]:
    """Parse a Manchester-syntax subsumption or equivalence axiom.

    Accepts exactly ``"C SubClassOf D"`` and ``"C EquivalentTo D"`` (the
    frame keyword may optionally carry its W3C-grammar trailing colon,
    ``"SubClassOf:"``/``"EquivalentTo:"``), where ``C`` and ``D`` are each
    parsed by :func:`parse_manchester`. The keyword is located at
    parenthesis-depth 0; it must occur exactly once.

    Args:
        text: An axiom of the form ``"<description> SubClassOf <description>"``
            or ``"<description> EquivalentTo <description>"``.

    Returns:
        ``("subclass", C, D)`` for ``C SubClassOf D``, or
        ``("equivalent", C, D)`` for ``C EquivalentTo D``.

    Raises:
        ManchesterSyntaxError: If no top-level ``SubClassOf``/``EquivalentTo``
            keyword is found, if more than one is found, or if either side
            fails to parse as an ALC description (see :func:`parse_manchester`).
    """
    tokens = _tokenize(text)
    depth = 0
    found: List[Tuple[int, str]] = []
    for idx, (ttype, _value, _pos) in enumerate(tokens):
        if ttype == "LPAREN":
            depth += 1
        elif ttype == "RPAREN":
            depth -= 1
        elif depth == 0 and ttype in ("SUBCLASSOF", "EQUIVALENTTO"):
            found.append((idx, ttype))
    if not found:
        raise ManchesterSyntaxError(
            "parse_manchester_axiom: expected exactly one top-level "
            f"'SubClassOf' or 'EquivalentTo' keyword, found none in {text!r}")
    if len(found) > 1:
        raise ManchesterSyntaxError(
            "parse_manchester_axiom: expected exactly one top-level "
            f"'SubClassOf'/'EquivalentTo' keyword, found {len(found)} in {text!r}")
    idx, kind = found[0]
    left_tokens = tokens[:idx] + [("EOF", "", tokens[idx][2])]
    right_tokens = tokens[idx + 1:]
    sub = _Parser(left_tokens, text, datatypes).parse_description()
    sup = _Parser(right_tokens, text, datatypes).parse_description()
    label = "subclass" if kind == "SUBCLASSOF" else "equivalent"
    return (label, sub, sup)


# Every OWL 2 object-property characteristic the W3C grammar recognises,
# mapped to this module's own tag for it (the first element of
# parse_manchester_role_axiom's return tuple). ALL SEVEN are read: a parser
# never refuses an axiom KIND -- see "Role axioms" in the module docstring.
_CHARACTERISTIC_TAGS = {
    "Transitive": "transitive",
    "Symmetric": "symmetric",
    "Asymmetric": "asymmetric",
    "Reflexive": "reflexive",
    "Irreflexive": "irreflexive",
    "Functional": "functional",
    "InverseFunctional": "inversefunctional",
}

#: ``tag -> (frame keyword, arity)`` for the four BINARY role-axiom frames
#: whose right-hand side is another ROLE NAME.
_BINARY_ROLE_FRAMES = {
    "SUBPROPERTYOF": ("subproperty", "SubPropertyOf"),
    "EQUIVALENTTO": ("equivalentproperty", "EquivalentTo"),
    "INVERSEOF": ("inverse", "InverseOf"),
    "DISJOINTWITH": ("disjoint", "DisjointWith"),
}

#: ``token -> (tag, frame keyword)`` for the two frames whose right-hand side
#: is a CLASS EXPRESSION, not a role: ``r Domain: A`` and ``r Range: A``. A
#: table of their own because the right side is parsed by ``_description()``
#: and the returned tuple carries a :class:`Concept`, which is what widens
#: :func:`parse_manchester_role_axiom`'s return type.
_FILLER_ROLE_FRAMES = {
    "DOMAIN": ("domain", "Domain"),
    "RANGE": ("range", "Range"),
}

_CHAIN_HINT = (
    "a PROPERTY CHAIN ('r o s SubPropertyOf t') is not one of this module's "
    "one-line role-axiom shapes: the bare name 'o' is deliberately not a "
    "keyword here, so a class or role literally named 'o' keeps working in "
    "parse_manchester. Read a chain with dl.parse_owl_functional "
    "('SubObjectPropertyOf(ObjectPropertyChain(r s) t)') or build it with "
    "dl.TBox.add_role_chain")


def _check_role_axiom_name(role: str, where: str) -> None:
    """Refuse an OWL 2 BUILT-IN property name in a Manchester role axiom.

    Refused in EVERY position, including the tautological super-role case
    ``dl.parse_owl_functional`` consumes as a no-op: a single-axiom parser has
    no return shape for "this axiom is nothing". Deliberate asymmetry between
    the two parsers, documented in both (see "Role axioms" in this module's
    docstring and "The OWL 2 built-in roles" in ``dl.tableau``'s).
    """
    builtin = reserved_role(role)
    if builtin is None:
        return
    universal = builtin in RESERVED_TOP_ROLES
    raise ManchesterSyntaxError(
        f"parse_manchester_role_axiom: {role!r} is an OWL 2 BUILT-IN property "
        f"({builtin} — "
        + ("the universal property: it relates every pair"
           if universal else "the empty property: it relates no pair at all")
        + f"), not an ordinary role name, and ALCHQ (this kit's DL fragment) "
        f"has neither the universal nor the empty role, so {where} cannot "
        f"carry it. "
        + ("An inclusion INTO it is a TAUTOLOGY, which this single-axiom "
           "parser has no return shape for — dl.parse_owl_functional reads "
           "that shape and consumes it as a documented no-op."
           if universal else
           "'P is empty' is the concept inclusion 'owl:Thing SubClassOf P only "
           "owl:Nothing', which parse_manchester_axiom does read.")
    )


def parse_manchester_role_axiom(text: str) -> Tuple[object, ...]:
    """Parse one Manchester-syntax role-box axiom.

    Seven one-line shapes, of the full W3C ``ObjectProperty:`` frame syntax —
    see "Role axioms" in the module docstring for why only these, and for the
    two shapes that stay refused by name. Every frame keyword may carry its
    W3C-grammar trailing colon (``"SubPropertyOf:"``), exactly like
    ``SubClassOf``/``SubClassOf:`` in :func:`parse_manchester_axiom`.

    Args:
        text: A single role axiom, e.g. ``"hasChild SubPropertyOf hasDescendant"``,
            ``"partOf InverseOf hasPart"``, ``"hasSink DisjointWith hasSource"``,
            ``"hasSink EquivalentTo hasOutput"``,
            ``"hasDescendant Characteristics: Transitive"``,
            ``"Covers Domain: Study"`` or ``"HasUnit Range: Unit and Measurable"``.

    Returns:
        ``("subproperty", sub_role, super_role)`` (feeding
        :meth:`~unicode_fol_kit.dl.tableau.TBox.add_role_inclusion`),
        ``("equivalentproperty", p, q)`` (``add_equivalent_roles``),
        ``("inverse", p, q)`` (``add_inverse_roles``),
        ``("disjoint", p, q)`` (``add_disjoint_roles``),
        ``("domain", role, Concept)`` (``add_role_domain``),
        ``("range", role, Concept)`` (``add_role_range``), or
        ``(tag, role)`` for a ``Characteristics:`` declaration, where ``tag``
        is one of :data:`_CHARACTERISTIC_TAGS`' values and
        ``"add_" + tag + "_role"`` is the builder — except
        ``"inversefunctional"``, whose builder is
        ``add_inverse_functional_role``.

    The return type is ``Tuple[object, ...]``, not ``Tuple[str, ...]``: the
    ``Domain:``/``Range:`` shapes carry a :class:`Concept` in the third slot,
    because a domain or range axiom's right-hand side IS a class expression —
    parsed by the same ``_description()`` every other class-expression position
    uses, so ``"r Domain: A and B"`` works.

    Raises:
        ManchesterSyntaxError: malformed input, an unknown role characteristic
            (named explicitly in the message), an OWL 2 built-in property
            name, a property chain, or anything not matching one of the seven
            shapes.
    """
    tokens = _tokenize(text)

    def error(message: str) -> ManchesterSyntaxError:
        return ManchesterSyntaxError(f"parse_manchester_role_axiom: {message} in {text!r}")

    if tokens[0][0] != "NAME":
        found = "end of input" if tokens[0][0] == "EOF" else f"{tokens[0][1]!r}"
        raise error(f"expected a role name but found {found} at position {tokens[0][2]}")
    role = tokens[0][1]
    keyword = tokens[1]

    if keyword[0] in _BINARY_ROLE_FRAMES:
        tag, spelling = _BINARY_ROLE_FRAMES[keyword[0]]
        if len(tokens) == 4 and tokens[2][0] == "NAME" and tokens[3][0] == "EOF":
            _check_role_axiom_name(role, f"a {spelling} axiom")
            _check_role_axiom_name(tokens[2][1], f"a {spelling} axiom")
            return (tag, role, tokens[2][1])
        if (keyword[0] in ("DISJOINTWITH", "EQUIVALENTTO")
                and any(t[0] == "NAME" for t in tokens[2:])
                and text.count(",") > 0):
            raise error(
                f"the comma-separated n-ary {spelling} frame slot is not one "
                f"of this module's one-line role-axiom shapes — only the "
                f"binary '<role> {spelling} <role>' is. Read the n-ary form "
                f"with dl.parse_owl_functional, which expands it correctly "
                f"(DisjointObjectProperties needs ALL pairs, not a chain of "
                f"consecutive ones), or call dl.TBox."
                + ("add_disjoint_roles" if keyword[0] == "DISJOINTWITH"
                   else "add_equivalent_roles")
                + " with every role")
        raise error(f"expected exactly '<role> {spelling} <role>'")

    if keyword[0] in _FILLER_ROLE_FRAMES:
        tag, spelling = _FILLER_ROLE_FRAMES[keyword[0]]
        _check_role_axiom_name(role, f"a {spelling}: axiom")
        if tokens[2][0] == "EOF":
            raise error(f"expected exactly '<role> {spelling}: <description>'")
        # The filler goes through the full description grammar, so
        # `r Domain: A and B` and `r Range: s some C` both read -- a domain or
        # range axiom's right-hand side is a CLASS EXPRESSION, not a name.
        filler = _Parser(list(tokens[2:]), text).parse_description()
        return (tag, role, filler)

    if keyword[0] == "CHARACTERISTICS":
        if len(tokens) == 4 and tokens[2][0] == "NAME" and tokens[3][0] == "EOF":
            characteristic = tokens[2][1]
            if characteristic in _CHARACTERISTIC_TAGS:
                _check_role_axiom_name(role, f"a Characteristics: "
                                             f"{characteristic} axiom")
                return (_CHARACTERISTIC_TAGS[characteristic], role)
            raise error(
                f"unknown role characteristic {characteristic!r} — OWL 2 has "
                f"exactly seven: " + ", ".join(sorted(_CHARACTERISTIC_TAGS)))
        raise error("expected exactly '<role> Characteristics: <characteristic>'")

    if keyword[0] == "NAME" and keyword[1] == "o":
        raise error(_CHAIN_HINT)

    found = "end of input" if keyword[0] == "EOF" else f"{keyword[1]!r}"
    raise error(
        f"expected 'SubPropertyOf', 'EquivalentTo', 'InverseOf', "
        f"'DisjointWith', 'Domain:', 'Range:' or 'Characteristics:' but found "
        f"{found} at position {keyword[2]}")


# --------------------------------------------------------------------------- #
# Renderer.
# --------------------------------------------------------------------------- #

# Same lattice as concepts.py's _PREC (Or=1 < And=2 < Not=Exists=ForAll=AtLeast=
# AtMost=3 < Atomic=4): see the module docstring's "Grammar and precedence" for why
# the two coincide.
_PREC = {Or: 1, And: 2, Not: 3, Exists: 3, ForAll: 3, AtLeast: 3, AtMost: 3,
         HasValue: 3, DataExists: 3, DataForAll: 3, DataHasValue: 3,
         DataAtLeast: 3, DataAtMost: 3,
         Atomic: 4, Top: 4, Bottom: 4, Nominal: 4}


def _one_name_token(spelled: str, name: str) -> Optional[List[_Token]]:
    """The tokens of ``spelled`` when the reader takes it for ONE plain name that
    is exactly ``name`` (not a keyword, not a literal, not several words), else
    ``None``."""
    try:
        tokens = _tokenize(spelled)
    except ManchesterSyntaxError:
        return None
    if len(tokens) == 2 and tokens[0][0] == "NAME" and tokens[0][1] == name:
        return tokens
    return None


def _why_no_spelling(name: str) -> str:
    """Why no spelling of ``name`` is read back as that one name."""
    if name == "":
        return "it is empty"
    if _FULL_IRI.fullmatch(name):
        return ("it already holds the angle brackets of a full IRI, and the reader "
                "stores an IRI without them, so <...> reads back as another name "
                "(the text between the brackets)")
    if any(ch.isspace() for ch in name):
        return ("it holds whitespace, where the reader splits a name, and only a "
                "full IRI (a scheme, no whitespace) is written in angle brackets")
    if _classify_word(name) != "NAME":
        return ("it is a keyword of this syntax, which has no escape for it: only "
                "a full IRI (a scheme, no whitespace) is written in angle brackets")
    if any(ch in _STRUCT_TOKENS for ch in name):
        return ("it holds one of ( ) { } [ ] , and has no scheme to be bracketed "
                "with as a full IRI")
    return "no spelling of it is read back as one name"


def _names_a_builtin_datatype(name: str) -> bool:
    """True iff ``name`` is a built-in datatype of the OWL 2 datatype map, in
    either spelling of its namespace (``xsd:integer`` or the full IRI, bracketed
    or not) — what the reader takes for a datatype wherever a datatype can stand."""
    return canonical_datatype_name(name) in BUILTIN_DATATYPES


_DATATYPE_CLASS_REASON = (
    "it is the name of a built-in datatype, and the reader reads that name as the "
    "datatype in every spelling (the full IRI and either namespace form included): "
    "after some / only / min / max / exactly it turns the restriction into a DATA "
    "restriction, and in any other position it refuses the text, because OWL 2 "
    "does not let one name be both a class and a datatype")


@functools.lru_cache(maxsize=8192)
def _name_spelling(name: str, kind: str) -> Tuple[Optional[str], str]:
    """``(spelling, "")`` for the one-token spelling of ``name`` that the reader
    reads back as exactly that name, or ``(None, reason)`` when there is none.

    The spellings tried are the full IRI ``<name>`` (first, for a name that holds
    ``://`` or a structural character, as before) and the bare name; a spelling
    counts only when the READER's own tokenizer takes it for one plain name, and,
    for a ``kind`` of ``"class"`` / ``"individual"``, when the reader's own
    parser then reads it back as that class / that individual and not as another
    expression (``owl:Thing`` is the top class in every spelling; a numeral is a
    data value).

    A class named like a built-in datatype has no spelling at all. The reader
    decides between an object and a data restriction by the FILLER, so
    ``r some xsd:integer`` is a data restriction whatever the writer meant, and
    the full IRI reads the same way: refusing the bare class alone, which the
    reader refuses on its own, would leave the same name written, and read as
    something else, in the one position where it is a filler.
    """
    candidates: List[str] = []
    bracketed = f"<{name}>"
    if ("://" in name or any(ch in _STRUCT_TOKENS for ch in name)) \
            and _FULL_IRI.fullmatch(bracketed):
        candidates.append(bracketed)
    candidates.append(name)
    for spelled in candidates:
        tokens = _one_name_token(spelled, name)
        if tokens is None:
            continue
        if kind == "class":
            if _names_a_builtin_datatype(name):
                return None, _DATATYPE_CLASS_REASON
            try:
                back = _Parser(tokens, spelled).parse_description()
            except ManchesterSyntaxError:
                return spelled, ""              # refused on reading: loud, not another reading
            if back != Atomic(name):
                return None, (f"read as a class it is {back!r}, in every spelling "
                              f"(owl:Thing and owl:Nothing are the top and the bottom class)")
        elif kind == "individual":
            text = f"r value {spelled}"
            try:
                back = _Parser(_tokenize(text), text).parse_description()
            except ManchesterSyntaxError:
                return spelled, ""
            if back != HasValue("r", name):
                return None, f"read after 'value' it is {back!r}, not an individual"
        return spelled, ""
    return None, _why_no_spelling(name)


def _render_name(name: str, kind: str = "name") -> str:
    """A kit name as ONE Manchester token that reads back as that name: ``<name>``
    when it is a full IRI (it holds ``://``) or holds a structural character a
    bare name could not carry, the bare name otherwise. The brackets are added
    here and only here (the readers store an IRI without them).

    ``kind`` is ``"class"`` or ``"individual"`` where the reader gives the name a
    meaning of its own (``owl:Thing``, a numeral), and ``"name"`` elsewhere.

    Raises:
        ValueError: no spelling reads back as ``name``: it is a keyword of the
            syntax, holds whitespace or a structural character that no full IRI
            can carry (an IRI needs a scheme and no whitespace), is empty, already
            holds the brackets of a full IRI (which the reader strips), is
            read as another expression (``owl:Thing``), or is a built-in
            datatype's name used as a class (the reader makes a restriction
            over it a data restriction). The text is never written as
            something that reads back as another name or expression.
    """
    spelling, reason = _name_spelling(name, kind)
    if spelling is None:
        if reason == _DATATYPE_CLASS_REASON:
            remedy = ("Rename the class: every reader of this kit reads a "
                      "built-in datatype's name as that datatype, or refuses it as "
                      "a class.")
        else:
            remedy = ("Rename it, or write the concept with "
                      "dl.to_owl_functional_class_expression, whose <...> carries a "
                      "name that has no '>' in it.")
        raise ValueError(
            f"to_manchester: the name {name!r} cannot be written so that "
            f"parse_manchester reads it back as that name: {reason}. {remedy}")
    return spelling


def _render_literal(literal: Literal) -> str:
    """A literal as one Manchester token: ``"5"^^xsd:integer`` with the datatype
    written through :func:`_render_name`, so a user datatype IRI is bracketed
    (``"5"^^<http://ex.org/dt,Small>``) and reads back as the same datatype."""
    return render_literal_fs(literal, _render_name)


def _render_role(role) -> str:
    """Render a ``role`` field: ``inverse r`` for an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole` (the W3C grammar's own
    spelling — see "Export-only asymmetry" in the module docstring), the bare
    name otherwise.
    """
    if isinstance(role, InverseRole):
        return f"inverse {_render_name(role.role)}"
    return _render_name(role)


def _render(c: Concept) -> str:
    """Render a concept with precedence-aware parenthesisation."""
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return _render_name(c.name, "class")
    if isinstance(c, Nominal):
        # Behind `some` / `only` / `min` / `max` the reader takes `{3}` for a set of
        # DATA values, not for a nominal, so an individual spelled like a numeral
        # has no nominal spelling that reads back as it (cf. the value restriction).
        if _bare_numeral(c.individual):
            raise ValueError(
                f"to_manchester: the individual {c.individual!r} of the nominal "
                f"{c.to_unicode()} is spelled like a numeral, and Manchester Syntax "
                f"reads '{{{c.individual}}}' behind a role keyword as a set of DATA "
                f"values. There is no spelling that reads back as this individual: "
                f"rename it, or write the concept with "
                f"dl.to_owl_functional_class_expression.")
        return "{" + _render_name(c.individual) + "}"
    if isinstance(c, Not):
        return "not " + _paren(c.concept, 3)
    # The reader folds a flat chain LEFT (``A and B and C`` is ``(A and B) and C``),
    # so only a LEFT operand of the same connective may go unparenthesised: the
    # right operand is written one level tighter, and an ``and`` inside an
    # ``and`` (an ``or`` inside an ``or``) on the right keeps its parentheses.
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} and {_paren(c.right, 3)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} or {_paren(c.right, 2)}"
    if isinstance(c, Exists):
        return f"{_render_role(c.role)} some {_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"{_render_role(c.role)} only {_paren(c.concept, 3)}"
    if isinstance(c, HasValue):
        # `r value 5` and `r value 1.5f` are DATA value restrictions to the
        # reader: an individual whose name is spelled like a bare numeral cannot
        # be written so that it reads back as an individual. Refused by name,
        # like every other text this writer would not read back as it was.
        if _bare_numeral(c.individual):
            raise ValueError(
                f"to_manchester: the individual {c.individual!r} of the value "
                f"restriction {c.to_unicode()} is spelled like a numeral, and "
                f"Manchester Syntax reads '{_render_role(c.role)} value "
                f"{c.individual}' as a DATA value restriction to that literal. "
                f"There is no spelling that reads back as this individual: "
                f"rename it, or write the axiom with dl.to_owl_functional.")
        # No _paren: the operand is an individual NAME, never a nested
        # description, so there is no precedence question to ask.
        return f"{_render_role(c.role)} value {_render_name(c.individual, 'individual')}"
    if isinstance(c, AtLeast):
        return _number_restriction_render(c.role, "min", c.n, c.concept)
    if isinstance(c, AtMost):
        return _number_restriction_render(c.role, "max", c.n, c.concept)
    # The data restrictions. The filler of a data cardinality is ALWAYS written
    # (even rdfs:Literal): `d min 2` alone reads back as an OBJECT restriction,
    # because with no filler there is nothing to say it is a data property.
    if isinstance(c, DataExists):
        return f"{_render_name(c.prop)} some {_render_datarange(c.datarange, paren=True)}"
    if isinstance(c, DataForAll):
        return f"{_render_name(c.prop)} only {_render_datarange(c.datarange, paren=True)}"
    if isinstance(c, DataHasValue):
        return f"{_render_name(c.prop)} value {_render_literal(c.value)}"
    if isinstance(c, DataAtLeast):
        return f"{_render_name(c.prop)} min {c.n} {_render_datarange(c.datarange, paren=True)}"
    if isinstance(c, DataAtMost):
        return f"{_render_name(c.prop)} max {c.n} {_render_datarange(c.datarange, paren=True)}"
    raise TypeError(f"to_manchester: unsupported concept {type(c).__name__}")


def _render_bound(bound: Literal, base: str) -> str:
    """A facet bound as a bare numeral if reading it back gives the same
    literal, else as a typed literal."""
    bare = bound.lexical.strip()
    if _bare_numeral(bare):
        try:
            if _bare_literal(bare, base) == bound:
                return bare
        except UnsupportedDatatypeError:
            pass
    return _render_literal(bound)


def _render_datarange(dr: DataRange, *, paren: bool = False) -> str:
    """Render a data range; ``paren`` parenthesises a compound one, for a slot
    (a restriction's filler, an ``and``/``or`` operand) that binds tighter."""
    if isinstance(dr, Datatype):
        return _render_name(dr.name)
    if isinstance(dr, DatatypeRestriction):
        facets = ", ".join(f"{_SYMBOL_OF_FACET[facet]} {_render_bound(bound, dr.base.name)}"
                           for facet, bound in dr.facets)
        return f"{_render_name(dr.base.name)}[{facets}]"
    if isinstance(dr, DataOneOf):
        return "{" + ", ".join(_render_bound(v, "") for v in dr.values) + "}"
    if isinstance(dr, DataComplementOf):
        return "not " + _render_datarange(dr.datarange, paren=True)
    if isinstance(dr, DataIntersectionOf):
        inner = " and ".join(_render_datarange(r, paren=True) for r in dr.ranges)
        return f"({inner})" if paren else inner
    if isinstance(dr, DataUnionOf):
        inner = " or ".join(_render_datarange(r, paren=True) for r in dr.ranges)
        return f"({inner})" if paren else inner
    raise TypeError(f"to_manchester: unsupported data range {type(dr).__name__}")


def _number_restriction_render(role, keyword: str, n: int, filler: Concept) -> str:
    """Render ``role (min|max) n filler``, omitting the qualifying class entirely
    when ``filler`` is ⊤ (the "unqualified restriction" shorthand — see the module
    docstring's "Qualified number restrictions"; both spellings parse back to the
    same ``Top()``-qualified concept).
    """
    rendered_role = _render_role(role)
    if isinstance(filler, Top):
        return f"{rendered_role} {keyword} {n}"
    return f"{rendered_role} {keyword} {n} {_paren(filler, 3)}"


def _paren(c: Concept, parent_prec: int) -> str:
    """Parenthesise ``c`` when its precedence is below the parent slot's threshold."""
    inner = _render(c)
    return f"({inner})" if _PREC.get(type(c), 4) < parent_prec else inner


#: ``tag -> frame keyword`` for the four binary shapes, derived from
#: :data:`_BINARY_ROLE_FRAMES` so the reader and the writer cannot name the
#: same shape differently.
_BINARY_FRAME_SPELLING = {tag: spelling
                          for tag, spelling in _BINARY_ROLE_FRAMES.values()}

#: ``tag -> frame keyword`` for the two CLASS-EXPRESSION frames, derived from
#: :data:`_FILLER_ROLE_FRAMES` for the same reason.
_FILLER_FRAME_SPELLING = {tag: spelling
                          for tag, spelling in _FILLER_ROLE_FRAMES.values()}

#: ``tag -> characteristic word``, the inverse of :data:`_CHARACTERISTIC_TAGS`.
_TAG_CHARACTERISTIC = {tag: word for word, tag in _CHARACTERISTIC_TAGS.items()}


def _renderable_role(role: object, axiom: Tuple[object, ...]) -> str:
    """The role operand of a role axiom, or a ``ValueError`` naming why not.

    The reader takes a plain role NAME in every position (an inverse role has
    no one-line spelling here, and the OWL 2 built-ins are refused by name), so
    writing anything else would print text that does not read back -- for an
    ``InverseRole`` the dataclass ``repr``, ``InverseRole(role='s')``, which
    no reader would take for a role.
    """
    if not isinstance(role, str):
        raise ValueError(
            f"role_axiom_to_manchester: a role operand must be a role NAME (a "
            f"str), got {role!r} in {axiom!r}. The one-line role-axiom syntax "
            f"has no spelling for an inverse role (dl.parse_manchester_role_axiom "
            f"reads none): write it with dl.to_owl_functional, which spells a "
            f"role inclusion with an inverse as SubObjectPropertyOf(r "
            f"ObjectInverseOf(s)).")
    builtin = reserved_role(role)
    if builtin is not None:
        raise ValueError(
            f"role_axiom_to_manchester: {role!r} is an OWL 2 BUILT-IN property "
            f"({builtin}), not an ordinary role name -- "
            f"dl.parse_manchester_role_axiom refuses it in every position, so "
            f"the text written here would not read back, in {axiom!r}.")
    return _render_name(role)


def role_axiom_to_manchester(*axiom: object) -> str:
    """Render a role-box axiom, dual to :func:`parse_manchester_role_axiom`.

    Round-trips: ``parse_manchester_role_axiom(role_axiom_to_manchester(*axiom))
    == axiom`` for every ``axiom`` one of that function's return shapes. All
    three tables are derived from the reader's own (see
    :data:`_BINARY_FRAME_SPELLING`), so a shape the reader gains cannot be
    spelled differently here.

    Args:
        *axiom: One of ``("subproperty", sub, sup)``,
            ``("equivalentproperty", p, q)``, ``("inverse", p, q)``,
            ``("disjoint", p, q)``, ``("domain", role, Concept)``,
            ``("range", role, Concept)`` or ``(characteristic_tag, role)`` —
            exactly what :func:`parse_manchester_role_axiom` returns.

    Returns:
        The one-line Manchester spelling, e.g.
        ``"partOf InverseOf hasPart"``, ``"r Characteristics: Asymmetric"`` or
        ``"Covers Domain: Study"``.

    Raises:
        ValueError: ``axiom`` is not one of the recognised shapes, or a role
            operand is not a plain role name (an ``InverseRole``, or an OWL 2
            built-in property name, which the reader refuses in every position
            -- text it would not read back is never written), or the class
            expression of a ``Domain:`` / ``Range:`` axiom has one as the role
            of a restriction at any depth (a
            :class:`~unicode_fol_kit.dl.tableau.RoleExpressionError`, as for
            :func:`to_manchester`).
    """
    # The tag is narrowed to `str` before any table lookup: the parameter is
    # `object` because the Domain:/Range: shapes carry a Concept, and a lookup
    # keyed on an un-narrowed `object` is exactly the kind of thing the pinned
    # mypy configuration refuses.
    tag = axiom[0] if axiom else None
    if not isinstance(tag, str):
        raise ValueError(
            f"role_axiom_to_manchester: the first element must be the shape's "
            f"TAG (a str), got {tag!r} in {axiom!r}")
    if len(axiom) == 3 and tag in _FILLER_FRAME_SPELLING:
        filler = axiom[2]
        if not isinstance(filler, Concept):
            raise ValueError(
                f"role_axiom_to_manchester: a {tag!r} axiom's third element is "
                f"its CLASS EXPRESSION, got {filler!r}")
        # The keyword keeps its colon here, unlike the role-to-role frames: the
        # W3C grammar's frame slot is `Domain: <description>` and the colon is
        # what tells a reader the right-hand side is a class expression (the
        # reader accepts it with or without, like every other frame keyword).
        role = _renderable_role(axiom[1], axiom)
        _reject_concept_roles_deep(filler, where="role_axiom_to_manchester")
        return f"{role} {_FILLER_FRAME_SPELLING[tag]}: {_render(filler)}"
    if len(axiom) == 3 and tag in _BINARY_FRAME_SPELLING:
        first = _renderable_role(axiom[1], axiom)
        second = _renderable_role(axiom[2], axiom)
        return f"{first} {_BINARY_FRAME_SPELLING[tag]} {second}"
    if len(axiom) == 2 and tag in _TAG_CHARACTERISTIC:
        role = _renderable_role(axiom[1], axiom)
        return f"{role} Characteristics: {_TAG_CHARACTERISTIC[tag]}"
    raise ValueError(
        f"role_axiom_to_manchester: expected one of "
        f"{sorted(_BINARY_FRAME_SPELLING)} with two roles, one of "
        f"{sorted(_FILLER_FRAME_SPELLING)} with a role and a concept, or one "
        f"of {sorted(_TAG_CHARACTERISTIC)} with one role, got {axiom!r}")
