"""Datatypes, literals and data ranges: the data half of the OWL 2 DL layer.

OWL 2 has two disjoint domains: the OBJECT domain (individuals, ``Δ_I``) and
the DATA domain (``Δ_D``: numbers, strings, dates, … — the *data values*).
Classes and object properties live over the first, datatypes and data
properties relate the first to the second. This module holds the pieces of the
second that the rest of :mod:`unicode_logic_kit.dl` needs:

* :class:`Literal` — a typed literal such as ``"400"^^xsd:integer``, and the
  term of the first-order image it becomes (:meth:`Literal.to_term`);
* the DATA-RANGE AST (:class:`Datatype`, :class:`DatatypeRestriction`,
  :class:`DataOneOf`, :class:`DataComplementOf`, :class:`DataIntersectionOf`,
  :class:`DataUnionOf`) and its first-order image
  (:func:`datarange_to_fol`);
* the tables the two-sorted image reads (:func:`datatype_ancestors`,
  :func:`datatype_family`) and the two reserved guard predicates
  :data:`OWL_THING` / :data:`OWL_DATA`.

The image is GUARDED ONE-SORTED first-order logic
---------------------------------------------------
Not the kit's many-sorted logic (``SortedQuantifier``/``SortedConstant``): a
sorted constant must be lower-case, and every OEO individual and literal is
CamelCase. A datatype ``D`` becomes the unary predicate ``D(v)``; the object
domain and the data domain become the two reserved unary predicates
``OwlThing`` and ``OwlData``, and ``rdfs:Literal`` — the datatype whose value
space IS the data domain — maps onto ``OwlData`` exactly as ``owl:Thing``
already maps onto ``⊤``. The axioms that make the two predicates a
two-sorted theory (their disjointness, the typing of every property, the
datatype lattice, …) are SIDE axioms of the knowledge base, never conjuncts of
its formula: see :func:`unicode_logic_kit.dl.translate.data_sort_axioms`.

What a literal becomes
-----------------------
OWL's literal-to-value map is fixed, so a literal denotes ONE data value and
the image needs a TERM for it that is the same term for the same value and a
different one for a different value:

* a literal of the exact-number family (``xsd:integer`` and its subtypes,
  ``xsd:decimal``) becomes ``Number(value)`` — ``"1"^^xsd:integer`` and
  ``"1.0"^^xsd:decimal`` are the SAME data value in OWL 2 (the value spaces
  overlap), so both become ``Number(1)``. A decimal that no kit ``Number``
  can hold EXACTLY (more than 15 significant digits, where two different
  decimals can be one float) is refused by name rather than read as another
  number;
* a literal of ``xsd:float``/``xsd:double`` is REFUSED by name: their value
  spaces are disjoint from the exact numbers (``-0``, ``NaN``, ``±INF``), so
  ``Number(1)`` would conflate two different values and any other term would
  be a made-up one;
* ``xsd:normalizedString`` and ``xsd:token`` accept any string once XSD's
  whitespace processing (§4.3.6) has run — *replace* (tab, line feed and
  carriage return become a space) for the first, *collapse* (replace, then runs
  of spaces become one and the ends are trimmed) for the second — so the literal
  denotes the same VALUE as the ``xsd:string`` of the processed text and gets
  that ``xsd:string`` term, typed by the datatype it was written with:
  ``"  a  b "^^xsd:token`` is ``"a b"^^xsd:string``. ``xsd:anyURI`` is a family
  of its own, disjoint from the strings, whose term is the collapsed text: two
  different texts are two different values. ``xsd:language``, ``xsd:Name``,
  ``xsd:NCName`` and ``xsd:NMTOKEN`` have lexical spaces (the XML name
  productions) this kit does not validate, so it can neither say that a literal
  of one denotes a value at all nor that it is the ``xsd:token`` of the same
  text: they are REFUSED by name, like ``xsd:float``;
* every other literal becomes ``Constant('"abc"^^xsd:string')`` — its own
  OWL text, kept verbatim, which is the convention :mod:`unicode_logic_kit.dl`
  already follows for IRI-shaped names. The unicode syntax writes a constant of
  any name in single quotes when its bare word would not read back as that
  constant, so this one prints ``'"abc"^^xsd:string'`` and reads back through
  ``api.parse_any`` as the very constant (a single quote inside the lexical form
  is escaped with a backslash between the quotes). What stays a documented limit
  of the printed form, and a limit of RULE 5 (what the kit prints reads back
  through ``api.parse_any``) that holds BY DESIGN for the data layer, is the name
  of a built-in datatype: it is a PREDICATE, a predicate has no quoted form, and
  so every image that names one (``xsd:integer(x0)``) prints text
  ``api.parse_any`` rejects, which ``tests/test_printed_text_reads_back.py``
  carves out. The AST route (``api.prove`` over the nodes) is unaffected. To
  print such an image as text the kit reads, rename its symbols with
  :func:`unicode_logic_kit.fol.sanitize.sanitize_all` over the WHOLE premise list
  with one shared mapping — ``sanitize_names`` applied to each formula with a
  fresh mapping gives ``xsd:integer`` and a class called ``Xsdinteger`` the same
  token, which is not injective.

The scope of facets
--------------------
The four ordering facets ``xsd:minInclusive`` / ``xsd:maxInclusive`` /
``xsd:minExclusive`` / ``xsd:maxExclusive`` on an exact-number base datatype
are the only facets with an image this kit can interpret: they become the
native comparison atoms ``≥ ≤ > <``. Every other facet (``xsd:pattern``, the
length facets, ``xsd:totalDigits``/``xsd:fractionDigits``, ``rdf:langRange``)
and an ordering facet on a non-numeric base (``xsd:dateTime``) is REFUSED by
name: its image would be an uninterpreted function or predicate that
constrains nothing while looking as though it did, which is exactly the silent
approximation this kit does not do.
"""

import re
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from typing import Callable, Dict, FrozenSet, Iterable, Optional, Tuple

from ..fol._fol_nodes import _numeral_from_text
from ..fol.nodes import And, Atom, Constant, Node, Not, Number, Or

__all__ = [
    "Literal", "DataRange", "Datatype", "DatatypeRestriction", "DataOneOf",
    "DataComplementOf", "DataIntersectionOf", "DataUnionOf",
    "UnsupportedDatatypeError", "datarange_to_fol", "OWL_THING", "OWL_DATA",
]

#: The reserved unary predicate of the OBJECT domain (``Δ_I``) in the
#: two-sorted image, and of the DATA domain (``Δ_D``). Fixed names, in the
#: way ``fol.qml`` fixes ``World``/``Object``: a knowledge base that uses
#: either as a class, role, property, individual or datatype name is refused
#: by name when the two-sorted axioms are asked for.
OWL_THING = "OwlThing"
OWL_DATA = "OwlData"


class UnsupportedDatatypeError(ValueError):
    """Raised for a datatype construct that is valid OWL 2 but has no faithful
    first-order image in this kit: an out-of-scope facet, an ordering facet on
    a non-numeric base, a literal whose value the kit cannot represent
    exactly, an ill-typed literal, or a knowledge base that uses a name the
    two-sorted image reserves.

    Always a refusal BY NAME, with the construct, the reason and the spelling
    to use instead — never an approximation.
    """


# --------------------------------------------------------------------------- #
# Names
# --------------------------------------------------------------------------- #

_NAMESPACES = (
    ("http://www.w3.org/2001/XMLSchema#", "xsd:"),
    ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:"),
    ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:"),
    ("http://www.w3.org/2002/07/owl#", "owl:"),
)


def canonical_datatype_name(name: str) -> str:
    """``name`` with a built-in namespace written as its usual prefix:
    ``http://www.w3.org/2001/XMLSchema#integer`` -- bracketed or not, as an IRI
    is written in Manchester and Functional-Style Syntax -- and ``xsd:integer``
    are one datatype, so they must be one NAME. Any other name is returned
    unchanged (brackets and all: a user datatype's IRI is its own name).
    """
    bare = name[1:-1] if name[:1] == "<" and name[-1:] == ">" else name
    for namespace, prefix in _NAMESPACES:
        if bare.startswith(namespace):
            return prefix + bare[len(namespace):]
    return name


_RDFS_LITERAL = "rdfs:Literal"

# Direct super-datatypes, from the OWL 2 datatype map (Structural Specification
# §4): the value space of each key is a SUBSET of its parents'.
_PARENTS: Dict[str, Tuple[str, ...]] = {
    "owl:real": (),
    "owl:rational": ("owl:real",),
    "xsd:decimal": ("owl:rational",),
    "xsd:integer": ("xsd:decimal",),
    "xsd:nonNegativeInteger": ("xsd:integer",),
    "xsd:positiveInteger": ("xsd:nonNegativeInteger",),
    "xsd:nonPositiveInteger": ("xsd:integer",),
    "xsd:negativeInteger": ("xsd:nonPositiveInteger",),
    "xsd:long": ("xsd:integer",),
    "xsd:int": ("xsd:long",),
    "xsd:short": ("xsd:int",),
    "xsd:byte": ("xsd:short",),
    "xsd:unsignedLong": ("xsd:nonNegativeInteger",),
    "xsd:unsignedInt": ("xsd:unsignedLong",),
    "xsd:unsignedShort": ("xsd:unsignedInt",),
    "xsd:unsignedByte": ("xsd:unsignedShort",),
    "rdf:PlainLiteral": (),
    "xsd:string": ("rdf:PlainLiteral",),
    "xsd:normalizedString": ("xsd:string",),
    "xsd:token": ("xsd:normalizedString",),
    "xsd:language": ("xsd:token",),
    "xsd:Name": ("xsd:token",),
    "xsd:NCName": ("xsd:Name",),
    "xsd:NMTOKEN": ("xsd:token",),
    "xsd:double": (),
    "xsd:float": (),
    "xsd:boolean": (),
    "xsd:hexBinary": (),
    "xsd:base64Binary": (),
    "xsd:anyURI": (),
    "xsd:dateTime": (),
    "xsd:dateTimeStamp": ("xsd:dateTime",),
    "rdf:XMLLiteral": (),
}

# The datatypes whose value spaces are pairwise DISJOINT in OWL 2: one entry
# per "family root". Two built-in datatypes of different families share no
# value (OWL 2 §4: even xsd:float/xsd:double are disjoint from owl:real and
# from each other). Within a family nothing is claimed — `xsd:Name` and
# `xsd:NMTOKEN` overlap, `xsd:positiveInteger` and `xsd:negativeInteger` do not,
# and the lattice edges are the only within-family facts the image states.
_FAMILY_ROOTS = ("owl:real", "xsd:double", "xsd:float", "rdf:PlainLiteral",
                 "xsd:boolean", "xsd:hexBinary", "xsd:base64Binary",
                 "xsd:anyURI", "xsd:dateTime", "rdf:XMLLiteral")

#: Every datatype of the OWL 2 datatype map this module knows, plus ``rdfs:Literal``.
BUILTIN_DATATYPES: FrozenSet[str] = frozenset(_PARENTS) | {_RDFS_LITERAL}


def datatype_ancestors(name: str) -> FrozenSet[str]:
    """Every built-in datatype that strictly CONTAINS ``name``'s value space
    (transitively, ``rdfs:Literal`` excluded — it contains everything). Empty
    for a name outside the OWL 2 datatype map: a user datatype's relation to
    the lattice is whatever its own ``DatatypeDefinition`` says.
    """
    name = canonical_datatype_name(name)
    found = set()
    stack = list(_PARENTS.get(name, ()))
    while stack:
        parent = stack.pop()
        if parent not in found:
            found.add(parent)
            stack.extend(_PARENTS.get(parent, ()))
    return frozenset(found)


def datatype_family(name: str) -> Optional[str]:
    """The family root (one of :data:`_FAMILY_ROOTS`) a built-in datatype
    belongs to, or ``None`` for ``rdfs:Literal`` and every name outside the
    OWL 2 datatype map. Two datatypes with DIFFERENT non-``None`` families are
    disjoint.
    """
    name = canonical_datatype_name(name)
    if name not in _PARENTS:
        return None
    for root in _FAMILY_ROOTS:
        if name == root or root in datatype_ancestors(name):
            return root
    return None


def is_builtin_datatype(name: str) -> bool:
    """True iff ``name`` is in the OWL 2 datatype map (or is ``rdfs:Literal``)."""
    return canonical_datatype_name(name) in BUILTIN_DATATYPES


# --------------------------------------------------------------------------- #
# Literals
# --------------------------------------------------------------------------- #

# (min, max) of each integer-valued datatype; ``None`` is unbounded.
_INTEGER_TYPES: Dict[str, Tuple[Optional[int], Optional[int]]] = {
    "xsd:integer": (None, None),
    "xsd:nonNegativeInteger": (0, None),
    "xsd:positiveInteger": (1, None),
    "xsd:nonPositiveInteger": (None, 0),
    "xsd:negativeInteger": (None, -1),
    "xsd:long": (-2 ** 63, 2 ** 63 - 1),
    "xsd:int": (-2 ** 31, 2 ** 31 - 1),
    "xsd:short": (-2 ** 15, 2 ** 15 - 1),
    "xsd:byte": (-2 ** 7, 2 ** 7 - 1),
    "xsd:unsignedLong": (0, 2 ** 64 - 1),
    "xsd:unsignedInt": (0, 2 ** 32 - 1),
    "xsd:unsignedShort": (0, 2 ** 16 - 1),
    "xsd:unsignedByte": (0, 2 ** 8 - 1),
}

#: The datatypes whose literals are EXACT numbers: the integer family and
#: ``xsd:decimal``. A literal of one of them becomes a ``Number``.
EXACT_NUMBER_DATATYPES: FrozenSet[str] = frozenset(_INTEGER_TYPES) | {"xsd:decimal"}

#: The datatypes an ordering facet may restrict: the exact numbers, plus the two
#: umbrella datatypes ``owl:real``/``owl:rational`` (which have no literals of
#: their own but are legal bases).
NUMERIC_BASES: FrozenSet[str] = EXACT_NUMBER_DATATYPES | {"owl:real", "owl:rational"}

_INTEGER_LEXICAL = re.compile(r"[+-]?[0-9]+")
_DECIMAL_LEXICAL = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)")
_FLOATING = frozenset({"xsd:float", "xsd:double"})


def _whitespace_replace(text: str) -> str:
    """XSD 1.1 §4.3.6 ``whiteSpace = replace``: tab, line feed and carriage
    return each become a space. (Exactly those three: Python's ``str.split`` and
    ``strip`` also treat form feed, NBSP and the Unicode spaces as white space,
    which XSD does not.)"""
    return text.replace("\t", " ").replace("\n", " ").replace("\r", " ")


def _whitespace_collapse(text: str) -> str:
    """XSD 1.1 §4.3.6 ``whiteSpace = collapse``: *replace*, then runs of spaces
    become one space and a leading or trailing space is removed."""
    return re.sub(" +", " ", _whitespace_replace(text)).strip(" ")


#: The datatypes whose lexical form is whitespace-processed before it denotes a
#: value, with the processing. ``xsd:string`` (and ``rdf:PlainLiteral``) PRESERVE.
_WHITESPACE_PROCESSING: Dict[str, Callable[[str], str]] = {
    "xsd:normalizedString": _whitespace_replace,
    "xsd:token": _whitespace_collapse,
    "xsd:anyURI": _whitespace_collapse,
}

#: ``xsd:string`` subtypes with no lexical constraint beyond the whitespace
#: processing: their literal denotes the ``xsd:string`` value of the processed text.
_STRING_VALUED = frozenset({"xsd:normalizedString", "xsd:token"})

#: Datatypes whose lexical space is an XML name production this kit does not
#: validate: a literal of one has no term (see :meth:`Literal.to_term`).
_UNVALIDATED_LEXICAL = frozenset({"xsd:language", "xsd:Name", "xsd:NCName",
                                  "xsd:NMTOKEN"})
_BOOLEAN_CANONICAL = {"true": "true", "1": "true", "false": "false", "0": "false"}


def _escape(lexical: str) -> str:
    """The OWL 2 Functional-Style string escape: a backslash before ``\\`` and ``"``."""
    return lexical.replace("\\", "\\\\").replace('"', '\\"')


@dataclass(frozen=True)
class Literal:
    """A typed literal ``"lexical"^^datatype`` (or a language-tagged string
    ``"lexical"@language``), OWL's ``DataPropertyAssertion`` value and the
    value operand of ``DataHasValue``/``DataOneOf``/a facet.

    Args:
        lexical: The lexical form, as written (``"400"``).
        datatype: The datatype name; a built-in namespace is canonicalised to
            its prefix, so ``<http://www.w3.org/2001/XMLSchema#integer>`` and
            ``xsd:integer`` are one datatype. Defaults to ``xsd:string``.
        language: A language tag, which makes the literal an ``rdf:PlainLiteral``
            (the only datatype that has one); stored lower-case, as language
            tags are case-insensitive.

    Raises:
        UnsupportedDatatypeError: the lexical form is ILL-TYPED for an
            exact-number datatype or for ``xsd:boolean`` (``"abc"^^xsd:integer``
            has no data value — an ontology containing it is inconsistent in
            OWL 2 and the kit does not guess), or a language tag is given on a
            datatype that has none. Other datatypes are not checked: only for
            the exact numbers, ``xsd:boolean`` and strings does this kit
            interpret the lexical form at all.
    """

    lexical: str
    datatype: str = "xsd:string"
    language: Optional[str] = None

    def __post_init__(self):
        datatype = canonical_datatype_name(self.datatype)
        if self.language is not None:
            if datatype not in ("xsd:string", "rdf:PlainLiteral"):
                raise UnsupportedDatatypeError(
                    f"dl.Literal: a language tag ({self.language!r}) belongs to "
                    f"rdf:PlainLiteral, not to {datatype!r}. Write the literal "
                    f"as \"{self.lexical}\"@{self.language} or drop the tag.")
            datatype = "rdf:PlainLiteral"
            object.__setattr__(self, "language", self.language.lower())
        elif datatype == "rdf:PlainLiteral":
            raise UnsupportedDatatypeError(
                f"dl.Literal: a rdf:PlainLiteral literal {self.lexical!r} without "
                f"a language tag is the xsd:string {self.lexical!r}; write it as "
                f"an xsd:string, or give a language tag.")
        object.__setattr__(self, "datatype", datatype)
        self._check_well_typed()

    def _check_well_typed(self) -> None:
        text = self.lexical.strip()
        if self.datatype in _INTEGER_TYPES:
            low, high = _INTEGER_TYPES[self.datatype]
            if not _INTEGER_LEXICAL.fullmatch(text) or not (
                    (low is None or int(text) >= low)
                    and (high is None or int(text) <= high)):
                raise UnsupportedDatatypeError(
                    f"dl.Literal: {self.lexical!r} is not a well-typed "
                    f"{self.datatype} literal (an ill-typed literal denotes no "
                    f"data value, and an ontology containing one is inconsistent "
                    f"in OWL 2 — this kit refuses it rather than guess).")
        elif self.datatype == "xsd:decimal":
            if not _DECIMAL_LEXICAL.fullmatch(text):
                raise UnsupportedDatatypeError(
                    f"dl.Literal: {self.lexical!r} is not a well-typed "
                    f"xsd:decimal literal (digits with an optional sign and "
                    f"decimal point; no exponent).")
        elif self.datatype == "xsd:boolean":
            if text not in _BOOLEAN_CANONICAL:
                raise UnsupportedDatatypeError(
                    f"dl.Literal: {self.lexical!r} is not a well-typed "
                    f"xsd:boolean literal (one of true, false, 1, 0).")

    # -- text ------------------------------------------------------------- #

    def canonical_lexical(self) -> str:
        """The lexical form the TERM is named after: ``xsd:boolean`` is folded
        onto ``true``/``false`` (``"1"`` and ``"true"`` are one value), the three
        datatypes whose whitespace facet is not *preserve* are folded onto the
        text XSD's whitespace processing makes of the lexical form
        (``xsd:normalizedString`` *replace*, ``xsd:token`` and ``xsd:anyURI``
        *collapse*) and every other datatype keeps the lexical form it was
        written with.
        """
        if self.datatype == "xsd:boolean":
            return _BOOLEAN_CANONICAL[self.lexical.strip()]
        process = _WHITESPACE_PROCESSING.get(self.datatype)
        if process is not None:
            return process(self.lexical)
        return self.lexical

    def to_unicode(self) -> str:
        """The OWL 2 text of the literal: ``"400"^^xsd:integer`` or
        ``"abc"@en``. A name written back in this spelling reads back as this
        literal through the OWL parsers.
        """
        if self.language is not None:
            return f'"{_escape(self.lexical)}"@{self.language}'
        return f'"{_escape(self.lexical)}"^^{self.datatype}'

    def __str__(self) -> str:
        return self.to_unicode()

    # -- value / term ----------------------------------------------------- #

    def exact_number(self) -> Optional[Decimal]:
        """The literal's value as an exact :class:`~decimal.Decimal` if its
        datatype is in the exact-number family, else ``None``."""
        if self.datatype not in EXACT_NUMBER_DATATYPES:
            return None
        try:
            return Decimal(self.lexical.strip())
        except InvalidOperation:        # pragma: no cover - checked at construction
            return None

    def to_term(self) -> Node:
        """The first-order TERM of the literal's data value.

        An exact number becomes ``Number`` (an ``int`` when integral, else a
        ``float`` — and only when the decimal has at most 15 significant digits,
        the rule of every numeral reader of the kit: see
        :func:`~unicode_logic_kit.fol._fol_nodes._numeral_from_text`).
        ``xsd:float``/``xsd:double``, a decimal no ``Number`` can
        hold exactly and the datatypes whose lexical space this kit does not
        validate (``xsd:language``, ``xsd:Name``, ``xsd:NCName``,
        ``xsd:NMTOKEN``) are REFUSED. ``xsd:normalizedString`` and ``xsd:token``
        become the ``xsd:string`` term of their whitespace-processed text.
        Everything else becomes a ``Constant`` named by the literal's own OWL
        text (see the module docstring).

        Raises:
            UnsupportedDatatypeError: see above.
        """
        if self.datatype in _FLOATING:
            raise UnsupportedDatatypeError(
                f"dl.Literal.to_term: the literal {self.to_unicode()} has no "
                f"first-order image in this kit. The value space of "
                f"{self.datatype} is disjoint from the exact numbers in OWL 2 "
                f"(it has -0, NaN and ±INF, and 1.0 is not the integer 1), so "
                f"the term Number(1.0) would conflate two different values and "
                f"any other term would be invented. Use xsd:decimal or "
                f"xsd:integer, or state the constraint outside the datatype.")
        if self.datatype in _UNVALIDATED_LEXICAL:
            raise UnsupportedDatatypeError(
                f"dl.Literal.to_term: the literal {self.to_unicode()} has no "
                f"first-order image in this kit. The lexical space of "
                f"{self.datatype} is an XML name production this kit does not "
                f"validate, so it cannot say whether the literal denotes a "
                f"value at all, nor that it is the xsd:token / xsd:string value "
                f"of the same text, and a term of its own would state a "
                f"distinctness or an identity the value space does not "
                f"guarantee. Write the value as an xsd:token or xsd:string "
                f"literal, or leave it out.")
        if self.datatype in _STRING_VALUED:
            # The same VALUE as the xsd:string of the processed text, so the
            # same term: the typing by the written datatype is a separate fact.
            return Constant(Literal(self.canonical_lexical(), "xsd:string")
                            .to_unicode())
        value = self.exact_number()
        if value is None:
            return Constant(Literal(self.canonical_lexical(), self.datatype,
                                    self.language).to_unicode())
        if value == value.to_integral_value():
            return Number(int(value))
        try:
            return Number(_numeral_from_text(format(value, "f")))
        except ValueError as exc:
            raise UnsupportedDatatypeError(
                f"dl.Literal.to_term: the decimal {self.to_unicode()} cannot be "
                f"held exactly by a kit Number, and reading it as the nearest "
                f"float would let two different data values collapse into one "
                f"term: {exc}.") from None


# --------------------------------------------------------------------------- #
# Data ranges
# --------------------------------------------------------------------------- #

class DataRange:
    """Base class for OWL 2 data ranges (see the module docstring)."""

    def to_unicode(self) -> str:
        """The data range in the kit's display notation (``xsd:integer[≥ 5]``,
        ``{1, 2}``, ``¬D``, ``D ⊓ E``, ``D ⊔ E``)."""
        return _render_range(self)

    def __str__(self) -> str:
        return self.to_unicode()


@dataclass(frozen=True)
class Datatype(DataRange):
    """A named datatype (``xsd:integer``, ``rdfs:Literal``, a user datatype
    defined by ``DatatypeDefinition``). A built-in namespace is canonicalised
    to its prefix."""

    name: str

    def __post_init__(self):
        object.__setattr__(self, "name", canonical_datatype_name(self.name))


#: The ordering facets, in canonical spelling, with the comparison atom each
#: becomes: ``value ≥ bound`` for ``xsd:minInclusive`` and so on.
_ORDER_FACETS = {
    "xsd:minInclusive": "≥",
    "xsd:maxInclusive": "≤",
    "xsd:minExclusive": ">",
    "xsd:maxExclusive": "<",
}

#: The facets this kit translates (see the module docstring's "The scope of facets").
SUPPORTED_FACETS: Tuple[str, ...] = tuple(_ORDER_FACETS)

_NO_IMAGE_FACETS = {
    "xsd:pattern": "regular-expression constraints over a literal's lexical "
                   "space are not first-order, and no backend here interprets them",
    "xsd:length": "string length is an uninterpreted function on every backend "
                  "here, so the axiom would constrain nothing while looking as "
                  "though it did",
    "xsd:minLength": "string length is an uninterpreted function on every "
                     "backend here, so the axiom would constrain nothing while "
                     "looking as though it did",
    "xsd:maxLength": "string length is an uninterpreted function on every "
                     "backend here, so the axiom would constrain nothing while "
                     "looking as though it did",
    "xsd:totalDigits": "digit counts are not first-order over the kit's numbers",
    "xsd:fractionDigits": "digit counts are not first-order over the kit's numbers",
    "rdf:langRange": "language-range matching is not first-order over the "
                     "kit's strings",
}


def _check_facet(base: str, facet: str, bound: "Literal") -> str:
    """Validate one facet of a restriction of ``base``; return its canonical name."""
    facet = canonical_datatype_name(facet)
    if facet not in _ORDER_FACETS:
        why = _NO_IMAGE_FACETS.get(facet, "it is not one of the four ordering facets")
        raise UnsupportedDatatypeError(
            f"dl.datatypes: the facet {facet!r} has no first-order image in this "
            f"kit — {why}. Supported facets are {', '.join(SUPPORTED_FACETS)} "
            f"on an exact-number base datatype; drop the facet, or state the "
            f"constraint outside the datatype.")
    if base not in NUMERIC_BASES:
        raise UnsupportedDatatypeError(
            f"dl.datatypes: the facet {facet!r} is supported only on an "
            f"exact-number base datatype (xsd:integer and its subtypes, "
            f"xsd:decimal), not on {base!r} — this kit's ≤/≥ atoms carry no "
            f"theory for it, so the image would be an uninterpreted predicate "
            f"over uninterpreted constants and would constrain nothing. Use "
            f"xsd:decimal or xsd:integer, or state the bound outside the "
            f"datatype.")
    if bound.exact_number() is None:
        raise UnsupportedDatatypeError(
            f"dl.datatypes: the bound {bound.to_unicode()} of the facet "
            f"{facet!r} is not an exact number (xsd:integer family or "
            f"xsd:decimal literal), so it has no ordering term in this kit.")
    return facet


@dataclass(frozen=True)
class DatatypeRestriction(DataRange):
    """``DatatypeRestriction(base facet₁ literal₁ …)``: the values of ``base``
    that satisfy every facet. ``facets`` is a tuple of ``(facet name, bound
    literal)``; it is validated against the supported scope on construction.

    Raises:
        UnsupportedDatatypeError: an out-of-scope facet, or an ordering facet
            on a non-numeric base (see the module docstring).
    """

    base: Datatype
    facets: Tuple[Tuple[str, Literal], ...]

    def __post_init__(self):
        base = self.base if isinstance(self.base, Datatype) else Datatype(self.base)
        object.__setattr__(self, "base", base)
        facets = tuple((facet, bound) for facet, bound in self.facets)
        if not facets:
            raise UnsupportedDatatypeError(
                "dl.DatatypeRestriction: a restriction needs at least one facet "
                "(OWL 2's grammar is DatatypeRestriction(DT (F lt)+)); a datatype "
                "with no facet is just the datatype.")
        checked = tuple((_check_facet(base.name, facet, bound), bound)
                        for facet, bound in facets)
        object.__setattr__(self, "facets", checked)


@dataclass(frozen=True)
class DataOneOf(DataRange):
    """``DataOneOf(lt₁ … ltₙ)``: exactly the listed data values."""

    values: Tuple[Literal, ...]

    def __post_init__(self):
        object.__setattr__(self, "values", tuple(self.values))
        if not self.values:
            raise UnsupportedDatatypeError(
                "dl.DataOneOf: needs at least one literal (OWL 2's grammar is "
                "DataOneOf(lt+)).")


@dataclass(frozen=True)
class DataComplementOf(DataRange):
    """``DataComplementOf(DR)``: the data values NOT in ``DR`` — the
    complement within the data domain, not within the whole universe."""

    datarange: DataRange


@dataclass(frozen=True)
class DataIntersectionOf(DataRange):
    """``DataIntersectionOf(DR₁ … DRₙ)``, ``n ≥ 2``."""

    ranges: Tuple[DataRange, ...]

    def __post_init__(self):
        object.__setattr__(self, "ranges", tuple(self.ranges))
        if len(self.ranges) < 2:
            raise UnsupportedDatatypeError(
                "dl.DataIntersectionOf: needs at least two data ranges.")


@dataclass(frozen=True)
class DataUnionOf(DataRange):
    """``DataUnionOf(DR₁ … DRₙ)``, ``n ≥ 2``."""

    ranges: Tuple[DataRange, ...]

    def __post_init__(self):
        object.__setattr__(self, "ranges", tuple(self.ranges))
        if len(self.ranges) < 2:
            raise UnsupportedDatatypeError(
                "dl.DataUnionOf: needs at least two data ranges.")


# --------------------------------------------------------------------------- #
# Display
# --------------------------------------------------------------------------- #

_FACET_SYMBOL = {facet: symbol for facet, symbol in _ORDER_FACETS.items()}


def _render_range(dr: DataRange) -> str:
    if isinstance(dr, Datatype):
        return dr.name
    if isinstance(dr, DatatypeRestriction):
        facets = ", ".join(f"{_FACET_SYMBOL[f]} {b.canonical_lexical()}"
                           for f, b in dr.facets)
        return f"{dr.base.name}[{facets}]"
    if isinstance(dr, DataOneOf):
        return "{" + ", ".join(v.to_unicode() for v in dr.values) + "}"
    if isinstance(dr, DataComplementOf):
        return "¬" + _paren_range(dr.datarange)
    if isinstance(dr, DataIntersectionOf):
        return " ⊓ ".join(_paren_range(r) for r in dr.ranges)
    if isinstance(dr, DataUnionOf):
        return " ⊔ ".join(_paren_range(r) for r in dr.ranges)
    raise TypeError(f"render: unsupported data range {type(dr).__name__}")


def _paren_range(dr: DataRange) -> str:
    inner = _render_range(dr)
    if isinstance(dr, (DataIntersectionOf, DataUnionOf)):
        return f"({inner})"
    return inner


# --------------------------------------------------------------------------- #
# The first-order image of a data range
# --------------------------------------------------------------------------- #

def _fold(ctor, parts: Iterable[Node]) -> Node:
    parts = list(parts)
    acc = parts[0]
    for part in parts[1:]:
        acc = ctor(acc, part)
    return acc


def datarange_to_fol(datarange: DataRange, term: Node) -> Node:
    """The first-order image ``δ(DR, t)`` of a data range, with ``term`` (a
    ``Variable``, or any other term) standing for the data value under
    discussion. OWL 2 direct semantics (Structural Specification §7):

    * ``Datatype(D)`` ↦ ``D(t)``; ``rdfs:Literal`` — whose value space is the
      whole data domain — ↦ ``OwlData(t)``;
    * ``DatatypeRestriction(D f₁ v₁ … fₙ vₙ)`` ↦ ``D(t) ∧ t ⋈₁ v₁ ∧ … ∧ t ⋈ₙ vₙ``
      (``(D)^DT ∩ ⋂ (fᵢ, vᵢ)^F`` is the conjunction of the base guard with
      one comparison atom per facet);
    * ``DataOneOf(l₁ … lₙ)`` ↦ ``t = l₁ ∨ … ∨ t = lₙ``;
    * ``DataComplementOf(DR)`` ↦ ``OwlData(t) ∧ ¬δ(DR, t)`` — the complement
      is taken WITHIN the data domain (``Δ_D \\ DR^DT``), so the ``OwlData``
      conjunct is load-bearing: without it the image would also admit
      individuals;
    * ``DataIntersectionOf`` ↦ ``∧``, ``DataUnionOf`` ↦ ``∨``.

    Raises:
        UnsupportedDatatypeError: a literal with no term (``xsd:double``, an
            inexact decimal).
    """
    if isinstance(datarange, Datatype):
        if datarange.name == _RDFS_LITERAL:
            return Atom(OWL_DATA, (term,))
        return Atom(datarange.name, (term,))
    if isinstance(datarange, DatatypeRestriction):
        parts = [datarange_to_fol(datarange.base, term)]
        for facet, bound in datarange.facets:
            parts.append(Atom(_ORDER_FACETS[facet], (term, bound.to_term())))
        return _fold(And, parts)
    if isinstance(datarange, DataOneOf):
        return _fold(Or, [Atom("=", (term, value.to_term()))
                          for value in datarange.values])
    if isinstance(datarange, DataComplementOf):
        return And(Atom(OWL_DATA, (term,)),
                   Not(datarange_to_fol(datarange.datarange, term)))
    if isinstance(datarange, DataIntersectionOf):
        return _fold(And, [datarange_to_fol(r, term) for r in datarange.ranges])
    if isinstance(datarange, DataUnionOf):
        return _fold(Or, [datarange_to_fol(r, term) for r in datarange.ranges])
    raise TypeError(f"datarange_to_fol: unsupported data range {type(datarange).__name__}")


# --------------------------------------------------------------------------- #
# Walking a data range
# --------------------------------------------------------------------------- #

def datarange_literals(datarange: DataRange) -> Tuple[Literal, ...]:
    """Every :class:`Literal` occurring in ``datarange`` (facet bounds and
    one-of values), in order of occurrence."""
    if isinstance(datarange, Datatype):
        return ()
    if isinstance(datarange, DatatypeRestriction):
        return tuple(bound for _, bound in datarange.facets)
    if isinstance(datarange, DataOneOf):
        return datarange.values
    if isinstance(datarange, DataComplementOf):
        return datarange_literals(datarange.datarange)
    if isinstance(datarange, (DataIntersectionOf, DataUnionOf)):
        return tuple(lit for r in datarange.ranges for lit in datarange_literals(r))
    raise TypeError(f"datarange_literals: unsupported data range {type(datarange).__name__}")


def datarange_datatypes(datarange: DataRange) -> Tuple[str, ...]:
    """Every datatype NAME occurring in ``datarange`` (a base, or a plain
    datatype), in order of occurrence — not the literals' datatypes, see
    :func:`datarange_literals`."""
    if isinstance(datarange, Datatype):
        return (datarange.name,)
    if isinstance(datarange, DatatypeRestriction):
        return (datarange.base.name,)
    if isinstance(datarange, DataOneOf):
        return ()
    if isinstance(datarange, DataComplementOf):
        return datarange_datatypes(datarange.datarange)
    if isinstance(datarange, (DataIntersectionOf, DataUnionOf)):
        return tuple(name for r in datarange.ranges for name in datarange_datatypes(r))
    raise TypeError(f"datarange_datatypes: unsupported data range {type(datarange).__name__}")


#: ``(callable)`` alias used by the OWL writers: maps a datatype NAME to the
#: text it is written as (``<IRI>`` brackets, a synthetic name, …).
NameRenderer = Callable[[str], str]


def render_literal_fs(literal: Literal, name: NameRenderer = lambda n: n) -> str:
    """The OWL 2 Functional-Style text of ``literal`` (``"400"^^xsd:integer``);
    ``name`` renders its DATATYPE name, exactly as it does the datatype names of
    :func:`render_datarange_fs` (default: verbatim).

    A writer that renders datatype names through a renderer of its own (an IRI in
    angle brackets, a synthetic ``:T1`` token) must render a literal's datatype
    through the SAME renderer: written verbatim it is a name the document never
    declared (or, for an IRI, an unbracketed one OWL 2 does not allow). A
    language-tagged literal has no datatype to render: ``"abc"@en``.
    """
    if literal.language is not None:
        return literal.to_unicode()
    return f'"{_escape(literal.lexical)}"^^{name(literal.datatype)}'


def render_datarange_fs(datarange: DataRange, name: NameRenderer = lambda n: n) -> str:
    """The OWL 2 Functional-Style text of ``datarange``; ``name`` renders a
    DATATYPE name (default: verbatim). A facet name is always written as it is:
    a facet is part of OWL 2's own vocabulary, never a name the caller owns."""
    if isinstance(datarange, Datatype):
        return name(datarange.name)
    if isinstance(datarange, DatatypeRestriction):
        body = " ".join(f"{f} {render_literal_fs(b, name)}" for f, b in datarange.facets)
        return f"DatatypeRestriction({name(datarange.base.name)} {body})"
    if isinstance(datarange, DataOneOf):
        return ("DataOneOf(" + " ".join(render_literal_fs(v, name) for v in datarange.values)
                + ")")
    if isinstance(datarange, DataComplementOf):
        return f"DataComplementOf({render_datarange_fs(datarange.datarange, name)})"
    if isinstance(datarange, DataIntersectionOf):
        return ("DataIntersectionOf("
                + " ".join(render_datarange_fs(r, name) for r in datarange.ranges) + ")")
    if isinstance(datarange, DataUnionOf):
        return ("DataUnionOf("
                + " ".join(render_datarange_fs(r, name) for r in datarange.ranges) + ")")
    raise TypeError(f"render: unsupported data range {type(datarange).__name__}")
