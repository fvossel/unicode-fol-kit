"""A string parser for ALC(Q) concepts, dual to :meth:`Concept.to_unicode`.

``dl.concepts`` builds concepts only by Python construction (``dl.And(A,
dl.Not(B))``); this module parses the glyph syntax that
:meth:`~unicode_fol_kit.dl.concepts.Concept.to_unicode` emits back into a
:class:`~unicode_fol_kit.dl.concepts.Concept`, so a rendered concept — or one
typed by hand in the same notation — round-trips: ``parse_concept(c.to_unicode())
== c`` for every constructor, including the qualified number restrictions
``AtLeast``/``AtMost`` (≥n r.C / ≤n r.C), with the documented exceptions below.

The reader folds a flat chain of one connective to the LEFT (``A ⊓ B ⊓ C`` is
``(A ⊓ B) ⊓ C``), so the printer writes a nested operand of the SAME connective
without parentheses on the left only: ``And(A, And(B, C))`` is ``A ⊓ (B ⊓ C)``,
never ``A ⊓ B ⊓ C``, which reads back as the other tree. The round trip is
therefore exact for every shape, not only for left-nested chains.

The first exceptions are the two constructors that name an INDIVIDUAL:
:class:`~unicode_fol_kit.dl.concepts.Nominal` renders as ``{a}`` and
:class:`~unicode_fol_kit.dl.concepts.HasValue` as ``∃r.{a}``, and neither reads
back — they are refused BY NAME instead (see ``_primary``). The glyph syntax
has no individual-name layer, so ``{a}`` cannot be told apart from a concept
NAME, and ``∃r.{a}`` cannot be told apart from ``∃r.`` applied to a nominal:
``HasValue("r", "a")`` and ``Exists("r", Nominal("a"))`` have the SAME
rendering, honestly, because they have the same models — but picking one of
them when reading the text back would be a silent normalisation of the other.
This is the same render-only asymmetry :func:`~unicode_fol_kit.dl.to_manchester`
already has for a nominal, and the two syntaxes that DO distinguish the pair,
Manchester (``r value a`` versus ``r some {a}``) and Functional
(``ObjectHasValue(r a)`` versus ``ObjectSomeValuesFrom(r ObjectOneOf(a))``),
round-trip it exactly.

The DATA restrictions (:class:`~unicode_fol_kit.dl.concepts.DataExists` and its
four siblings) are render-only in the same way, for the same reason: the glyph
syntax has no data-range layer, and ``∃d.xsd:integer`` is the text of BOTH
``DataExists("d", Datatype("xsd:integer"))`` and ``Exists("d",
Atomic("xsd:integer"))`` -- two concepts about different sorts. Reading it as
the second would be the silent misreading ``dl.parse_manchester`` had for
``d some xsd:integer`` before the data layer. So a NAME that is a BUILT-IN
datatype (``xsd:integer``, ``rdfs:Literal``, …) is refused by name below; OWL 2
forbids a class with a datatype's name anyway. A USER-defined datatype
(``∃d.Digit``) cannot be told from a class by its spelling and reads as the
object restriction -- the limit the Manchester reader avoids by being told the
datatype names (``datatypes=``). Read data restrictions with
``dl.parse_manchester`` or ``dl.parse_owl_functional_class_expression``.

An :class:`~unicode_fol_kit.dl.concepts.InverseRole` is the last one: it prints
as ``r⁻`` (``∃r⁻.C``), and the reader refuses a role name that ends in ``⁻`` BY
NAME (see ``_role_name``) instead of reading a plain role called ``r⁻``, which
would turn an inverse role into an unrelated one without a word.

Names. The grammar below says which names the reader can read. A name outside
it (one that holds whitespace, an ``.`` or a parenthesis, one of the reserved
glyphs, or nothing at all) is printed as it is, for display, and the reader then
refuses the text: this syntax has no escape (the Manchester and Functional-Style
writers bracket such a name as a full IRI). The one thing the printer does not do
is print a name so that the text reads back as ANOTHER concept — ``Atomic("A ⊓ B")``
would print ``A ⊓ B``, the intersection of two classes — and
``Concept.to_unicode`` raises :class:`ValueError` for it.

Grammar (loosest-binding first, matching ``concepts.py``'s ``_PREC`` table
exactly — ⊔ at precedence 1, ⊓ at 2, ¬/∃/∀/≥/≤ at 3, atoms/⊤/⊥ at 4)::

    concept  := or
    or       := and ("⊔" and)*
    and      := unary ("⊓" unary)*
    unary    := "¬" unary
              | ("∃" | "∀") NAME "." unary
              | ("≥" | "≤") NUMBER NAME "." unary
              | primary
    primary  := "⊤" | "⊥" | NAME | "(" concept ")"
    NAME     := a maximal run of characters that are none of: whitespace,
                the glyphs ⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀ ≥ ≤ ( ) . ⊑ { }
    NUMBER   := a NAME token consisting only of ASCII digits

A concept/role NAME may be any length and contain any characters outside
that reserved set (digits, underscores, non-ASCII letters, …) — e.g.
``hasChild``, ``Doctor42``, ``θ``. ``{`` and ``}`` are in that reserved set
since 0.30.0 and are refused BY NAME (see ``_primary``): a nominal-shaped
text like ``{a}`` was a legal NAME before, so ``parse_concept("{a}")``
returned ``Atomic("{a}")`` -- a concept with a bogus class name -- silently,
for text ``dl.concepts`` itself prints. A concept name containing a literal
brace therefore stops parsing; there is no such name in the kit, its tests or
the OEO ontology this was measured against.
Restricting ``unary``'s operand (rather
than the full ``concept``) is what makes ``∃r.∀s.C`` and ``¬¬C`` parse
without parentheses while ``∃r.(C ⊓ D)`` requires them, mirroring
``concepts.py``'s ``_paren`` exactly — so the grammar is precedence-faithful
by construction, not just by testing. ``≥``/``≤`` need a NUMBER token (the
bound ``n``) between the glyph and the role name, rendered by
``Concept.to_unicode`` with a mandatory space before the role name (``"≥2
r.C"``, never ``"≥2r.C"``) so the tokenizer — which has no notion of a
digit/letter boundary — can always split the two apart; see ``_unary`` below.

This module intentionally implements a small hand-rolled recursive-descent
parser rather than reusing the Lark-based registry machinery in
``fol/msflparser.py``: that machinery is purpose-built for assembling several
large, mutually-exclusive FOL dialects (FOL/MSFOL/MSFL/modal/…) that share a
term/atom/lambda layer, none of which applies here — ALC concepts are a tiny,
fixed, single-purpose grammar with no term layer, no dialects, and no
sharing to gain from the registry. A ~150-line hand-rolled parser is both
simpler and easier to audit for this shape of grammar than standing up a
Lark grammar file plus transformer for it.

Glyph-only: there is no ASCII fallback syntax (no ``E`` for ``∃``, ``A`` for
``∀``, ``&`` for ``⊓``, …). Unlike the operator glyphs, ``A`` and ``E`` are
exactly the kind of short identifiers real concept/role names use (as they
do throughout ``tests/test_dl_alc.py``), so ASCII keyword fallbacks for the
quantifier-like operators would silently swallow a large fraction of
plausible concept names — not "trivially cheap" — so they are not provided.

GCIs (general concept inclusions, ``C ⊑ D``): ``concepts.py`` has no
renderer for them (:class:`~unicode_fol_kit.dl.tableau.TBox` carries
``(Concept, Concept)`` pairs with no ``to_unicode``), so there is no
round-trip counterpart to test :func:`parse_gci` against — it is provided as
a convenience for hand-written GCI text using ⊑, the glyph the ``TBox`` /
``subsumes`` docstrings already use for this notion, and is verified directly
against hand-picked expected ``(Concept, Concept)`` pairs instead.
"""

from typing import List, Tuple

from .datatypes import is_builtin_datatype
from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
)
from .tableau import RoleExpressionError, _reject_concept_role

__all__ = ["parse_concept", "parse_gci", "ConceptSyntaxError"]


class ConceptSyntaxError(ValueError):
    """Raised by :func:`parse_concept` / :func:`parse_gci` on malformed input."""


# --------------------------------------------------------------------------- #
# Tokenizer.
# --------------------------------------------------------------------------- #

_GLYPH_TOKENS = {
    "⊤": "TOP", "⊥": "BOT", "¬": "NOT", "⊓": "AND", "⊔": "OR",
    "∃": "EXISTS", "∀": "FORALL", "≥": "ATLEAST", "≤": "ATMOST",
    "(": "LPAREN", ")": "RPAREN", ".": "DOT", "⊑": "SUBSUME",
    # RESERVED since 0.30.0, so `{a}` is refused BY NAME instead of read as a
    # concept NAME spelled "{a}" -- see _primary's LBRACE branch.
    "{": "LBRACE", "}": "RBRACE",
}

# A Token is (type: str, value: str, pos: int).
_Token = Tuple[str, str, int]


def _tokenize(text: str) -> List[_Token]:
    """Split ``text`` into glyph tokens and maximal-run NAME tokens, plus a
    trailing EOF sentinel (whose ``pos`` is ``len(text)``, for error messages).
    """
    tokens: List[_Token] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch in _GLYPH_TOKENS:
            tokens.append((_GLYPH_TOKENS[ch], ch, i))
            i += 1
            continue
        start = i
        while i < n and not text[i].isspace() and text[i] not in _GLYPH_TOKENS:
            i += 1
        tokens.append(("NAME", text[start:i], start))
    tokens.append(("EOF", "", n))
    return tokens


# --------------------------------------------------------------------------- #
# Recursive-descent parser.
# --------------------------------------------------------------------------- #

class _Parser:
    """A single parse of one token stream; not re-used across calls."""

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

    def _error(self, message: str) -> ConceptSyntaxError:
        return ConceptSyntaxError(f"{message} in {self._text!r}")

    def _expect(self, ttype: str, what: str) -> _Token:
        tok = self._peek()
        if tok[0] != ttype:
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(
                f"parse_concept: expected {what} but found {found} "
                f"at position {tok[2]}")
        return self._advance()

    def _expect_eof(self) -> None:
        tok = self._peek()
        if tok[0] != "EOF":
            raise self._error(
                f"parse_concept: unexpected trailing input {tok[1]!r} "
                f"at position {tok[2]}")

    # -- grammar levels, loosest first (mirrors concepts.py's _PREC) -------- #

    def _or(self) -> Concept:
        left = self._and()
        while self._peek()[0] == "OR":
            self._advance()
            left = Or(left, self._and())
        return left

    def _and(self) -> Concept:
        left = self._unary()
        while self._peek()[0] == "AND":
            self._advance()
            left = And(left, self._unary())
        return left

    def _checked(self, concept: Concept, pos: int) -> Concept:
        """``concept``, unless its role is an OWL 2 built-in property name (or
        ``=``/``≠``) — refused BY NAME, the way ``dl.parse_owl_functional`` and
        the Manchester parser refuse it. ``∃owl:topObjectProperty.A`` used to
        read as an ordinary role of that name, whose verdict (satisfiable) is
        not the universal property's (every element is related to itself)."""
        try:
            _reject_concept_role(concept, where="parse_concept")
        except RoleExpressionError as exc:
            raise self._error(f"{exc} (at position {pos})") from exc
        return concept

    def _unary(self) -> Concept:
        ttype, _, pos = self._peek()
        if ttype == "NOT":
            self._advance()
            return Not(self._unary())
        if ttype in ("EXISTS", "FORALL"):
            self._advance()
            role = self._role_name()
            self._expect("DOT", "'.' after the role name")
            body = self._unary()
            return self._checked(
                Exists(role, body) if ttype == "EXISTS" else ForAll(role, body), pos)
        if ttype in ("ATLEAST", "ATMOST"):
            self._advance()
            n = self._expect_number()
            role = self._role_name()
            self._expect("DOT", "'.' after the role name")
            body = self._unary()
            return self._checked(
                AtLeast(n, role, body) if ttype == "ATLEAST" else AtMost(n, role, body),
                pos)
        return self._primary()

    def _role_name(self) -> str:
        """Consume the NAME token of a restriction's role.

        A name that ends in the inverse glyph ``⁻`` is refused BY NAME: that is
        how ``Concept.to_unicode`` writes ``Exists(InverseRole("r"), C)``
        (``∃r⁻.C``), a role EXPRESSION this syntax has no layer for, so reading
        the text as a role NAMED ``r⁻`` would silently turn an inverse role into
        an unrelated plain one.
        """
        tok = self._expect("NAME", "a role name")
        if tok[1].endswith("⁻"):
            raise self._error(
                f"parse_concept: {tok[1]!r} (position {tok[2]}) is the glyph "
                f"spelling of an INVERSE role, which the glyph syntax cannot "
                f"read — reading it as a role named {tok[1]!r} would silently "
                f"change what it says. Build dl.InverseRole({tok[1][:-1]!r}) "
                f"directly (the in-house tableau refuses it by name; the "
                f"external reasoner, dl.owl_reasoner, decides it)")
        return tok[1]

    def _expect_number(self) -> int:
        """Consume a NAME token of only ASCII digits (the ``n`` in ``≥n``/``≤n``)."""
        tok = self._peek()
        if tok[0] == "NAME" and tok[1].isdigit():
            self._advance()
            return int(tok[1])
        found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
        raise self._error(
            f"parse_concept: expected a non-negative integer but found {found} "
            f"at position {tok[2]}")

    def _primary(self) -> Concept:
        ttype, value, pos = self._peek()
        if ttype == "TOP":
            self._advance()
            return Top()
        if ttype == "BOT":
            self._advance()
            return Bottom()
        if ttype in ("LBRACE", "RBRACE"):
            # A nominal-shaped text. Until 0.30.0 braces were not reserved, so
            # `{a}` was a legal NAME and parse_concept("{a}") returned
            # Atomic("{a}") -- a concept with a bogus class name, silently, for
            # text this module's own siblings print. dl.parse_manchester
            # already refused the same text by name; now so does this.
            #
            # Teaching it to BUILD a nominal was the alternative and is wrong:
            # `∃r.{a}` is AMBIGUOUS between dl.HasValue(r, "a") and
            # dl.Exists(r, dl.Nominal("a")) -- the glyph syntax has no
            # individual-name layer to tell them apart -- and always picking
            # one would be a silent normalisation of the other.
            raise self._error(
                f"parse_concept: nominal and value concepts "
                f"('{{a}}', '∃r.{{a}}') are not supported — the glyph syntax "
                f"has no individual-name layer, so '{{a}}' cannot be told "
                f"apart from a concept NAME, and '∃r.{{a}}' cannot be told "
                f"apart from a value restriction (found {value!r} at position "
                f"{pos}). Build dl.Nominal('a') or dl.HasValue(role, 'a') "
                f"directly, or read 'r value a' with dl.parse_manchester / "
                f"'ObjectHasValue(r a)' with "
                f"dl.parse_owl_functional_class_expression")
        if ttype == "NAME":
            if is_builtin_datatype(value):
                raise self._error(
                    f"parse_concept: {value!r} (position {pos}) is a built-in "
                    f"DATATYPE, not a class, and the glyph syntax has no "
                    f"data-range layer -- reading '∃d.{value}' as an object "
                    f"restriction would silently change what it says. Read a "
                    f"data restriction with dl.parse_manchester "
                    f"('d some {value}') or "
                    f"dl.parse_owl_functional_class_expression "
                    f"('DataSomeValuesFrom(d {value})')")
            self._advance()
            return Atomic(value)
        if ttype == "LPAREN":
            self._advance()
            inner = self._or()
            self._expect("RPAREN", "')'")
            return inner
        found = "end of input" if ttype == "EOF" else f"{value!r}"
        raise self._error(
            f"parse_concept: unexpected {found} at position {pos}; expected "
            "'⊤', '⊥', a concept name, '¬', '∃', '∀', '≥', '≤', or '('")

    # -- entry points --------------------------------------------------- #

    def parse_concept(self) -> Concept:
        c = self._or()
        self._expect_eof()
        return c

    def parse_gci(self) -> Tuple[Concept, Concept]:
        sub = self._or()
        self._expect("SUBSUME", "'⊑'")
        sup = self._or()
        self._expect_eof()
        return sub, sup


def parse_concept(text: str) -> Concept:
    """Parse ``text`` (the ⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀ ≥ ≤ glyph syntax) into a :class:`Concept`.

    Round-trips against :meth:`Concept.to_unicode`: ``parse_concept(c.to_unicode())
    == c`` for every concept ``c`` EXCEPT the ones the glyph syntax cannot read:
    the two that name an individual
    (:class:`~unicode_fol_kit.dl.concepts.Nominal` and
    :class:`~unicode_fol_kit.dl.concepts.HasValue`, which render as ``{a}`` and
    ``∃r.{a}`` and are refused by name on the way back in — see the module
    docstring and :class:`~unicode_fol_kit.dl.concepts.HasValue`; the same
    render-only asymmetry ``dl.to_manchester`` has for a nominal), the data
    restrictions, and an inverse role (``∃r⁻.C``), all refused by name. The
    shape of a chain is exact: ``And(A, And(B, C))`` is written ``A ⊓ (B ⊓ C)``.
    Raises :class:`ConceptSyntaxError` on
    malformed input (unbalanced parentheses, a missing '.' after a role name,
    a stray operator, trailing garbage, …).
    """
    return _Parser(_tokenize(text), text).parse_concept()


def parse_gci(text: str) -> Tuple[Concept, Concept]:
    """Parse a general concept inclusion ``"C ⊑ D"`` into ``(C, D)``.

    See the module docstring for why this has no round-trip counterpart to
    test against (``concepts.py`` never renders a GCI). Raises
    :class:`ConceptSyntaxError` on malformed input.
    """
    return _Parser(_tokenize(text), text).parse_gci()
