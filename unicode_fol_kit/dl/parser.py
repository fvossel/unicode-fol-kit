"""A string parser for ALC concepts, dual to :meth:`Concept.to_unicode`.

``dl.concepts`` builds concepts only by Python construction (``dl.And(A,
dl.Not(B))``); this module parses the glyph syntax that
:meth:`~unicode_fol_kit.dl.concepts.Concept.to_unicode` emits back into a
:class:`~unicode_fol_kit.dl.concepts.Concept`, so a rendered concept — or one
typed by hand in the same notation — round-trips: ``parse_concept(c.to_unicode())
== c`` for every constructor.

Grammar (loosest-binding first, matching ``concepts.py``'s ``_PREC`` table
exactly — ⊔ at precedence 1, ⊓ at 2, ¬/∃/∀ at 3, atoms/⊤/⊥ at 4)::

    concept  := or
    or       := and ("⊔" and)*
    and      := unary ("⊓" unary)*
    unary    := "¬" unary
              | ("∃" | "∀") NAME "." unary
              | primary
    primary  := "⊤" | "⊥" | NAME | "(" concept ")"
    NAME     := a maximal run of characters that are none of: whitespace,
                the glyphs ⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀ ( ) . ⊑

A concept/role NAME may be any length and contain any characters outside
that reserved set (digits, underscores, non-ASCII letters, …) — e.g.
``hasChild``, ``Doctor42``, ``θ``. Restricting ``unary``'s operand (rather
than the full ``concept``) is what makes ``∃r.∀s.C`` and ``¬¬C`` parse
without parentheses while ``∃r.(C ⊓ D)`` requires them, mirroring
``concepts.py``'s ``_paren`` exactly — so the grammar is precedence-faithful
by construction, not just by testing.

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

from .concepts import Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll

__all__ = ["parse_concept", "parse_gci", "ConceptSyntaxError"]


class ConceptSyntaxError(ValueError):
    """Raised by :func:`parse_concept` / :func:`parse_gci` on malformed input."""


# --------------------------------------------------------------------------- #
# Tokenizer.
# --------------------------------------------------------------------------- #

_GLYPH_TOKENS = {
    "⊤": "TOP", "⊥": "BOT", "¬": "NOT", "⊓": "AND", "⊔": "OR",
    "∃": "EXISTS", "∀": "FORALL", "(": "LPAREN", ")": "RPAREN",
    ".": "DOT", "⊑": "SUBSUME",
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

    def _unary(self) -> Concept:
        ttype, _, _ = self._peek()
        if ttype == "NOT":
            self._advance()
            return Not(self._unary())
        if ttype in ("EXISTS", "FORALL"):
            self._advance()
            role = self._expect("NAME", "a role name")[1]
            self._expect("DOT", "'.' after the role name")
            body = self._unary()
            return Exists(role, body) if ttype == "EXISTS" else ForAll(role, body)
        return self._primary()

    def _primary(self) -> Concept:
        ttype, value, pos = self._peek()
        if ttype == "TOP":
            self._advance()
            return Top()
        if ttype == "BOT":
            self._advance()
            return Bottom()
        if ttype == "NAME":
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
            "'⊤', '⊥', a concept name, '¬', '∃', '∀', or '('")

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
    """Parse ``text`` (the ⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀ glyph syntax) into a :class:`Concept`.

    Round-trips against :meth:`Concept.to_unicode`: ``parse_concept(c.to_unicode())
    == c`` for every concept ``c``. Raises :class:`ConceptSyntaxError` on
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
