"""A parser/renderer for the **OWL 2 Manchester Syntax**, restricted to ALC.

`OWL 2 Manchester Syntax <https://www.w3.org/TR/owl2-manchester-syntax/>`_ is
the W3C-standardised, keyword-based (as opposed to :mod:`unicode_fol_kit.dl.parser`'s
glyph-based) concrete syntax for OWL 2 class expressions — the notation Protégé
and most OWL tooling show by default (``Person and hasChild some Doctor``
rather than ``Person ⊓ ∃hasChild.Doctor``). This module is the *OWL bridge,
part 1*: it parses (and renders) exactly the ALC-expressible fragment of that
syntax into/from the kit's existing :class:`~unicode_fol_kit.dl.concepts.Concept`
AST, so any Manchester-syntax ALC expression becomes reachable by every kit
reasoner and export (:mod:`unicode_fol_kit.dl.tableau`,
:mod:`unicode_fol_kit.dl.translate`, …) with no separate code path.

Supported fragment (exactly ALC, matching :mod:`unicode_fol_kit.dl.concepts`)
    - class names (``Person``, ``hasChild`` as a role name);
    - ``C and D``, ``C or D``, ``not C``;
    - ``r some C`` (∃r.C), ``r only C`` (∀r.C);
    - parentheses;
    - ``owl:Thing`` / ``owl:Nothing`` for ⊤ / ⊥ (the W3C grammar treats these
      as ordinary ``owl:``-prefixed class names, not keywords — see "Top and
      Bottom" below — and this module maps exactly those two spellings onto
      :class:`~unicode_fol_kit.dl.concepts.Top` / :class:`~unicode_fol_kit.dl.concepts.Bottom`).

Rejected (real Manchester/OWL 2 syntax, but outside ALC — see "Rejected
constructs" below): cardinality restrictions (``min``/``max``/``exactly``),
``value`` restrictions, ``Self`` restrictions, inverse roles (``inverse r``),
nominal ("one-of") concepts (``{a, b}``), and datatype facet restrictions
(``dtype[>= 0]``). Each is rejected with a :class:`ManchesterSyntaxError`
naming the specific construct, per the kit's honesty convention (an
unsupported construct is a loud, precise error — never a silent
mistranslation or a weaker-than-requested result).

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
  :mod:`unicode_fol_kit.dl.parser`'s glyph parser exactly.

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
constructors, this module special-cases exactly those two spellings (nothing
else under the ``owl:`` prefix is recognised) rather than leaving them as
opaque :class:`~unicode_fol_kit.dl.concepts.Atomic` names, so
``owl:Thing and C`` reasons exactly like ``⊤ ⊓ C`` under
:func:`unicode_fol_kit.dl.tableau.concept_satisfiable` and friends.

Round-trip guarantee
---------------------
``parse_manchester(to_manchester(c)) == c`` for every ALC concept ``c`` — see
``tests/test_owl_manchester.py`` for the hand-checked precedence cases (the
grammar/lattice argument above is why this holds structurally, not just on
the tested examples: :func:`to_manchester` parenthesises a child exactly
when its precedence is below the parent slot's threshold, the same rule
:func:`parse_manchester` uses to *resolve* precedence when reading text back
in).
"""

from typing import List, Tuple

from .concepts import Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll

__all__ = [
    "parse_manchester", "to_manchester", "parse_manchester_axiom",
    "ManchesterSyntaxError",
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

_STRUCT_TOKENS = {
    "(": "LPAREN", ")": "RPAREN",
    "{": "LBRACE", "}": "RBRACE",
    "[": "LBRACKET", "]": "RBRACKET",
}

# A Token is (type: str, value: str, pos: int).
_Token = Tuple[str, str, int]


def _classify_word(word: str) -> str:
    """Classify a maximal non-structural, non-whitespace run as a keyword or NAME."""
    if word in _KEYWORDS:
        return _KEYWORDS[word]
    bare = word[:-1] if word.endswith(":") else word
    if bare in _AXIOM_KEYWORDS:
        return _AXIOM_KEYWORDS[bare]
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
                self._reject("datatype facet restrictions ('[...]')", self._peek())
            nxt = self._peek()
            if nxt[0] == "SOME":
                self._advance()
                return Exists(value, self._primary())
            if nxt[0] == "ONLY":
                self._advance()
                return ForAll(value, self._primary())
            if nxt[0] in ("MIN", "MAX", "EXACTLY"):
                self._reject(f"cardinality restrictions ('{nxt[1]}')", nxt)
            if nxt[0] == "VALUE":
                self._reject("value restrictions ('value')", nxt)
            if nxt[0] == "SELF":
                self._reject("Self restrictions ('Self')", nxt)
            if value == "owl:Thing":
                return Top()
            if value == "owl:Nothing":
                return Bottom()
            return Atomic(value)
        found = "end of input" if ttype == "EOF" else f"{value!r}"
        raise self._error(
            f"parse_manchester: unexpected {found} at position {pos}; "
            "expected a class name, 'not', 'owl:Thing', 'owl:Nothing', or '('")

    def parse_description(self) -> Concept:
        c = self._description()
        self._expect_eof()
        return c


# --------------------------------------------------------------------------- #
# Public API.
# --------------------------------------------------------------------------- #

def parse_manchester(text: str) -> Concept:
    """Parse ``text`` (OWL 2 Manchester Syntax, ALC fragment) into a :class:`Concept`.

    Round-trips against :func:`to_manchester`: ``parse_manchester(to_manchester(c))
    == c`` for every ALC concept ``c`` (see the module docstring's "Round-trip
    guarantee").

    Args:
        text: A Manchester-syntax class expression, e.g.
            ``"Person and hasChild some (Doctor and not Rich)"``.

    Returns:
        The parsed :class:`Concept`.

    Raises:
        ManchesterSyntaxError: On malformed input (unbalanced parentheses, a
            stray keyword, trailing garbage, …) or on syntax that is valid
            Manchester/OWL 2 but outside ALC (cardinalities, ``value``,
            ``Self``, ``inverse``, nominals, datatype facets — see the module
            docstring's "Rejected constructs").
    """
    return _Parser(_tokenize(text), text).parse_description()


def to_manchester(concept: Concept) -> str:
    """Render ``concept`` in OWL 2 Manchester Syntax, dual to :func:`parse_manchester`.

    Parenthesises a child expression exactly when its precedence is below the
    threshold of the slot it sits in (see the module docstring's "Grammar and
    precedence"), so the output is minimally parenthesised and re-parses to
    an identical AST.

    Args:
        concept: Any ALC :class:`Concept` (as built by
            :mod:`unicode_fol_kit.dl.concepts`'s constructors).

    Returns:
        The Manchester-syntax rendering, e.g. ``"r some (A and B)"``.
    """
    return _render(concept)


def parse_manchester_axiom(text: str) -> Tuple[str, Concept, Concept]:
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
    sub = _Parser(left_tokens, text).parse_description()
    sup = _Parser(right_tokens, text).parse_description()
    label = "subclass" if kind == "SUBCLASSOF" else "equivalent"
    return (label, sub, sup)


# --------------------------------------------------------------------------- #
# Renderer.
# --------------------------------------------------------------------------- #

# Same lattice as concepts.py's _PREC (Or=1 < And=2 < Not=Exists=ForAll=3 < Atomic=4):
# see the module docstring's "Grammar and precedence" for why the two coincide.
_PREC = {Or: 1, And: 2, Not: 3, Exists: 3, ForAll: 3, Atomic: 4, Top: 4, Bottom: 4}


def _render(c: Concept) -> str:
    """Render a concept with precedence-aware parenthesisation."""
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return c.name
    if isinstance(c, Not):
        return "not " + _paren(c.concept, 3)
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} and {_paren(c.right, 2)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} or {_paren(c.right, 1)}"
    if isinstance(c, Exists):
        return f"{c.role} some {_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"{c.role} only {_paren(c.concept, 3)}"
    raise TypeError(f"to_manchester: unsupported concept {type(c).__name__}")


def _paren(c: Concept, parent_prec: int) -> str:
    """Parenthesise ``c`` when its precedence is below the parent slot's threshold."""
    inner = _render(c)
    return f"({inner})" if _PREC.get(type(c), 4) < parent_prec else inner
