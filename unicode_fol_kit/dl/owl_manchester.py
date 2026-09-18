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
constructs" below): ``value`` restrictions, ``Self`` restrictions, inverse
roles (``inverse r``), nominal ("one-of") concepts (``{a, b}``), and datatype
facet restrictions (``dtype[>= 0]``). Each is rejected with a
:class:`ManchesterSyntaxError` naming the specific construct, per the kit's
honesty convention (an unsupported construct is a loud, precise error —
never a silent mistranslation or a weaker-than-requested result).

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
``parse_manchester(to_manchester(c)) == c`` for every ALC concept ``c`` — see
``tests/test_owl_manchester.py`` for the hand-checked precedence cases (the
grammar/lattice argument above is why this holds structurally, not just on
the tested examples: :func:`to_manchester` parenthesises a child exactly
when its precedence is below the parent slot's threshold, the same rule
:func:`parse_manchester` uses to *resolve* precedence when reading text back
in).

Role axioms: ``SubPropertyOf`` / ``Characteristics: Transitive``
-------------------------------------------------------------------
:func:`parse_manchester_role_axiom` reads the two RBox axiom shapes
:class:`~unicode_fol_kit.dl.tableau.TBox` supports (role inclusions and
transitivity declarations — see "Role hierarchies and transitive roles
(RBox)" in :mod:`unicode_fol_kit.dl.tableau`'s module docstring), each as the
one-line spelling this module already uses for :func:`parse_manchester_axiom`
rather than the full multi-line W3C ``ObjectProperty:`` frame (with its
``Domain``/``Range``/annotation slots, none of which this kit's RBox
represents): ``"r SubPropertyOf s"`` (the frame keyword ``SubPropertyOf``
may carry its W3C-grammar trailing colon, exactly like ``SubClassOf``/
``SubClassOf:`` above) and ``"r Characteristics: Transitive"`` (the W3C
frame's ``Characteristics:`` slot, here restricted to a single
characteristic value). Every OTHER OWL role characteristic —
``Functional``, ``InverseFunctional``, ``Symmetric``, ``Asymmetric``,
``Reflexive``, ``Irreflexive`` — sits outside ALCHQ (most need inverse roles,
which this kit's DL fragment does not have; a role-level characteristic like
``Functional`` is also a different thing from this module's concept-level
``AtLeast``/``AtMost`` — see "Qualified number restrictions" above — and is
not sugared into one) and is rejected by NAME, per the kit's honesty
convention, rather than silently ignored. :func:`role_axiom_to_manchester`
is the dual renderer.
"""

from typing import List, Tuple

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal,
)

__all__ = [
    "parse_manchester", "to_manchester", "parse_manchester_axiom",
    "parse_manchester_role_axiom", "role_axiom_to_manchester",
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

# Role-axiom-frame keywords (see "Role axioms" in the module docstring), same
# colon-optional convention as _AXIOM_KEYWORDS above.
_ROLE_AXIOM_KEYWORDS = {"SubPropertyOf": "SUBPROPERTYOF", "Characteristics": "CHARACTERISTICS"}

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
                self._advance()
                return self._number_restriction(nxt[0], value)
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

    # -- qualified number restrictions ('min'/'max'/'exactly') ---------- #

    _PRIMARY_START = {"NOT", "INVERSE", "LBRACE", "LPAREN", "NAME"}

    def _number_restriction(self, kind: str, role: str) -> Concept:
        """Parse the ``n primary?`` tail of ``role (min|max|exactly) n primary?``,
        having already consumed ``role`` and the ``kind`` keyword (see the module
        docstring's "Qualified number restrictions"). The qualifying class defaults
        to ``owl:Thing`` (⊤) when the next token cannot start a ``primary``.
        """
        n = self._expect_nonneg_int()
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


_SUPPORTED_CHARACTERISTIC = "Transitive"

# Every OWL 2 role characteristic recognised by the W3C grammar, for the error
# message when a real-but-unsupported one is used (see module docstring).
_ALL_CHARACTERISTICS = {
    "Functional", "InverseFunctional", "Reflexive", "Irreflexive",
    "Symmetric", "Asymmetric", "Transitive",
}


def parse_manchester_role_axiom(text: str) -> Tuple[str, ...]:
    """Parse a Manchester-syntax role inclusion or transitivity declaration.

    Accepts exactly ``"r SubPropertyOf s"`` (the frame keyword may optionally
    carry its W3C-grammar trailing colon, ``"SubPropertyOf:"``, exactly like
    ``SubClassOf``/``SubClassOf:`` in :func:`parse_manchester_axiom`) and
    ``"r Characteristics: Transitive"`` — see "Role axioms" in the module
    docstring for why only these two one-line shapes, of the full W3C
    ``ObjectProperty:`` frame syntax, are supported.

    Args:
        text: A single role axiom, e.g. ``"hasChild SubPropertyOf hasDescendant"``
            or ``"hasDescendant Characteristics: Transitive"``.

    Returns:
        ``("subproperty", sub_role, super_role)`` for a ``SubPropertyOf``
        axiom (feeding :meth:`~unicode_fol_kit.dl.tableau.TBox.add_role_inclusion`),
        or ``("transitive", role)`` for a ``Characteristics: Transitive``
        declaration (feeding :meth:`~unicode_fol_kit.dl.tableau.TBox.add_transitive_role`).

    Raises:
        ManchesterSyntaxError: malformed input, a role characteristic other
            than ``Transitive`` (named explicitly in the message — see the
            module docstring), or anything not matching one of the two shapes.
    """
    tokens = _tokenize(text)

    def error(message: str) -> ManchesterSyntaxError:
        return ManchesterSyntaxError(f"parse_manchester_role_axiom: {message} in {text!r}")

    if tokens[0][0] != "NAME":
        found = "end of input" if tokens[0][0] == "EOF" else f"{tokens[0][1]!r}"
        raise error(f"expected a role name but found {found} at position {tokens[0][2]}")
    role = tokens[0][1]
    keyword = tokens[1]

    if keyword[0] == "SUBPROPERTYOF":
        if len(tokens) == 4 and tokens[2][0] == "NAME" and tokens[3][0] == "EOF":
            return ("subproperty", role, tokens[2][1])
        raise error("expected exactly '<role> SubPropertyOf <role>'")

    if keyword[0] == "CHARACTERISTICS":
        if len(tokens) == 4 and tokens[2][0] == "NAME" and tokens[3][0] == "EOF":
            characteristic = tokens[2][1]
            if characteristic == _SUPPORTED_CHARACTERISTIC:
                return ("transitive", role)
            if characteristic in _ALL_CHARACTERISTICS:
                raise error(
                    f"role characteristic {characteristic!r} is not supported — "
                    "ALCHQ (this kit's DL fragment) has no inverse roles, and a "
                    "role-level characteristic is not the same as this module's "
                    "concept-level AtLeast/AtMost number restrictions, so only "
                    "'Transitive' is expressible")
            raise error(f"unknown role characteristic {characteristic!r}")
        raise error("expected exactly '<role> Characteristics: <characteristic>'")

    found = "end of input" if keyword[0] == "EOF" else f"{keyword[1]!r}"
    raise error(
        f"expected 'SubPropertyOf' or 'Characteristics:' but found {found} "
        f"at position {keyword[2]}")


# --------------------------------------------------------------------------- #
# Renderer.
# --------------------------------------------------------------------------- #

# Same lattice as concepts.py's _PREC (Or=1 < And=2 < Not=Exists=ForAll=AtLeast=
# AtMost=3 < Atomic=4): see the module docstring's "Grammar and precedence" for why
# the two coincide.
_PREC = {Or: 1, And: 2, Not: 3, Exists: 3, ForAll: 3, AtLeast: 3, AtMost: 3,
         Atomic: 4, Top: 4, Bottom: 4, Nominal: 4}


def _render_role(role) -> str:
    """Render a ``role`` field: ``inverse r`` for an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole` (the W3C grammar's own
    spelling — see "Export-only asymmetry" in the module docstring), the bare
    name otherwise.
    """
    if isinstance(role, InverseRole):
        return f"inverse {role.role}"
    return role


def _render(c: Concept) -> str:
    """Render a concept with precedence-aware parenthesisation."""
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return c.name
    if isinstance(c, Nominal):
        return "{" + c.individual + "}"
    if isinstance(c, Not):
        return "not " + _paren(c.concept, 3)
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} and {_paren(c.right, 2)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} or {_paren(c.right, 1)}"
    if isinstance(c, Exists):
        return f"{_render_role(c.role)} some {_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"{_render_role(c.role)} only {_paren(c.concept, 3)}"
    if isinstance(c, AtLeast):
        return _number_restriction_render(c.role, "min", c.n, c.concept)
    if isinstance(c, AtMost):
        return _number_restriction_render(c.role, "max", c.n, c.concept)
    raise TypeError(f"to_manchester: unsupported concept {type(c).__name__}")


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


def role_axiom_to_manchester(*axiom: str) -> str:
    """Render a role axiom, dual to :func:`parse_manchester_role_axiom`.

    Round-trips: ``parse_manchester_role_axiom(role_axiom_to_manchester(*axiom))
    == axiom`` for every ``axiom`` one of that function's two return shapes.

    Args:
        *axiom: Either ``("subproperty", sub_role, super_role)`` or
            ``("transitive", role)`` — exactly what :func:`parse_manchester_role_axiom`
            returns.

    Returns:
        ``"sub_role SubPropertyOf super_role"`` or ``"role Characteristics: Transitive"``.

    Raises:
        ValueError: ``axiom`` is not one of the two recognised shapes.
    """
    if len(axiom) == 3 and axiom[0] == "subproperty":
        _, sub_role, super_role = axiom
        return f"{sub_role} SubPropertyOf {super_role}"
    if len(axiom) == 2 and axiom[0] == "transitive":
        _, role = axiom
        return f"{role} Characteristics: {_SUPPORTED_CHARACTERISTIC}"
    raise ValueError(
        f"role_axiom_to_manchester: expected ('subproperty', sub, sup) or "
        f"('transitive', role), got {axiom!r}")
