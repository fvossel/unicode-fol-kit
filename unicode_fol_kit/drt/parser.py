"""Two parsers into :class:`~unicode_fol_kit.drt.nodes.DRS`: a compact hand-rolled box
notation (:func:`parse_drs`), and a documented SUBSET of the Parallel Meaning Bank's
Sequence Box Notation (:func:`parse_sbn`) — the PMB's line-based interchange format for
DRS-like structures (van Noord et al.'s Parallel Meaning Bank project releases sense-
disambiguated, role-annotated semantic parses in this format; it is the natural "found
data" source for DRSs, hence the SBN import path).

Both are small, purpose-built, single-shot grammars — no dialect sharing, no term/lambda
layer — so, exactly as ``unicode_fol_kit.dl.parser`` argues for ALC concepts, a hand-rolled
tokenizer/recursive-descent parser is simpler and gives better per-construct error messages
than standing up a Lark grammar + transformer for either of them.

=================================================================================
1. The box notation (``parse_drs``)
=================================================================================

Grammar (``|`` = alternative, ``?`` = optional, ``*`` = zero-or-more; NAME classes are
exactly ``unicode_fol_kit.drt.nodes``'s ``is_referent`` / ``is_predicate_name`` /
``is_constant_name``, i.e. the kit's own VARIABLE / PREDICATE / NAME lexical conventions)::

    document  := boxexpr EOF
    boxexpr   := "~" box                        # -> Neg(box)
               | box (("->" | "∨") box)?         # -> box | Impl(box, box) | Or(box, box)

    box       := "[" refs? "|" conds? "]"
    refs      := REF ("," REF)*
    conds     := cond ("," cond)*
    cond      := pred_cond | eq_cond
               | "~" box                         # -> Neg(box)
               | box ("->" | "∨") box             # -> Impl(box, box) | Or(box, box)

    pred_cond := PRED "(" term ("," term)* ")"
    eq_cond   := term "=" term
    term      := REF | CONST | STRING

    REF       : a single lowercase letter optionally followed by digits (x, y, e12, ...)
    CONST     : a lowercase-initial bare identifier of >= 2 characters (john, daisy, ...)
    PRED      : an uppercase-initial alphanumeric identifier (Farmer, Owns, ...)
    STRING    : a double-quoted literal ("John Doe") — sanitized to a legal CONST via
                unicode_fol_kit.fol.sanitize.NameMapping (kept consistent within one
                parse_drs call; not returned — see "Quoted constants" below)

Worked example (the classic donkey sentence, exactly as it appears in the kit roadmap)::

    [x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]

parses to ``DRS((), (Impl(DRS(("x","y"), (Pred("Farmer",("x",)), Pred("Donkey",("y",)),
Pred("Owns",("x","y")))), DRS((), (Pred("Beats",("x","y")),))),))`` — a top-level bare
``Impl``/``Neg``/``Or`` result is wrapped as the sole condition of an empty-referent DRS
(a "bare box" result, with no trailing ``->``/``∨``, IS the returned DRS directly).

**Deliberately unambiguous, at the cost of expressiveness.** ``boxexpr`` accepts AT MOST
ONE ``->``/``∨`` after a box, and ``~`` only ever prefixes a bare ``box`` (never a whole
``boxexpr``) — so ``~[...] -> [...]`` and ``[...] -> [...] -> [...]`` are BOTH refused
(with a message naming the dangling trailing token) rather than silently picking a
left/right-associativity or an operator-precedence convention nobody asked for. Nest boxes
explicitly instead — e.g. ``[ | ~[...]] -> [...]`` for the first case — box notation has
no expressiveness loss, only a syntax-level one. A "cond" that is a bare box with no
``->``/``∨`` suffix is refused too (naming the position): a bare DRS is not one of the five
condition variants (:mod:`unicode_fol_kit.drt.nodes`) — wrap it in ``~[...]`` or make it a
``->``/``∨`` operand.

**Quoted constants.** A bare CONST token is already legal (``is_constant_name``) and passes
through unchanged. A quoted ``"..."`` STRING is for constants box notation's bare-token
syntax cannot express as-is (spaces, punctuation, digit-leading, single characters that
would otherwise collide with the referent namespace, non-ASCII, ...); it is sanitized via a
fresh :class:`~unicode_fol_kit.fol.sanitize.NameMapping` PER ``parse_drs`` CALL (consistent
within one call — the same quoted string always sanitizes to the same constant — but not
returned to the caller, since the primary, recommended path is to just write a legal bare
CONST directly, as the roadmap's own donkey-sentence facts do: ``Farmer(john)``, no quotes
needed). :func:`parse_sbn` below, whose quoted constants are the norm rather than an
escape hatch, DOES return its mapping.

=================================================================================
2. The SBN subset (``parse_sbn``)
=================================================================================

Real SBN is a line-per-token format: each line names a WordNet-style sense for one token of
the sentence, optionally followed by semantic-role edges to OTHER lines (by relative line
offset) or to literal constants. This function implements a precisely bounded SUBSET,
documented here in full — anything outside it is REFUSED, naming the construct, rather than
silently mis-parsed:

    sbn      := line+
    line     := TABS (sense_line | "NEGATION") COMMENT?
    sense_line := SENSE (ROLE target)*
    SENSE    := LEMMA "." POS "." SENSE_NUM         # e.g. farmer.n.01
        LEMMA     : /[a-z][a-z_]*/                  # underscore-joined lowercase words
        POS       : one of n, v, a, r, s
        SENSE_NUM : exactly two digits
    ROLE     := /[A-Z][a-zA-Z0-9]*/                 # e.g. Agent, Patient, Theme
    target   := OFFSET | STRING
        OFFSET  : /[+-][0-9]+/                      # relative CONTENT-line index (see below)
        STRING  : a double-quoted literal
    COMMENT  := "%" rest-of-line, ignored wherever it appears
    blank (whitespace-only) lines are ignored and do not consume a content-line index.

* **Indentation is exactly TAB characters** (one tab = one nesting depth; mixing in spaces,
  or indenting with spaces at all, is refused). Depth 0 lines form the outermost DRS; a
  depth-``d`` line may only be followed by a depth-``d+1`` line if it is a ``NEGATION``
  line (opening a sub-box that the following, deeper-indented lines belong to, up to but
  not including the next line at depth <= d, or EOF) — any other depth jump (skipping a
  level, or dedenting to a depth that was never open) is refused, naming the line.
* **Line numbering.** Every CONTENT line (a ``sense_line`` or a ``NEGATION`` line — blank
  and comment-only lines do not count) gets a 1-based index in document order, REGARDLESS
  of indentation depth; a ``sense_line`` at index ``i`` introduces the referent ``f"e{i}"``.
  A ``NEGATION`` line consumes an index too (so offsets past it stay stable) but introduces
  no referent of its own — targeting one is refused, naming the line ("a box-operator line
  has no referent in this subset").
* **Sense -> predicate, exactly as the kit roadmap specifies**: ``person.n.01`` becomes the
  predicate ``PersonN01`` (each dot-separated part capitalised — an underscore-joined lemma
  like ``get_up.v.02`` becomes ``GetUpV02`` — and concatenated; PoS and sense-number keep
  their literal digits/letter). The token -> predicate mapping is recorded and returned
  (:class:`SBNMapping.predicates`) since it is lossy (case and the dots are gone).
* **Role -> binary predicate**, exactly as written (``Agent``) applied to
  ``(this_line's_referent, target)`` — i.e. ``Agent(e3, e1)`` style, per the roadmap.
* **The only supported box-changing operator is ``NEGATION``.** Any other ALL-CAPS token
  in sense-token position (``POSSIBLE``, ``NECESSARY``, ``DISCOURSE_REFERENCE``, PMB's
  other real operators, ...) is REFUSED BY NAME: this subset is negation-only. A
  ``NEGATION`` line with no more-indented line following it (an empty scope) is refused too
  — in this subset a box operator only ever appears to introduce content, never vacuously.
* **Quoted constants** are sanitized via :class:`~unicode_fol_kit.fol.sanitize.NameMapping`
  (lower-cased first, so ``"John"`` and ``"john"` map together), and the mapping IS returned
  (:class:`SBNMapping.constants`) — unlike the box notation's escape-hatch quoting, a
  quoted literal is SBN's ONLY way to write a constant, so recovering the original matters.

**What is explicitly out of scope** (refused by name, never silently dropped): event
quantification / plural referents, presupposition triggers, any operator besides NEGATION,
multi-word discourse (this parses ONE sbn "document" — i.e. one sentence's worth of boxes —
per call, matching this kit subpackage's single-sentence-plus-anaphora scope; see the
``unicode_fol_kit.drt`` package docstring).

The 2-3 SBN examples exercised in ``tests/test_drt.py`` are CONSTRUCTED BY HAND for this
subset's test coverage — they are illustrative, not verbatim PMB corpus data.
"""

import re
from dataclasses import dataclass
from typing import Dict, List, Tuple, Union

from ..fol.sanitize import NameMapping
from .nodes import (
    DRS, Condition, Pred, Eq, Neg, Impl, Or,
    is_referent, is_predicate_name, is_constant_name,
)

__all__ = [
    "parse_drs", "DRSSyntaxError",
    "parse_sbn", "SBNSyntaxError", "SBNMapping",
]


class DRSSyntaxError(ValueError):
    """Raised by :func:`parse_drs` on malformed box-notation input."""


class SBNSyntaxError(ValueError):
    """Raised by :func:`parse_sbn` on malformed input, or a construct outside the
    documented SBN subset (see the module docstring)."""


# =============================================================================
# 1. Box notation.
# =============================================================================

_GLYPHS = {
    "[": "LB", "]": "RB", "|": "PIPE", ",": "COMMA", "~": "TILDE",
    "=": "EQ", "(": "LP", ")": "RP", "∨": "OR",
}

# A Token is (type: str, value: str, pos: int).
_Token = Tuple[str, str, int]


def _tokenize_drs(text: str) -> List[_Token]:
    """Split ``text`` into box-notation tokens, plus a trailing EOF sentinel."""
    tokens: List[_Token] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "-" and i + 1 < n and text[i + 1] == ">":
            tokens.append(("ARROW", "->", i))
            i += 2
            continue
        if ch in _GLYPHS:
            tokens.append((_GLYPHS[ch], ch, i))
            i += 1
            continue
        if ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 1
            if j >= n:
                raise DRSSyntaxError(
                    f"parse_drs: unterminated string literal starting at position "
                    f"{i} in {text!r}")
            tokens.append(("STRING", text[i + 1:j], i))
            i = j + 1
            continue
        if ch.isalpha():
            j = i
            while j < n and text[j].isalnum():
                j += 1
            word = text[i:j]
            if is_predicate_name(word):
                tokens.append(("PRED", word, i))
            elif is_referent(word):
                tokens.append(("REF", word, i))
            elif is_constant_name(word):
                tokens.append(("CONST", word, i))
            else:
                raise DRSSyntaxError(
                    f"parse_drs: {word!r} at position {i} is not a legal referent, "
                    f"constant, or predicate name in {text!r}")
            i = j
            continue
        raise DRSSyntaxError(f"parse_drs: unexpected character {ch!r} at position {i} in {text!r}")
    tokens.append(("EOF", "", n))
    return tokens


class _DRSParser:
    """A single parse of one token stream; not re-used across calls."""

    def __init__(self, tokens: List[_Token], text: str):
        self._tokens = tokens
        self._text = text
        self._i = 0
        self._mapping = NameMapping()

    def _peek(self) -> _Token:
        return self._tokens[self._i]

    def _advance(self) -> _Token:
        tok = self._tokens[self._i]
        self._i += 1
        return tok

    def _error(self, message: str) -> DRSSyntaxError:
        return DRSSyntaxError(f"parse_drs: {message} in {self._text!r}")

    def _expect(self, ttype: str, what: str) -> _Token:
        tok = self._peek()
        if tok[0] != ttype:
            found = "end of input" if tok[0] == "EOF" else f"{tok[1]!r}"
            raise self._error(f"expected {what} but found {found} at position {tok[2]}")
        return self._advance()

    # -- grammar ---------------------------------------------------------- #

    def parse_document(self) -> DRS:
        result = self._boxexpr()
        eof = self._peek()
        if eof[0] != "EOF":
            raise self._error(
                f"unexpected trailing input {eof[1]!r} at position {eof[2]} (chaining "
                f"multiple ->/∨/~ at the top level is not supported — nest boxes "
                f"explicitly instead)")
        if isinstance(result, DRS):
            return result
        return DRS((), (result,))

    def _boxexpr(self) -> Union[DRS, Condition]:
        if self._peek()[0] == "TILDE":
            self._advance()
            return Neg(self._box())
        box = self._box()
        nxt = self._peek()
        if nxt[0] == "ARROW":
            self._advance()
            return Impl(box, self._box())
        if nxt[0] == "OR":
            self._advance()
            return Or(box, self._box())
        return box

    def _box(self) -> DRS:
        self._expect("LB", "'['")
        refs = self._refs()
        self._expect("PIPE", "'|' separating referents from conditions")
        conds = self._conds()
        self._expect("RB", "']'")
        return DRS(tuple(refs), tuple(conds))

    def _refs(self) -> List[str]:
        if self._peek()[0] != "REF":
            return []
        out = [self._advance()[1]]
        while self._peek()[0] == "COMMA":
            self._advance()
            out.append(self._expect("REF", "a referent name after ','")[1])
        return out

    def _conds(self) -> List[Condition]:
        if self._peek()[0] == "RB":
            return []
        out = [self._cond()]
        while self._peek()[0] == "COMMA":
            self._advance()
            out.append(self._cond())
        return out

    def _cond(self) -> Condition:
        t = self._peek()
        if t[0] == "TILDE":
            self._advance()
            return Neg(self._box())
        if t[0] == "LB":
            box = self._box()
            nxt = self._peek()
            if nxt[0] == "ARROW":
                self._advance()
                return Impl(box, self._box())
            if nxt[0] == "OR":
                self._advance()
                return Or(box, self._box())
            raise self._error(
                f"a bare DRS ({box.to_box_notation()}) is not a valid condition by "
                f"itself at position {t[2]} — wrap it in negation (~[...]) or make it "
                f"one side of a duplex condition ([...] -> [...] / [...] ∨ [...])")
        if t[0] == "PRED":
            return self._pred_cond()
        if t[0] in ("REF", "CONST", "STRING"):
            return self._eq_cond()
        raise self._error(
            f"expected a condition (a predicate, an equality, ~[...], or "
            f"[...] -> / ∨ [...]) but found "
            f"{'end of input' if t[0] == 'EOF' else repr(t[1])} at position {t[2]}")

    def _term(self) -> str:
        t = self._peek()
        if t[0] in ("REF", "CONST"):
            self._advance()
            return t[1]
        if t[0] == "STRING":
            self._advance()
            return self._mapping.for_constant(t[1])
        raise self._error(
            f"expected a referent, constant, or quoted string but found "
            f"{'end of input' if t[0] == 'EOF' else repr(t[1])} at position {t[2]}")

    def _pred_cond(self) -> Pred:
        name = self._advance()[1]
        self._expect("LP", "'(' after the predicate name")
        args = [self._term()]
        while self._peek()[0] == "COMMA":
            self._advance()
            args.append(self._term())
        self._expect("RP", "')'")
        return Pred(name, tuple(args))

    def _eq_cond(self) -> Eq:
        a = self._term()
        self._expect("EQ", "'=' (only a predicate application or an equality may "
                            "start with a referent/constant/string)")
        b = self._term()
        return Eq(a, b)


def parse_drs(text: str) -> DRS:
    """Parse ``text`` (the compact box notation documented in the module docstring)
    into a :class:`~unicode_fol_kit.drt.nodes.DRS`. Raises :class:`DRSSyntaxError` on
    malformed input (unbalanced brackets, a bare box used as a condition, chained
    ``->``/``∨``/``~``, an illegal referent/constant/predicate token, ...)."""
    parser = _DRSParser(_tokenize_drs(text), text)
    return parser.parse_document()


# =============================================================================
# 2. SBN subset.
# =============================================================================

_SENSE_RE = re.compile(r"^([a-z][a-z_]*)\.([nvars])\.([0-9]{2})$")
_ROLE_RE = re.compile(r"^[A-Z][a-zA-Z0-9]*$")
_OFFSET_RE = re.compile(r"^([+-])([0-9]+)$")
_ALLCAPS_RE = re.compile(r"^[A-Z_]+$")

_NEGATION = "NEGATION"


@dataclass(frozen=True)
class SBNMapping:
    """The mappings :func:`parse_sbn` used, so a lossy sanitization can be undone.

    ``predicates`` maps each original sense token (``"person.n.01"``) to the predicate
    name it became (``"PersonN01"``); ``constants`` maps each original (lower-cased)
    quoted string to its sanitized constant name.
    """

    predicates: Dict[str, str]
    constants: Dict[str, str]

    def to_dict(self) -> dict:
        return {"predicates": dict(self.predicates), "constants": dict(self.constants)}


def _sbn_predicate_name(token: str) -> str:
    """Turn a WordNet-style sense token into a legal predicate name (see the module
    docstring: ``person.n.01`` -> ``PersonN01``). Raises :class:`SBNSyntaxError` if
    ``token`` is not a well-formed ``lemma.pos.NN`` sense token."""
    m = _SENSE_RE.fullmatch(token)
    if not m:
        raise SBNSyntaxError(
            f"parse_sbn: sense token {token!r} is not of the form 'lemma.pos.NN' "
            f"(lowercase underscore-joined lemma, pos in n/v/a/r/s, two-digit sense) "
            f"— this SBN subset only supports well-formed WordNet-style sense tokens.")
    lemma, pos, sense = m.groups()
    pascal = "".join(part[:1].upper() + part[1:] for part in lemma.split("_") if part)
    return f"{pascal}{pos.upper()}{sense}"


def _split_respecting_quotes(s: str, lineno: int) -> List[str]:
    """Whitespace-tokenize ``s``, keeping a quoted ``"..."`` span (which may itself
    contain whitespace) as a single token including its quotes."""
    tokens: List[str] = []
    i, n = 0, len(s)
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 1
            if j >= n:
                raise SBNSyntaxError(f"parse_sbn: line {lineno}: unterminated quoted constant")
            tokens.append(s[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and not s[j].isspace():
                j += 1
            tokens.append(s[i:j])
            i = j
    return tokens


def _split_sbn_lines(text: str) -> List[Tuple[str, int, int]]:
    """Pass 1: strip comments/blanks, measure TAB-only indentation depth. Returns
    ``(content, lineno, depth)`` triples for every content line."""
    out: List[Tuple[str, int, int]] = []
    for lineno, raw in enumerate(text.split("\n"), start=1):
        line = raw.split("%", 1)[0]
        if not line.strip():
            continue
        no_lead = line.lstrip(" \t")
        leading = line[:len(line) - len(no_lead)]
        if " " in leading:
            raise SBNSyntaxError(
                f"parse_sbn: line {lineno} is indented with a space character; this "
                f"SBN subset requires TAB-only indentation")
        out.append((no_lead.strip(), lineno, len(leading)))
    if not out:
        raise SBNSyntaxError("parse_sbn: empty input (no content lines)")
    return out


@dataclass
class _SBNLine:
    lineno: int
    depth: int
    index: int
    kind: str                       # "sense" | "negation"
    predicate: str = ""             # sanitized predicate name, kind == "sense" only
    role_targets: tuple = ()        # tuple of (role, raw_target) pairs


def parse_sbn(text: str) -> Tuple[DRS, SBNMapping]:
    """Parse ``text`` (the documented SBN SUBSET — see the module docstring) into a
    ``(DRS, SBNMapping)`` pair. Raises :class:`SBNSyntaxError` on malformed input or on
    any construct outside the documented subset (naming it explicitly)."""
    raw_lines = _split_sbn_lines(text)

    # Pass 2: tokenize each line's own payload (sense/NEGATION keyword + role/target
    # pairs), without resolving offset targets yet — that needs the full index->kind map.
    pred_mapping: Dict[str, str] = {}
    parsed_lines: List[_SBNLine] = []
    for index, (content, lineno, depth) in enumerate(raw_lines, start=1):
        parts = _split_respecting_quotes(content, lineno)
        head, rest = parts[0], parts[1:]
        if head == _NEGATION:
            if rest:
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: 'NEGATION' takes no roles/targets in "
                    f"this subset, found {rest!r}")
            parsed_lines.append(_SBNLine(lineno, depth, index, "negation"))
            continue
        if _ALLCAPS_RE.fullmatch(head):
            raise SBNSyntaxError(
                f"parse_sbn: line {lineno}: box-operator {head!r} is not supported by "
                f"this SBN subset (only NEGATION is) — refusing rather than silently "
                f"misreading it.")
        if len(rest) % 2 != 0:
            raise SBNSyntaxError(
                f"parse_sbn: line {lineno}: role {rest[-1]!r} has no target")
        role_targets = []
        for k in range(0, len(rest), 2):
            role, target = rest[k], rest[k + 1]
            if not _ROLE_RE.fullmatch(role):
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: role {role!r} must be uppercase-initial "
                    f"alphanumeric (e.g. 'Agent', 'Theme')")
            role_targets.append((role, target))
        predicate = pred_mapping.get(head)
        if predicate is None:
            predicate = _sbn_predicate_name(head)
            pred_mapping[head] = predicate
        parsed_lines.append(_SBNLine(lineno, depth, index, "sense", predicate, tuple(role_targets)))

    n = len(parsed_lines)
    kind_by_index = {pl.index: pl.kind for pl in parsed_lines}

    # Pass 3: resolve each role's raw target token to a final DRS term string.
    const_mapping = NameMapping()
    resolved: List[Tuple[_SBNLine, tuple]] = []
    for pl in parsed_lines:
        if pl.kind != "sense":
            resolved.append((pl, ()))
            continue
        terms = []
        for role, target in pl.role_targets:
            m = _OFFSET_RE.fullmatch(target)
            if m:
                sign, digits = m.groups()
                delta = int(digits) if sign == "+" else -int(digits)
                target_index = pl.index + delta
                if target_index < 1 or target_index > n:
                    raise SBNSyntaxError(
                        f"parse_sbn: line {pl.lineno}: offset {target!r} on role "
                        f"{role!r} points to line index {target_index}, outside the "
                        f"document (1..{n})")
                if kind_by_index[target_index] != "sense":
                    raise SBNSyntaxError(
                        f"parse_sbn: line {pl.lineno}: offset {target!r} on role "
                        f"{role!r} targets line {target_index}, a box-operator line "
                        f"with no referent of its own in this subset")
                terms.append((role, f"e{target_index}"))
            elif target.startswith('"') and target.endswith('"') and len(target) >= 2:
                raw_const = target[1:-1].lower()
                terms.append((role, const_mapping.for_constant(raw_const)))
            else:
                raise SBNSyntaxError(
                    f"parse_sbn: line {pl.lineno}: target {target!r} on role {role!r} "
                    f'is neither a signed line offset (+N / -N) nor a quoted constant ("...")')
        resolved.append((pl, tuple(terms)))

    # Pass 4: build the nested DRS via an indentation-driven stack of open boxes.
    class _Frame:
        __slots__ = ("depth", "referents", "conditions")

        def __init__(self, depth: int):
            self.depth = depth
            self.referents: List[str] = []
            self.conditions: List[Condition] = []

    def _close(frame: "_Frame") -> DRS:
        return DRS(tuple(frame.referents), tuple(frame.conditions))

    def _pop_negation(stack: List["_Frame"]) -> None:
        closed = stack.pop()
        if not closed.referents and not closed.conditions:
            raise SBNSyntaxError(
                "parse_sbn: a NEGATION line has no content — every NEGATION in this "
                "subset must be followed by at least one more-indented line")
        stack[-1].conditions.append(Neg(_close(closed)))

    stack: List[_Frame] = [_Frame(0)]
    for pl, terms in resolved:
        d = pl.depth
        while len(stack) > 1 and stack[-1].depth > d:
            _pop_negation(stack)
        current = stack[-1]
        if current.depth != d:
            raise SBNSyntaxError(
                f"parse_sbn: line {pl.lineno}: indentation depth {d} does not open or "
                f"continue any box (expected depth {current.depth})")
        if pl.kind == "negation":
            stack.append(_Frame(d + 1))
        else:
            ref = f"e{pl.index}"
            current.referents.append(ref)
            current.conditions.append(Pred(pl.predicate, (ref,)))
            for role, term in terms:
                current.conditions.append(Pred(role, (ref, term)))

    while len(stack) > 1:
        _pop_negation(stack)

    root = _close(stack[0])
    # Offsets are only range/kind-checked above; an offset that crosses a
    # NEGATION box boundary builds a structurally well-formed but
    # ACCESSIBILITY-violating DRS (review-flagged: a referent used outside
    # the box that declares it). Validate before handing it out so a caller
    # never receives a silently invalid tree — the violation surfaces here,
    # named, instead of downstream in drs_to_fol.
    root.validate()
    mapping = SBNMapping(predicates=dict(pred_mapping), constants=dict(const_mapping.constant))
    return root, mapping
