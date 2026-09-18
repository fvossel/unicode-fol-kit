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
               | "Card" "(" term "," CMP "," NUMBER ")"   # -> Card (0.24.0; the operator
               |                                          #    slot disambiguates against
               |                                          #    a Pred merely NAMED Card)
               | "Part_of" "(" term "," term ")"          # -> Part (0.24.0; exactly 2 args)
    eq_cond   := term "=" term
    term      := REF | CONST | STRING
    CMP       := ">=" | "<=" | "=" | ">" | "<"
    NUMBER    := /[0-9]+/

    REF       : a single lowercase letter optionally followed by digits (x, y, e12, ...)
    CONST     : a lowercase-initial bare identifier of >= 2 characters (john, daisy, ...)
    PRED      : an uppercase-initial identifier, underscores allowed in
                continuation (Farmer, Owns, Has_bond_to, ...)
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
silently mis-parsed::

    sbn      := line+
    line     := TABS (sense_line | "NEGATION") COMMENT?
    sense_line := SENSE (ROLE target)*
    SENSE    := LEMMA "." POS "." SENSE_NUM         # e.g. farmer.n.01
        LEMMA     : /[a-z][a-z_]*/                  # underscore-joined lowercase words
        POS       : one of n, v, a, r, s
        SENSE_NUM : exactly two digits
    ROLE     := /[A-Z][a-zA-Z0-9]*(-[A-Z][a-zA-Z0-9]*)?/  # e.g. Agent, Patient, Co-Theme
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
  **A role name may carry one hyphenated segment** (``Co-Theme``, ``Co-Agent``,
  ``Co-Patient``, ...) — VerbNet's own "Co-" compounding, common throughout real PMB
  releases; the hyphen is dropped when the role becomes a predicate name (``Co-Theme``
  -> ``CoTheme``, since the kit PREDICATE convention has no hyphen). This is part of the
  BASE grammar above, in force in both SBN dialects this function reads (see 2b below) —
  real PMB documents use ``Co-``-compounded roles whether or not they also happen to use
  the connector dialect's own box-operator mechanism (e.g. a flat document with no
  ``NEGATION`` line at all can still carry a ``Co-Theme`` role), so this widening cannot
  be gated to one dialect without silently refusing real, in-scope input.
* **The only supported box-changing operator is ``NEGATION``.** Any other ALL-CAPS token
  in sense-token position (``POSSIBLE``, ``NECESSARY``, ``DISCOURSE_REFERENCE``, PMB's
  other real operators, ...) is REFUSED BY NAME: this subset is negation-only. A
  ``NEGATION`` line with no more-indented line following it (an empty scope) is refused too
  — in this subset a box operator only ever appears to introduce content, never vacuously.
* **Quoted constants** are sanitized via :class:`~unicode_fol_kit.fol.sanitize.NameMapping`
  (lower-cased first, so ``"John"`` and ``"john"`` map together), and the mapping IS
  returned (:class:`SBNMapping.constants`) — unlike the box notation's escape-hatch
  quoting, a quoted literal is SBN's ONLY way to write a constant, so recovering the
  original matters.
* **Bare (unquoted) constants**: the four deictic references Bos (2023) §2.1 documents
  (``now``/``speaker``/``hearer``/``here`` — utterance time/speaker/addressee/location) and
  a bare UNSIGNED integer (``Quantity 3``) are also accepted as constant targets, routed
  through the same :class:`NameMapping` as quoted constants. Unambiguous with an OFFSET
  target, which always carries a sign.
* **A comment may itself contain a ``%``, ANSI colour escapes, or start with the PMB release
  format's own ``%%%``-prefixed generation-command header** — all of that is already inside
  the comment by the ``COMMENT`` rule above (everything from the first ``%`` on the line),
  so none of it needs special handling.

**What is explicitly out of scope** (refused by name, never silently dropped): event
quantification / plural referents, presupposition triggers, any operator besides NEGATION,
multi-word discourse (this parses ONE sbn "document" — i.e. one sentence's worth of boxes —
per call, matching this kit subpackage's single-sentence-plus-anaphora scope; see the
``unicode_fol_kit.drt`` package docstring).

=================================================================================
2b. A second SBN dialect: PMB's own released format (the "connector" dialect)
=================================================================================

The dialect above was hand-written before any real PMB release was measured against it.
PMB's actual gold releases (verified against pmb-5.1.0's
``data/<lang>/gold/p<NN>/d<NNNN>/<lang>.drs.sbn`` files) use a DIFFERENT, but fully
documented, mechanism instead of textual indentation — Bos (2023), "The Sequence Notation:
Catching Complex Meanings in Simple Graphs" (IWCS 2023), §§2.1/3.4/4.1.
:func:`parse_sbn` recognizes it automatically (see "Dialect selection" below) and reads it
as follows — everything not listed here (LEMMA/POS/SENSE_NUM, roles, quoted constants,
comments, ...) is exactly as in the dialect above:

* **Leading whitespace is PURE COSMETIC COLUMN ALIGNMENT**, never nesting depth (verified:
  no CONCEPT line in pmb-5.1.0 ever carries leading whitespace; only box-operator lines do,
  padding them to the sense-token column for human readability) — this dialect ignores it
  entirely, on every line, and never refuses a space the indentation dialect above would.
* **A box-operator line carries a trailing CONNECTOR token** (``<N``, a positive integer)
  instead of relying on indentation. Contexts (boxes) are numbered by INTRODUCTION ORDER:
  context 0 is the outermost, implicit context holding everything before the first
  separator; the K-th separator encountered (1-based, document order) introduces context K.
  Its connector ``<N`` (``1 <= N <= K``) says the separator's OWN reading (``Neg`` for
  ``NEGATION``) is a CONDITION of context ``K - N`` — e.g. ``<1`` attaches to the immediately
  preceding context, ``<2`` skips one further back, and so on; several separators may attach
  to the SAME earlier context (e.g. "she is neither rich nor famous": ``NEGATION <1`` then
  ``NEGATION <2``, both landing on context 0, giving ``¬Rich(x) ∧ ¬Famous(x)`` rather than a
  nested double negation — Bos 2023 Figure 4). As above, only ``NEGATION`` is a supported
  separator; every other name PMB emits (``POSSIBILITY``, ``NECESSITY``, and the SDRT
  discourse relations ``CONTINUATION``, ``CONTRAST``, ``CONJUNCTION``, ...) is refused by
  name — this subset's DRS conditions have no modal-box or discourse-relation reading for
  them. A FORWARD connector (``>N``) is refused too (it needs two-pass resolution this
  subset does not implement).
* **Role-hook indices (``+N``/``-N``) count CONCEPT (sense) lines ONLY**, skipping every
  box-operator line entirely — DELIBERATELY DIFFERENT from the dialect above's own
  numbering (which counts box-operator lines too, so that offsets stay stable across them):
  this is what Bos (2023) §3.3 and pmb-5.1.0 itself actually implement. Changing the other
  dialect's existing (self-consistent, if non-standard) numbering would break its own
  already-accepted inputs, so both numbering conventions coexist, one per dialect.
* A role target that is itself a connector (``Proposition >1`` — an embedded-clause /
  propositional-attitude argument pointing AT A CONTEXT rather than a concept) is refused by
  name: this subset only resolves entity-valued role targets.
* Role names may carry one hyphenated segment (``Co-Theme``, ``Co-Agent``, ...) — this is
  the BASE grammar's own rule (see the ``ROLE`` widening in section 2 above), not a
  connector-dialect addition; it is repeated here only because ``Co-`` compounding is
  especially common throughout pmb-5.1.0's connector-dialect documents. Comparison/
  temporal/spatial OPERATOR tokens (``EQU``, ``TPR``, ...) are lexically indistinguishable
  from roles in this subset and get the SAME uninterpreted binary-predicate treatment —
  none of their axiomatic content (e.g. ``EQU``'s reflexivity) is asserted, only the atom
  itself.

**Dialect selection.** :func:`parse_sbn` looks at every box-operator line up front: if ANY
of them carries a trailing connector token, the WHOLE document is read in the connector
dialect (every box-operator line must then carry one, or the specific line is named and
refused); otherwise it is read in the indentation dialect above (a bare ``NEGATION``, TAB
depth). The two dialects' numbering/indentation conventions are per-document, never mixed
within one call — this is exactly why every existing ``parse_sbn`` input (none of which
contains a connector token) keeps parsing to the identical DRS it always has.

The 2-3 SBN examples exercised in ``tests/test_drt.py`` for the indentation dialect are
CONSTRUCTED BY HAND — they are illustrative, not verbatim PMB corpus data. The connector
dialect is exercised against both hand-written fixtures and, when a caller points
``UFK_PMB_SBN_DIR`` at one, a real PMB gold release — see
:mod:`unicode_fol_kit.eval.datasets.pmb` and ``tests/test_datasets_pmb.py``.
"""

import re
from dataclasses import dataclass
from typing import Dict, List, Tuple, Union

from ..fol.sanitize import NameMapping
from .nodes import (
    DRS, Card, Condition, Pred, Eq, Neg, Impl, Or, Part,
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
        if ch in "<>":
            if i + 1 < n and text[i + 1] == "=":
                tokens.append(("CMP", ch + "=", i))
                i += 2
            else:
                tokens.append(("CMP", ch, i))
                i += 1
            continue
        if ch.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            tokens.append(("NUMBER", text[i:j], i))
            i = j
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
            # `_` is a word CONTINUATION character, never a start: the
            # name validators below decide legality (Has_bond_to is a
            # predicate, c_o1 a constant), the tokenizer only spans the
            # word. Stopping at `_` instead would split `Has_bond_to`
            # into three tokens and mis-parse it.
            while j < n and (text[j].isalnum() or text[j] == "_"):
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

    def _peek(self, ahead: int = 0) -> _Token:
        return self._tokens[min(self._i + ahead, len(self._tokens) - 1)]

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

    def _pred_cond(self) -> Condition:
        name = self._advance()[1]
        self._expect("LP", "'(' after the predicate name")
        args = [self._term()]
        if name == "Card" and self._peek()[0] == "COMMA":
            # Card(g, >=, 3): the second element is a comparison OPERATOR,
            # which no legal term can be -- so peeking one token past the
            # comma decides Card-vs-Pred without ambiguity, and a Pred that
            # happens to be NAMED Card (term-shaped args only) still parses.
            if self._peek(1)[0] in ("CMP", "EQ"):
                self._advance()  # the comma
                op = self._advance()[1]
                self._expect("COMMA", "',' before the cardinality bound")
                number = self._expect("NUMBER", "a non-negative integer bound")
                self._expect("RP", "')'")
                return Card(args[0], op, int(number[1]))
        while self._peek()[0] == "COMMA":
            self._advance()
            args.append(self._term())
        self._expect("RP", "')'")
        if name == "Part_of":
            # The typed membership condition (see nodes.Part): exactly two
            # arguments, and a programmatically built Pred("Part_of", (m, g))
            # re-parses as Part -- harmless on purpose, both export to the
            # same Part_of atom.
            if len(args) != 2:
                raise self._error(
                    f"Part_of takes exactly two arguments (member, group), "
                    f"got {len(args)}")
            return Part(args[0], args[1])
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
_ROLE_RE = re.compile(r"^[A-Z][a-zA-Z0-9]*(?:-[A-Z][a-zA-Z0-9]*)?$")
_OFFSET_RE = re.compile(r"^([+-])([0-9]+)$")
_ALLCAPS_RE = re.compile(r"^[A-Z_]+$")
_CONNECTOR_RE = re.compile(r"^([<>])([0-9]+)$")
_BARE_INTEGER_RE = re.compile(r"^[0-9]+$")

_NEGATION = "NEGATION"
#: The deictic-reference constants Bos (2023) §2.1 documents as bare (unquoted)
#: literals: the utterance time, its speaker, its addressee, and its location.
_DEICTIC_CONSTANTS = frozenset({"now", "speaker", "hearer", "here"})


@dataclass(frozen=True)
class SBNMapping:
    """The mappings :func:`parse_sbn` used, so a lossy sanitization can be undone.

    ``predicates`` maps each original sense token (``"person.n.01"``) to the predicate
    name it became (``"PersonN01"``); ``constants`` maps each original literal constant
    token — a (lower-cased) quoted string, or one of this subset's bare literals (a
    deictic reference or a bare integer, accepted in either dialect — see the module
    docstring's "Bare (unquoted) constants" bullet, part of the shared base grammar) —
    to its sanitized constant name.
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


def _sbn_role_predicate_name(role: str) -> str:
    """A ROLE (or comparison/temporal/spatial OPERATOR token, e.g. ``EQU`` — lexically
    indistinguishable from a role in this subset, see the module docstring) as a legal
    kit predicate name. Each hyphen-segment of a VerbNet 'Co-' compound (``Co-Theme``,
    :data:`_ROLE_RE`) is already uppercase-initial, so dropping the hyphen keeps it
    PascalCase (``CoTheme``) — the kit PREDICATE convention has no hyphen. A no-op for
    every role that has none, so this changes nothing for an already-accepted input."""
    return role.replace("-", "")


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


# Any line-break convention: a document handed over as a string may use CRLF
# or a bare CR, and a bare-CR one would otherwise be ONE line, its nesting lost.
_LINE_BREAK_RE = re.compile(r"\r\n?|\n")


def _split_sbn_lines(text: str) -> List[Tuple[str, int, str]]:
    """Pass 1: strip comments (a PMB ``%%%``-prefixed generation-command header is just
    another ``%...`` comment under this rule) and blank lines. Returns ``(content,
    lineno, leading)`` triples, ``leading`` the RAW leading-whitespace substring —
    whether it means TAB-only nesting depth or is pure cosmetic column alignment
    depends on which of :func:`parse_sbn`'s two dialects the document uses (decided by
    :func:`_uses_connector_dialect` once the whole document has been split), so it is
    NOT validated here."""
    out: List[Tuple[str, int, str]] = []
    for lineno, raw in enumerate(_LINE_BREAK_RE.split(text), start=1):
        line = raw.split("%", 1)[0]
        if not line.strip():
            continue
        no_lead = line.lstrip(" \t")
        leading = line[:len(line) - len(no_lead)]
        out.append((no_lead.strip(), lineno, leading))
    if not out:
        raise SBNSyntaxError("parse_sbn: empty input (no content lines)")
    return out


def _require_tab_indentation(lines: List[Tuple[str, int, str]]) -> None:
    """The indentation dialect's own rule (see the module docstring): leading
    whitespace is nesting depth and must be TAB-only. Raises on the first line that
    isn't — unchanged from before the connector dialect existed."""
    for _, lineno, leading in lines:
        if " " in leading:
            raise SBNSyntaxError(
                f"parse_sbn: line {lineno} is indented with a space character; this "
                f"SBN subset requires TAB-only indentation")


def _uses_connector_dialect(lines: List[Tuple[str, int, str]]) -> bool:
    """True iff any box-operator line carries a trailing CONNECTOR token (``<N`` /
    ``>N``) — decides which of :func:`parse_sbn`'s two dialects (see the module
    docstring's "Dialect selection") to read the WHOLE document in. None of the
    dialect-1 fixtures in ``tests/test_drt.py`` contain one, so they always resolve
    False here, keeping their parse behaviour exactly as before."""
    for content, _, _ in lines:
        parts = content.split()
        if (parts and _ALLCAPS_RE.fullmatch(parts[0])
                and len(parts) == 2 and _CONNECTOR_RE.fullmatch(parts[1])):
            return True
    return False


@dataclass
class _SBNLine:
    lineno: int
    depth: int
    index: int
    kind: str                       # "sense" | "negation"
    predicate: str = ""             # sanitized predicate name, kind == "sense" only
    role_targets: tuple = ()        # tuple of (role, raw_target) pairs


def parse_sbn(text: str) -> Tuple[DRS, SBNMapping]:
    """Parse ``text`` into a ``(DRS, SBNMapping)`` pair, in whichever of the module
    docstring's two documented SBN dialects ``text`` turns out to use (decided by
    :func:`_uses_connector_dialect`). Raises :class:`SBNSyntaxError` on malformed
    input or on any construct outside the chosen dialect's documented subset (naming
    it explicitly)."""
    raw_lines = _split_sbn_lines(text)
    if _uses_connector_dialect(raw_lines):
        return _parse_sbn_connector(raw_lines)
    _require_tab_indentation(raw_lines)
    return _parse_sbn_classic(raw_lines)


def _parse_sbn_classic(raw_lines: List[Tuple[str, int, str]]) -> Tuple[DRS, SBNMapping]:
    """Dialect 1, the indentation dialect (see the module docstring): a bare
    ``NEGATION`` line opens a sub-box via TAB depth. This is ``parse_sbn``'s ORIGINAL
    subset — every input it already accepted parses to the identical DRS it always
    did; the only additions since (widened ``_ROLE_RE``, the bare deictic/integer
    constants below) are no-ops on any input that does not use them."""
    # Pass 2: tokenize each line's own payload (sense/NEGATION keyword + role/target
    # pairs), without resolving offset targets yet — that needs the full index->kind map.
    pred_mapping: Dict[str, str] = {}
    parsed_lines: List[_SBNLine] = []
    for index, (content, lineno, leading) in enumerate(raw_lines, start=1):
        depth = len(leading)
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
                    f"alphanumeric, optionally with one hyphenated segment (e.g. "
                    f"'Agent', 'Theme', 'Co-Theme')")
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
            elif target in _DEICTIC_CONSTANTS or _BARE_INTEGER_RE.fullmatch(target):
                terms.append((role, const_mapping.for_constant(target)))
            else:
                raise SBNSyntaxError(
                    f"parse_sbn: line {pl.lineno}: target {target!r} on role {role!r} "
                    f"is neither a signed line offset (+N / -N), a quoted constant "
                    f'("..."), nor one of this subset\'s bare constant literals '
                    f"(now/speaker/hearer/here, or a bare integer).")
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
                current.conditions.append(Pred(_sbn_role_predicate_name(role), (ref, term)))

    while len(stack) > 1:
        _pop_negation(stack)

    root = _close(stack[0])
    # Offsets are only range/kind-checked above; an offset that crosses a
    # NEGATION box boundary builds a structurally well-formed but
    # ACCESSIBILITY-violating DRS (review-flagged: a referent used outside
    # the box that declares it). Validate before handing it out so a caller
    # never receives a silently invalid tree — the violation surfaces here,
    # named, instead of downstream in drs_to_fol. nodes.DRS.validate raises a
    # plain ValueError (it has no SBN-specific vocabulary of its own); re-raise
    # as SBNSyntaxError so every parse_sbn refusal is uniformly that one type.
    try:
        root.validate()
    except ValueError as e:
        raise SBNSyntaxError(str(e)) from e
    mapping = SBNMapping(predicates=dict(pred_mapping), constants=dict(const_mapping.constant))
    return root, mapping


def _parse_sbn_connector(raw_lines: List[Tuple[str, int, str]]) -> Tuple[DRS, SBNMapping]:
    """Dialect 2, the connector dialect (see the module docstring): PMB's own
    released SBN format. Leading whitespace is ignored throughout; box nesting comes
    from each box-operator line's trailing connector (``<N``) rather than
    indentation, and role-hook indices count CONCEPT lines only."""

    class _Context:
        __slots__ = ("referents", "slots")

        def __init__(self) -> None:
            self.referents: List[str] = []
            # Each slot is either a ("concept", i) placeholder (i indexes `concepts`
            # below) or a ("neg", child_context_index) placeholder — both resolved
            # into actual Conditions only once every concept's offsets and every
            # child context are known (see the two passes below).
            self.slots: List[Tuple[str, int]] = []

    contexts: List[_Context] = [_Context()]     # context 0 = the outermost, implicit context
    neg_lineno: Dict[int, int] = {}              # child context index -> its NEGATION's line
    current = 0
    pred_mapping: Dict[str, str] = {}
    const_mapping = NameMapping()
    concepts: List[dict] = []                    # concept-only registry, in document order

    # Pass 1: one linear scan building the context graph and every concept's raw
    # (unresolved) role targets — an offset may point FORWARD to a concept not yet
    # seen, so resolution is deferred to pass 2 below.
    for content, lineno, _leading in raw_lines:
        head = content.split(None, 1)[0]
        if _ALLCAPS_RE.fullmatch(head):
            rest = content.split()[1:]
            if len(rest) != 1 or not _CONNECTOR_RE.fullmatch(rest[0]):
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: a box-operator line in the connector "
                    f"dialect (see the module docstring) must be followed by exactly "
                    f"one connector (e.g. 'NEGATION <1'), found {rest!r}")
            sign, digits = rest[0][0], rest[0][1:]
            if sign == ">":
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: a forward connector ({rest[0]!r}) is "
                    f"not supported by this SBN subset — only backward ('<N') "
                    f"connectors are.")
            if head != _NEGATION:
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: box-operator {head!r} is not "
                    f"supported by this SBN subset (only NEGATION is) — refusing "
                    f"rather than silently misreading it.")
            n = int(digits)
            new_index = len(contexts)
            target_index = new_index - n
            if n < 1 or target_index < 0:
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: connector '<{n}' refers to context "
                    f"{target_index}, outside the document (contexts "
                    f"0..{new_index - 1} exist at this point)")
            contexts.append(_Context())
            contexts[target_index].slots.append(("neg", new_index))
            neg_lineno[new_index] = lineno
            current = new_index
            continue

        # A concept (sense) line — tokenized quote-aware (unlike the box-operator
        # check above, a concept's role targets may be quoted strings).
        toks = _split_respecting_quotes(content, lineno)
        head, rest = toks[0], toks[1:]
        if len(rest) % 2 != 0:
            raise SBNSyntaxError(
                f"parse_sbn: line {lineno}: role {rest[-1]!r} has no target")
        role_targets = []
        for k in range(0, len(rest), 2):
            role, target = rest[k], rest[k + 1]
            if not _ROLE_RE.fullmatch(role):
                raise SBNSyntaxError(
                    f"parse_sbn: line {lineno}: role {role!r} must be uppercase-initial "
                    f"alphanumeric, optionally with one hyphenated segment (e.g. "
                    f"'Agent', 'Theme', 'Co-Theme')")
            role_targets.append((role, target))
        predicate = pred_mapping.get(head)
        if predicate is None:
            predicate = _sbn_predicate_name(head)
            pred_mapping[head] = predicate
        concept_index = len(concepts)                       # 0-based position
        ref = f"e{concept_index + 1}"
        contexts[current].referents.append(ref)
        contexts[current].slots.append(("concept", concept_index))
        concepts.append({"lineno": lineno, "ref": ref, "predicate": predicate,
                         "role_targets": role_targets, "resolved": None})

    n_concepts = len(concepts)

    # Pass 2: resolve every role-hook target now that each concept's CONCEPT-ONLY
    # position (1-based, box-operator lines excluded — see the module docstring) is
    # known.
    for i, c in enumerate(concepts, start=1):
        resolved_terms = []
        for role, target in c["role_targets"]:
            m = _OFFSET_RE.fullmatch(target)
            if m:
                sign, digits = m.groups()
                delta = int(digits) if sign == "+" else -int(digits)
                target_index = i + delta
                if target_index < 1 or target_index > n_concepts:
                    raise SBNSyntaxError(
                        f"parse_sbn: line {c['lineno']}: offset {target!r} on role "
                        f"{role!r} points to concept index {target_index}, outside "
                        f"the document ({n_concepts} concept(s))")
                resolved_terms.append((role, concepts[target_index - 1]["ref"]))
            elif target.startswith('"') and target.endswith('"') and len(target) >= 2:
                raw_const = target[1:-1].lower()
                resolved_terms.append((role, const_mapping.for_constant(raw_const)))
            elif target in _DEICTIC_CONSTANTS or _BARE_INTEGER_RE.fullmatch(target):
                resolved_terms.append((role, const_mapping.for_constant(target)))
            elif _CONNECTOR_RE.fullmatch(target):
                raise SBNSyntaxError(
                    f"parse_sbn: line {c['lineno']}: role {role!r}'s target "
                    f"{target!r} is a context/box reference (an embedded-clause or "
                    f"propositional-attitude argument) — this SBN subset does not "
                    f"support box-valued role targets.")
            else:
                raise SBNSyntaxError(
                    f"parse_sbn: line {c['lineno']}: target {target!r} on role "
                    f"{role!r} is neither a signed concept offset (+N / -N), a "
                    f'quoted constant ("..."), nor one of this subset\'s bare '
                    f"constant literals (now/speaker/hearer/here, or a bare integer).")
        c["resolved"] = resolved_terms

    # Pass 3: close every context bottom-up. A "neg" slot always names a context
    # with a STRICTLY GREATER index than its own (target_index < new_index above),
    # so resolving from the highest index down guarantees a child is already closed
    # by the time its parent needs it.
    closed: Dict[int, DRS] = {}
    for k in range(len(contexts) - 1, -1, -1):
        conditions: List[Condition] = []
        for kind, idx in contexts[k].slots:
            if kind == "concept":
                c = concepts[idx]
                conditions.append(Pred(c["predicate"], (c["ref"],)))
                for role, term in c["resolved"]:
                    conditions.append(Pred(_sbn_role_predicate_name(role), (c["ref"], term)))
            else:                                            # "neg"
                conditions.append(Neg(closed[idx]))
        if k != 0 and not contexts[k].referents and not conditions:
            raise SBNSyntaxError(
                f"parse_sbn: line {neg_lineno[k]}: NEGATION introduces an empty "
                f"context — every NEGATION in this subset must be followed by at "
                f"least one concept before the next box-operator or the end of the "
                f"document")
        closed[k] = DRS(tuple(contexts[k].referents), tuple(conditions))

    root = closed[0]
    # See the identical comment in _parse_sbn_classic above: validated here rather
    # than left for drs_to_fol to discover downstream, and re-raised as
    # SBNSyntaxError so every parse_sbn refusal is uniformly that one type.
    try:
        root.validate()
    except ValueError as e:
        raise SBNSyntaxError(str(e)) from e
    mapping = SBNMapping(predicates=dict(pred_mapping), constants=dict(const_mapping.constant))
    return root, mapping
