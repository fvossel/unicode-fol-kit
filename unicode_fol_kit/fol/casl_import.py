r"""CASL text parsing for classical FOL and many-sorted FOL (MSFOL) — the
importer half of the export/import pair completed by
:mod:`unicode_fol_kit.fol.casl_export`.

:func:`parse_casl_spec` turns ``spec <NAME> = ... end`` CASL text back into a
:class:`CaslSpec` (a declared :class:`~unicode_fol_kit.fol.signature.Signature`
plus the axiom/conjecture ASTs) — a hand-rolled recursive-descent parser, not
a Lark grammar, since this module owns no ``.lark`` file and is scoped to
exactly the CASL fragment :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
emits (plus a small, explicitly bounded tolerant superset — see "Scope"
below), not general CASL. Anything outside that fragment is refused loudly
with :class:`CaslImportError` naming the offending construct and the line it
was found on — never silently dropped or mistranslated, the same honesty
convention :mod:`~unicode_fol_kit.fol.casl_export`'s own docstring states for
the export direction.

Scope: exactly ``to_casl_spec``'s emission, plus a bounded tolerant superset
--------------------------------------------------------------------------
SUPPORTED (byte-for-byte what :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
emits, plus the listed tolerances):

* One flat ``spec <NAME> = <items> end`` block. ``end`` is OPTIONAL (bare
  end-of-input also terminates the item list — CASL's own basic-spec grammar
  makes the trailing ``end`` optional; this parser follows that rather than
  being stricter than CASL itself).
* ``sort``/``sorts`` (singular and plural both accepted as synonyms),
  comma-separated sort names.
* ``op``/``ops`` and ``pred``/``preds`` (singular and plural both accepted),
  semicolon-separated entries. An operation entry is ``name : S1 * … -> R``
  (a function, arity = number of argument sorts) or a bare ``name : S`` (a
  0-ary operation — see "0-ary operations import as Constant" below). A
  predicate entry is ``name : S1 * … * Sn`` or ``name : ()`` for 0-ary.
* Formulas: ``not``, ``/\``, ``\/``, ``=>``, ``<=>``, ``=``, ``forall``/
  ``exists`` with ``x : Sort . <body>``, parentheses, nested quantifiers.
  Precedence (tolerant extension: ``to_casl_spec`` itself always emits full
  parenthesisation, so nothing in ``to_casl_spec`` output actually exercises
  precedence, but hand-written or other tools' CASL text might): ``not`` >
  ``/\`` (left-assoc) > ``\/`` (left-assoc) > ``=>`` (right-assoc) > ``<=>``
  (left-assoc chain) — matching ``to_casl_spec``'s own documented reading
  wherever both are defined; verified directly against every golden case in
  ``tests/test_casl_export.py``.
* Multiple variables per quantifier, one shared sort: ``forall x, y : S .
  phi`` desugars to nested same-type/same-sort quantifiers, innermost
  wrapping the body (``forall x : S . forall y : S . phi``) — a tolerant
  extension beyond ``to_casl_spec``, which only ever emits one variable per
  quantifier, but a direct, unambiguous reading of CASL's own VAR-DECL
  grammar (a comma-separated variable list sharing one sort).
* ``%%`` line comments and the ``%implied`` conjecture annotation, both
  anywhere whitespace-flexible; arbitrary whitespace/newlines everywhere.

REFUSED with :class:`CaslImportError` (a specific line number and construct
name in every message — never silently accepted as if it meant something
narrower): partial function arrows (``->?``), subsorting (``S < T``), free/
generated types (``free type``/``generated type``/bare ``type``/``types``
items), structured-specification constructs inside the one spec body
(``then``, ``view``, ``given``, ``arch``, ``unit``, …), and operation/
predicate attributes (``, assoc``, ``, comm``, …). None of these can ever
appear in ``to_casl_spec`` output, so refusing them costs nothing against the
round-trip contract below and keeps this parser from silently accepting CASL
it cannot faithfully turn back into a kit AST.

0-ary operations import as :class:`~unicode_fol_kit.fol.nodes.Constant`, never
:class:`~unicode_fol_kit.fol.nodes.SortedConstant` — an inherent, documented
information loss
----------------------------------------------------------------------------
``to_casl_spec`` renders a 0-ary operation's ``ops`` entry as a bare
``name : Sort`` — INDISTINGUISHABLE, by design, from how it would render if
that name were instead a 0-ary :class:`~unicode_fol_kit.fol.nodes.Function`
(see :func:`~unicode_fol_kit.fol.casl_export._render_op_type`'s own
docstring: "indistinguishable in shape from a constant's own type"). And
every TERM reference to that name — whether the original kit AST built it as
a plain (unsorted) :class:`Constant`, an explicitly-sorted
:class:`SortedConstant`, or (in principle) a 0-ary
:class:`~unicode_fol_kit.fol.nodes.Function` — renders as the exact same bare
identifier (:func:`~unicode_fol_kit.fol.casl_export._render_term`). So CASL
text carries no information distinguishing any of these three kit-AST shapes
for a 0-ary symbol: the ``ops`` declaration only ever states the RESOLVED
sort (which may have been inferred purely through union-find propagation
from some OTHER axiom entirely, with no explicit annotation anywhere near
this occurrence — see ``casl_export``'s own worked example,
``test_golden_person_animal_msfol_worked_example``, where an unsorted
``Constant("socrates")`` gets ``ops socrates : Person`` purely from
appearing in the same predicate argument position as a ``Person``-sorted
variable in a DIFFERENT axiom).

Given that, this parser makes ONE deliberate, uniform choice: every bare
0-ary term reference resolves to a plain :class:`Constant` — never
:class:`SortedConstant`, never a 0-ary :class:`Function`. This is not a
guess dressed up as a default; it is the only choice that does not invent
information the text does not carry, and it is exactly what makes the
round-trip contract below hold for ``to_casl_spec``'s own worked example
(where the original constant WAS a bare, unsorted ``Constant`` despite its
inferred CASL sort not equal ``default_sort``). A caller whose original
formulas used :class:`SortedConstant` throughout will NOT get
byte-identical structural equality back through
``parse_casl_spec(to_casl_spec(f))`` — this is the one place the export/
import pair is lossy, and it is lossy on the EXPORT side (the CASL text
itself has already thrown the distinction away by the time this parser ever
sees it), not something this parser could recover with a cleverer grammar.

The round-trip contract
------------------------
For a list ``fs`` of the kit's own classical/many-sorted formulas built with
plain :class:`~unicode_fol_kit.fol.nodes.Constant` (never
:class:`SortedConstant`) and without :class:`~unicode_fol_kit.fol.nodes.Xor`
(see below)::

    parse_casl_spec(to_casl_spec(fs, conjectures=cjs)).axioms == tuple(fs)
    parse_casl_spec(to_casl_spec(fs, conjectures=cjs)).conjectures == tuple(cjs)

holds by structural equality (the kit's node dataclasses are frozen with
value equality). ``tests/test_casl_import.py`` hand-verifies this over a
representative formula set covering both quantifier kinds, equality, every
supported connective, function terms, 0-ary predicates/operations, and
``%implied``.

:class:`~unicode_fol_kit.fol.nodes.Xor` is EXCLUDED from that contract for a
reason internal to the exporter, not this module: ``to_casl_spec`` has no
CASL operator for XOR and expands it to the classically-equivalent
``not (<a> <=> <b>)`` (see ``casl_export``'s own docstring). Parsing that
text back necessarily yields ``Not(Iff(a, b))``, not ``Xor(a, b)`` — a
different (semantically equivalent, structurally distinct) tree. This parser
is faithful to the TEXT it is given: ``not (P <=> Q)`` always means
``Not(Iff(P, Q))``, exactly like every other ``not``/``<=>`` occurrence,
never a special-cased reconstruction of ``Xor`` that no other tool
generating CASL text would expect.

A THIRD disclosed exception, exactly analogous to the 0-ary
Constant-vs-SortedConstant case above (adversarial review, Tier 3): a
:class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` whose explicit ``sort``
EQUALS ``default_sort`` renders the very same CASL text as a plain
:class:`~unicode_fol_kit.fol.nodes.Quantifier` (both emit
``forall x : <default_sort> . <body>``), so the wire format has already
thrown the node-type distinction away and this parser's reconstruction rule
(``sort == default_sort`` → plain ``Quantifier``) necessarily collapses it.
``∀x:Thing P(x)`` therefore round-trips to the semantically identical but
structurally distinct ``∀x P(x)`` under the default ``default_sort="Thing"``
— pinned by ``test_round_trip_sorted_quantifier_at_default_sort_collapses``.

Reserved words
---------------
Every identifier this parser reads into a declaration OR a reference
(sort/predicate/operation/variable/spec name) is checked against the same
CASL keyword list :mod:`~unicode_fol_kit.fol.casl_export` refuses on export
(``_CASL_KEYWORDS`` there). This is an intentional small independent literal
copy, not an import of that module's private name — the same reasoning
:mod:`unicode_fol_kit.fol.signature`'s own docstring gives for its identical
choice about ``_BUILTIN_PREDS``/``_BUILTIN_FUNCS``: importing a leading-
underscore name across modules would make this parser depend on
``casl_export``'s internals staying stable, when the two lists just happen
to need to agree by CONTENT, not by object identity.
"""

from collections import namedtuple
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple
import re

from .nodes import (
    Node, Variable, Constant, Function,
    Atom, Not, And, Or, Implies, Iff,
    Quantifier, SortedQuantifier,
)
from .signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl

__all__ = ["parse_casl_spec", "CaslSpec", "CaslImportError"]


class CaslImportError(ValueError):
    """A CASL text construct is outside :func:`parse_casl_spec`'s supported
    grammar, or the text is otherwise malformed.

    Every raise site names the specific construct and where it sits — a
    ``line N:`` prefix for lexical/grammatical refusals, or the axiom/
    conjecture position for the post-parse usage-conformance pass (see
    :func:`_validate_usage` — by then the text positions are gone but the
    formula order is stable). This is the import-side half of the kit's
    "refuse loudly, never silently mistranslate" convention (see
    :mod:`unicode_fol_kit.fol.casl_export`'s module docstring for the same
    principle stated for export).
    """


@dataclass(frozen=True)
class CaslSpec:
    """One parsed CASL ``spec`` block: its name, declared vocabulary, and
    formulas, split into axioms and ``%implied`` conjectures.

    ``signature`` is built directly from the ``sorts``/``ops``/``preds``
    declarations actually present in the text (never re-inferred from the
    formula ASTs the way :meth:`~unicode_fol_kit.fol.signature.Signature.from_formulas`
    would) — CASL text already states arities and argument/result sorts
    explicitly, so re-inferring would either duplicate that information or
    risk silently disagreeing with it.
    """

    name: str
    signature: Signature
    axioms: Tuple[Node, ...]
    conjectures: Tuple[Node, ...]

    def to_dict(self) -> dict:
        """JSON-compatible dict: ``name``, ``signature`` (via
        :meth:`~unicode_fol_kit.fol.signature.Signature.to_dict`), and
        ``axioms``/``conjectures`` as lists of node dicts (via each node's
        own ``to_dict``)."""
        return {
            "name": self.name,
            "signature": self.signature.to_dict(),
            "axioms": [a.to_dict() for a in self.axioms],
            "conjectures": [c.to_dict() for c in self.conjectures],
        }


# =============================================================================
# Reserved words (see module docstring's "Reserved words" section)
# =============================================================================

_CASL_KEYWORDS = frozenset({
    "and", "arch", "as", "assoc", "axiom", "axioms", "closed", "comm", "def",
    "else", "end", "exists", "false", "fit", "forall", "free", "from",
    "generated", "get", "given", "hide", "idem", "if", "in", "lambda",
    "library", "local", "logic", "not", "op", "ops", "pred", "preds",
    "result", "reveal", "sort", "sorts", "spec", "then", "to", "true",
    "type", "types", "unit", "units", "var", "vars", "version", "view",
    "when", "with", "within",
})

#: Item-position keywords naming a refused structuring construct: any of
#: these appearing where a sort/op/pred declaration or an axiom is expected
#: means the input is a STRUCTURED spec (or a library-level item), which is
#: out of scope — see the module docstring's "Scope" section.
_STRUCTURING_KEYWORDS = frozenset({
    "then", "view", "given", "arch", "unit", "units", "hide", "reveal",
    "local", "within", "closed", "library", "logic", "and", "fit",
})

#: Item-position keywords naming a refused free/generated-type construct.
_FREE_TYPE_KEYWORDS = frozenset({"free", "type", "types", "generated"})


# =============================================================================
# Tokenizer
# =============================================================================

_Token = namedtuple("_Token", "kind value line")

# Order matters: alternation tries each pattern in LISTED order at a given
# position (Python `re` alternation is first-match, not longest-match), so
# every prefix relationship below is resolved by listing the LONGER/more
# specific pattern first: ARROW_PARTIAL before ARROW (both start with '->'),
# IFF before LT (both start with '<'), IMPLIES before EQ (both start with
# '='), COMMENT before PERCENT_WORD (both start with '%').
_TOKEN_SPEC = [
    ("COMMENT", r"%%[^\n]*"),
    ("PERCENT_WORD", r"%\S*"),
    ("NEWLINE", r"\n"),
    ("WS", r"[ \t\r]+"),
    ("ARROW_PARTIAL", r"->\?"),
    ("ARROW", r"->"),
    ("IFF", r"<=>"),
    ("IMPLIES", r"=>"),
    ("AND", r"/\\"),
    ("OR", r"\\/"),
    ("LPAREN", r"\("),
    ("RPAREN", r"\)"),
    ("COMMA", r","),
    ("SEMI", r";"),
    ("COLON", r":"),
    ("DOT", r"\."),
    ("STAR", r"\*"),
    ("LT", r"<"),
    ("EQ", r"="),
    ("IDENT", r"[A-Za-z][A-Za-z0-9_]*"),
]
_MASTER_RE = re.compile("|".join(f"(?P<{name}>{pat})" for name, pat in _TOKEN_SPEC))


class _Lexer:
    """Scans ``text`` into tokens ON DEMAND, buffering only as much
    lookahead as :class:`_Parser` actually asks for (via :meth:`peek`/
    :meth:`next`), rather than tokenizing the whole input up front.

    This matters for refusal quality, not just laziness for its own sake:
    an out-of-scope construct this parser means to refuse by NAME (e.g. a
    ``free type ... ::= zero | succ(Nat)`` declaration) may contain
    characters this grammar has no token for at all (``|``) FURTHER ALONG
    in the same construct. Eager whole-text tokenization would hit that
    unrecognized character first and raise a generic "unrecognized
    character" error before the parser ever gets a chance to recognize
    ``free`` at item-position and give its specific, named refusal. Lazy
    scanning means the parser sees (and can react to) the ``free`` token
    the moment it asks for the next one, without this lexer ever having
    attempted to scan past it into the unsupported tail of the construct.

    Comments (``%%...`` to end of line) and whitespace/newlines are
    consumed silently while scanning — callers never see them as tokens. A
    bare ``%word`` other than ``%implied`` is refused immediately (a CASL
    annotation this parser does not support, e.g. ``%(label)%`` or
    ``%def`` — none of these are ever emitted by ``to_casl_spec``).
    """

    def __init__(self, text: str):
        self._text = text
        self._pos = 0
        self._n = len(text)
        self._line = 1
        self._buffer: List[_Token] = []

    def _scan_one(self) -> _Token:
        while self._pos < self._n:
            m = _MASTER_RE.match(self._text, self._pos)
            if not m:
                raise CaslImportError(
                    f"line {self._line}: unrecognized character "
                    f"{self._text[self._pos]!r} in CASL text"
                )
            kind, value = m.lastgroup, m.group()
            if kind == "NEWLINE":
                self._line += 1
                self._pos = m.end()
                continue
            if kind in ("WS", "COMMENT"):
                self._pos = m.end()
                continue
            if kind == "PERCENT_WORD":
                if value != "%implied":
                    raise CaslImportError(
                        f"line {self._line}: unsupported CASL annotation "
                        f"{value!r} — only '%implied' (conjecture marker) "
                        "and '%%' line comments are supported"
                    )
                kind = "IMPLIED"
            self._pos = m.end()
            return _Token(kind, value, self._line)
        return _Token("EOF", "", self._line)

    def peek(self, ahead: int = 0) -> _Token:
        """Return the token ``ahead`` positions past the cursor without
        consuming it (``ahead=0`` is the next token to be consumed)."""
        while len(self._buffer) <= ahead:
            self._buffer.append(self._scan_one())
        return self._buffer[ahead]

    def next(self) -> _Token:
        """Consume and return the next token."""
        self.peek(0)
        return self._buffer.pop(0)


# =============================================================================
# Recursive-descent parser
# =============================================================================

class _Parser:
    """Consumes a token list once, left to right, building spec-level
    declarations and formula ASTs. See the module docstring's "Scope"
    section for the exact grammar and the refusal classes."""

    def __init__(self, lexer: "_Lexer", default_sort: str):
        self._lexer = lexer
        self.default_sort = default_sort
        self.sorts: set = set()
        self.predicates: Dict[str, PredicateDecl] = {}
        self.functions: Dict[str, FunctionDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}
        self.axioms: List[Node] = []
        self.conjectures: List[Node] = []

    # -- token helpers --------------------------------------------------

    def _cur(self) -> _Token:
        return self._lexer.peek(0)

    def _at(self, kind: str) -> bool:
        return self._cur().kind == kind

    def _at_ident(self, *values: str) -> bool:
        t = self._cur()
        return t.kind == "IDENT" and t.value in values

    def _advance(self) -> _Token:
        return self._lexer.next()

    def _expect(self, kind: str, what: str) -> _Token:
        if not self._at(kind):
            self._error(f"expected {what}, found {self._describe(self._cur())}")
        return self._advance()

    def _expect_ident(self, *values: str) -> _Token:
        if not self._at_ident(*values):
            self._error(
                f"expected one of {sorted(values)!r}, found "
                f"{self._describe(self._cur())}"
            )
        return self._advance()

    @staticmethod
    def _describe(t: _Token) -> str:
        return f"{t.kind} {t.value!r}" if t.value else t.kind

    def _error(self, msg: str):
        raise CaslImportError(f"line {self._cur().line}: {msg}")

    def _check_reserved(self, name: str, kind: str, line: int) -> None:
        if name in _CASL_KEYWORDS:
            raise CaslImportError(
                f"line {line}: {kind} name '{name}' collides with the "
                f"reserved CASL keyword '{name}'"
            )

    # -- top level --------------------------------------------------------

    def parse(self) -> str:
        """Parse ``spec NAME = <items> end`` (``end`` optional); return NAME."""
        self._expect_ident("spec")
        name_tok = self._expect("IDENT", "spec name")
        self._check_reserved(name_tok.value, "spec name", name_tok.line)
        self._expect("EQ", "'=' after spec name")
        while True:
            if self._at("EOF"):
                break
            if self._at_ident("end"):
                self._advance()
                break
            if self._at("DOT"):
                self._parse_axiom_line()
                continue
            if self._at_ident("sort", "sorts"):
                self._parse_sort_decl()
                continue
            if self._at_ident("op", "ops"):
                self._parse_op_decl()
                continue
            if self._at_ident("pred", "preds"):
                self._parse_pred_decl()
                continue
            if self._at_ident(*_FREE_TYPE_KEYWORDS):
                self._error(
                    f"free/generated type declaration ({self._cur().value!r}) "
                    "is outside parse_casl_spec's supported grammar"
                )
            if self._at_ident(*_STRUCTURING_KEYWORDS):
                self._error(
                    f"structured-specification construct "
                    f"{self._cur().value!r} is outside parse_casl_spec's "
                    "supported grammar — only a single flat "
                    "'spec NAME = ... end' block is supported"
                )
            if self._at("IDENT"):
                nxt = self._lexer.peek(1)
                if nxt.kind == "IDENT" and nxt.value == "then":
                    self._error(
                        "structured-specification construct 'then' (spec "
                        f"extension, e.g. 'spec X = {self._cur().value} "
                        "then ...') is outside parse_casl_spec's supported "
                        "grammar — only a single flat 'spec NAME = ... end' "
                        "block is supported (see unicode_fol_kit.hets.dol "
                        "for DOL library 'extends' emission)"
                    )
            self._error(
                f"unexpected {self._describe(self._cur())} where a sort/op/"
                "pred declaration or an axiom ('.') was expected"
            )
        if not self._at("EOF"):
            self._error("unexpected content after 'end'")
        return name_tok.value

    # -- declarations -------------------------------------------------------

    def _check_no_attributes(self) -> None:
        """Refuse a trailing ``, assoc`` / ``, comm`` / … attribute list —
        the only thing a ',' can legally introduce after an op/pred type in
        this grammar."""
        if self._at("COMMA"):
            self._error(
                "operation/predicate attributes (e.g. ', assoc', ', comm') "
                "are outside parse_casl_spec's supported grammar"
            )

    def _parse_sort_decl(self) -> None:
        self._advance()  # 'sort' | 'sorts'
        while True:
            tok = self._expect("IDENT", "sort name")
            self._check_reserved(tok.value, "sort", tok.line)
            if self._at("LT"):
                self._error(
                    f"subsorting ('{tok.value} < ...') is outside "
                    "parse_casl_spec's supported grammar"
                )
            self.sorts.add(tok.value)
            if self._at("COMMA"):
                self._advance()
                continue
            break

    def _parse_op_decl(self) -> None:
        self._advance()  # 'op' | 'ops'
        while True:
            name_tok = self._expect("IDENT", "operation name")
            name = name_tok.value
            self._check_reserved(name, "operation", name_tok.line)
            self._expect("COLON", "':' after operation name")
            arg_sorts, result_sort = self._parse_op_type()
            self._check_no_attributes()
            if arg_sorts:
                self._declare_function(name, arg_sorts, result_sort, name_tok.line)
            else:
                self._declare_constant(name, result_sort, name_tok.line)
            if self._at("SEMI"):
                self._advance()
                continue
            break

    def _parse_op_type(self) -> Tuple[List[str], str]:
        if self._at("ARROW_PARTIAL"):
            self._error(
                "partial function arrow ('->?') is outside parse_casl_spec's "
                "supported grammar"
            )
        first = self._expect("IDENT", "sort name")
        self._check_reserved(first.value, "sort", first.line)
        sorts = [first.value]
        while self._at("STAR"):
            self._advance()
            tok = self._expect("IDENT", "sort name")
            self._check_reserved(tok.value, "sort", tok.line)
            sorts.append(tok.value)
        if self._at("ARROW_PARTIAL"):
            self._error(
                "partial function arrow ('->?') is outside parse_casl_spec's "
                "supported grammar"
            )
        if self._at("ARROW"):
            self._advance()
            result = self._expect("IDENT", "result sort name")
            self._check_reserved(result.value, "sort", result.line)
            for s in sorts:
                self.sorts.add(s)
            self.sorts.add(result.value)
            return sorts, result.value
        if len(sorts) != 1:
            self._error(
                "expected '->' after a multi-sort argument list in an "
                "operation type"
            )
        self.sorts.add(sorts[0])
        return [], sorts[0]

    def _parse_pred_decl(self) -> None:
        self._advance()  # 'pred' | 'preds'
        while True:
            name_tok = self._expect("IDENT", "predicate name")
            name = name_tok.value
            self._check_reserved(name, "predicate", name_tok.line)
            self._expect("COLON", "':' after predicate name")
            arg_sorts = self._parse_pred_type()
            self._check_no_attributes()
            self._declare_predicate(name, arg_sorts, name_tok.line)
            if self._at("SEMI"):
                self._advance()
                continue
            break

    def _parse_pred_type(self) -> List[str]:
        if self._at("LPAREN"):
            self._advance()
            self._expect("RPAREN", "')' closing a 0-ary predicate type")
            return []
        tok = self._expect("IDENT", "sort name")
        self._check_reserved(tok.value, "sort", tok.line)
        sorts = [tok.value]
        self.sorts.add(tok.value)
        while self._at("STAR"):
            self._advance()
            tok = self._expect("IDENT", "sort name")
            self._check_reserved(tok.value, "sort", tok.line)
            sorts.append(tok.value)
            self.sorts.add(tok.value)
        return sorts

    def _declare_function(self, name: str, arg_sorts: List[str],
                          result_sort: str, line: int) -> None:
        if name in self.constants:
            self._error(
                f"'{name}' is declared both as a 0-ary operation and as a "
                "function with arguments — a signature declares at most "
                "one meaning per operation name"
            )
        decl = FunctionDecl(name, len(arg_sorts), tuple(arg_sorts), result_sort)
        if name in self.functions and self.functions[name] != decl:
            self._error(f"operation '{name}' redeclared with a conflicting type")
        self.functions[name] = decl

    def _declare_constant(self, name: str, sort: str, line: int) -> None:
        if name in self.functions:
            self._error(
                f"'{name}' is declared both as a 0-ary operation and as a "
                "function with arguments — a signature declares at most "
                "one meaning per operation name"
            )
        decl = ConstantDecl(name, sort)
        if name in self.constants and self.constants[name] != decl:
            self._error(f"operation '{name}' redeclared with a conflicting sort")
        self.constants[name] = decl

    def _declare_predicate(self, name: str, arg_sorts: List[str], line: int) -> None:
        decl = PredicateDecl(name, len(arg_sorts), tuple(arg_sorts) if arg_sorts else None)
        if name in self.predicates and self.predicates[name] != decl:
            self._error(f"predicate '{name}' redeclared with a conflicting type")
        self.predicates[name] = decl

    # -- axioms / formulas ----------------------------------------------

    def _parse_axiom_line(self) -> None:
        self._advance()  # leading '.'
        formula = self._parse_formula(frozenset())
        if self._at("IMPLIED"):
            self._advance()
            self.conjectures.append(formula)
        else:
            self.axioms.append(formula)

    def _parse_formula(self, env: frozenset) -> Node:
        return self._parse_iff(env)

    def _parse_iff(self, env: frozenset) -> Node:
        left = self._parse_implies(env)
        while self._at("IFF"):
            self._advance()
            right = self._parse_implies(env)
            left = Iff(left, right)
        return left

    def _parse_implies(self, env: frozenset) -> Node:
        left = self._parse_or(env)
        if self._at("IMPLIES"):
            self._advance()
            right = self._parse_implies(env)  # right-associative
            return Implies(left, right)
        return left

    def _parse_or(self, env: frozenset) -> Node:
        left = self._parse_and(env)
        while self._at("OR"):
            self._advance()
            right = self._parse_and(env)
            left = Or(left, right)
        return left

    def _parse_and(self, env: frozenset) -> Node:
        left = self._parse_unary(env)
        while self._at("AND"):
            self._advance()
            right = self._parse_unary(env)
            left = And(left, right)
        return left

    def _parse_unary(self, env: frozenset) -> Node:
        if self._at_ident("not"):
            self._advance()
            return Not(self._parse_unary(env))
        return self._parse_primary(env)

    def _parse_primary(self, env: frozenset) -> Node:
        if self._at_ident("forall", "exists"):
            return self._parse_quantifier(env)
        if self._at("LPAREN"):
            self._advance()
            f = self._parse_formula(env)
            self._expect("RPAREN", "')'")
            return f
        return self._parse_atom_or_equality(env)

    def _parse_quantifier(self, env: frozenset) -> Node:
        kw = self._advance()  # 'forall' | 'exists'
        qtype = "∀" if kw.value == "forall" else "∃"
        names = []
        tok = self._expect("IDENT", "quantified variable name")
        self._check_reserved(tok.value, "variable", tok.line)
        names.append(tok.value)
        while self._at("COMMA"):
            self._advance()
            tok = self._expect("IDENT", "quantified variable name")
            self._check_reserved(tok.value, "variable", tok.line)
            names.append(tok.value)
        self._expect("COLON", "':' after quantified variable(s)")
        sort_tok = self._expect("IDENT", "sort name")
        sort = sort_tok.value
        self._check_reserved(sort, "sort", sort_tok.line)
        self.sorts.add(sort)
        self._expect("DOT", "'.' after the quantifier's sort")
        new_env = env | frozenset(names)
        body = self._parse_formula(new_env)
        result = body
        for name in reversed(names):
            var = Variable(name)
            if sort == self.default_sort:
                result = Quantifier(qtype, var, result)
            else:
                result = SortedQuantifier(qtype, var, sort, result)
        return result

    def _parse_atom_or_equality(self, env: frozenset) -> Node:
        name_tok = self._expect(
            "IDENT", "an atom, predicate application, or term")
        name = name_tok.value
        self._check_reserved(name, "predicate/operation", name_tok.line)
        args = self._parse_optional_arg_list(env)
        if self._at("EQ"):
            left_term = self._resolve_term(name, args, env)
            self._advance()  # '='
            right_term = self._parse_term(env)
            return Atom("=", (left_term, right_term))
        return Atom(name, tuple(args))

    def _parse_term(self, env: frozenset) -> Node:
        tok = self._expect("IDENT", "a term (variable, constant, or function)")
        name = tok.value
        self._check_reserved(name, "predicate/operation", tok.line)
        args = self._parse_optional_arg_list(env)
        return self._resolve_term(name, args, env)

    def _parse_optional_arg_list(self, env: frozenset) -> List[Node]:
        if not self._at("LPAREN"):
            return []
        self._advance()
        args = [self._parse_term(env)]
        while self._at("COMMA"):
            self._advance()
            args.append(self._parse_term(env))
        self._expect("RPAREN", "')' closing an argument list")
        return args

    @staticmethod
    def _resolve_term(name: str, args: List[Node], env: frozenset) -> Node:
        """A bare designator resolves to a bound :class:`Variable` (if
        ``name`` is in scope), else a :class:`Constant`; an applied one
        (``args`` non-empty) always resolves to a :class:`Function` — see
        the module docstring's "0-ary operations import as Constant"
        section for why a bare reference never becomes a
        :class:`~unicode_fol_kit.fol.nodes.SortedConstant` or a 0-ary
        :class:`Function`."""
        if args:
            return Function(name, tuple(args))
        if name in env:
            return Variable(name)
        return Constant(name)


# =============================================================================
# Public API
# =============================================================================

def _validate_usage(parser: "_Parser") -> None:
    """Post-parse conformance pass: every symbol the formulas USE must have
    been DECLARED, with matching arity.

    The recursive-descent parser builds Atom/Function/Constant nodes purely
    from the tokens it encounters; without this pass a symbol used but never
    declared silently produced a :class:`CaslSpec` whose signature does not
    describe its own axioms, and a declared/used arity mismatch was accepted
    outright (adversarial review, Tier 3) — both violating the module's
    "refuse loudly" contract. Runs after the whole spec is parsed (a
    declaration is in scope for every formula regardless of textual order),
    so errors carry the axiom/conjecture position instead of a line number.
    """
    labeled = (
        [(f"axiom {i + 1}", f) for i, f in enumerate(parser.axioms)]
        + [(f"%implied conjecture {i + 1}", f)
           for i, f in enumerate(parser.conjectures)])
    for label, formula in labeled:
        for node in formula.walk():
            if isinstance(node, Atom) and node.predicate != "=":
                decl = parser.predicates.get(node.predicate)
                if decl is None:
                    raise CaslImportError(
                        f"{label}: predicate '{node.predicate}' is used but "
                        f"never declared (add a 'preds {node.predicate} : "
                        f"...' declaration)")
                if decl.arity != len(node.args):
                    raise CaslImportError(
                        f"{label}: predicate '{node.predicate}' is declared "
                        f"with arity {decl.arity} but used with "
                        f"{len(node.args)} argument(s)")
            elif isinstance(node, Function):
                decl = parser.functions.get(node.name)
                if decl is None:
                    raise CaslImportError(
                        f"{label}: operation '{node.name}' is used but never "
                        f"declared (add an 'ops {node.name} : ...' "
                        f"declaration)")
                if decl.arity != len(node.args):
                    raise CaslImportError(
                        f"{label}: operation '{node.name}' is declared with "
                        f"arity {decl.arity} but used with "
                        f"{len(node.args)} argument(s)")
            elif isinstance(node, Constant):
                if node.name not in parser.constants:
                    raise CaslImportError(
                        f"{label}: constant '{node.name}' is used but never "
                        f"declared (add an 'ops {node.name} : <Sort>' "
                        f"declaration)")


def parse_casl_spec(text: str, *, default_sort: str = "Thing") -> CaslSpec:
    """Parse one CASL ``spec <NAME> = ... end`` block into a :class:`CaslSpec`.

    See the module docstring for the exact grammar supported (a bounded
    tolerant superset of what
    :func:`unicode_fol_kit.fol.casl_export.to_casl_spec` emits), the round-
    trip contract this establishes with that exporter, and the refusal
    classes below.

    Args:
        text: CASL spec text.
        default_sort: the sort a PLAIN (unsorted)
            :class:`~unicode_fol_kit.fol.nodes.Quantifier` is reconstructed
            for — a quantifier declared at exactly this sort in the text
            becomes a plain ``Quantifier``; any other sort becomes a
            :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier`. Must match
            whatever ``default_sort`` the text was originally exported with
            for the round-trip contract to hold.

    Returns:
        A :class:`CaslSpec` carrying the spec's name, its declared
        :class:`~unicode_fol_kit.fol.signature.Signature` (read directly off
        the ``sorts``/``ops``/``preds`` declarations, not re-inferred from
        the formulas), and its axioms/conjectures as kit ASTs.

    Raises:
        CaslImportError: a construct outside the supported grammar (partial
            functions, subsorting, free/generated types, structured-spec
            constructs, operation/predicate attributes, an unrecognized
            token, a malformed op/pred type, a reserved-word identifier, or
            any other parse failure) — always with a line number and the
            offending construct named.
    """
    lexer = _Lexer(text)
    parser = _Parser(lexer, default_sort)
    name = parser.parse()
    _validate_usage(parser)
    signature = Signature(
        predicates=dict(parser.predicates),
        functions=dict(parser.functions),
        constants=dict(parser.constants),
        sorts=frozenset(parser.sorts),
    )
    return CaslSpec(
        name=name,
        signature=signature,
        axioms=tuple(parser.axioms),
        conjectures=tuple(parser.conjectures),
    )
