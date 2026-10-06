"""Prover9 / LADR input: read Prover9-syntax formulas into the AST.

This is the inverse of :meth:`Node.to_prover9`. Prover9's surface syntax differs
from the toolkit's Unicode notation (``all X``/``exists X`` quantifiers, ``-`` for
negation, ``&  |  ->  <->`` connectives, infix comparison predicates), so it gets
its own Lark grammar.

Variables. :meth:`Node.to_prover9` writes under ``set(prolog_style_variables)``, and this
reader reads names by Prover9's own rules (measured on Prover9 2026-8A):

* ``all x`` and ``exists x`` bind the SYMBOL they name, whatever its case. In
  ``all x (man(x) -> mortal(x))`` and in ``all X (man(X) -> mortal(X))`` the three occurrences
  are one :class:`Variable`, for as long as the operand that follows the variable lasts (it
  ends before a ``&``, ``|``, ``->``, ``<->`` or ``<-``). A quantifier over the same spelling
  inside that operand rebinds it. A name that is applied to arguments (``x(a)``) is a
  predicate or a function, not an occurrence of the variable.
* A name that no quantifier binds is a variable or a constant by the convention of the text.
  Under ``set(prolog_style_variables)`` a name that begins with an upper-case letter
  (``A`` to ``Z``; an underscore does not count) is a variable and every other name a
  constant; without that flag a name that begins with ``u`` to ``z`` is a variable.
  :func:`parse_prover9_problem` reads the flag as Prover9 does: the LAST ``set`` or ``clear``
  of ``prolog_style_variables`` in the file decides for every formula of it, a file without
  one reads Prover9's default. :func:`parse_prover9` has no file around the formula and keeps
  ``set(prolog_style_variables)`` (or pass ``prolog_style_variables=False``).
* Variables are compared as written: ``Xa`` and ``XA`` are two variables, and so are ``x``
  and ``X``. The name of a :class:`Variable` is the lower-case of its spelling (the inverse of
  :meth:`Variable.to_prover9`, which upper-cases), and a spelling whose lower-case another
  spelling already has gets a fresh name (``x0``): two spellings are never one variable.
  Constants, predicates and functions keep their case.

A name applied to arguments is a predicate (in formula position) or function (in term
position) and keeps its case; a bare name in FORMULA position is a nullary (propositional)
predicate (Prover9 itself refuses a bare upper-case proposition, which it reads as a variable,
and a bound name used as a formula; this reader is more lenient about the first and refuses
the second). Comparison operators map back to the ``=`` / ``≠`` /
``<`` / ``>`` / ``≤`` / ``≥`` atoms and ``+ - * /`` to the arithmetic functions.

Connectives: ``->``, ``<->`` and the reverse implication ``<-`` (``p <- q`` is ``q -> p``)
bind looser than ``|`` and ``&``. Prover9 reads the three as non-associative: a chain or a mix
of two of them without parentheses (``a <- b <- c``, ``a <- b -> c``) is a syntax error there
(measured), and this reader refuses a ``<-`` in such a chain as well. It still reads
``a -> b -> c`` as ``a -> (b -> c)``, which Prover9 refuses. ``<`` is the comparison only where
no ``-`` follows it directly: ``a <-b`` is a reverse implication, ``a < -b`` the comparison
of ``a`` and ``-b``.

Keywords: ``all`` and ``exists`` are quantifiers only as words of their own, followed by a
variable. ``allowed(a)``, ``exists_in(b)`` and ``allergic(a)`` are atoms, and so is ``all(a)``,
as in Prover9.

Prover9's own constants are read too: ``$T`` and ``$F`` in formula position are the
truth constants, the nullary atoms ``$true`` and ``$false`` (the atoms
:meth:`Node.to_prover9` writes as ``$T`` and ``$F``, so ``parse_prover9(node.to_prover9())
== node`` for them). They are formulas, not terms: ``P($T)`` is refused.

Quoted symbols: a double-quoted symbol is never a variable in Prover9 (LADR stores it
with its quote characters, so the first character it tests is the quote), which is how
:meth:`Node.to_prover9` writes a constant or a proposition whose name begins with an
upper-case letter or an underscore (``P("Gaseous")``, ``"Rain"``). This reader reads
it back as a name that is never a variable: ``"Rain"`` in formula position is the
nullary atom ``Rain``, ``"Gaseous"`` in term position the :class:`Constant`
``Gaseous``, and a quoted name applied to arguments (``"Mother"(a)``) an atom or a
:class:`Function` of that name. Prover9 keeps ``"rain"`` and ``rain`` apart as two
symbols and this reader does not (the AST has one name), so a text that writes the
SAME symbol (the same predicate, function, constant or number, at one arity) both
with and without quotes is refused by name as a :class:`Prover9ParsingError`, rather
than read as one symbol: a file is one text, and the record of what was met is kept
across all its formulas. (``"Rain"`` as a proposition next to ``Rain(x)`` as a
predicate is not that: they are two symbols here too.) Only a quoted name made of
letters, digits and an underscore (``[A-Za-z_][A-Za-z0-9_]*``) is read, because that
is what the writer produces and the only shape :meth:`Node.to_prover9` can write
back, and a quoted NUMERAL (``"2.5"``, ``"-1"``) in term position, which is the
:class:`Number` of that value (the text must be the canonical spelling of the number,
as :meth:`Number.to_prover9` writes it, one per value: ``"2.50"`` and ``"1.0"`` are
refused, because Prover9 keeps them apart from ``"2.5"`` and ``"1"``, which are the same
numbers); any other quoted text
is refused by name as a :class:`Prover9ParsingError`. The file scanner of
:func:`parse_prover9_problem` skips a quoted symbol whole: a ``.`` or a ``%`` inside it
ends no statement and starts no comment.

A term can be written ``-(a, b)``: the function ``-`` of two arguments, which is how
:meth:`Function.to_prover9` writes a binary minus (Prover9 has no infix minus, ``(a - b)``
is a syntax error there; the infix ``a - b`` of this reader's grammar is kept for the
files it has always read). A prefix minus is the function ``-`` of one argument, and binds
as Prover9's does (priority 350, tighter than the comparisons and the sums): ``-(a)``,
``-a`` and ``- f(a)`` are terms, ``-a = b`` is the equation of the terms ``-a`` and ``b``
(Prover9 echoes ``-a = b.``), ``-a + b = c`` is ``(-a) + b = c``, and only a minus in front
of a formula that is not a comparison, or of a parenthesised formula, is a negation
(``-P(a)``, ``-(a = b)``, which Prover9 echoes ``a != b``). A bare ``-1`` is read as the
number minus one, also in front of a comparison (``-1 < x``), although Prover9 reads it as
``-`` applied to the constant ``1``: the writer of this kit writes the number as ``"-1"``.

A text that spells one numeral two ways is refused by name: Prover9 keeps ``01`` and ``1``,
``1.0`` and ``1``, ``2.50`` and ``2.5`` apart as symbols, a :class:`Number` has one text per
value, and the file ``P(01). -P(1).`` (consistent for Prover9) would be read as ``P(1)`` and
``¬P(1)``. Every formula of a file counts for it, as for a symbol written both quoted and bare.
A numeral that stands alone in a text is read as the number it spells.

Depth: the parse tree is transformed with an explicit stack, so a chain of operands or a stack
of negations or quantifiers is read at any depth the parser itself reads. A formula that
still exhausts the interpreter's recursion limit is a :class:`Prover9ParsingError`, never a
bare ``RecursionError``.

A free variable: Prover9 closes each formula of a file universally, so ``P(X)`` there says
``∀X P(X)``. This reader reads the text and does not close it: the variable stays free in the
AST, and the kit's provers read a free variable of a problem as ONE unknown element, the same
in every formula (a parameter). A problem built from such a file therefore asks another
question than Prover9 does for the file; wrap the formula in ``∀`` first when the closure is
what is meant.

Note: :meth:`Node.to_prover9` desugars exclusive-or to ``(a | b) & -(a & b)`` (Prover9
has no xor operator), so an :class:`Xor` round-trips to that conjunctive form, not to
``Xor``.

op(...) declarations: :func:`parse_prover9_problem` applies a genuinely NEW
``op(precedence, type, symbol)`` directive (Prover9's own syntax for declaring an
operator; the manual's page on parsing declarations —
https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/syntax.html, mirroring
``ladr/parse.c``'s ``declare_standard_parse_types()`` in the Prover9/LADR source —
is the citation for every precedence number and type keyword below) to every
formula that follows it in the same file. Two things are refused outright, by
name, as a :class:`Prover9ParsingError`, regardless of whether the declared
operator is ever used — because applying them could silently change the
meaning of other, unrelated text already in the file:

- **Redeclaring a built-in** (any symbol already in :data:`_DEFAULT_OPS`, e.g.
  ``op(500, infix, "+")``) is refused: doing this properly would mean making the
  *entire* grammar table-driven, a much larger and riskier change this reader does
  not make (see ``tests/test_prover9_ops.py`` and
  ``tests/test_prover9_entailment.py``'s module docstrings for how the reader is
  checked against an independent route and, where a binary exists, against a real
  Prover9).
- **Redeclaring a symbol this same file already declared** is refused the same way.

A **malformed** ``op(...)`` (wrong arity, a non-integer precedence, an unknown
type keyword, a symbol that is not a bare or double-quoted identifier, or a
precedence Prover9 itself would not accept — outside 1-998) is also refused by
name; these are syntax problems in the directive itself, independent of placement.

Everything else syntactically well-formed is *accepted* (matching real Prover9,
which does not reject any of it either) and applied where this reader has a
splice point for it, left harmlessly **inert** otherwise — see
:func:`_classify_and_splice` for exactly which placements splice and which are
inert (``type="ordinary"``; a precedence tying a built-in tier; a precedence at
or above the quantifier tier 750; prefix/postfix at an atom-tier precedence). An
inert declaration still blocks a later redeclaration of the same name, but a
formula that tries to *use* it as an operator sees an ordinary undeclared name
and fails to parse — loudly, just at that point rather than at the declaration
(this mirrors every op() directive's behaviour before this feature existed, for
exactly the declarations this reader still cannot safely place).

What DOES splice in: a new symbol at a **term-tier** precedence (< 500) becomes a
:class:`Function`-producing operator spliced next to ``unit_term`` (so its
operands are atomic terms — parenthesize an arithmetic sub-expression used as an
operand); a new symbol at an **atom-tier** precedence (501-699 or 701-749) becomes
an :class:`Atom`-producing operator spliced next to the existing comparisons, with
:class:`Node` operands taken from the ``term`` grammar. ``infix`` (Prover9's
``xfx``, non-associative) chains only inside explicit parentheses — exactly as in
Prover9 itself; ``infix_left``/``infix_right`` (``yfx``/``xfy``) chain without
parentheses in that direction. ``prefix``/``prefix_paren`` and
``postfix``/``postfix_paren`` splice in at the term tier only; this reader does
not distinguish ``fy`` from ``fx`` self-chaining (both may chain without
parentheses) — a narrower distinction real Prover9 makes and this one does not
need for any formula it still *accepts* (it only widens what parses, never what
a given input means). Only the 3-argument ``op(...)`` form is read; Prover9's
2-argument ``op(type, symbol)`` shorthand (valid only for ``type="ordinary"``)
is a malformed-arity refusal here.

Public API: :func:`parse_prover9` (a single formula; a trailing ``.`` is accepted).
"""

import re
from dataclasses import dataclass
from functools import lru_cache

from lark import Lark, Transformer, Tree

from ._fol_nodes import NumeralTextError, _numeral_from_text
from ._identifiers import fresh_variable_like
from ._numeral_symbols import numeral_name
from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Implies, Iff, Quantifier,
)
from .naming import ParsingError


class Prover9ParsingError(ParsingError):
    """A Prover9 import failure carrying a plain message (subclasses ParsingError)."""

    def __init__(self, message: str):
        self.args = (message,)

    def __str__(self):
        return self.args[0]


def _where(token) -> str:
    """Where ``token`` stands in the text that was parsed, for a message (``""`` when unknown)."""
    line, column = getattr(token, "line", None), getattr(token, "column", None)
    if line is None or column is None:
        return ""
    return f" (at line {line}, column {column} of the formula)"


def _numeral(text: str, token=None):
    """The value of the decimal numeral ``text``, read exactly (see
    :func:`~unicode_fol_kit.fol._fol_nodes._numeral_from_text`); a
    :class:`Prover9ParsingError` when no number holds it, which names the position of
    ``token`` (the token the numeral was read from) when one is given. Whatever the numeral
    reader refuses with (a ``ValueError`` for a text of thousands of digits, an ``OverflowError``,
    its own :class:`~unicode_fol_kit.fol._fol_nodes.NumeralTextError`) is that error here."""
    try:
        return _numeral_from_text(text)
    except (ValueError, ArithmeticError, NumeralTextError) as exc:
        message = str(exc)
        if message.startswith("SYNTAX_ERROR: "):
            message = message[len("SYNTAX_ERROR: "):]
        raise Prover9ParsingError(f"SYNTAX_ERROR: {message}{_where(token)}") from None


# The formula sub-grammar, shared by the single-formula parser and the whole-file
# parser. Deliberately kept free of the file-level keyword terminals
# (set/clear/assign/formulas/end_of_list): in single-formula mode a predicate that
# happens to be named e.g. ``set`` still lexes as a NAME, preserving backward
# compatibility for :func:`parse_prover9`.
#
# ``{atom_extra}`` / ``{term_extra}`` / ``{unit_term_extra}`` are splice points for
# newly op()-declared operators (see :func:`_build_custom_grammar`); with all three
# empty (the default, and the common case — a file with no custom operators) this
# formats to byte-identical text to the fixed grammar this module has always used,
# so the shared singleton parser below is neither rebuilt nor slowed down.
_FORMULA_RULES_TEMPLATE = r"""
?formula: equiv
?equiv: imp
      | imp "<->" imp     -> iff_
      | disj "<-" disj    -> rimplies_
?imp: disj
    | disj "->" imp       -> implies_
?disj: conj
     | disj "|" conj      -> or_
?conj: unary
     | conj "&" unary     -> and_
?unary: "-" negated       -> neg
      | _ALL NAME unary       -> forall
      | _EXISTS NAME unary    -> exists
      | "(" formula ")"
      | atom

?negated: "-" negated     -> neg
        | _ALL NAME unary       -> forall
        | _EXISTS NAME unary    -> exists
        | "(" formula ")"
        | plain_atom

?atom: comparison
     | plain_atom

?comparison: term "=" term      -> equality
           | term "!=" term     -> disequality
           | term "<=" term     -> le
           | term ">=" term     -> ge
           | term _LT term      -> lt
           | term ">" term      -> gt{atom_extra}

?plain_atom: NAME "(" termlist ")"  -> pred_app
           | QNAME "(" termlist ")" -> qpred_app
           | NAME                   -> prop_atom
           | TRUTH                  -> truth_atom
           | QNAME                  -> qprop_atom

?term: sum{term_extra}
?sum: product
    | sum "+" product     -> add
    | sum "-" product     -> sub
?product: unit_term
        | product "*" unit_term  -> mul
        | product "/" unit_term  -> div
?unit_term: signed_term
          | NUMBER                 -> number{unit_term_extra}
?signed_term: NAME "(" termlist ")"  -> func_app
            | QNAME "(" termlist ")" -> qfunc_app
            | "-" "(" term "," termlist ")" -> minus_app
            | NAME                   -> name_term
            | QNAME                  -> qname_term
            | "(" term ")"
            | "-" signed_term        -> uminus

termlist: term ("," term)*

NAME: /[A-Za-z_][A-Za-z0-9_]*/
_ALL: /all(?![A-Za-z0-9_])/
_EXISTS: /exists(?![A-Za-z0-9_])/
_LT: /<(?!-)/
QNAME: /"[^"]*"/
TRUTH: /\$[TF](?![A-Za-z0-9_])/
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\r\n]*/
"""

_FORMULA_RULES = _FORMULA_RULES_TEMPLATE.format(atom_extra="", term_extra="", unit_term_extra="")
_GRAMMAR = "?start: formula\n\n" + _FORMULA_RULES


@dataclass(frozen=True)
class Prover9Formula:
    """One formula read from a Prover9 file: its ``role`` and parsed ``formula``.

    ``role`` is the enclosing ``formulas(<name>)`` list name (``"sos"`` /
    ``"assumptions"`` / ``"goals"`` / …), or ``""`` for a bare top-level formula.
    """

    role: str
    formula: Node


# --- op(...) operator declarations (see the module docstring) ---

@dataclass(frozen=True)
class _CustomOp:
    """One parsed ``op(precedence, type, symbol)`` record."""

    precedence: int
    type: str
    symbol: str


# Prover9's own default operator table, from ``ladr/parse.c``'s
# ``declare_standard_parse_types()`` in the Prover9/LADR source (mirrored by the
# manual's "Clauses and Formulas" / parsing-declarations page — see the module
# docstring for the URL). Each entry is (precedence, type, symbol); type uses
# Prover9's own op()-command keywords, not Prolog's xfx/xfy/yfx names (the manual
# documents the correspondence: infix=xfx, infix_left=yfx, infix_right=xfy,
# prefix=fy, prefix_paren=fx, postfix=yf, postfix_paren=xf). Only the subset this
# reader's own grammar implements matters for parsing; the FULL real table is kept
# here anyway so that redeclaring any genuine Prover9 built-in — even one this
# reader's grammar never parses on its own, like "^" or "#" — is refused by name.
_DEFAULT_OPS = (
    (810, "infix_right", "#"),
    (800, "infix", "<->"),
    (800, "infix", "->"),
    (800, "infix", "<-"),
    (790, "infix_right", "|"),
    (780, "infix_right", "&"),
    (700, "infix", "="),
    (700, "infix", "!="),
    (700, "infix", "=="),
    (700, "infix", "<"),
    (700, "infix", "<="),
    (700, "infix", ">"),
    (700, "infix", ">="),
    (500, "infix", "+"),
    (500, "infix", "*"),
    (500, "infix", "@"),
    (500, "infix", "/"),
    (500, "infix", "\\"),
    (500, "infix", "^"),
    (500, "infix", "v"),
    (350, "prefix", "-"),
    (300, "postfix", "'"),
)
_DEFAULT_OP_SYMBOLS = frozenset(sym for _prec, _type, sym in _DEFAULT_OPS)
# "all"/"exists" are hard-coded grammar keywords rather than entries in
# _DEFAULT_OPS (they are not ordinary binary/unary operators — quantifiers bind a
# variable), but redeclaring them by name is refused the same way.
_RESERVED_SYMBOLS = _DEFAULT_OP_SYMBOLS | {"all", "exists"}

# Precedences that coincide with a built-in tier (every distinct precedence in
# _DEFAULT_OPS — 300, 350, 500, 700 — plus the quantifiers' 750 and the
# argument-list comma's 999, both declared standalone in
# declare_standard_parse_types() rather than through _DEFAULT_OPS's op()-style
# entries; 780/790/800/810 are already covered by _DEFAULT_OPS's own
# precedences). A NEW operator declared at exactly one of these ties an
# existing tier: this reader's placement rule (below 500 is a term operator,
# 500-750 an atom operator) cannot tell which side of the tie it belongs on —
# see _classify_and_splice for what happens then (left inert, not refused; a
# declaration this reader cannot safely place is simply never applied, exactly
# like every op() directive before this feature existed).
_RESERVED_PRECEDENCES = frozenset({300, 350, 500, 700, 750, 780, 790, 800, 810, 999})

_P9_OP_TYPE_NAMES = (
    "infix", "infix_left", "infix_right",
    "prefix", "prefix_paren", "postfix", "postfix_paren", "ordinary",
)
_P9_OP_BODY_RE = re.compile(r"^op\((?P<inner>.*)\)$", re.DOTALL)
_P9_INT_RE = re.compile(r"^-?[0-9]+$")
_P9_QUOTED_SYMBOL_RE = re.compile(r'^"([^"\\]*)"$')
_P9_BARE_SYMBOL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def _split_top_level_commas(text: str) -> list:
    """Split ``text`` on commas that are not nested inside ``[...]`` or ``"..."``.

    Used both for the outer ``op(precedence, type, symbol_or_list)`` arguments
    and for the inner ``[sym1, sym2, ...]`` symbol list.
    """
    parts = []
    depth = 0
    in_quotes = False
    current = []
    for ch in text:
        if in_quotes:
            current.append(ch)
            if ch == '"':
                in_quotes = False
            continue
        if ch == '"':
            in_quotes = True
            current.append(ch)
        elif ch == "[":
            depth += 1
            current.append(ch)
        elif ch == "]":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(ch)
    parts.append("".join(current))
    return [p.strip() for p in parts]


def _parse_op_symbol(token: str) -> str:
    """Read one op() symbol token: a bare identifier or a double-quoted one.

    Only symbols shaped like the grammar's own NAME terminal
    (``[A-Za-z_][A-Za-z0-9_]*``) are supported — a symbolic token such as
    ``"++"`` cannot be spliced into the grammar as a new keyword-like literal
    the way an identifier can (see the module docstring), so it is refused.
    A symbolic token that names an existing built-in (``"+"``, ``"&"``, …) is
    let through here regardless of shape, so :func:`_classify_and_splice` can
    give the specific "redeclaring built-in" error instead of this generic one.
    """
    quoted = _P9_QUOTED_SYMBOL_RE.match(token)
    name = quoted.group(1) if quoted else token
    if name in _RESERVED_SYMBOLS or _P9_BARE_SYMBOL_RE.match(name):
        return name
    raise Prover9ParsingError(
        f"SYNTAX_ERROR: op() symbol {token!r} is not supported by this reader "
        "(only alphanumeric/underscore operator names are; a symbolic token "
        "cannot be declared or redeclared here)")


def _parse_op_directive(body: str) -> list:
    """Parse one ``op(precedence, type, symbol)`` directive body (``body`` is the
    whole statement text, e.g. ``op(650, infix, "before")``, sans the trailing
    ``.``) into a list of :class:`_CustomOp` records — one per symbol, all
    sharing ``precedence``/``type``; ``op(N, TYPE, [s1, s2])`` yields two records.

    Only the 3-argument form is supported — see the module docstring.

    Raises:
        Prover9ParsingError: on any malformed ``op(...)`` (bad arity, a
            non-integer precedence, an unknown type keyword, or a symbol token
            this reader does not support).
    """
    match = _P9_OP_BODY_RE.match(body)
    if not match:
        raise Prover9ParsingError(f"SYNTAX_ERROR: malformed op(...) directive: {body!r}")
    args = _split_top_level_commas(match.group("inner"))
    if len(args) != 3:
        raise Prover9ParsingError(
            "SYNTAX_ERROR: op(...) needs exactly 3 arguments (precedence, type, "
            f"symbol[s]) — Prover9's 2-argument ordinary-only form is not "
            f"supported by this reader; got {len(args)}: {body!r}")
    prec_text, type_text, symbols_text = args
    if not _P9_INT_RE.match(prec_text):
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: op() precedence must be an integer, got {prec_text!r}")
    try:
        precedence = int(prec_text)
    except ValueError:      # Python's int() refuses a text of thousands of digits
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: op() precedence {prec_text[:12]!r}... has {len(prec_text.lstrip('-'))} digits: "
            "it is out of Prover9's valid range (1-998)") from None
    if type_text not in _P9_OP_TYPE_NAMES:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: unknown op() type {type_text!r} (expected one of "
            + ", ".join(_P9_OP_TYPE_NAMES) + ")")
    if symbols_text.startswith("[") and symbols_text.endswith("]"):
        inner_tokens = _split_top_level_commas(symbols_text[1:-1])
        if inner_tokens == [""]:
            raise Prover9ParsingError(f"SYNTAX_ERROR: empty op() symbol list: {body!r}")
    else:
        inner_tokens = [symbols_text]
    symbols = [_parse_op_symbol(tok) for tok in inner_tokens]
    return [_CustomOp(precedence, type_text, sym) for sym in symbols]


#: The first characters that make a bare name a variable (LADR ``variable_name``, measured on
#: Prover9 2026-8A, by every first letter and with names of several characters): under
#: ``set(prolog_style_variables)`` an upper-case ASCII letter, without it ``u`` to ``z``. Nothing
#: else is: ``_x`` is a constant in both conventions, and a quoted symbol never is.
_PROLOG_VARIABLE_INITIALS = frozenset("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
_STANDARD_VARIABLE_INITIALS = frozenset("uvwxyz")


def _is_variable(name: str, prolog_style: bool = True) -> bool:
    """Whether Prover9 reads the bare name ``name`` as a variable when no quantifier binds it:
    its first character is ``A``..``Z`` under ``set(prolog_style_variables)``, ``u``..``z``
    without it."""
    return name[:1] in (_PROLOG_VARIABLE_INITIALS if prolog_style else _STANDARD_VARIABLE_INITIALS)


_P9_QUOTED_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_P9_QUOTED_NUMERAL_RE = re.compile(r"-?[0-9]+(\.[0-9]+)?")


def _unquote(token) -> str:
    """The name inside a double-quoted symbol token, or a refusal by name.

    Prover9 accepts any text without a double quote between the quotes. Only an
    identifier-shaped name is read here (see the module docstring): the AST has no
    way to carry another one that :meth:`Node.to_prover9` could write back.
    """
    name = str(token)[1:-1]
    if not _P9_QUOTED_NAME_RE.fullmatch(name):
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: the quoted symbol {str(token)!r} is not supported by this "
            "reader: Prover9 accepts any text between double quotes, but this reader "
            "reads only a quoted name made of letters, digits and underscores that "
            "does not begin with a digit (the shape Node.to_prover9 writes), or a "
            "quoted numeral (\"2.5\", \"-1\"), because any other name could not be "
            "written back as the same symbol")
    return name


def _quoted_numeral(token) -> "Number":
    """The :class:`Number` a quoted numeral symbol (``"2.5"``, ``"-1"``) stands for, or a
    refusal by name when the text is not the canonical spelling of that number.

    Prover9 keeps ``"2.5"`` and ``"2.50"``, and ``"1"`` and ``"1.0"``, apart as two symbols;
    a :class:`Number` is identified by its value and has one text, so only the spelling
    :meth:`Number.to_prover9` writes is read (``"1"``, never ``"1.0"``).
    """
    text = str(token)[1:-1]
    value = _numeral(text, token)
    if text != numeral_name(value):
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: the quoted numeral {str(token)!r} is not read: Prover9 keeps "
            f"it apart from the quoted numeral {numeral_name(value)!r} that is the same "
            "number, and a Number node has one text, so reading it would merge two "
            "symbols. Write the number in its canonical form")
    return Number(value)


class _Prover9Transformer(Transformer):
    """Turn the Lark parse tree into the toolkit AST."""

    def iff_(self, items):
        return Iff(items[0], items[1])

    def implies_(self, items):
        return Implies(items[0], items[1])

    def rimplies_(self, items):
        # ``p <- q`` is ``q -> p``.
        return Implies(items[1], items[0])

    def or_(self, items):
        return Or(items[0], items[1])

    def and_(self, items):
        return And(items[0], items[1])

    def neg(self, items):
        return Not(items[0])

    # The binder and every occurrence of a variable carry the NAME of the AST variable already
    # (see :func:`_resolve_variables`, which runs first and decides what each spelling is).
    def forall(self, items):
        return Quantifier("∀", Variable(str(items[0])), items[1])

    def exists(self, items):
        return Quantifier("∃", Variable(str(items[0])), items[1])

    # --- atoms ---
    def equality(self, items):
        return Atom("=", [items[0], items[1]])

    def disequality(self, items):
        return Atom("≠", [items[0], items[1]])

    def le(self, items):
        return Atom("≤", [items[0], items[1]])

    def ge(self, items):
        return Atom("≥", [items[0], items[1]])

    def lt(self, items):
        return Atom("<", [items[0], items[1]])

    def gt(self, items):
        return Atom(">", [items[0], items[1]])

    def pred_app(self, items):
        return Atom(str(items[0]), items[1])

    def prop_atom(self, items):
        return Atom(str(items[0]), [])

    # --- Prover9's own constants: $T is true, $F is false ---
    def truth_atom(self, items):
        return Atom("$true" if str(items[0]) == "$T" else "$false", [])

    # --- quoted symbols: never a variable, whatever their first letter ---
    def qpred_app(self, items):
        return Atom(_unquote(items[0]), items[1])

    def qprop_atom(self, items):
        return Atom(_unquote(items[0]), [])

    # --- terms ---
    def add(self, items):
        return Function("+", [items[0], items[1]])

    def sub(self, items):
        return Function("-", [items[0], items[1]])

    def mul(self, items):
        return Function("*", [items[0], items[1]])

    def div(self, items):
        return Function("/", [items[0], items[1]])

    def func_app(self, items):
        return Function(str(items[0]), items[1])

    def name_term(self, items):
        # A bare name that is no variable (see :func:`_resolve_variables`): a constant.
        return Constant(str(items[0]))

    def var_term(self, items):
        return Variable(str(items[0]))

    def qfunc_app(self, items):
        return Function(_unquote(items[0]), items[1])

    def qname_term(self, items):
        if _P9_QUOTED_NUMERAL_RE.fullmatch(str(items[0])[1:-1]):
            return _quoted_numeral(items[0])
        return Constant(_unquote(items[0]))

    def minus_app(self, items):
        return Function("-", [items[0], *items[1]])

    def uminus(self, items):
        return Function("-", [items[0]])

    def number(self, items):
        return Number(_numeral(str(items[0]), items[0]))

    def termlist(self, items):
        return list(items)


_PARSER = Lark(_GRAMMAR, start="start", parser="earley")
_TRANSFORMER = _Prover9Transformer()


def _classify_and_splice(custom_ops: tuple) -> tuple:
    """Validate ``custom_ops`` (in declaration order) and split them into the
    grammar-splice buckets :func:`_build_custom_grammar` needs: atom-tier infix,
    term-tier infix, term-tier prefix and term-tier postfix.

    Two things are refused outright, by name, regardless of whether the
    operator is ever used in a formula — because accepting them would risk
    silently reinterpreting other, unrelated text in the same file:
    redeclaring an existing built-in (:data:`_RESERVED_SYMBOLS`), and
    redeclaring a symbol this same file already gave a custom meaning to.

    Everything else that is syntactically well-formed is accepted (matching
    real Prover9, which does not reject any of it either) and is spliced into
    the grammar when it falls in a window this reader supports — below the
    arithmetic tier (< 500) for a :class:`Function`-producing term operator,
    or between the arithmetic and quantifier tiers (500-750, excluding the
    comparison tier at 700) for an :class:`Atom`-producing one. A declaration
    this reader has no splice point for — ``type="ordinary"``, a precedence
    that exactly ties a built-in tier (:data:`_RESERVED_PRECEDENCES`), a
    precedence at or above the quantifier tier (750), or prefix/postfix at an
    atom-tier precedence — is simply left inert: recorded (so it still blocks
    a later redeclaration) but never spliced in, exactly like every op()
    directive before this feature existed. A formula that then tries to use
    such an operator sees an ordinary undeclared name and fails to parse —
    loudly, just at that point rather than at the declaration.
    """
    seen = set()
    atom_ops, term_infix, term_prefix, term_postfix = [], [], [], []
    for op in custom_ops:
        if op.symbol in _RESERVED_SYMBOLS:
            raise Prover9ParsingError(
                f"SYNTAX_ERROR: redeclaring built-in Prover9 operator {op.symbol!r} "
                "is not supported")
        if op.symbol in seen:
            raise Prover9ParsingError(
                f"SYNTAX_ERROR: operator {op.symbol!r} is already declared by an "
                "earlier op(...) in this file")
        seen.add(op.symbol)
        if not (1 <= op.precedence <= 998):
            raise Prover9ParsingError(
                f"SYNTAX_ERROR: op() precedence {op.precedence} is out of "
                "Prover9's valid range (1-998)")
        if op.type == "ordinary":
            continue  # not a mixfix operator: nothing to splice, just reserves the name
        if op.precedence in _RESERVED_PRECEDENCES:
            continue  # ties a built-in tier: left inert (see docstring above)
        if op.precedence < 500:
            kind = "term"
        elif op.precedence < 750:
            kind = "atom"
        else:
            continue  # would graft onto the quantifier/connective grammar: left inert
        if kind == "atom" and op.type not in ("infix", "infix_left", "infix_right"):
            continue  # prefix/postfix only supported at a term-tier precedence: left inert
        if kind == "atom":
            atom_ops.append(op)
        elif op.type in ("infix", "infix_left", "infix_right"):
            term_infix.append(op)
        elif op.type in ("prefix", "prefix_paren"):
            term_prefix.append(op)
        else:
            term_postfix.append(op)
    return tuple(atom_ops), tuple(term_infix), tuple(term_prefix), tuple(term_postfix)


def _infix_rule(rule: str, alias: str, sym: str, op_type: str, operand: str) -> str:
    """Build one Lark rule definition for a new infix operator.

    ``infix`` (xfx) is a single non-recursive alternative — deliberately: with
    no self-recursive branch, a chain like ``a sym b sym c`` cannot be produced
    by this rule at all, which is exactly Prover9's own non-associative
    semantics (both operands of an xfx operator need strictly lower precedence,
    so a bare 3-way chain needs explicit parentheses in real Prover9 too).
    ``infix_right`` (xfy) recurses on the right operand, ``infix_left`` (yfx) on
    the left, each with a non-recursive base alternative for the single-use case.
    """
    if op_type == "infix":
        return f'{rule}: {operand} "{sym}" {operand} -> {alias}'
    if op_type == "infix_right":
        return (f'{rule}: {operand} "{sym}" {rule} -> {alias}\n'
                f'     | {operand} "{sym}" {operand} -> {alias}')
    return (f'{rule}: {rule} "{sym}" {operand} -> {alias}\n'
            f'     | {operand} "{sym}" {operand} -> {alias}')


@lru_cache(maxsize=256)
def _build_custom_grammar(custom_ops: tuple):
    """Build (and cache, by the exact tuple of active op() declarations) a Lark
    parser + transformer pair that extends the shared grammar with newly
    op()-declared operators. An empty tuple returns the shared singleton
    (:data:`_PARSER`, :data:`_TRANSFORMER`) unchanged — no rebuild, no perf
    regression for the common case of a file with no custom operators.

    Validation (redeclaration, tie, range and placement checks — see
    :func:`_classify_and_splice`) happens here, so it runs once per distinct
    set of active declarations and is then free on every later call.

    Generated Lark rule/alias names are built from a per-bucket numeric index,
    never from ``op.symbol`` itself: Lark's own grammar meta-language requires
    a RULE/alias identifier to start with a lowercase letter (or underscore)
    and never contain an uppercase one (an uppercase-leading token is instead
    read as a TERMINAL reference), while op() symbols accepted here
    (:func:`_parse_op_symbol`) are only required to match the *formula*
    grammar's own ``NAME`` terminal — which does allow uppercase. Splicing an
    uppercase-containing symbol straight into a generated rule name (e.g.
    ``atom_chain_Before``) would therefore be lexed as two malformed grammar
    tokens and make the ``Lark(...)`` call below raise
    ``lark.exceptions.UnexpectedToken`` — a bare Lark internals leak, not a
    targeted :class:`Prover9ParsingError`, for a symbol shape this reader's
    own validator otherwise accepts. The real symbol still appears in the
    grammar, but only inside a quoted string literal (``"{op.symbol}"``),
    where Lark's syntax places no case restriction.
    """
    if not custom_ops:
        return _PARSER, _TRANSFORMER
    atom_ops, term_infix, term_prefix, term_postfix = _classify_and_splice(custom_ops)

    atom_extra, term_extra, unit_extra = [], [], []
    extra_rules = []
    handlers = {}

    for idx, op in enumerate(atom_ops):
        alias = f"custom_atom_{idx}"
        rule = f"atom_chain_{idx}"
        extra_rules.append(_infix_rule(rule, alias, op.symbol, op.type, "term"))
        atom_extra.append(f"\n     | {rule}")
        handlers[alias] = (lambda items, _s=op.symbol: Atom(_s, [items[0], items[1]]))

    for idx, op in enumerate(term_infix):
        alias = f"custom_term_{idx}"
        rule = f"term_chain_{idx}"
        extra_rules.append(_infix_rule(rule, alias, op.symbol, op.type, "unit_term"))
        term_extra.append(f"\n     | {rule}")
        handlers[alias] = (lambda items, _s=op.symbol: Function(_s, [items[0], items[1]]))

    for idx, op in enumerate(term_prefix):
        alias = f"custom_prefix_{idx}"
        rule = f"unit_prefix_{idx}"
        extra_rules.append(f'{rule}: "{op.symbol}" unit_term -> {alias}')
        unit_extra.append(f"\n          | {rule}")
        handlers[alias] = (lambda items, _s=op.symbol: Function(_s, [items[0]]))

    for idx, op in enumerate(term_postfix):
        alias = f"custom_postfix_{idx}"
        rule = f"unit_postfix_{idx}"
        extra_rules.append(f'{rule}: unit_term "{op.symbol}" -> {alias}')
        unit_extra.append(f"\n          | {rule}")
        handlers[alias] = (lambda items, _s=op.symbol: Function(_s, [items[0]]))

    rules_text = _FORMULA_RULES_TEMPLATE.format(
        atom_extra="".join(atom_extra),
        term_extra="".join(term_extra),
        unit_term_extra="".join(unit_extra),
    )
    grammar_text = "?start: formula\n\n" + rules_text + "\n" + "\n".join(extra_rules) + "\n"
    parser = Lark(grammar_text, start="start", parser="earley")
    transformer = _Prover9Transformer()
    for name, handler in handlers.items():
        setattr(transformer, name, handler)
    return parser, transformer


def _normalize_custom_ops(custom_ops) -> tuple:
    """Coerce ``custom_ops`` into a tuple of :class:`_CustomOp` (accepting plain
    ``(precedence, type, symbol)`` triples, the public/documented shape, as well
    as already-built :class:`_CustomOp` records)."""
    result = []
    for item in custom_ops:
        if isinstance(item, _CustomOp):
            result.append(item)
        else:
            precedence, op_type, symbol = item
            result.append(_CustomOp(int(precedence), str(op_type), str(symbol)))
    return tuple(result)


def parse_prover9(text: str, custom_ops=(), *, prolog_style_variables: bool = True) -> Node:
    """Parse a single Prover9-syntax formula into a toolkit :class:`Node`.

    A trailing period (Prover9 terminates each formula with ``.``) is accepted
    and ignored.

    A formula has no file around it to say which names are variables, so this reader
    keeps the convention of :meth:`Node.to_prover9`, ``set(prolog_style_variables)``: a name
    that no quantifier binds is a variable when it begins with an upper-case letter and a
    constant otherwise (see the module docstring for what a quantifier binds). Pass
    ``prolog_style_variables=False`` for Prover9's default, where it is a variable when it
    begins with ``u`` to ``z``.

    Args:
        text: a Prover9 formula, e.g. ``"(all X (man(X) -> mortal(X)))"``.
        custom_ops: previously-declared ``op(precedence, type, symbol)``
            operators that extend the grammar for this one parse, as
            ``(precedence, type, symbol)`` triples, in declaration order — see
            the module docstring's "op(...) declarations" section for exactly
            which operators are applied and which are refused.
            :func:`parse_prover9_problem` builds and threads this automatically
            from a file's own ``op(...)`` directives; most callers parsing a
            single formula never need to pass it.
        prolog_style_variables: which of the two conventions reads a name that is bound
            by no quantifier (``True`` is the default of this function).

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        Prover9ParsingError: if ``text`` is not a well-formed Prover9 formula,
            or ``custom_ops`` contains a declaration this reader refuses.
    """
    return _parse_formula(text, custom_ops, {}, prolog_style_variables)


# The tree nodes that name a symbol, with the key of the symbol they stand for.
# ``(kind, name, arity)`` as the AST keeps it: a name in formula position is a predicate, in
# term position a function (a constant is a function of arity 0), a number its own kind.
_P9_BARE_SYMBOL_RULES = {"pred_app": "predicate", "func_app": "function"}
_P9_QUOTED_SYMBOL_RULES = {"qpred_app": "predicate", "qfunc_app": "function"}


def _symbol_spellings(tree) -> list:
    """Every symbol of a parse tree as ``(key, "bare" | "quoted")``, ``key`` being
    ``(kind, name, arity)`` as the AST keeps a symbol (the name only, not its quotes).

    A variable is no symbol: :func:`_resolve_variables` has turned every name in term position
    that is a variable (bound by a quantifier, or one by the convention of the file) into a
    ``var_term`` node, so the ``name_term`` nodes that are left are constants.
    """
    found = []
    for sub in tree.iter_subtrees():
        rule = str(sub.data)
        if rule in _P9_BARE_SYMBOL_RULES or rule in _P9_QUOTED_SYMBOL_RULES:
            bare = rule in _P9_BARE_SYMBOL_RULES
            kind = _P9_BARE_SYMBOL_RULES[rule] if bare else _P9_QUOTED_SYMBOL_RULES[rule]
            name = str(sub.children[0]) if bare else str(sub.children[0])[1:-1]
            found.append(((kind, name, len(sub.children[1].children)), "bare" if bare else "quoted"))
        elif rule == "prop_atom":
            found.append((("predicate", str(sub.children[0]), 0), "bare"))
        elif rule == "qprop_atom":
            found.append((("predicate", str(sub.children[0])[1:-1], 0), "quoted"))
        elif rule == "name_term":
            found.append((("function", str(sub.children[0]), 0), "bare"))
        elif rule == "qname_term":
            name = str(sub.children[0])[1:-1]
            if _P9_QUOTED_NUMERAL_RE.fullmatch(name):
                found.append((("numeral", name, 0), "quoted"))
            else:
                found.append((("function", name, 0), "quoted"))
        elif rule == "number":
            found.append((("numeral", str(sub.children[0]), 0), "bare"))
    return found


def _refuse_two_spellings(tree, spellings: dict) -> None:
    """Refuse a symbol that is written both with and without double quotes.

    Prover9 keeps ``"rain"`` and ``rain`` apart as two symbols, and this reader has one
    name per symbol, so a text that uses both for the same predicate, function, constant
    or number would be read as ONE and mean something else. ``spellings`` carries the
    symbols already met (a file is one text), and is updated.
    """
    for key, how in _symbol_spellings(tree):
        seen = spellings.setdefault(key, set())
        seen.add(how)
        if len(seen) == 2:
            kind, name, arity = key
            what = {"predicate": "predicate" if arity else "proposition",
                    "function": "function" if arity else "constant",
                    "numeral": "number"}[kind]
            raise Prover9ParsingError(
                f"SYNTAX_ERROR: the {what} {name!r} is written both with and without double "
                f"quotes (\"{name}\" and {name}): Prover9 reads them as two symbols, this "
                "reader has one name per symbol and would read them as one, so the text "
                "would mean something else. Write the symbol one way.")


def _refuse_two_numeral_spellings(tree, spellings: dict) -> None:
    """Refuse a text that spells one numeral value two ways (``01`` and ``1``, ``1.0`` and ``1``).

    Prover9 keeps such numerals apart as symbols of their own, and a :class:`Number` is identified
    by its value, so this reader would read the two as ONE numeral: ``P(01). -P(1).`` is consistent
    (U = {0, 1}, 01 = 0, 1 = 1, P = {0}), and read as ``P(1), ¬P(1)`` it proves everything.
    ``spellings`` is the record shared by every formula of a file (a numeral value -> the texts
    it was written as), and is updated.
    """
    for sub in tree.iter_subtrees():
        rule = str(sub.data)
        if rule == "number":
            written = str(sub.children[0])
        elif rule == "qname_term" and _P9_QUOTED_NUMERAL_RE.fullmatch(str(sub.children[0])[1:-1]):
            written = str(sub.children[0])[1:-1]
        else:
            continue
        value = _numeral(written, sub.children[0])
        texts = spellings.setdefault(("numeral value", numeral_name(value)), set())
        texts.add(written)
        if len(texts) > 1:
            first, second = sorted(texts, key=lambda t: (len(t), t))[:2]
            raise Prover9ParsingError(
                f"SYNTAX_ERROR: the numerals {first} and {second} are written in one text: Prover9 "
                "reads them as two symbols, this reader has one numeral per value and would read "
                "them as one, so the text would mean something else. Write the number one way.")


_P9_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _resolve_variables(tree, prolog_style: bool, record: dict, text: str) -> None:
    """Decide which names of a parse tree are variables, and give each variable its AST name.

    Prover9 reads a quantifier as binding the SYMBOL it names, whatever its case: in
    ``all x (man(x) -> mortal(x))`` the three ``x`` are one variable, and the same text with
    ``X`` says the same (measured on Prover9 2026-8A, with and without
    ``set(prolog_style_variables)``). Inside the scope of the quantifier (the operand that
    follows the variable) a bare name in term position is that variable; an inner quantifier
    over the same spelling rebinds it, a name that is applied to arguments or stands as a
    formula is no term occurrence, and outside every quantifier the convention of the file
    decides (:func:`_is_variable`). The transformation builds a body before it meets the binder
    that is above it, so this runs first, over the finished parse tree, with an explicit stack: a
    ``name_term`` that is a variable becomes a ``var_term``, and the NAME of the binder and of
    every variable occurrence is replaced by the name of the :class:`Variable` it stands for.

    Variables are compared as written (``Xa`` and ``XA`` are two variables, ``x`` and ``X``
    too): each spelling gets the lower-case of itself as its name, which is what
    :meth:`Variable.to_prover9` (it upper-cases) is the inverse of, and a spelling whose
    lower-case another spelling of the same formula already has gets a fresh name instead
    (:func:`~unicode_fol_kit.fol._identifiers.fresh_variable_like`, fresh against every word of
    the text). A variable that no quantifier binds is one unknown element of the whole file (the
    same in every formula), so its spelling keeps its name in all of them: ``record`` is shared by
    all formulas of a file and holds those names.

    Raises:
        Prover9ParsingError: a bound name stands as a formula (``all x (P(x) & x)``), which
            Prover9 refuses as well, because a variable cannot be an atomic formula.
    """
    scope: dict = {}                    # spelling -> number of enclosing quantifiers that bind it
    sites: list = []                    # (tree node, spelling, free) of every variable, in text order
    seen: set = set()
    stack = [(tree, False)]
    while stack:
        node, leaving = stack.pop()
        if leaving:
            scope[str(node.children[0])] -= 1
            continue
        if id(node) in seen:
            continue
        seen.add(id(node))
        rule = node.data
        if rule == "name_term":
            spelling = str(node.children[0])
            bound = bool(scope.get(spelling))
            if bound or _is_variable(spelling, prolog_style):
                node.data = "var_term"
                sites.append((node, spelling, not bound))
            continue
        if rule == "prop_atom":
            spelling = str(node.children[0])
            if scope.get(spelling):
                raise Prover9ParsingError(
                    f"SYNTAX_ERROR: the name {spelling!r} stands as a formula inside the scope of "
                    f"'all {spelling}' / 'exists {spelling}', where it is a variable: Prover9 refuses "
                    "a variable as an atomic formula, and so does this reader.")
            continue
        if rule in ("forall", "exists"):
            spelling = str(node.children[0])
            sites.append((node, spelling, False))
            scope[spelling] = scope.get(spelling, 0) + 1
            stack.append((node, True))
        stack.extend((child, False) for child in reversed(node.children) if isinstance(child, Tree))
    if not sites:
        return
    free_names = record.setdefault(("variable names",), {})         # free spelling -> name, in all of the file
    free_taken = record.setdefault(("variable names taken",), set())
    free_spellings = {spelling for _, spelling, free in sites if free}
    spellings = list(dict.fromkeys(spelling for _, spelling, _ in sites))
    reserved = {s.lower() for s in spellings} | {w.lower() for w in _P9_WORD_RE.findall(text)}
    names: dict = {}
    used: set = set()                                               # the names this formula has given out
    for free_pass in (True, False):
        for spelling in spellings:
            if (spelling in free_spellings) != free_pass:
                continue
            name = free_names.get(spelling) if free_pass else None
            if name is None:
                name = spelling.lower()
                if name in used or (free_pass and name in free_taken):
                    name = fresh_variable_like(name, used | free_taken | reserved)
                if free_pass:
                    free_names[spelling] = name
                    free_taken.add(name)
            names[spelling] = name
            used.add(name)
    for node, spelling, _ in sites:
        node.children[0] = names[spelling]


def _parse_formula(text: str, custom_ops, spellings: dict, prolog_style: bool = True) -> Node:
    """:func:`parse_prover9` for a text that is part of a bigger one: ``spellings`` is the
    record of :func:`_refuse_two_spellings` and of the names of the variables, shared by every
    formula of a file, and ``prolog_style`` the convention of the file (see :func:`_is_variable`)."""
    ops = _normalize_custom_ops(custom_ops)
    parser, transformer = _build_custom_grammar(ops) if ops else (_PARSER, _TRANSFORMER)
    stripped = text.strip()
    if stripped.endswith("."):
        stripped = stripped[:-1]
    try:
        tree = parser.parse(stripped)
    except RecursionError:
        raise Prover9ParsingError(_TOO_DEEP) from None
    except Exception as exc:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: could not parse Prover9 formula: {exc}")
    try:
        _resolve_variables(tree, prolog_style, spellings, stripped)
        _refuse_two_spellings(tree, spellings)
        _refuse_two_numeral_spellings(tree, spellings)
        return _transform_tree(tree, transformer)
    except ParsingError:
        raise
    except RecursionError:
        raise Prover9ParsingError(_TOO_DEEP) from None
    except Exception as original:
        raise Prover9ParsingError(f"SYNTAX_ERROR: in Prover9 formula: {original}")


#: The refusal for a formula that the Python recursion limit stops the reader on.
_TOO_DEEP = (
    "SYNTAX_ERROR: the formula is nested too deeply for this reader (reading it reached "
    "Python's recursion limit). Split the formula, or raise sys.setrecursionlimit.")


def _transform_tree(tree, transformer):
    """``transformer.transform(tree)`` without recursion in Python.

    The transformer of Lark visits the tree recursively, so a chain of a few hundred
    operands (``a | b | c | ...`` is a left-nested tree) overflowed the stack of the
    interpreter. This visits the same nodes in the same order (children before their
    parent), each node through the method of its name, with an explicit stack; the
    callbacks are the ones of ``transformer``, and so are the exceptions they raise.
    """
    done: dict = {}
    stack = [(tree, False)]
    while stack:
        node, ready = stack.pop()
        if id(node) in done:
            continue
        if not ready:
            stack.append((node, True))
            stack.extend((child, False) for child in node.children
                         if isinstance(child, Tree) and id(child) not in done)
            continue
        children = [done[id(child)] if isinstance(child, Tree) else child
                    for child in node.children]
        callback = getattr(transformer, node.data, None)
        done[id(node)] = callback(children) if callback is not None else Tree(
            node.data, children, node.meta)
    return done[id(tree)]


# --- whole-file statement scanner (deterministic; see parse_prover9_problem) ---
# A line comment runs from '%' to end of line (LF, CRLF or a bare CR). A statement is a run of text ending
# at a '.' that terminates it — i.e. a '.' that is NOT the decimal point of a number
# (``.`` immediately followed by a digit, preceded by a digit, stays inside the run).
# A double-quoted symbol is skipped whole by both expressions: a '%' inside it starts no comment and a '.' inside
# it ends no statement (LADR reads quoted text raw). A quote is a pair; an odd number of them is refused.
_P9_COMMENT_RE = re.compile(r'("[^"]*")|%[^\r\n]*')
_P9_STATEMENT_RE = re.compile(r'(?:"[^"]*"|[^."])*(?:\.[0-9](?:"[^"]*"|[^."])*)*\.', re.DOTALL)
# A top-level directive is ``set``/``clear``/``assign``/``op`` applied with parens.
_P9_DIRECTIVES = frozenset({"set", "clear", "assign", "op"})
_P9_HEAD_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*\(")
_P9_FORMULAS_RE = re.compile(r"^formulas\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)$")
_P9_FORMULAS_CALL_RE = re.compile(r"^formulas\s*\(")
_P9_VARIABLE_FLAG_RE = re.compile(r"^(set|clear)\s*\(\s*prolog_style_variables\s*\)$")


def _formulas_header_arguments(body: str) -> int:
    """The number of arguments of ``body`` when it is ONE call ``formulas( ... )`` that ends
    with the statement, else ``0`` (a call whose parenthesis is never closed counts as ``1``: it is
    a header that is not well formed).

    A list header has exactly one argument, so INSIDE a list a statement that is a call of
    ``formulas`` with two or more is an atom (``formulas(alpha, beta)``, which Prover9 reads there
    like any predicate, and which the writer of this kit writes for a predicate of that name), and
    so is a statement that goes on after the call (``formulas(a, b) = c``,
    ``formulas(alpha) & Q``). Outside every list the same call is a header that is not well formed
    (Prover9 stops at it with "Unrecognized command or list"; :func:`_statement_kind`). Quoted
    symbols and nested parentheses are skipped when the arguments are counted.
    """
    start = _P9_FORMULAS_CALL_RE.match(body)
    if start is None:
        return 0
    depth, arguments, quoted = 0, 1, False
    for index in range(start.end() - 1, len(body)):
        character = body[index]
        if quoted:
            quoted = character != '"'
        elif character == '"':
            quoted = True
        elif character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                return arguments if index == len(body) - 1 else 0
        elif character == "," and depth == 1:
            arguments += 1
    return 1          # the parenthesis is never closed: a header that is not well formed


def _statement_kind(body: str, in_list: bool) -> str:
    """What one statement of a file is: ``"directive"`` (``set``, ``clear``, ``assign``,
    ``op`` outside every list), ``"header"`` (``formulas(NAME)``, the call with ONE argument; also
    a call with more arguments outside every list, which is a header that is not well formed),
    ``"end"`` (``end_of_list``) or ``"formula"`` (inside a list ``formulas(alpha, beta)`` is one:
    an atom)."""
    head_m = _P9_HEAD_RE.match(body)
    head = head_m.group(1) if head_m else None
    if not in_list and head in _P9_DIRECTIVES:
        return "directive"
    if head == "formulas":
        arguments = _formulas_header_arguments(body)
        if arguments == 1 or (arguments > 1 and not in_list):
            return "header"
    if body == "end_of_list":
        return "end"
    return "formula"


def _prolog_style_of(statements: list) -> bool:
    """Whether a file reads its names under ``set(prolog_style_variables)``.

    Measured on Prover9 2026-8A: the LAST ``set(prolog_style_variables)`` or
    ``clear(prolog_style_variables)`` of the file decides for EVERY formula of it, the ones that
    come before it included (a flag is read before any formula is interpreted), and a file that
    never sets it reads Prover9's default. Only a directive outside the lists counts.
    """
    prolog, in_list = False, False
    for body in statements:
        kind = _statement_kind(body, in_list)
        if kind == "directive":
            flag = _P9_VARIABLE_FLAG_RE.match(body)
            if flag is not None:
                prolog = flag.group(1) == "set"
        elif kind == "header":
            in_list = True
        elif kind == "end":
            in_list = False
    return prolog


def parse_prover9_problem(text: str) -> list:
    """Parse a whole Prover9 / LADR input file into a list of :class:`Prover9Formula`.

    Reads ``set`` / ``clear`` / ``assign`` directives (recognised and skipped),
    ``op(precedence, type, symbol)`` directives (recognised and, when the
    declared operator is genuinely new, applied to every formula parsed after
    it — see the module docstring's "op(...) declarations" section for exactly
    what is applied and what is refused), ``formulas(LIST). … end_of_list.``
    blocks, and bare top-level ``formula.`` statements (``%`` line comments are
    ignored). Each formula is returned tagged with its list name as ``role``
    (``""`` for a bare top-level formula), in source order.

    Statements are scanned deterministically (split on the terminating ``.``, with a
    ``.`` inside a decimal number or inside a double-quoted symbol kept; a ``%`` inside
    a quoted symbol is no comment), and each formula is parsed by
    :func:`parse_prover9` under whatever ``op(...)`` declarations are active at that
    point in the file (a formula using a name before its own ``op(...)`` directive
    sees it as an ordinary, undeclared name, not as an operator). A ``formulas(...)``
    header with no matching ``end_of_list.``, a stray ``end_of_list.``, or a
    malformed header is a hard error — unlike a grammar that could silently
    reinterpret an unterminated list as bare formulas. A header is the call
    ``formulas(NAME)`` with ONE argument: inside a list a call with two or more is an atom of the
    predicate ``formulas`` (``formulas(alpha, beta).``, which Prover9 reads as one and the writer of
    this kit writes for such a predicate), and so is a statement that goes on after the call;
    outside every list a call with two or more is a malformed header, as it is for Prover9
    ("Unrecognized command or list").

    Names are read under the convention the file sets (see the module docstring): the last
    ``set(prolog_style_variables)`` or ``clear(prolog_style_variables)`` of the file decides for
    all of its formulas, and a file that never sets it reads Prover9's default, where a name
    that no quantifier binds is a variable when it begins with ``u`` to ``z``.

    Args:
        text: the contents of a Prover9 problem file.

    Returns:
        A list of :class:`Prover9Formula` ``(role, formula)`` records.

    Raises:
        Prover9ParsingError: if the text is not a well-formed Prover9 problem (within
            the supported subset; an individual formula is parsed by
            :func:`parse_prover9`), or an ``op(...)`` directive is malformed or
            refused.
    """
    stripped = _P9_COMMENT_RE.sub(lambda m: m.group(1) or "", text)
    if stripped.count('"') % 2:
        raise Prover9ParsingError(
            "SYNTAX_ERROR: a double quote without its closing double quote "
            "(a quoted symbol is not closed)")
    statements = []
    pos = 0
    for match in _P9_STATEMENT_RE.finditer(stripped):
        if match.start() != pos:
            break         # text was skipped, so a statement is open: the leftover check reports it
        pos = match.end()
        body = match.group(0).strip()[:-1].strip()   # drop the terminating '.'
        if body:
            statements.append(body)
    prolog_style = _prolog_style_of(statements)
    records = []
    role = None          # the open formulas(...) list name, or None at top level
    active_ops = ()       # _CustomOp records declared so far, in order
    spellings: dict = {}  # symbol -> how it was written so far (see _refuse_two_spellings)
    for body in statements:
        kind = _statement_kind(body, role is not None)
        if kind == "directive":
            directive = _P9_HEAD_RE.match(body)
            if directive is not None and directive.group(1) == "op":
                new_ops = _parse_op_directive(body)
                active_ops = active_ops + tuple(new_ops)
                _build_custom_grammar(active_ops)  # validates now; result is cached
            continue                                  # top-level flag/op directive: skip
        if kind == "header":
            list_m = _P9_FORMULAS_RE.match(body)
            if not list_m:
                raise Prover9ParsingError(
                    f"SYNTAX_ERROR: malformed 'formulas(...)' header: {body!r}")
            if role is not None:
                raise Prover9ParsingError(
                    "SYNTAX_ERROR: nested 'formulas(...)' list "
                    f"(the '{role}' list was not closed by 'end_of_list.')")
            role = list_m.group(1)
            continue
        if kind == "end":
            if role is None:
                raise Prover9ParsingError(
                    "SYNTAX_ERROR: 'end_of_list.' without an open 'formulas(...)' list")
            role = None
            continue
        records.append(Prover9Formula(
            role or "", _parse_formula(body, active_ops, spellings, prolog_style)))
    if role is not None:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: 'formulas({role})' list not closed by 'end_of_list.'")
    leftover = stripped[pos:].strip()
    if leftover:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: unterminated Prover9 statement (missing '.'): {leftover[:60]!r}")
    return records


def load_prover9(path: str) -> list:
    """Read a Prover9 / LADR input file and :func:`parse_prover9_problem` its contents.

    Args:
        path: path to a Prover9 ``.in`` / ``.p9`` input file.

    Returns:
        A list of :class:`Prover9Formula` records.
    """
    with open(path, "r", encoding="utf-8") as handle:
        return parse_prover9_problem(handle.read())
