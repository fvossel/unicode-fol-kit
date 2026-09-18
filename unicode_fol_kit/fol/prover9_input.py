"""Prover9 / LADR input: read Prover9-syntax formulas into the AST.

This is the inverse of :meth:`Node.to_prover9`. Prover9's surface syntax differs
from the toolkit's Unicode notation (``all X``/``exists X`` quantifiers, ``-`` for
negation, ``&  |  ->  <->`` connectives, infix comparison predicates), so it gets
its own Lark grammar.

Convention: the toolkit's :meth:`Node.to_prover9` emits under
``set(prolog_style_variables)``, where a bound symbol is a **variable** iff it begins
with an uppercase letter or an underscore. This reader follows the same rule — a
bare uppercase/underscore-initial name in TERM position becomes a lowercase
:class:`Variable`; a bare lowercase name becomes a :class:`Constant`; a name applied
to arguments is a predicate (in formula position) or function (in term position) and
keeps its case; a bare name in FORMULA position is a nullary (propositional) predicate.
Comparison operators map back to the ``=`` / ``≠`` / ``<`` / ``>`` / ``≤`` / ``≥``
atoms and ``+ - * /`` to the arithmetic functions.

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
  not make (there is also no live Prover9 binary in this environment to
  differentially verify such a rewrite against — see ``tests/test_prover9_ops.py``
  and ``tests/test_prover9_entailment.py``'s module docstrings).
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

from lark import Lark, Transformer
from lark.exceptions import VisitError

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
?imp: disj
    | disj "->" imp       -> implies_
?disj: conj
     | disj "|" conj      -> or_
?conj: unary
     | conj "&" unary     -> and_
?unary: "-" unary         -> neg
      | "all" NAME unary       -> forall
      | "exists" NAME unary    -> exists
      | "(" formula ")"
      | atom

?atom: term "=" term      -> equality
     | term "!=" term     -> disequality
     | term "<=" term     -> le
     | term ">=" term     -> ge
     | term "<" term      -> lt
     | term ">" term      -> gt
     | NAME "(" termlist ")"  -> pred_app
     | NAME                   -> prop_atom{atom_extra}

?term: sum{term_extra}
?sum: product
    | sum "+" product     -> add
    | sum "-" product     -> sub
?product: unit_term
        | product "*" unit_term  -> mul
        | product "/" unit_term  -> div
?unit_term: NAME "(" termlist ")"  -> func_app
          | NAME                   -> name_term
          | NUMBER                 -> number
          | "(" term ")"{unit_term_extra}

termlist: term ("," term)*

NAME: /[A-Za-z_][A-Za-z0-9_]*/
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\n]*/
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
    precedence = int(prec_text)
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


def _is_variable(name: str) -> bool:
    """Prolog-style: a symbol is a variable iff it starts uppercase or with ``_``."""
    return name[0].isupper() or name[0] == "_"


class _Prover9Transformer(Transformer):
    """Turn the Lark parse tree into the toolkit AST."""

    def iff_(self, items):
        return Iff(items[0], items[1])

    def implies_(self, items):
        return Implies(items[0], items[1])

    def or_(self, items):
        return Or(items[0], items[1])

    def and_(self, items):
        return And(items[0], items[1])

    def neg(self, items):
        return Not(items[0])

    def forall(self, items):
        return Quantifier("∀", Variable(str(items[0]).lower()), items[1])

    def exists(self, items):
        return Quantifier("∃", Variable(str(items[0]).lower()), items[1])

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
        name = str(items[0])
        return Variable(name.lower()) if _is_variable(name) else Constant(name)

    def number(self, items):
        text = str(items[0])
        return Number(float(text) if "." in text else int(text))

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


def parse_prover9(text: str, custom_ops=()) -> Node:
    """Parse a single Prover9-syntax formula into a toolkit :class:`Node`.

    A trailing period (Prover9 terminates each formula with ``.``) is accepted
    and ignored.

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

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        Prover9ParsingError: if ``text`` is not a well-formed Prover9 formula,
            or ``custom_ops`` contains a declaration this reader refuses.
    """
    ops = _normalize_custom_ops(custom_ops)
    parser, transformer = _build_custom_grammar(ops) if ops else (_PARSER, _TRANSFORMER)
    stripped = text.strip()
    if stripped.endswith("."):
        stripped = stripped[:-1]
    try:
        tree = parser.parse(stripped)
    except Exception as exc:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: could not parse Prover9 formula: {exc}")
    try:
        return transformer.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        if isinstance(original, ParsingError):
            raise original
        raise Prover9ParsingError(f"SYNTAX_ERROR: in Prover9 formula: {original}")


# --- whole-file statement scanner (deterministic; see parse_prover9_problem) ---
# A line comment runs from '%' to end of line. A statement is a run of text ending
# at a '.' that terminates it — i.e. a '.' that is NOT the decimal point of a number
# (``.`` immediately followed by a digit, preceded by a digit, stays inside the run).
_P9_COMMENT_RE = re.compile(r"%[^\n]*")
_P9_STATEMENT_RE = re.compile(r"[^.]*(?:\.[0-9][^.]*)*\.", re.DOTALL)
# A top-level directive is ``set``/``clear``/``assign``/``op`` applied with parens.
_P9_DIRECTIVES = frozenset({"set", "clear", "assign", "op"})
_P9_HEAD_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*\(")
_P9_FORMULAS_RE = re.compile(r"^formulas\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)$")


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
    ``.`` inside a decimal number kept), and each formula is parsed by
    :func:`parse_prover9` under whatever ``op(...)`` declarations are active at that
    point in the file (a formula using a name before its own ``op(...)`` directive
    sees it as an ordinary, undeclared name, not as an operator). A ``formulas(...)``
    header with no matching ``end_of_list.``, a stray ``end_of_list.``, or a
    malformed header is a hard error — unlike a grammar that could silently
    reinterpret an unterminated list as bare formulas.

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
    stripped = _P9_COMMENT_RE.sub("", text)
    records = []
    role = None          # the open formulas(...) list name, or None at top level
    active_ops = ()       # _CustomOp records declared so far, in order
    pos = 0
    for match in _P9_STATEMENT_RE.finditer(stripped):
        pos = match.end()
        body = match.group(0).strip()[:-1].strip()   # drop the terminating '.'
        if not body:
            continue
        head_m = _P9_HEAD_RE.match(body)
        head = head_m.group(1) if head_m else None
        if role is None and head in _P9_DIRECTIVES:
            if head == "op":
                new_ops = _parse_op_directive(body)
                active_ops = active_ops + tuple(new_ops)
                _build_custom_grammar(active_ops)  # validates now; result is cached
            continue                                  # top-level flag/op directive: skip
        if head == "formulas":
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
        if body == "end_of_list":
            if role is None:
                raise Prover9ParsingError(
                    "SYNTAX_ERROR: 'end_of_list.' without an open 'formulas(...)' list")
            role = None
            continue
        records.append(Prover9Formula(role or "", parse_prover9(body, custom_ops=active_ops)))
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
