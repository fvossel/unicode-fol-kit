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

Public API: :func:`parse_prover9` (a single formula; a trailing ``.`` is accepted).
"""

import re
from dataclasses import dataclass

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
_FORMULA_RULES = r"""
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
     | NAME                   -> prop_atom

?term: sum
?sum: product
    | sum "+" product     -> add
    | sum "-" product     -> sub
?product: unit_term
        | product "*" unit_term  -> mul
        | product "/" unit_term  -> div
?unit_term: NAME "(" termlist ")"  -> func_app
          | NAME                   -> name_term
          | NUMBER                 -> number
          | "(" term ")"

termlist: term ("," term)*

NAME: /[A-Za-z_][A-Za-z0-9_]*/
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\n]*/
"""

_GRAMMAR = "?start: formula\n\n" + _FORMULA_RULES


@dataclass(frozen=True)
class Prover9Formula:
    """One formula read from a Prover9 file: its ``role`` and parsed ``formula``.

    ``role`` is the enclosing ``formulas(<name>)`` list name (``"sos"`` /
    ``"assumptions"`` / ``"goals"`` / …), or ``""`` for a bare top-level formula.
    """

    role: str
    formula: Node


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


def parse_prover9(text: str) -> Node:
    """Parse a single Prover9-syntax formula into a toolkit :class:`Node`.

    A trailing period (Prover9 terminates each formula with ``.``) is accepted and
    ignored.

    Args:
        text: a Prover9 formula, e.g. ``"(all X (man(X) -> mortal(X)))"``.

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        Prover9ParsingError: if ``text`` is not a well-formed Prover9 formula.
    """
    stripped = text.strip()
    if stripped.endswith("."):
        stripped = stripped[:-1]
    try:
        tree = _PARSER.parse(stripped)
    except Exception as exc:
        raise Prover9ParsingError(
            f"SYNTAX_ERROR: could not parse Prover9 formula: {exc}")
    try:
        return _TRANSFORMER.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        if isinstance(original, ParsingError):
            raise original
        raise Prover9ParsingError(f"SYNTAX_ERROR: in Prover9 formula: {original}")


def parse_prover9_problem(text: str) -> list:
    """Parse a whole Prover9 / LADR input file into a list of :class:`Prover9Formula`.

    Reads ``set`` / ``clear`` / ``assign`` / ``op`` directives (recognised and skipped),
    ``formulas(LIST). … end_of_list.`` blocks, and bare top-level ``formula.``
    statements (``%`` line comments are ignored). Each formula is returned tagged with
    its list name as ``role`` (``""`` for a bare top-level formula), in source order.

    Statements are scanned deterministically (split on the terminating ``.``, with a
    ``.`` inside a decimal number kept), and each formula is parsed by
    :func:`parse_prover9`. A ``formulas(...)`` header with no matching ``end_of_list.``,
    a stray ``end_of_list.``, or a malformed header is a hard error — unlike a grammar
    that could silently reinterpret an unterminated list as bare formulas.

    Args:
        text: the contents of a Prover9 problem file.

    Returns:
        A list of :class:`Prover9Formula` ``(role, formula)`` records.

    Raises:
        Prover9ParsingError: if the text is not a well-formed Prover9 problem (within
            the supported subset; an individual formula is parsed by
            :func:`parse_prover9`).
    """
    stripped = _P9_COMMENT_RE.sub("", text)
    records = []
    role = None          # the open formulas(...) list name, or None at top level
    pos = 0
    for match in _P9_STATEMENT_RE.finditer(stripped):
        pos = match.end()
        body = match.group(0).strip()[:-1].strip()   # drop the terminating '.'
        if not body:
            continue
        head_m = _P9_HEAD_RE.match(body)
        head = head_m.group(1) if head_m else None
        if role is None and head in _P9_DIRECTIVES:
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
        records.append(Prover9Formula(role or "", parse_prover9(body)))
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
