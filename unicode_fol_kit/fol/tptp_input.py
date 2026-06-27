"""TPTP input: read TPTP ``fof`` / ``cnf`` formulas and whole problem files into the AST.

This is the inverse of :meth:`Node.to_tptp`. TPTP has a genuinely different surface
syntax from the toolkit's Unicode notation (the ``fof(name, role, formula).`` wrapper,
``! [X] : φ`` / ``? [X] : φ`` quantifiers, uppercase variables, lowercase
constants/functions/predicates, ``& | ~ => <=> <~>`` connectives, ``$less``/``$sum``
dollar-words), so it gets its own Lark grammar rather than the glyph-translation used
for LaTeX import.

Public API:

- :func:`parse_tptp_formula` — parse a single bare FOF/CNF formula into a :class:`Node`.
- :func:`parse_tptp` — parse a whole TPTP problem (one or more ``fof``/``cnf``
  statements) into a list of :class:`TptpFormula` ``(name, role, formula)`` records.
- :func:`load_tptp` — read a ``.p`` / ``.tptp`` file and :func:`parse_tptp` it.

Naming conventions (the exact inverse of :meth:`Node.to_tptp`): a TPTP **variable**
(uppercase) becomes a lowercase :class:`Variable`; a **predicate** (lowercase in TPTP)
is capitalised to match the toolkit's uppercase-predicate convention, so ``loves`` ↦
``Loves`` and ``p`` ↦ ``P``; **constants** and **functions** stay lowercase; ``=`` /
``!=`` map to the ``=`` / ``≠`` atoms; the comparison dollar-words ``$less`` /
``$greater`` / ``$lesseq`` / ``$greatereq`` map to the ``<`` / ``>`` / ``≤`` / ``≥``
atoms; and the arithmetic dollar-words ``$sum`` / ``$difference`` / ``$product`` /
``$quotient`` map to the ``+`` / ``-`` / ``*`` / ``/`` functions. ``$true`` / ``$false``
are imported as opaque nullary atoms (the toolkit has no boolean-constant node).

Scope: the first-order ``fof`` fragment and ``cnf`` clauses. Typed (``tff``/``thf``)
formulas, ``include`` directives, and the optional 4th/5th annotation fields of a
statement are out of scope.
"""

from dataclasses import dataclass

from lark import Lark, Transformer
from lark.exceptions import VisitError

from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
)
from .naming import ParsingError


class TptpParsingError(ParsingError):
    """A TPTP import failure, carrying a plain message.

    Subclasses :class:`ParsingError` (so ``except ParsingError`` still catches it)
    but takes a string instead of a Lark exception — the same pattern
    :class:`ConflictingArityError` uses.
    """

    def __init__(self, message: str):
        self.args = (message,)

    def __str__(self):
        return self.args[0]


# Dollar-word predicate / function dictionaries — the inverse of the
# PREFIX_PREDS_TPTP / TPTP_ARITH_OPS tables in _fol_nodes.py.
_DOLLAR_PRED = {"$less": "<", "$greater": ">", "$lesseq": "≤", "$greatereq": "≥"}
_DOLLAR_FUNC = {"$sum": "+", "$difference": "-", "$product": "*", "$quotient": "/"}


@dataclass(frozen=True)
class TptpFormula:
    """One annotated TPTP statement: its ``name``, ``role``, and parsed ``formula``."""

    name: str
    role: str
    formula: Node


_GRAMMAR = r"""
file: stmt+
stmt: LOWER "(" fof_name "," LOWER "," formula ")" "."
fof_name: LOWER | NUMBER

?formula: equiv
?equiv: imp
      | imp "<=>" imp   -> iff
      | imp "<~>" imp   -> xor
?imp: disj
    | disj "=>" imp     -> implies
    | disj "<=" imp     -> rev_implies
?disj: conj
     | disj "|" conj    -> or_
     | disj "~|" conj   -> nor
?conj: unary
     | conj "&" unary   -> and_
     | conj "~&" unary  -> nand
?unary: "~" unary       -> neg
      | "!" "[" varlist "]" ":" unary  -> forall
      | "?" "[" varlist "]" ":" unary  -> exists
      | "(" formula ")"
      | atom

varlist: VAR ("," VAR)*

?atom: term "=" term    -> equality
     | term "!=" term   -> disequality
     | DOLLARWORD "(" termlist ")"  -> dollar_atom
     | LOWER "(" termlist ")"       -> pred_app
     | DOLLARWORD                   -> bool_const
     | LOWER                        -> prop_atom

?term: VAR                          -> var
     | DOLLARWORD "(" termlist ")"  -> dollar_func_app
     | LOWER "(" termlist ")"       -> func_app
     | LOWER                        -> constant
     | NUMBER                       -> number

termlist: term ("," term)*

VAR: /[A-Z][A-Za-z0-9_]*/
LOWER: /[a-z][A-Za-z0-9_]*/
DOLLARWORD: /\$[a-z_]+/
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\n]*/
%ignore /\/\*(.|\n)*?\*\//
"""


def _cap(name: str) -> str:
    """Capitalise the first letter (invert to_tptp's predicate lower-casing)."""
    return name[:1].upper() + name[1:] if name else name


class _TptpTransformer(Transformer):
    """Turn the Lark parse tree into the toolkit AST."""

    # --- whole-file / statements ---
    def file(self, items):
        return list(items)

    def stmt(self, items):
        keyword = str(items[0])
        if keyword not in ("fof", "cnf"):
            raise TptpParsingError(
                f"SYNTAX_ERROR: unsupported TPTP statement '{keyword}' "
                "(only fof and cnf are supported)."
            )
        name, role, formula = str(items[1]), str(items[2]), items[3]
        return TptpFormula(name, role, formula)

    def fof_name(self, items):
        return str(items[0])

    # --- connectives ---
    def iff(self, items):
        return Iff(items[0], items[1])

    def xor(self, items):
        return Xor(items[0], items[1])

    def implies(self, items):
        return Implies(items[0], items[1])

    def rev_implies(self, items):
        # TPTP  a <= b  means "a if b", i.e. b => a.
        return Implies(items[1], items[0])

    def or_(self, items):
        return Or(items[0], items[1])

    def nor(self, items):
        return Not(Or(items[0], items[1]))

    def and_(self, items):
        return And(items[0], items[1])

    def nand(self, items):
        return Not(And(items[0], items[1]))

    def neg(self, items):
        return Not(items[0])

    # --- quantifiers ---
    def forall(self, items):
        return self._quantify("∀", items[0], items[1])

    def exists(self, items):
        return self._quantify("∃", items[0], items[1])

    def _quantify(self, qtype, variables, body):
        for var in reversed(variables):
            body = Quantifier(qtype, var, body)
        return body

    def varlist(self, items):
        return [Variable(str(tok).lower()) for tok in items]

    # --- atoms ---
    def equality(self, items):
        return Atom("=", [items[0], items[1]])

    def disequality(self, items):
        return Atom("≠", [items[0], items[1]])

    def pred_app(self, items):
        return Atom(_cap(str(items[0])), items[1])

    def prop_atom(self, items):
        return Atom(_cap(str(items[0])), [])

    def dollar_atom(self, items):
        word = str(items[0])
        if word in _DOLLAR_PRED:
            return Atom(_DOLLAR_PRED[word], items[1])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word predicate '{word}'."
        )

    def bool_const(self, items):
        word = str(items[0])
        if word in ("$true", "$false"):
            return Atom(word, [])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word '{word}'."
        )

    # --- terms ---
    def var(self, items):
        return Variable(str(items[0]).lower())

    def constant(self, items):
        return Constant(str(items[0]))

    def number(self, items):
        text = str(items[0])
        return Number(float(text) if "." in text else int(text))

    def func_app(self, items):
        return Function(str(items[0]), items[1])

    def dollar_func_app(self, items):
        word = str(items[0])
        if word in _DOLLAR_FUNC:
            return Function(_DOLLAR_FUNC[word], items[1])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word function '{word}'."
        )

    def termlist(self, items):
        return list(items)


_FORMULA_PARSER = Lark(_GRAMMAR, start="formula", parser="earley")
_FILE_PARSER = Lark(_GRAMMAR, start="file", parser="earley")
_TRANSFORMER = _TptpTransformer()


def _parse(text: str, parser: Lark, what: str):
    """Parse + transform with unified error handling (unwrapping lark's VisitError)."""
    try:
        tree = parser.parse(text)
    except TptpParsingError:
        raise
    except Exception as exc:
        raise TptpParsingError(f"SYNTAX_ERROR: could not parse TPTP {what}: {exc}")
    try:
        return _TRANSFORMER.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        if isinstance(original, ParsingError):
            raise original
        raise TptpParsingError(f"SYNTAX_ERROR: in TPTP {what}: {original}")


def parse_tptp_formula(text: str) -> Node:
    """Parse a single bare TPTP FOF/CNF formula (no ``fof(...)`` wrapper) into a Node.

    Args:
        text: a TPTP formula, e.g. ``"![X]: (p(X) => q(X))"``.

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        ParsingError: if ``text`` is not a well-formed TPTP formula.
    """
    return _parse(text, _FORMULA_PARSER, "formula")


def parse_tptp(text: str) -> list:
    """Parse a whole TPTP problem into a list of :class:`TptpFormula` records.

    Args:
        text: the contents of a TPTP problem — one or more ``fof(...)`` / ``cnf(...)``
            statements (``%`` line comments and ``/* */`` block comments are ignored).

    Returns:
        A list of :class:`TptpFormula` ``(name, role, formula)`` in source order.

    Raises:
        ParsingError: if the text is not a well-formed TPTP problem.
    """
    return _parse(text, _FILE_PARSER, "problem")


def load_tptp(path: str) -> list:
    """Read a TPTP problem file and :func:`parse_tptp` its contents.

    Args:
        path: path to a ``.p`` / ``.tptp`` file.

    Returns:
        A list of :class:`TptpFormula` records.
    """
    with open(path, "r", encoding="utf-8") as handle:
        return parse_tptp(handle.read())
