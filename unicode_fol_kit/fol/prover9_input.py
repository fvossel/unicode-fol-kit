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


_GRAMMAR = r"""
?start: formula

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
