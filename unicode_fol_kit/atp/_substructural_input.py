"""What the propositional substructural calculi read, and what they refuse.

Intuitionistic linear logic (:mod:`~unicode_fol_kit.atp.linear`) and the Lambek calculus
(:mod:`~unicode_fol_kit.atp.lambek`) decide derivability between formulas built from
CATEGORIES by the calculus' own connectives. "No derivation" is a statement about a sequent
the calculus can state, so each calculus reads exactly the node classes it has rules for, and
refuses every other node by name.

What each calculus reads (the two allow-lists, :data:`ILL` and :data:`LAMBEK`):

* intuitionistic linear logic: the connectives ``⊗`` (``Tensor``), ``&`` (``With``), ``⊕``
  (``OPlus``), ``⊸`` (``LinearImplies``), ``!`` (``OfCourse``) and the units ``𝟙`` (``One``),
  ``⊤`` (``Top``), ``𝟘`` (``Zero``), over atoms;
* the Lambek calculus: the connectives ``•`` (``Product``), ``\\`` (``Under``) and ``/``
  (``Over``), over atoms.

These are the node classes the two grammars (``MSFLParser(linear=True)`` and
``MSFLParser(lambek=True)``) produce, and the classes the proof checkers and the Isabelle export
of the two calculi have rules for; nothing either grammar can write is refused. An atom is read
with its terms (variables, constants, numerals and function terms) as written.

Both calculi are propositional: a sequent has no individuals to quantify over, no counting and
no identity. An atom over terms (``P(alpha)``, ``Loves(john, mary)``, ``Q(f(x))``, a free
variable included) is read as ONE category, identified by its predicate and its terms as
written. That reading is sound in both directions: a quantifier-free, equality-free sequent has
no rule that substitutes a term for another, so its first-order derivations and its
propositional derivations over those categories are the same derivations, and a sequent with no
derivation of the one kind has none of the other.

Every other node is refused, in three kinds.

* A quantifier, a counting or cardinality node, a sorted constant. Read as one more opaque
  category they make a derivability verdict about ANOTHER formula: ``∀x P(x) ⊢ P(alpha)``
  holds in first-order linear logic (instantiation) and has no derivation between the two
  categories ``∀x P(x)`` and ``P(alpha)``. A sorted constant ``c:S`` asserts ``S(c)``, which the
  category reading drops.
* An equality or disequality atom: ``⊢ alpha = alpha`` holds with identity and has no derivation
  between categories.
* A node of any other logic: a classical connective (``And``, ``Or``, ``Not``, ``Implies``,
  ``Iff``, ``Xor``), a modal, temporal, epistemic or hybrid operator, a connective of the other
  calculus, a lambda, an application or a predicate in argument position (the lambda layer is
  the one thing both grammars write besides their connectives and atoms: ``(λx. P(x))(a) ⊢ P(a)``
  holds by beta reduction and has no derivation between the category of an application and the
  category ``P(a)``). Neither calculus has a rule for it; ``And(A, B) ⊢ A`` holds classically
  and has no derivation between the categories ``And(A, B)`` and ``A``. A term (a variable, a
  constant, a numeral, a function term) where a formula stands is refused as well: it is not
  an atom, and only an atom is a category.

:func:`refuse_unreadable_input` names such a node, its class and the calculus, lists the
connectives the calculus has, and says what to do instead.
"""

from dataclasses import dataclass
from typing import Iterable, Optional, Tuple

from ..fol._linear_nodes import Top, Zero
from ..fol.nodes import (
    Atom, Cardinality, Constant, Count, Function, LinearImplies, Node, Number, OfCourse, One,
    OPlus, Over, Product, Quantifier, SecondOrderQuantifier, SlashedExists, SortedCardinality,
    SortedConstant, SortedCount, SortedQuantifier, Tensor, Under, Variable, With,
)
from ..semantics._modal_reject import is_equality_atom

__all__ = ["Calculus", "ILL", "LAMBEK", "refuse_unreadable_input", "unreadable_reason"]


@dataclass(frozen=True)
class Calculus:
    """A propositional substructural calculus, by what it has rules for.

    Fields:

    * ``name``: how a message calls the calculus.
    * ``connectives``: the node classes the calculus has rules for (atoms are read besides).
    * ``glyphs``: those connectives as the calculus' own grammar writes them.
    """

    name: str
    connectives: Tuple[type, ...]
    glyphs: str


#: Intuitionistic linear logic: the connectives of the ``linear`` grammar.
ILL = Calculus(
    "intuitionistic linear logic",
    (Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero),
    "⊗ & ⊕ ⊸ ! 𝟙 ⊤ 𝟘")

#: The Lambek calculus: the connectives of the ``lambek`` grammar.
LAMBEK = Calculus("the Lambek calculus", (Product, Under, Over), "• \\ /")

#: The node classes of an atom's terms, read as written inside the category.
_TERMS: Tuple[type, ...] = (Variable, Constant, Number, Function)

#: The first-order node classes refused wherever they stand, with what each is called in a message.
_FIRST_ORDER: Tuple[Tuple[Tuple[type, ...], str], ...] = (
    ((Quantifier, SortedQuantifier, SecondOrderQuantifier, SlashedExists), "quantifier"),
    ((Count, SortedCount), "counting quantifier"),
    ((Cardinality, SortedCardinality), "cardinality term"),
    ((SortedConstant,), "sorted constant"),
)

#: The longest rendering of a refused node a message quotes.
_QUOTE_LIMIT = 100


def _first_order_label(node: Node) -> Optional[str]:
    """What a first-order node is called, or ``None`` for any other node."""
    for classes, label in _FIRST_ORDER:
        if isinstance(node, classes):
            return label
    return None


def _quote(node: Node) -> str:
    """The node's own rendering, shortened for a message."""
    text = node.to_unicode_str()
    return text if len(text) <= _QUOTE_LIMIT else text[:_QUOTE_LIMIT - 1] + "…"


def _outside(node: Node, calculus: Calculus, formula_position: bool = True) -> Optional[Node]:
    """The first node, in pre-order, that is not read where it stands, or ``None``.

    A formula is an atom or a connective of the calculus whose operands are formulas; the
    arguments of an atom are terms (variables, constants, numerals and function terms over
    terms). Any other node, and a term where a formula stands, is outside.
    """
    if formula_position:
        if isinstance(node, Atom):
            operands, operand_position = node._child_nodes(), False
        elif isinstance(node, calculus.connectives):
            operands, operand_position = node._child_nodes(), True
        else:
            return node
    elif isinstance(node, _TERMS):
        operands, operand_position = node._child_nodes(), False
    else:
        return node
    for operand in operands:
        found = _outside(operand, calculus, operand_position)
        if found is not None:
            return found
    return None


#: The kinds of refusal, in the order they are looked for.
_FIRST_ORDER_KIND, _OUTSIDE_KIND, _IDENTITY_KIND = "first order", "outside", "identity"


def _first_refused(formulas: Tuple[Node, ...], calculus: Calculus) -> Optional[Tuple[Node, str, str]]:
    """The first node ``calculus`` cannot read, what it is called, and the kind of refusal it gets.

    The kinds, in the order they are looked for: first order (a quantifier, a count, a
    cardinality, a sorted constant), outside (a node of another logic, or a term where a formula
    stands), identity (an equality or disequality atom). An identity atom that merely holds a
    refused term (``|{v : P(v)}| = 2``) is reported through that term, which says more than the
    comparison around it, and a quantifier that holds a classical connective is reported as the
    quantifier.
    """
    nodes = [node for formula in formulas for node in formula.walk()]
    for node in nodes:
        label = _first_order_label(node)
        if label is not None:
            return node, label, _FIRST_ORDER_KIND
    for formula in formulas:
        outside = _outside(formula, calculus)
        if outside is not None:
            label = "term where a formula stands" if isinstance(outside, _TERMS) else "node of another logic"
            return outside, label, _OUTSIDE_KIND
    for node in nodes:
        if is_equality_atom(node):
            return node, "equality atom" if node.predicate == "=" else "disequality atom", _IDENTITY_KIND
    return None


def unreadable_reason(formulas: Iterable[Node], route: str, calculus: Calculus) -> Optional[str]:
    """Why ``calculus`` cannot read ``formulas``, or ``None`` when it can.

    The text :func:`refuse_unreadable_input` raises, for a caller that reports a refusal as an
    answer instead of an exception (a backend, a proof checker).
    """
    found = _first_refused(tuple(formulas), calculus)
    if found is None:
        return None
    node, what, kind = found
    name = type(node).__name__
    head = (f"{route}: the {what} {_quote(node)!r} ({name}) is refused by name — "
            f"{calculus.name} has the connectives {calculus.glyphs} over categories")
    if kind != _OUTSIDE_KIND:
        return (
            f"{head}, with no individuals, quantifiers, counting, sorts or identity, and reading "
            "the node as one more opaque category would answer about another formula "
            "(∀x P(x) ⊢ P(alpha) holds in every first-order reading and has no derivation "
            "between the two categories). Decide it with a first-order route (z3, vampire, "
            "eprover, tableau, resolution), or write the category as an atom over terms, "
            "without the quantifier, count, sort or identity.")
    if isinstance(node, _TERMS):
        return (
            f"{head}, and a term is not one of them: reading {name} as a category would answer "
            "about another formula. Write the category as an atom, a predicate over terms.")
    return (
        f"{head}, and has no rule for {name}: it belongs to another logic (or to the lambda "
        "layer every grammar shares), and "
        "reading it as one more opaque category would answer about another formula "
        "(And(A, B) ⊢ A holds classically and has no derivation between the categories "
        "And(A, B) and A). Decide it with a route of the logic the node belongs to "
        "(list_backends names them), or write it with the connectives "
        f"{calculus.glyphs} of {calculus.name}.")


def refuse_unreadable_input(formulas: Iterable[Node], route: str, calculus: Calculus) -> None:
    """Raise ``NotImplementedError`` naming the first node ``calculus`` cannot read, if any.

    ``formulas`` are the antecedent formulas and the goal of one sequent. ``calculus`` reads the
    node classes it has rules for (:data:`ILL`, :data:`LAMBEK`) and atoms over terms; a
    quantifier (sorted, second-order or slashed), a counting or cardinality node, a sorted
    constant, an equality or disequality atom and a node of any other logic are refused (see the
    module docstring for the two allow-lists and for why an atom over terms is sound). ``route``
    names the function or backend that refuses. The message quotes the node, names its class and
    the calculus, lists the connectives the calculus has and says what to do instead. Returns
    ``None`` when every formula is readable.

    Raises:
        NotImplementedError: a node of one of the refused kinds occurs in ``formulas``.
    """
    reason = unreadable_reason(formulas, route, calculus)
    if reason is not None:
        raise NotImplementedError(reason)
