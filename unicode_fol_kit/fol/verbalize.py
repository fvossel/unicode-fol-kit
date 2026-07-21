"""Verbalize a formula as an English sentence (a readability aid, not a parse inverse).

``to_english(node)`` renders a formula with structural English templates: ``∀x φ`` →
"for every x, …", ``A → B`` → "if A, then B", a unary atom ``Human(x)`` → "x is
human", an equality → "a is equal to b", and so on. It is deliberately predictable
rather than fluent, and — unlike ``to_unicode_str``/``parse`` — it is **not** an exact
round-trip: the English phrasing of nested connectives can be ambiguous. Use it to
explain a formula, not to re-parse one.

Public API: :func:`to_english`.
"""

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
    SortedQuantifier, SortedConstant,
    Count, Measure, Cardinality, Contrast,
    SortedCount, SortedCardinality,
    Nominal, At,
    Dependence, SlashedExists,
    Tensor, With, OPlus, LinearImplies, OfCourse, One,
    Product, Under, Over,
    Box, Diamond, Knows, Believes, Says, Wants, Obligatory, Permitted,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Would, Might,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
)
from ._so_nodes import SecondOrderQuantifier
from ._modal_nodes import Announce, AnnounceDiamond


# Counting-quantifier op codes → English determiner phrases.
_COUNT_WORDS = {"ge": "at least", "le": "at most", "eq": "exactly"}


# Comparison / equality predicates rendered with an English copula.
_COPULA = {
    "=": ("is equal to", "is not equal to"),
    "≠": ("is not equal to", "is equal to"),
    "<": ("is less than", "is not less than"),
    ">": ("is greater than", "is not greater than"),
    "≤": ("is at most", "is greater than"),
    "≥": ("is at least", "is less than"),
}


def _term(node: Node) -> str:
    """Render a term in a readable form."""
    if isinstance(node, (Variable, Constant, SortedConstant)):
        return node.name
    if isinstance(node, Number):
        return str(node.value)
    if isinstance(node, Function):
        return f"{node.name}({', '.join(_term(a) for a in node.args)})"
    if isinstance(node, Measure):
        return f"the {_term(node.dimension)} of {_term(node.entity)}"
    if isinstance(node, Cardinality):
        return f"the number of {node.variable.name} such that {to_english(node.formula)}"
    if isinstance(node, SortedCardinality):
        return (f"the number of {node.variable.name} of sort {node.sort} such that "
                f"{to_english(node.formula)}")
    return node.to_unicode_str()


def _atom(node: Atom, negated: bool = False) -> str:
    """Render an atom (optionally negated) in English."""
    pred, args = node.predicate, node.args
    if pred in _COPULA and len(args) == 2:
        phrase = _COPULA[pred][1 if negated else 0]
        return f"{_term(args[0])} {phrase} {_term(args[1])}"
    if len(args) == 0:
        body = pred
        return f"it is not the case that {body}" if negated else body
    if len(args) == 1:
        # "x is human" / "x is not human"
        prop = pred.lower()
        return f"{_term(args[0])} is {'not ' if negated else ''}{prop}"
    call = f"{pred}({', '.join(_term(a) for a in args)})"
    return f"it is not the case that {call}" if negated else call


def _needs_clause(node: Node) -> bool:
    """True if a sub-formula should be wrapped as a parenthetical clause for clarity."""
    return isinstance(node, (And, Or, Xor, Implies, Iff))


def _sub(node: Node) -> str:
    """Render a sub-formula, parenthesising a nested binary connective."""
    text = to_english(node)
    return f"({text})" if _needs_clause(node) else text


def to_english(node: Node) -> str:
    """Return an English paraphrase of ``node`` (best-effort, not a parse inverse)."""
    if isinstance(node, Atom):
        return _atom(node)

    if isinstance(node, Not):
        inner = node.formula
        if isinstance(inner, Atom):
            return _atom(inner, negated=True)
        return f"it is not the case that {_sub(inner)}"

    if isinstance(node, And):
        return f"{_sub(node.left)} and {_sub(node.right)}"

    if isinstance(node, Or):
        return f"{_sub(node.left)} or {_sub(node.right)}"

    if isinstance(node, Xor):
        return f"either {_sub(node.left)} or {_sub(node.right)}, but not both"

    if isinstance(node, Contrast):
        return f"{_sub(node.left)}, whereas {_sub(node.right)}"

    if isinstance(node, Implies):
        return f"if {_sub(node.left)}, then {_sub(node.right)}"

    if isinstance(node, Iff):
        return f"{_sub(node.left)} if and only if {_sub(node.right)}"

    if isinstance(node, SortedQuantifier):
        kind = "every" if node.type in ("∀", "forall") else "some"
        return f"for {kind} {node.variable.name} of sort {node.sort}, {to_english(node.formula)}"

    if isinstance(node, Quantifier):
        if node.type in ("∀", "forall"):
            return f"for every {node.variable.name}, {to_english(node.formula)}"
        return f"for some {node.variable.name}, {to_english(node.formula)}"

    if isinstance(node, Count):
        return (f"there are {_COUNT_WORDS[node.op]} {node.n.value} {node.variable.name} "
                f"such that {to_english(node.formula)}")

    if isinstance(node, SortedCount):
        return (f"there are {_COUNT_WORDS[node.op]} {node.n.value} {node.variable.name} "
                f"of sort {node.sort} such that {to_english(node.formula)}")

    if isinstance(node, SecondOrderQuantifier):
        kind = "every" if node.type in ("∀", "forall") else "some"
        return f"for {kind} {node.arity}-ary predicate {node.predicate}, {to_english(node.formula)}"

    # --- modal / temporal / epistemic / doxastic / deontic ---
    if isinstance(node, Box):
        return f"necessarily, {_sub(node.formula)}"
    if isinstance(node, Diamond):
        return f"possibly, {_sub(node.formula)}"
    if isinstance(node, Knows):
        return f"agent {_term(node.agent)} knows that {_sub(node.formula)}"
    if isinstance(node, Believes):
        return f"agent {_term(node.agent)} believes that {_sub(node.formula)}"
    if isinstance(node, Says):
        return f"agent {_term(node.agent)} says that {_sub(node.formula)}"
    if isinstance(node, Wants):
        return f"agent {_term(node.agent)} wants it to be that {_sub(node.formula)}"
    if isinstance(node, Obligatory):
        return f"it is obligatory that {_sub(node.formula)}"
    if isinstance(node, Permitted):
        return f"it is permitted that {_sub(node.formula)}"
    if isinstance(node, Always):
        return f"it will always be the case that {_sub(node.formula)}"
    if isinstance(node, Eventually):
        return f"it will eventually be the case that {_sub(node.formula)}"
    if isinstance(node, Next):
        return f"at the next moment, {_sub(node.formula)}"
    if isinstance(node, Until):
        return f"{_sub(node.left)} until {_sub(node.right)}"
    if isinstance(node, Historically):
        return f"it has always been the case that {_sub(node.formula)}"
    if isinstance(node, Once):
        return f"it was once the case that {_sub(node.formula)}"
    if isinstance(node, Previous):
        return f"at the previous moment, {_sub(node.formula)}"
    if isinstance(node, Since):
        return f"{_sub(node.left)} since {_sub(node.right)}"

    # --- public announcement logic (PAL) ---
    if isinstance(node, Announce):
        return (f"after it is truthfully announced that {to_english(node.announcement)}, "
                f"{_sub(node.formula)}")
    if isinstance(node, AnnounceDiamond):
        return (f"{to_english(node.announcement)}, and after it is truthfully "
                f"announced, {_sub(node.formula)}")

    # --- counterfactual conditionals (subjunctive, not material) ---
    if isinstance(node, Would):
        return f"if {_sub(node.left)} were the case, {_sub(node.right)} would be"
    if isinstance(node, Might):
        return f"if {_sub(node.left)} were the case, {_sub(node.right)} might be"

    # --- hybrid (nominals and @) ---
    if isinstance(node, Nominal):
        return f"this is world {node.name}"
    if isinstance(node, At):
        return f"at world {node.nominal.name}, {_sub(node.formula)}"

    # --- dependence / IF (team semantics) ---
    if isinstance(node, Dependence):
        if len(node.args) == 1:
            return f"the value of {_term(node.args[0])} is constant"
        deps = ", ".join(_term(a) for a in node.args[:-1])
        return (f"the value of {_term(node.args[-1])} is functionally "
                f"determined by {deps}")
    if isinstance(node, SlashedExists):
        indep = ", ".join(node.slashed)
        return (f"for some {node.variable.name} chosen independently of "
                f"{indep}, {to_english(node.formula)}")

    # --- linear logic (resource reading) ---
    if isinstance(node, Tensor):
        return f"{_sub(node.left)} together with {_sub(node.right)}"
    if isinstance(node, With):
        return f"a free choice between {_sub(node.left)} and {_sub(node.right)}"
    if isinstance(node, OPlus):
        return f"{_sub(node.left)} or else {_sub(node.right)}"
    if isinstance(node, LinearImplies):
        return f"consuming {_sub(node.left)} yields {_sub(node.right)}"
    if isinstance(node, OfCourse):
        return f"an unlimited supply of {_sub(node.formula)}"
    if isinstance(node, One):
        return "the empty resource"

    # --- Lambek calculus (categorial reading) ---
    if isinstance(node, Product):
        return f"{_sub(node.left)} followed by {_sub(node.right)}"
    if isinstance(node, Under):
        return (f"something that combines with {_sub(node.left)} on its left "
                f"to give {_sub(node.right)}")
    if isinstance(node, Over):
        return (f"something that combines with {_sub(node.right)} on its right "
                f"to give {_sub(node.left)}")

    # --- fuzzy (Łukasiewicz): name the strong/weak/Łukasiewicz operators so they do
    # NOT read as their classical look-alikes ---
    if isinstance(node, LukNegation):
        return f"it is fuzzily not the case that {_sub(node.formula)}"
    if isinstance(node, WeakConjunction):
        return f"{_sub(node.left)} and weakly {_sub(node.right)}"
    if isinstance(node, WeakDisjunction):
        return f"{_sub(node.left)} or weakly {_sub(node.right)}"
    if isinstance(node, StrongConjunction):
        return f"{_sub(node.left)} and strongly {_sub(node.right)}"
    if isinstance(node, StrongDisjunction):
        return f"{_sub(node.left)} or strongly {_sub(node.right)}"
    if isinstance(node, LukImplication):
        return f"if {_sub(node.left)} then fuzzily {_sub(node.right)}"
    if isinstance(node, LukEquivalence):
        return f"{_sub(node.left)} is fuzzily equivalent to {_sub(node.right)}"

    # Anything else (e.g. lambda) falls back to its glyph form.
    return node.to_unicode_str()
