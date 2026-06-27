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
)


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

    # Anything else (modal, lambda, second-order, fuzzy) falls back to its glyph form.
    return node.to_unicode_str()
