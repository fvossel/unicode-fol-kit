"""Equality of two formulas up to the names of their bound variables.

Two formulas are the same up to bound names when one is the other with some of its bound
variables renamed (each binder and every occurrence it binds, nothing else). The
comparison replaces every bound occurrence by the distance to its binder (a de Bruijn
index, innermost binder 0), and a free variable, a constant and every other field are
compared as they are.
"""
from dataclasses import fields, is_dataclass

from unicode_logic_kit.fol.nodes import Node

_BINDERS = ("Quantifier", "SortedQuantifier")


def canonical(node, scope=()):
    """A hashable form of ``node`` in which bound variables carry no name.

    ``scope`` holds the names of the enclosing binders, innermost last.
    """
    if isinstance(node, Node):
        kind = type(node).__name__
        if kind == "Variable":
            for distance, name in enumerate(reversed(scope)):
                if name == node.name:
                    return ("bound", distance)
            return ("free", node.name)
        if kind in _BINDERS:
            rest = tuple(
                (field.name, canonical(getattr(node, field.name), scope + (node.variable.name,)))
                for field in fields(node) if field.name != "variable")
            return (kind, rest)
        if is_dataclass(node):
            return (kind, tuple((field.name, canonical(getattr(node, field.name), scope))
                                for field in fields(node)))
    if isinstance(node, (list, tuple)):
        return tuple(canonical(item, scope) for item in node)
    return node


def same_up_to_bound_names(left, right) -> bool:
    """Whether ``left`` and ``right`` differ at most in the names of bound variables."""
    return canonical(left) == canonical(right)
