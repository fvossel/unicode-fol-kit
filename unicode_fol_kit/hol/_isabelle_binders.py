"""The names an Isabelle writer gives its binders, kept off every symbol of the theory.

An Isabelle binder ``\\<forall>x::i.`` or ``\\<lambda>x::i.`` shadows a constant ``x`` inside its own
scope, so a binder that is spelled like a constant, a function, a predicate or one of the embedding's
own abbreviations captures it: ``∀x P(x, c_x)`` written as ``\\<forall>x::i. (P x x)`` is the formula
``∀x P(x, x)``. The writers of the second order, the third order and the third-order modal embedding
print the names of the source, so each of them asks this module for the name of every binder: the
source name when no symbol of the theory is spelled like it, a suffixed variant (``x_2``) when one is.

A binder is either a VARIABLE (an object quantifier, a lambda parameter, the variable of a
cardinality term: all individuals, one namespace) or a PREDICATE variable (bound by a second-order
quantifier). Two binders of one kind and one name are one token: shadowing means the same in the
text as in the source. A variable and a predicate variable of one name get two tokens.
"""

import re
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Tuple

from ..fol._symbol_names import dedupe
from ..fol.nodes import (
    Node, Quantifier, Cardinality, SortedCardinality, Lambda, SecondOrderQuantifier,
)

__all__ = ["VARIABLE", "PREDICATE", "declared_names", "binder_tokens", "collect_binders",
           "BinderScope"]

VARIABLE = "variable"
PREDICATE = "predicate"

_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
_DECLARATION = re.compile(r"^\s*(?:consts|abbreviation|definition|fun|primrec|inductive)\s+"
                          r"([A-Za-z][A-Za-z0-9_']*)")

#: Names the writers' own text gives a meaning to inside a binder's scope.
_BUILT_IN = frozenset({"True", "False", "card"})


def declared_names(lines: Iterable[str]) -> FrozenSet[str]:
    """The names that the declarations among ``lines`` (``consts``, ``abbreviation``, …) introduce.

    These are the symbols of the theory a binder must keep clear of; they are read off the text
    the writer emits, so a symbol added to the vocabulary later is covered without being listed.
    """
    names = set(_BUILT_IN)
    for line in "\n".join(lines).splitlines():      # an element may hold several lines
        match = _DECLARATION.match(line)
        if match:
            names.add(match.group(1))
    return frozenset(names)


def _identifier(name: str) -> str:
    """``name`` as a legal Isabelle identifier: letters, digits and underscores, a letter first."""
    if _IDENTIFIER.match(name):
        return name
    safe = "".join(c if (c.isascii() and (c.isalnum() or c == "_")) else "_" for c in name)
    return safe if safe[:1].isalpha() else "v" + safe


def binder_tokens(binders: Iterable[Tuple[str, str]],
                  taken: Iterable[str]) -> Dict[Tuple[str, str], str]:
    """The name each binder is printed under, ``{(kind, name): token}``.

    ``binders`` are ``(kind, name)`` pairs, ``kind`` being :data:`VARIABLE` or :data:`PREDICATE`;
    ``taken`` are the names of the theory (:func:`declared_names`). The token of a binder is its
    own name (as a legal identifier) unless that is taken, by a symbol or by the token of another
    binder, in which case it is the first of ``name_2``, ``name_3``, … that is not. The order of
    ``binders`` does not matter: they are claimed in sorted order.
    """
    used = set(taken)
    tokens: Dict[Tuple[str, str], str] = {}
    for kind, name in sorted(set(binders), key=lambda b: (b[1], b[0])):
        tokens[(kind, name)] = dedupe(_identifier(name), used)
    return tokens


class BinderScope:
    """The binders in scope at one point of a formula, and the names they are printed under.

    Immutable: :meth:`enter` returns the scope inside a binder. An occurrence of a variable is
    printed under its binder's token when a binder of that name encloses it, and under
    ``default`` otherwise (a free individual, declared as a constant of its own name).
    """

    __slots__ = ("_tokens", "_in_scope")

    def __init__(self, tokens: Mapping[Tuple[str, str], str],
                 in_scope: Optional[Mapping[Tuple[str, str], str]] = None):
        self._tokens = tokens
        self._in_scope: Dict[Tuple[str, str], str] = dict(in_scope or {})

    def enter(self, kind: str, name: str) -> Tuple[str, "BinderScope"]:
        """``(token, scope inside the binder)`` for a binder of ``kind`` and ``name``: its token
        when it has one, its own name when it has none."""
        token = self._tokens.get((kind, name), name)
        inner = dict(self._in_scope)
        inner[(kind, name)] = token
        return token, BinderScope(self._tokens, inner)

    def token(self, kind: str, name: str, default: Optional[str] = None) -> str:
        """The token of the enclosing binder of ``kind`` and ``name``, else ``default``
        (``name`` itself when no default is given)."""
        found = self._in_scope.get((kind, name))
        if found is not None:
            return found
        return name if default is None else default


def collect_binders(formulas: Iterable[Node]) -> List[Tuple[str, str]]:
    """Every binder of ``formulas``, as ``(kind, name)``.

    An object quantifier, a cardinality term and a lambda abstraction bind a VARIABLE (the name
    of its ``variable`` or ``param``); a second-order quantifier binds a PREDICATE variable
    (its ``predicate``).
    """
    found: List[Tuple[str, str]] = []
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, (Quantifier, Cardinality, SortedCardinality)):
                found.append((VARIABLE, node.variable.name))
            elif isinstance(node, Lambda):
                found.append((VARIABLE, node.param.name))
            elif isinstance(node, SecondOrderQuantifier):
                found.append((PREDICATE, node.predicate))
    return found
