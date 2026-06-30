"""Rewrite AST symbol names to MSFLParser-legal tokens for a round-trippable render.

An imported formula (e.g. from a TPTP file produced by an OWL→FOL translation) can
carry symbol names that the toolkit's AST accepts but the ``MSFLParser`` *lexer* does
not — IRIs with underscores and mixed case (``'http___example_org_Thing'`` →
``Http___example_org_Thing``), single-letter or digit-leading constants, and so on.
Rendering such a node with :meth:`Node.to_unicode_str` then produces a string that does
**not** re-parse.

:func:`sanitize_names` rewrites every symbol name to a token that re-parses to its
intended class, so ``parse(sanitized.to_unicode_str()) == sanitized``:

- **predicates** → ``[A-Z][a-zA-Z0-9]*`` (uppercase-initial, alphanumeric);
- **functions** → a multi-letter lowercase ``NAME``;
- **constants** → kept verbatim if already a legal bare ``NAME``, else the explicit
  ``c_…`` constant form (so a single-letter or digit-bearing constant such as ``a`` /
  ``x1`` does not collapse to a variable on re-parse);
- **variables** → kept if already ``[a-z][0-9]*``, else mapped to ``v0`` / ``v1`` / …

Already-legal names pass through unchanged, so a clean classical formula is untouched.
Distinct original names always map to distinct legal names (collisions get a numeric
suffix), so the rewrite is structure-preserving and the returned :class:`NameMapping`
recovers the originals. Pass the mapping back across calls to keep names consistent over
a whole problem (the same IRI maps to the same token in every formula).

Public API: :func:`sanitize_names`, :func:`sanitize_all`, :class:`NameMapping`.
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .nodes import Node, Variable, Constant, Atom, Function

# Operator-valued predicate / function names are rendered as glyphs, not emitted as
# identifiers, so they are never renamed.
_COMPARISONS = frozenset({"=", "≠", "<", ">", "≤", "≥"})
_ARITH = frozenset({"+", "-", "*", "/"})

# A bare NAME (function symbol or unmarked constant) in MSFLParser: lowercase-initial,
# at least two letters. A VARIABLE is a single lowercase letter with an optional digit
# tail. Used to decide whether a name is already legal in its class.
_NAME_RE = re.compile(r"[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*")
_VAR_RE = re.compile(r"[a-z][0-9]*")
_PRED_RE = re.compile(r"[A-Z][a-zA-Z0-9]*")


def _alnum(name: str) -> str:
    """Keep only the ASCII-alphanumeric characters of ``name``."""
    return "".join(ch for ch in name if ("a" <= ch <= "z") or ("A" <= ch <= "Z") or ch.isdigit())


@dataclass
class NameMapping:
    """The original→legal renamings chosen by :func:`sanitize_names`, per symbol class.

    Each of ``predicate`` / ``function`` / ``constant`` / ``variable`` maps an original
    name to the legal token it was rewritten to. ``used`` is the set of legal tokens
    already handed out (shared across classes so no two symbols ever collide). Reuse one
    instance across calls to keep names consistent over a whole problem.
    """

    predicate: Dict[str, str] = field(default_factory=dict)
    function: Dict[str, str] = field(default_factory=dict)
    constant: Dict[str, str] = field(default_factory=dict)
    variable: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _var_counter: int = 0

    def reverse(self) -> Dict[str, str]:
        """Return a flat ``legal → original`` dict over every class (for recovery)."""
        out: Dict[str, str] = {}
        for table in (self.predicate, self.function, self.constant, self.variable):
            for orig, legal in table.items():
                out[legal] = orig
        return out

    # -- internal --------------------------------------------------------------
    def _reserve(self, candidate: str) -> str:
        """Return ``candidate`` (or ``candidate``+suffix) not yet used; reserve it."""
        if candidate not in self.used:
            self.used.add(candidate)
            return candidate
        i = 2
        while f"{candidate}{i}" in self.used:
            i += 1
        chosen = f"{candidate}{i}"
        self.used.add(chosen)
        return chosen

    def for_predicate(self, name: str) -> str:
        """Legal predicate token for ``name`` (memoised)."""
        if name in self.predicate:
            return self.predicate[name]
        base = _alnum(name)
        if not base or not base[0].isalpha():
            base = "P" + base
        base = base[0].upper() + base[1:]
        legal = self._reserve(base)
        self.predicate[name] = legal
        return legal

    def for_function(self, name: str) -> str:
        """Legal function token (multi-letter lowercase NAME) for ``name`` (memoised)."""
        if name in self.function:
            return self.function[name]
        base = _alnum(name)
        if not base or not base[0].isalpha():
            base = "f" + base
        base = base[0].lower() + base[1:]
        if sum(ch.isalpha() for ch in base) < 2:   # NAME needs >= 2 letters
            base = base + "fn"
        legal = self._reserve(base)
        self.function[name] = legal
        return legal

    def for_constant(self, name: str) -> str:
        """Legal constant token for ``name``: keep a legal bare NAME, else the c_ form."""
        if name in self.constant:
            return self.constant[name]
        if _NAME_RE.fullmatch(name):
            legal = self._reserve(name)            # already a legal bare constant
        else:
            legal = self._reserve("c_" + (_alnum(name) or "0"))
        self.constant[name] = legal
        return legal

    def for_variable(self, name: str) -> str:
        """Legal variable token for ``name``: keep ``[a-z][0-9]*``, else map to v0/v1/…."""
        if name in self.variable:
            return self.variable[name]
        if _VAR_RE.fullmatch(name):
            legal = self._reserve(name)
        else:
            cand = f"v{self._var_counter}"
            self._var_counter += 1
            while cand in self.used:
                cand = f"v{self._var_counter}"
                self._var_counter += 1
            legal = self._reserve(cand)
        self.variable[name] = legal
        return legal


def _rewrite(node: Node, m: NameMapping) -> Node:
    """Rebuild ``node`` with every symbol name replaced via ``m`` (capture-consistent).

    Variables are renamed uniformly by name, so a binder's bound variable and its body
    occurrences get the same legal name — binding structure is preserved without
    per-binder special-casing.
    """
    cls = type(node).__name__
    if cls == "Variable":
        return Variable(m.for_variable(node.name))
    if cls == "Constant":
        return Constant(m.for_constant(node.name))
    if cls == "Atom":
        pred = node.predicate if node.predicate in _COMPARISONS else m.for_predicate(node.predicate)
        return Atom(pred, [_rewrite(a, m) for a in node.args])
    if cls == "Function":
        name = node.name if node.name in _ARITH else m.for_function(node.name)
        return Function(name, [_rewrite(a, m) for a in node.args])
    if cls in ("Number", "LambdaVar"):
        return node
    # Every other node (connectives, quantifiers, binders, modal operators, …) is
    # structural: its bound variable (if any) is a Variable child and is renamed
    # uniformly above, so map_children rebuilds it correctly.
    return node.map_children(lambda c: _rewrite(c, m))


def _collect(node: Node, m: NameMapping) -> None:
    """Pre-register every symbol's legal name in first-occurrence order (deterministic)."""
    for n in node.walk():
        cls = type(n).__name__
        if cls == "Atom" and n.predicate not in _COMPARISONS:
            m.for_predicate(n.predicate)
        elif cls == "Function" and n.name not in _ARITH:
            m.for_function(n.name)
        elif cls == "Constant":
            m.for_constant(n.name)
        elif cls == "Variable":
            m.for_variable(n.name)


def sanitize_names(node: Node, mapping: Optional[NameMapping] = None) -> Tuple[Node, NameMapping]:
    """Return ``(sanitized_node, mapping)`` with all names rewritten to legal tokens.

    ``parse(sanitized_node.to_unicode_str()) == sanitized_node`` holds for the default
    ``MSFLParser`` (FOL mode). Already-legal names are unchanged. Pass the returned
    ``mapping`` back in (``mapping=…``) to keep names consistent across formulas of one
    problem; use :meth:`NameMapping.reverse` to recover the originals.

    Args:
        node: any AST node (typically a classical FOL formula from an importer).
        mapping: an existing :class:`NameMapping` to extend, or ``None`` for a fresh one.

    Returns:
        The rewritten node and the (possibly extended) mapping.
    """
    if mapping is None:
        mapping = NameMapping()
    _collect(node, mapping)
    return _rewrite(node, mapping), mapping


def sanitize_all(nodes, mapping: Optional[NameMapping] = None) -> Tuple[List[Node], NameMapping]:
    """Sanitize a sequence of formulas with one shared, consistent :class:`NameMapping`.

    Returns ``(sanitized_nodes, mapping)``; the same original symbol maps to the same
    legal token in every formula, so a whole TPTP/Prover9 problem stays coherent.
    """
    if mapping is None:
        mapping = NameMapping()
    out = [sanitize_names(n, mapping)[0] for n in nodes]
    return out, mapping
