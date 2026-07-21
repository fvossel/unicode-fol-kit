"""Shared symbol-name de-collision for the HOL / THF / Isabelle exporters.

Every exporter that sanitises predicate / constant / function names into a target
syntax must guarantee that **distinct source symbols never collapse to one emitted
name** — otherwise a non-valid formula could be emitted as a tautology (e.g. ``□Ab →
□ab`` collapsing to ``□ab → □ab``) or produce duplicate / ill-typed declarations. This
module factors out the two pieces that were duplicated across those exporters:

- :func:`dedupe` — assign a unique identifier by suffixing ``_2``, ``_3``, …;
- :class:`SymbolNames` — collect every ``(kind, name, arity)`` symbol of a formula and
  map each to a unique functor, keyed so a predicate used at two arities is two symbols.
  Parameterised by the target's base sanitiser and its alias map, so the THF and
  Isabelle resolvers are one shared implementation.
"""

from typing import Callable

from .nodes import Atom, Constant, Number, Function, Node


def dedupe(base: str, used: set) -> str:
    """Return ``base`` (or ``base_2``, ``base_3``, …) not already in ``used``; mark it used."""
    name, i = base, 2
    while name in used:
        name, i = f"{base}_{i}", i + 1
    used.add(name)
    return name


class SymbolNames:
    """Map each distinct ``(kind, name, arity)`` symbol of ``formula`` to a unique name.

    ``sanitize`` turns a raw name into a (possibly non-injective) target identifier;
    ``alias`` is the set/mapping of names that should claim their natural sanitised form
    first (e.g. ``=`` → ``feq``), so a user symbol that sanitises to the same stem is
    pushed off it rather than the other way round. Predicates are keyed by
    ``(name, arity)`` so a predicate used at two arities yields two distinct symbols.

    ``reserved`` pre-claims the target's OWN fixed identifiers (built-in functors,
    relation names, defined operators), so a user symbol that sanitises onto one of
    them is pushed to a suffixed variant instead of silently colliding with — and
    re-typing — a built-in (e.g. a user predicate named ``r`` colliding with the THF
    accessibility relation ``r``, which would emit two conflicting declarations).
    """

    def __init__(self, formula: Node, sanitize: Callable[[str], str], alias=frozenset(),
                 reserved=frozenset()):
        preds, consts, funcs = set(), set(), set()
        for n in formula.walk():
            if isinstance(n, Atom):
                preds.add((n.predicate, len(n.args)))
            elif isinstance(n, Constant):
                consts.add(n.name)
            elif isinstance(n, Number):
                consts.add("n" + str(n.value))
            elif isinstance(n, Function):
                funcs.add((n.name, len(n.args)))
        used: set = set(reserved)
        self.pred, self.const, self.func = {}, {}, {}
        for key in sorted(preds, key=lambda k: (k[0] not in alias, k)):
            self.pred[key] = dedupe(sanitize(key[0]), used)
        for name in sorted(consts):
            self.const[name] = dedupe(sanitize(name), used)
        for key in sorted(funcs):
            self.func[key] = dedupe(sanitize(key[0]), used)

    def atom(self, node: Atom) -> str:
        return self.pred[(node.predicate, len(node.args))]

    def constant(self, name: str) -> str:
        return self.const[name]

    def function(self, node) -> str:
        return self.func[(node.name, len(node.args))]
