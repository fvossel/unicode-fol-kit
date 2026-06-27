"""Intuitionistic propositional logic — Kripke semantics and a validity/countermodel search.

Intuitionistic logic drops the law of excluded middle and double-negation elimination;
its models are **Kripke models**: a partial order of *worlds* (stages of knowledge)
with a **monotone** forcing relation (once an atom is forced at a world it is forced at
every later world). The connectives ``→`` and ``¬`` quantify over future worlds, which
is exactly what makes ``P ∨ ¬P`` and ``¬¬P → P`` fail.

- :class:`IntKripkeModel` — build a model and ask ``model.forces(world, φ)``.
- :func:`int_valid` — is ``φ`` intuitionistically valid? Decided by searching every
  small Kripke model (intuitionistic propositional logic has the finite-model property,
  so this is a genuine decision procedure up to ``max_worlds`` worlds).
- :func:`int_countermodel` — a model + world where ``φ`` fails (a witness that it is
  *not* intuitionistically valid), or None.

Propositional only — each atom (by surface form) is a propositional variable; quantified
formulas are rejected. Every intuitionistic validity is also classically valid (a
one-world model is a classical valuation), which the test-suite cross-checks.

Public API: :class:`IntKripkeModel`, :func:`int_valid`, :func:`int_countermodel`.
"""

from dataclasses import dataclass
from itertools import combinations, product
from typing import Dict, FrozenSet, List, Optional, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, SortedQuantifier
from ..fol._so_nodes import SecondOrderQuantifier


def _check_propositional(formula: Node) -> None:
    """Raise ValueError if ``formula`` contains a quantifier (FOL is out of scope here)."""
    for node in formula.walk():
        if isinstance(node, (Quantifier, SortedQuantifier, SecondOrderQuantifier)):
            raise ValueError(
                "intuitionistic: only propositional formulas are supported "
                "(quantified intuitionistic logic needs varying domains, out of scope)."
            )


@dataclass(frozen=True)
class IntKripkeModel:
    """A finite intuitionistic Kripke model over worlds ``0 .. n-1``.

    ``upset[w]`` is the set of worlds accessible from ``w`` (its up-set in the partial
    order, reflexive and transitive — including ``w`` itself). ``valuation[key]`` is the
    up-closed set of worlds forcing the atom ``key`` (its surface form). Build directly,
    or let :func:`int_countermodel` produce one.
    """

    upset: Dict[int, FrozenSet[int]]
    valuation: Dict[str, FrozenSet[int]]

    def forces(self, world: int, formula: Node) -> bool:
        """Return whether ``world`` forces ``formula`` (the intuitionistic clauses)."""
        if isinstance(formula, Atom):
            return world in self.valuation.get(formula.to_unicode_str(), frozenset())
        if isinstance(formula, And):
            return self.forces(world, formula.left) and self.forces(world, formula.right)
        if isinstance(formula, Or):
            return self.forces(world, formula.left) or self.forces(world, formula.right)
        if isinstance(formula, Implies):
            # w ⊩ A→B  iff  for every w' ≥ w, w' ⊩ A implies w' ⊩ B.
            return all(self.forces(w2, formula.right)
                       for w2 in self.upset[world] if self.forces(w2, formula.left))
        if isinstance(formula, Not):
            # w ⊩ ¬A  iff  no w' ≥ w forces A.
            return not any(self.forces(w2, formula.formula) for w2 in self.upset[world])
        if isinstance(formula, Iff):
            return (self.forces(world, Implies(formula.left, formula.right))
                    and self.forces(world, Implies(formula.right, formula.left)))
        if isinstance(formula, Xor):
            # Defined intuitionistically as (A ∨ B) ∧ ¬(A ∧ B).
            a, b = formula.left, formula.right
            return self.forces(world, And(Or(a, b), Not(And(a, b))))
        raise ValueError(f"intuitionistic forcing: unsupported node "
                         f"{type(formula).__name__}")


def _atom_keys(formula: Node) -> List[str]:
    """Distinct atom surface-forms (propositional variables) in ``formula``."""
    keys: List[str] = []
    seen = set()
    for node in formula.walk():
        if isinstance(node, Atom):
            key = node.to_unicode_str()
            if key not in seen:
                seen.add(key)
                keys.append(key)
    return keys


def _partial_orders(n: int):
    """Yield each partial order on ``{0..n-1}`` as a dict ``world -> up-set frozenset``.

    Enumerates reflexive relations and keeps the transitive (and antisymmetric) ones;
    the up-set ``upset[w] = {w' : w ≤ w'}`` is what the forcing clauses consult.
    """
    worlds = list(range(n))
    off_diagonal = [(i, j) for i in worlds for j in worlds if i != j]
    for mask in product((False, True), repeat=len(off_diagonal)):
        leq = {(i, i) for i in worlds}
        leq |= {pair for pair, inc in zip(off_diagonal, mask) if inc}
        # transitivity
        if any((a, b) in leq and (b, c) in leq and (a, c) not in leq
               for a in worlds for b in worlds for c in worlds):
            continue
        # antisymmetry (a genuine partial order; preorders collapse to these for forcing)
        if any(a != b and (a, b) in leq and (b, a) in leq for a in worlds for b in worlds):
            continue
        yield {w: frozenset(j for j in worlds if (w, j) in leq) for w in worlds}


def _monotone_valuations(upset: Dict[int, FrozenSet[int]], keys: List[str]):
    """Yield every monotone (up-closed) valuation of ``keys`` over the order ``upset``."""
    worlds = list(upset)
    # Up-closed subsets: a set S with w∈S ⇒ upset[w] ⊆ S.
    upclosed = []
    for r in range(len(worlds) + 1):
        for combo in combinations(worlds, r):
            s = frozenset(combo)
            if all(upset[w] <= s for w in s):
                upclosed.append(s)
    for choice in product(upclosed, repeat=len(keys)):
        yield dict(zip(keys, choice))


def int_countermodel(formula: Node, max_worlds: int = 3) -> Optional[Tuple[IntKripkeModel, int]]:
    """Return ``(model, world)`` where ``formula`` fails intuitionistically, or None.

    Searches every Kripke model up to ``max_worlds`` worlds; a returned pair witnesses
    that ``formula`` is *not* intuitionistically valid.
    """
    _check_propositional(formula)
    keys = _atom_keys(formula)
    for n in range(1, max_worlds + 1):
        for upset in _partial_orders(n):
            for valuation in _monotone_valuations(upset, keys):
                model = IntKripkeModel(upset, valuation)
                for w in range(n):
                    if not model.forces(w, formula):
                        return model, w
    return None


def int_valid(formula: Node, max_worlds: int = 3) -> bool:
    """Return True iff ``formula`` is intuitionistically valid (no countermodel found).

    A genuine decision procedure for intuitionistic *propositional* logic up to
    ``max_worlds`` worlds (the logic has the finite-model property). ``int_valid(φ)``
    being False is always backed by :func:`int_countermodel`.
    """
    return int_countermodel(formula, max_worlds) is None
