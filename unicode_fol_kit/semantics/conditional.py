"""Counterfactual conditionals — Lewis / Stalnaker sphere semantics.

The material conditional gets counterfactuals wrong: "if kangaroos had no tails they
would topple over" is not made true by kangaroos having tails. **Counterfactuals**
``A □→ B`` ("if A were the case, B would be") are evaluated over a *similarity*
ordering of worlds: from the actual world ``w`` you look at the **closest** worlds
where ``A`` holds and check that ``B`` holds throughout them.

This module uses Lewis's **system of spheres**: each world ``w`` carries a nested
sequence of sets of worlds ``$_w$`` (innermost first, ``w`` in the innermost), read as
"increasingly distant neighbourhoods". The truth condition (finite version)::

    w ⊨ A □→ B   iff   no sphere of w contains an A-world (vacuously true),
                       or, for the smallest sphere S that does, every A-world in S is a B-world.

The "might" counterfactual is the dual ``A ◇→ B ≡ ¬(A □→ ¬B)``. Antecedents and
consequents are ordinary propositional formulas (atoms, ¬ ∧ ∨ → ↔). With a single
innermost sphere ``{closest A-world}`` this is Stalnaker's semantics; with ties it is
Lewis's.

Public API: :class:`CounterfactualModel`, :func:`would`, :func:`might`.
"""

from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff


@dataclass(frozen=True)
class CounterfactualModel:
    """A Lewis sphere model over a set of worlds.

    ``valuation`` maps each world to the set of atom keys (``atom.to_unicode_str()``)
    true there. ``spheres`` maps each world ``w`` to its nested system of spheres — a
    list of frozensets ordered **innermost (closest) first**, each a superset of the
    previous, with ``w`` in the first. A world omitted from ``spheres`` is taken to
    have the single sphere ``{w}``.
    """

    worlds: Tuple[Any, ...]
    valuation: Dict[Any, FrozenSet[str]]
    spheres: Dict[Any, List[FrozenSet[Any]]]

    def sphere_system(self, world: Any) -> List[FrozenSet[Any]]:
        """The nested spheres around ``world`` (default ``[{world}]``)."""
        return self.spheres.get(world, [frozenset({world})])


def _eval(formula: Node, true_atoms: FrozenSet[str]) -> bool:
    """Evaluate a propositional formula against the atoms true at one world."""
    if isinstance(formula, Atom):
        return formula.to_unicode_str() in true_atoms
    if isinstance(formula, Not):
        return not _eval(formula.formula, true_atoms)
    if isinstance(formula, And):
        return _eval(formula.left, true_atoms) and _eval(formula.right, true_atoms)
    if isinstance(formula, Or):
        return _eval(formula.left, true_atoms) or _eval(formula.right, true_atoms)
    if isinstance(formula, Xor):
        return _eval(formula.left, true_atoms) != _eval(formula.right, true_atoms)
    if isinstance(formula, Implies):
        return (not _eval(formula.left, true_atoms)) or _eval(formula.right, true_atoms)
    if isinstance(formula, Iff):
        return _eval(formula.left, true_atoms) == _eval(formula.right, true_atoms)
    raise TypeError(
        f"conditional: antecedent/consequent must be propositional, got "
        f"{type(formula).__name__}.")


def would(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent □→ consequent`` (Lewis "would" counterfactual).

    Vacuously true if no sphere of ``world`` holds an antecedent-world; otherwise the
    consequent must hold at every antecedent-world of the smallest antecedent-permitting
    sphere.
    """
    def holds_a(w):
        return _eval(antecedent, model.valuation.get(w, frozenset()))

    def holds_c(w):
        return _eval(consequent, model.valuation.get(w, frozenset()))

    for sphere in model.sphere_system(world):
        a_worlds = [w for w in sphere if holds_a(w)]
        if a_worlds:
            return all(holds_c(w) for w in a_worlds)
    return True                                  # no antecedent-world anywhere → vacuous


def might(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent ◇→ consequent`` — the dual ``¬(A □→ ¬B)``."""
    return not would(model, world, antecedent, Not(consequent))
