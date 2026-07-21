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

``□→`` and ``◇→`` parse in modal mode (``MSFLParser(modal=True)``) as the
:class:`~unicode_fol_kit.fol.nodes.Would` / :class:`~unicode_fol_kit.fol.nodes.Might`
nodes, so a whole formula can be handed to :func:`cf_satisfies` directly; the
sphere ordering is not an accessibility relation, so these nodes have no
first-order export and the Kripke evaluator rejects them.

Public API: :class:`CounterfactualModel`, :func:`cf_satisfies`, :func:`would`,
:func:`might`.
"""

from dataclasses import dataclass
from itertools import product
from typing import Any, Dict, FrozenSet, List, Optional, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff, Would, Might


def _reject_free_variable_atom(atom: Atom) -> None:
    """Reject an atom with a free Variable argument: the sphere semantics is
    propositional/ground. Keying such an atom by its surface string would treat
    ``P(x)`` as one opaque proposition and silently return a verdict for an
    out-of-contract formula — the sibling ``to_isabelle_conditional`` already
    rejects the identical input, and the two must agree."""
    from ..fol.nodes import Variable
    for arg in atom.args:
        for sub in arg.walk():
            if isinstance(sub, Variable):
                raise TypeError(
                    f"conditional: atom {atom.to_unicode_str()!r} has a free "
                    "variable — the Lewis sphere semantics here is "
                    "propositional/ground. Use ground atoms (constants are "
                    "fine), matching hol.isabelle_conditional.")


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


def cf_satisfies(formula: Node, model: CounterfactualModel, world: Any) -> bool:
    """Return whether ``world`` satisfies ``formula`` in the sphere ``model``.

    Handles the propositional connectives plus the counterfactual conditionals
    :class:`~unicode_fol_kit.fol.nodes.Would` (``□→``) and
    :class:`~unicode_fol_kit.fol.nodes.Might` (``◇→``), so a parsed formula can be
    evaluated directly and counterfactuals may NEST — a conditional in an antecedent
    or consequent is evaluated at the world under consideration, with that world's own
    spheres, which is what Lewis's semantics prescribes.

    Raises:
        TypeError: on any other node (quantifiers, modal operators, …), and on an
            atom with a FREE VARIABLE argument (``P(x)``) — the sphere semantics is
            propositional/ground here; a Kripke accessibility relation is a
            different structure, so mixing ``□`` with ``□→`` is rejected rather than
            silently reinterpreted, and a first-order atom is rejected rather than
            silently read as one opaque proposition (matching
            ``hol.isabelle_conditional``).
    """
    if isinstance(formula, Atom):
        _reject_free_variable_atom(formula)
        return formula.to_unicode_str() in model.valuation.get(world, frozenset())
    if isinstance(formula, Not):
        return not cf_satisfies(formula.formula, model, world)
    if isinstance(formula, And):
        return (cf_satisfies(formula.left, model, world)
                and cf_satisfies(formula.right, model, world))
    if isinstance(formula, Or):
        return (cf_satisfies(formula.left, model, world)
                or cf_satisfies(formula.right, model, world))
    if isinstance(formula, Xor):
        return (cf_satisfies(formula.left, model, world)
                != cf_satisfies(formula.right, model, world))
    if isinstance(formula, Implies):
        return ((not cf_satisfies(formula.left, model, world))
                or cf_satisfies(formula.right, model, world))
    if isinstance(formula, Iff):
        return (cf_satisfies(formula.left, model, world)
                == cf_satisfies(formula.right, model, world))
    if isinstance(formula, Would):
        return _would_holds(model, world, formula.left, formula.right)
    if isinstance(formula, Might):
        # The dual ¬(A □→ ¬B). Note this makes ◇→ vacuously FALSE exactly where
        # □→ is vacuously true (no antecedent-world in any sphere).
        return not _would_holds(model, world, formula.left, Not(formula.right))
    raise TypeError(
        f"conditional: formula must be propositional or a counterfactual, got "
        f"{type(formula).__name__}.")


def _would_holds(model: CounterfactualModel, world: Any,
                 antecedent: Node, consequent: Node) -> bool:
    """The Lewis sphere condition for ``antecedent □→ consequent`` at ``world``."""
    for sphere in model.sphere_system(world):
        a_worlds = [w for w in sphere if cf_satisfies(antecedent, model, w)]
        if a_worlds:
            return all(cf_satisfies(consequent, model, w) for w in a_worlds)
    return True                                  # no antecedent-world anywhere → vacuous


def would(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent □→ consequent`` (Lewis "would" counterfactual).

    Vacuously true if no sphere of ``world`` holds an antecedent-world; otherwise the
    consequent must hold at every antecedent-world of the smallest antecedent-permitting
    sphere. Equivalent to ``cf_satisfies(Would(antecedent, consequent), model, world)``.
    """
    return _would_holds(model, world, antecedent, consequent)


def might(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent ◇→ consequent`` — the dual ``¬(A □→ ¬B)``."""
    return not _would_holds(model, world, antecedent, Not(consequent))


# --------------------------------------------------------------------------- #
# Bounded countermodel search / validity over Lewis sphere models.
# --------------------------------------------------------------------------- #

def _atom_keys(formula: Node) -> Tuple[str, ...]:
    """The distinct atom keys (``atom.to_unicode_str()``) of ``formula``, sorted.

    Rejects free-variable atoms upfront (same contract as :func:`cf_satisfies`),
    so ``cf_countermodel`` / ``cf_valid`` fail fast instead of mid-enumeration.
    """
    keys = set()
    for n in formula.walk():
        if isinstance(n, Atom):
            _reject_free_variable_atom(n)
            keys.add(n.to_unicode_str())
    return tuple(sorted(keys))


def _sphere_chains(world: int, worlds: Tuple[int, ...]):
    """Yield every nested sphere system around ``world`` over ``worlds``.

    A system is a strictly increasing chain ``S₁ ⊂ S₂ ⊂ … ⊂ Sₖ`` of frozensets
    with ``world ∈ S₁`` (the model contract's centering), including the empty
    chain ``[]`` (no sphere holds any world — every ``□→`` vacuously true there).
    Strictness loses no generality: a repeated sphere changes no truth value.
    """
    others = [w for w in worlds if w != world]
    subsets = []
    for k in range(len(others) + 1):
        for bits in product((False, True), repeat=len(others)):
            if sum(bits) == k:
                subsets.append(frozenset({world} | {o for o, b in zip(others, bits) if b}))
    # subsets is now ordered by size, so chains can be built left-to-right.
    def extend(chain, start):
        yield list(chain)
        for i in range(start, len(subsets)):
            if not chain or chain[-1] < subsets[i]:      # strict superset
                yield from extend(chain + [subsets[i]], i + 1)
    yield from extend([], 0)


def cf_countermodel(formula: Node,
                    max_worlds: int = 2) -> Optional[Tuple[CounterfactualModel, Any]]:
    """Return ``(model, world)`` where ``formula`` fails, or None.

    EXHAUSTIVE search over every Lewis sphere model with ``|W| ≤ max_worlds``:
    every valuation of the formula's atoms and every nested sphere system around
    every world (including the empty system). The failure check *is*
    :func:`cf_satisfies`, so a non-None result definitively refutes validity —
    the countermodel is verified by construction.

    The space is exponential: ``2^(n·a)`` valuations times ``c(n)ⁿ`` sphere
    assignments (``c(2) = 4`` chains, ``c(3) = 12``) for ``n`` worlds and ``a``
    atoms. ``max_worlds=2`` with ≤ 3 atoms is a few thousand models; keep the
    bound small.
    """
    atoms = _atom_keys(formula)
    for n in range(1, max_worlds + 1):
        worlds = tuple(range(n))
        chain_options = [list(_sphere_chains(w, worlds)) for w in worlds]
        for bits in product((False, True), repeat=n * max(1, len(atoms))):
            valuation = {
                w: frozenset(a for j, a in enumerate(atoms)
                             if bits[w * len(atoms) + j])
                for w in worlds
            } if atoms else {w: frozenset() for w in worlds}
            for chains in product(*chain_options):
                model = CounterfactualModel(
                    worlds, valuation,
                    {w: chains[w] for w in worlds})
                for w in worlds:
                    if not cf_satisfies(formula, model, w):
                        return (model, w)
    return None


def cf_valid(formula: Node, max_worlds: int = 2) -> bool:
    """Return True iff no sphere countermodel to ``formula`` is found within the bound.

    HONEST CONTRACT (mirroring :func:`~unicode_fol_kit.semantics.relevant.rel_valid`):
    ``False`` is *definitive* — it is backed by an explicit,
    :func:`cf_satisfies`-verified countermodel from :func:`cf_countermodel`, so
    the formula is certainly not valid over Lewis sphere models. ``True`` means
    only "no countermodel with at most ``max_worlds`` worlds"; a non-theorem
    whose smallest refuting model needs more worlds is (spuriously) reported
    valid — for a certified positive verdict use
    :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_counterfactual`,
    whose proof battery is a real validity proof over ALL nested sphere systems.
    Raising ``max_worlds`` never turns a ``False`` into a ``True``.
    """
    return cf_countermodel(formula, max_worlds) is None
