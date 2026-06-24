"""Kripke (possible-worlds) semantics for the propositional modal fragment.

A :class:`KripkeModel` is a possible-worlds frame: a set of worlds, a family of
named accessibility relations between worlds, and a per-world valuation of the
ground atoms. :func:`satisfies_modal` computes the truth value of a modal
formula *at a world*, following the standard Kripke satisfaction relation.

Only the **propositional / ground** modal fragment is interpreted here (this is
v1): the modal operators wrap classical connectives and ground atoms. A ground
atom is identified by its rendered Unicode key (``atom.to_unicode_str()``, e.g.
``"P"`` or ``"Likes(a, b)"``); a world's valuation is the set of atom keys true
there, so a missing key is false. First-order quantifiers, sorted quantifiers,
Łukasiewicz operators, and lambda nodes are rejected with NotImplementedError —
quantified / fuzzy modal logic is future work.

Relation-name convention (keys of :attr:`KripkeModel.relations`):

- ``"alethic"``        — the accessibility relation for Box □ / Diamond ◇.
- ``"K:" + agent``     — the epistemic relation for ``Knows(agent, …)``.
- ``"B:" + agent``     — the doxastic relation for ``Believes(agent, …)``.
- ``"temporal"``       — the one-step successor relation for Next / Always /
                         Eventually / Until.
- ``"deontic"``        — the (serial) accessibility relation for Obligatory O /
                         Permitted P (Standard Deontic Logic, the system KD).

A missing relation denotes the empty relation; a missing world valuation denotes
the empty set (every atom false there). Inputs are never mutated: the closure
and path helpers build fresh sets.

Documented temporal semantics:

- ``Next φ``: φ holds at **all** immediate ``"temporal"``-successors of the
  current world. On a deterministic / linear frame (each world has at most one
  successor) this is exactly "φ at the unique next state"; on a branching frame
  it is read universally (the "for all next states" reading).
- ``Always φ`` (G): φ holds at every world reachable from the current world via
  the **reflexive-transitive** closure of ``"temporal"`` (the current world
  included).
- ``Eventually φ`` (F): φ holds at **some** such reachable world (current world
  included).
- ``Until(φ, ψ)``: there is a finite ``"temporal"`` path
  ``w0 → w1 → … → wn`` (n ≥ 0) starting at the current world with ψ true at
  ``wn`` and φ true at every earlier world ``w0 … w(n-1)``. This is the
  finite-reachability reading of strong Until; the search is depth-first with a
  visited guard so cycles in the frame terminate.
"""

from typing import Any, Dict, FrozenSet, Iterable, Mapping, Optional, Set, Tuple

from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Obligatory, Permitted,
)
from ._modal_reject import (
    FUZZY_TYPES, LAMBDA_TYPES,
    reject_quantifier, reject_fuzzy, reject_lambda,
)

# Relation-name prefixes / keys (kept here so the model and the standard
# translation stay in sync via documentation; the strings are the contract).
_ALETHIC = "alethic"
_TEMPORAL = "temporal"
_DEONTIC = "deontic"
_KNOWS_PREFIX = "K:"
_BELIEVES_PREFIX = "B:"

World = Any
Edge = Tuple[World, World]


class KripkeModel:
    """A Kripke model: worlds, named accessibility relations, and a valuation.

    Args:
        worlds: an iterable of worlds (any hashable values). Stored as a frozen
            set; duplicates collapse.
        relations: maps a relation NAME (str) to a set of ``(w, w')`` edges.
            Recognised names: ``"alethic"`` (Box/Diamond), ``"K:"+agent``
            (Knows), ``"B:"+agent`` (Believes), ``"temporal"`` (Next / Always /
            Eventually / Until), ``"deontic"`` (Obligatory / Permitted; serial
            in Standard Deontic Logic). A missing name is the empty relation.
            Each edge set is copied into a frozen set.
        valuation: maps a world to the set of GROUND-ATOM KEYS true there, where
            a key is ``atom.to_unicode_str()`` (e.g. ``"P"`` or ``"Likes(a, b)"``).
            A missing world maps to the empty set (every atom false there). Each
            entry is copied into a frozen set.

    All mappings default to empty, so ``KripkeModel({0, 1})`` is a valid
    (atom-free, relation-free) frame. The constructor copies every container, so
    later edits to the caller's structures never leak in.
    """

    def __init__(
        self,
        worlds: Iterable[World],
        relations: Optional[Mapping[str, Iterable[Edge]]] = None,
        valuation: Optional[Mapping[World, Iterable[str]]] = None,
    ):
        """Build a Kripke model, copying every container so edits never leak in."""
        self.worlds: FrozenSet[World] = frozenset(worlds)
        self.relations: Dict[str, FrozenSet[Edge]] = {
            name: frozenset(edges) for name, edges in (relations or {}).items()
        }
        self.valuation: Dict[World, FrozenSet[str]] = {
            world: frozenset(keys) for world, keys in (valuation or {}).items()
        }

    def __repr__(self) -> str:
        """Show world count and the relation / valuation tables for inspection."""
        return (
            f"KripkeModel(worlds={set(self.worlds)!r}, "
            f"relations={ {k: set(v) for k, v in self.relations.items()} !r}, "
            f"valuation={ {k: set(v) for k, v in self.valuation.items()} !r})"
        )

    def relation(self, name: str) -> FrozenSet[Edge]:
        """Return the edge set of a named relation (empty if undeclared)."""
        return self.relations.get(name, frozenset())

    def successors(self, name: str, world: World) -> Set[World]:
        """Return the set of ``w'`` with ``(world, w')`` in the named relation."""
        return {w2 for (w1, w2) in self.relation(name) if w1 == world}

    def atoms_true_at(self, world: World) -> FrozenSet[str]:
        """Return the ground-atom keys true at ``world`` (empty if undeclared)."""
        return self.valuation.get(world, frozenset())


def reflexive_transitive_closure(
    edges: Iterable[Edge],
    sources: Iterable[World],
) -> Set[World]:
    """Return every world reachable from ``sources`` along ``edges``, reflexively.

    The result contains each source world itself (reflexive) and every world
    reachable from a source by following one or more edges (transitive). A
    breadth-first walk with a visited set; the input edge collection is never
    mutated. Used by Always / Eventually over the ``"temporal"`` relation.
    """
    edge_set = set(edges)
    reachable: Set[World] = set()
    frontier = list(sources)
    while frontier:
        w = frontier.pop()
        if w in reachable:
            continue
        reachable.add(w)
        for (w1, w2) in edge_set:
            if w1 == w and w2 not in reachable:
                frontier.append(w2)
    return reachable


def _until_holds(
    left: Node,
    right: Node,
    model: KripkeModel,
    world: World,
) -> bool:
    """Decide ``Until(left, right)`` at ``world`` by finite-path search.

    Searches for a finite ``"temporal"`` path ``world = w0 → … → wn`` (n ≥ 0)
    with ``right`` true at ``wn`` and ``left`` true at every earlier ``wi``. A
    depth-first search guarded by a visited set: if ``right`` already holds we
    succeed immediately (n = 0); otherwise ``left`` must hold here and the
    search continues into the temporal successors. The visited guard makes the
    search terminate on cyclic frames.
    """
    edges = model.relation(_TEMPORAL)

    def search(w: World, visited: FrozenSet[World]) -> bool:
        """Return whether some path from ``w`` witnesses the Until."""
        if satisfies_modal(right, model, w):
            return True
        if not satisfies_modal(left, model, w):
            return False
        next_visited = visited | {w}
        for w2 in {b for (a, b) in edges if a == w}:
            if w2 not in next_visited and search(w2, next_visited):
                return True
        return False

    return search(world, frozenset())


def satisfies_modal(formula: Node, model: KripkeModel, world: World) -> bool:
    """Return whether ``formula`` is true at ``world`` in the Kripke ``model``.

    The Kripke satisfaction relation for the propositional / ground modal
    fragment:

    - ``Atom`` — its Unicode key is in the world's valuation.
    - ``Not / And / Or / Xor / Implies / Iff`` — the classical truth tables,
      recursing at the **same** world.
    - ``Box φ`` — φ holds at every ``"alethic"``-successor; ``Diamond φ`` — at
      some ``"alethic"``-successor.
    - ``Knows(a, φ)`` — φ holds at every ``"K:"+a``-successor (universal).
    - ``Believes(a, φ)`` — φ holds at every ``"B:"+a``-successor (universal).
    - ``Obligatory φ`` — φ holds at every ``"deontic"``-successor (universal);
      ``Permitted φ`` — at some ``"deontic"``-successor.
    - ``Next φ`` — φ holds at every immediate ``"temporal"``-successor.
    - ``Always φ`` / ``Eventually φ`` — φ holds at all / some worlds in the
      reflexive-transitive closure of ``"temporal"`` from ``world``.
    - ``Until(φ, ψ)`` — see :func:`_until_holds` (finite-path strong Until).

    Raises:
        NotImplementedError: on a Quantifier / SortedQuantifier (first-order
            modal logic is out of scope for v1), a Łukasiewicz node, or a lambda
            node.
    """
    # --- atomic ---
    if isinstance(formula, Atom):
        return formula.to_unicode_str() in model.atoms_true_at(world)

    # --- classical connectives (recurse at the same world) ---
    if isinstance(formula, Not):
        return not satisfies_modal(formula.formula, model, world)
    if isinstance(formula, And):
        return (satisfies_modal(formula.left, model, world)
                and satisfies_modal(formula.right, model, world))
    if isinstance(formula, Or):
        return (satisfies_modal(formula.left, model, world)
                or satisfies_modal(formula.right, model, world))
    if isinstance(formula, Xor):
        return (satisfies_modal(formula.left, model, world)
                != satisfies_modal(formula.right, model, world))
    if isinstance(formula, Implies):
        return ((not satisfies_modal(formula.left, model, world))
                or satisfies_modal(formula.right, model, world))
    if isinstance(formula, Iff):
        return (satisfies_modal(formula.left, model, world)
                == satisfies_modal(formula.right, model, world))

    # --- alethic ---
    if isinstance(formula, Box):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_ALETHIC, world)
        )
    if isinstance(formula, Diamond):
        return any(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_ALETHIC, world)
        )

    # --- epistemic / doxastic (both universal) ---
    if isinstance(formula, Knows):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_KNOWS_PREFIX + formula.agent, world)
        )
    if isinstance(formula, Believes):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_BELIEVES_PREFIX + formula.agent, world)
        )

    # --- deontic (Standard Deontic Logic / KD over a serial "deontic" relation) ---
    if isinstance(formula, Obligatory):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_DEONTIC, world)
        )
    if isinstance(formula, Permitted):
        return any(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_DEONTIC, world)
        )

    # --- temporal ---
    if isinstance(formula, Next):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_TEMPORAL, world)
        )
    if isinstance(formula, Always):
        reachable = reflexive_transitive_closure(model.relation(_TEMPORAL), [world])
        return all(
            satisfies_modal(formula.formula, model, w2) for w2 in reachable
        )
    if isinstance(formula, Eventually):
        reachable = reflexive_transitive_closure(model.relation(_TEMPORAL), [world])
        return any(
            satisfies_modal(formula.formula, model, w2) for w2 in reachable
        )
    if isinstance(formula, Until):
        return _until_holds(formula.left, formula.right, model, world)

    # --- rejected: out-of-scope node kinds ---
    if isinstance(formula, (Quantifier, SortedQuantifier)):
        reject_quantifier(formula, "satisfies_modal")
    if isinstance(formula, FUZZY_TYPES):
        reject_fuzzy(formula, "satisfies_modal")
    if isinstance(formula, LAMBDA_TYPES):
        reject_lambda(formula, "satisfies_modal")

    raise NotImplementedError(
        f"satisfies_modal: unsupported node type {type(formula).__name__}."
    )


def models_at(formula: Node, model: KripkeModel, world: World) -> bool:
    """Convenience alias for :func:`satisfies_modal` reading "model, world ⊨ φ"."""
    return satisfies_modal(formula, model, world)
