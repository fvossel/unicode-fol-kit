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
- ``"Say:" + agent``   — the assertive relation for ``Says(agent, …)`` (non-factive).
- ``"Want:" + agent``  — the bouletic relation for ``Wants(agent, …)`` (non-veridical).
- ``"temporal"``       — the one-step successor relation for Next / Always /
                         Eventually / Until.
- ``"deontic"``        — the (serial) accessibility relation for Obligatory O /
                         Permitted P (Standard Deontic Logic, the system KD).

A missing relation denotes the empty relation; a missing world valuation denotes
the empty set (every atom false there). Inputs are never mutated: the closure
and path helpers build fresh sets.

Hybrid logic H(@) is interpreted through the optional ``nominals`` mapping
(name → world): ``Nominal(i)`` is true exactly at the world the assignment
names, and ``At(i, φ)`` evaluates φ *at* that world, wherever the evaluation
currently stands. A nominal without an assignment raises a ValueError naming
it (rather than silently defaulting), since a nominal must name exactly one
world for the hybrid semantics to make sense.

Public announcement logic (PAL) is interpreted directly — ``Announce`` (``[φ!]ψ``)
and ``AnnounceDiamond`` (``⟨φ!⟩ψ``) are the only two constructs here that do NOT
just recurse at a fixed world or along a fixed relation: they build the
φ-restricted model ``M|φ`` (:func:`unicode_fol_kit.semantics.dynamic_epistemic.announce`)
and evaluate ``ψ`` there. This is the ORACLE that
:func:`unicode_fol_kit.fol.pal.reduce_announcements` (a purely SYNTACTIC
elimination of Announce/AnnounceDiamond, sound only for the propositional-modal
fragment interpreted here) is differentially tested against.

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
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Nominal, At,
    Constant, substitute,
)
from ..fol._modal_nodes import Announce, AnnounceDiamond
from ._modal_reject import (
    FUZZY_TYPES, LAMBDA_TYPES,
    reject_fuzzy, reject_lambda,
)

# Quantifier-type spellings used by the AST.
_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

# Relation-name prefixes / keys (kept here so the model and the standard
# translation stay in sync via documentation; the strings are the contract).
_ALETHIC = "alethic"
_TEMPORAL = "temporal"
_DEONTIC = "deontic"
_KNOWS_PREFIX = "K:"
_BELIEVES_PREFIX = "B:"
_SAYS_PREFIX = "Say:"
_WANTS_PREFIX = "Want:"


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic agent term.

    The agent is a term (Variable or Constant). Object quantifiers ground a bound
    agent to a Constant before the modality is reached (``∀x (… → K_x φ)`` becomes
    ``K_<d> φ`` per individual ``d``), so this is the constant/variable name and the
    relation key matches the model's ``"K:"+name`` / ``"B:"+name`` convention.
    """
    return getattr(agent, "name", None) or agent.to_unicode_str()

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
        nominals: maps a NOMINAL NAME (str) to the single world it names (the
            hybrid-logic assignment interpreting ``Nominal`` / ``At``). Defaults
            to empty. Every referenced world must be in ``worlds`` — a dangling
            assignment raises ValueError at construction time.

    All mappings default to empty, so ``KripkeModel({0, 1})`` is a valid
    (atom-free, relation-free) frame. The constructor copies every container, so
    later edits to the caller's structures never leak in.
    """

    def __init__(
        self,
        worlds: Iterable[World],
        relations: Optional[Mapping[str, Iterable[Edge]]] = None,
        valuation: Optional[Mapping[World, Iterable[str]]] = None,
        domains: Optional[Mapping[World, Iterable[Any]]] = None,
        domain: Optional[Iterable[Any]] = None,
        nominals: Optional[Mapping[str, World]] = None,
    ):
        """Build a Kripke model, copying every container so edits never leak in.

        ``domains`` maps each world to the set of individuals existing there (the
        per-world object domain ``D_w`` of quantified modal logic); ``domain`` is a
        shorthand for a **constant** domain (the same individuals at every world).
        Supplying either lets :func:`satisfies_modal` interpret object quantifiers
        (``∀x`` / ``∃x``) *actualistically* — at a world ``w`` they range over
        ``D_w`` — so the Barcan formulas come out valid or invalid according to how
        the domains vary. Omit both for the purely propositional fragment.

        ``nominals`` maps each hybrid nominal name to the ONE world it names;
        every referenced world must exist in ``worlds`` (checked here, so a
        dangling nominal fails fast instead of at evaluation time).
        """
        self.worlds: FrozenSet[World] = frozenset(worlds)
        self.relations: Dict[str, FrozenSet[Edge]] = {
            name: frozenset(edges) for name, edges in (relations or {}).items()
        }
        self.valuation: Dict[World, FrozenSet[str]] = {
            world: frozenset(keys) for world, keys in (valuation or {}).items()
        }
        if domains is not None:
            self.domains: Optional[Dict[World, FrozenSet[Any]]] = {
                world: frozenset(ind) for world, ind in domains.items()
            }
        elif domain is not None:
            const = frozenset(domain)
            self.domains = {world: const for world in self.worlds}
        else:
            self.domains = None
        self.nominals: Dict[str, World] = dict(nominals or {})
        for name, named in self.nominals.items():
            if named not in self.worlds:
                raise ValueError(
                    f"KripkeModel: nominal {name!r} is assigned to world "
                    f"{named!r}, which is not among the model's worlds."
                )

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

    def domain_at(self, world: World) -> FrozenSet[Any]:
        """Return the individuals existing at ``world`` (the object domain ``D_w``).

        Raises ValueError if the model carries no domains (a purely propositional
        model), since object quantifiers cannot then be interpreted.
        """
        if self.domains is None:
            raise ValueError(
                "satisfies_modal: this Kripke model has no object domains, so "
                "object quantifiers (∀x / ∃x) cannot be evaluated — build the model "
                "with domains={world: [...]} (varying) or domain=[...] (constant)."
            )
        return self.domains.get(world, frozenset())


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


def _predecessors(model: KripkeModel, name: str, world: World) -> Set[World]:
    """Return the set of ``w'`` with ``(w', world)`` in the named relation (its converse successors)."""
    return {w1 for (w1, w2) in model.relation(name) if w2 == world}


def _since_holds(
    left: Node,
    right: Node,
    model: KripkeModel,
    world: World,
) -> bool:
    """Decide ``Since(left, right)`` at ``world`` — the backward mirror of Until.

    Searches for a finite ``"temporal"`` path into the PAST
    ``world = w0 ← w1 ← … ← wn`` (each step ``(w(i+1), wi)`` a temporal edge, n ≥ 0)
    with ``right`` true at ``wn`` and ``left`` true at every later ``wi`` (i < n). A
    depth-first search guarded by a visited set, so cyclic frames terminate.
    """
    edges = model.relation(_TEMPORAL)

    def search(w: World, visited: FrozenSet[World]) -> bool:
        """Return whether some backward path from ``w`` witnesses the Since."""
        if satisfies_modal(right, model, w):
            return True
        if not satisfies_modal(left, model, w):
            return False
        next_visited = visited | {w}
        for w0 in {a for (a, b) in edges if b == w}:
            if w0 not in next_visited and search(w0, next_visited):
                return True
        return False

    return search(world, frozenset())


def _nominal_world(model: KripkeModel, name: str) -> World:
    """Return the world the nominal ``name`` names; raise if it is unassigned.

    A nominal must name exactly one world, so an assignment-free nominal is a
    modelling error — the ValueError names the offending nominal and shows the
    ``nominals=`` fix rather than silently picking a truth value.
    """
    if name not in model.nominals:
        raise ValueError(
            f"satisfies_modal: the nominal {name!r} has no world assignment in "
            f"this model — build the KripkeModel with nominals={{{name!r}: world}}."
        )
    return model.nominals[name]


def satisfies_modal(formula: Node, model: KripkeModel, world: World) -> bool:
    """Return whether ``formula`` is true at ``world`` in the Kripke ``model``.

    The Kripke satisfaction relation for the propositional / ground modal
    fragment:

    - ``Atom`` — its Unicode key is in the world's valuation.
    - ``Nominal i`` — true iff ``world`` IS the world ``model.nominals[i]``
      names (a nominal holds at exactly one world).
    - ``At(i, φ)`` — φ holds at the world named ``i``, regardless of the
      current world (the hybrid satisfaction operator ``@i φ``).
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
    - ``Announce(φ, ψ)`` (``[φ!]ψ``) — ``φ`` false at ``world`` makes this
      vacuously true; otherwise ``ψ`` must hold at ``world`` in the model
      restricted to the ``φ``-worlds (:func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce`).
    - ``AnnounceDiamond(φ, ψ)`` (``⟨φ!⟩ψ``) — the dual: ``φ`` true at ``world``
      AND ``ψ`` holds at ``world`` in the ``φ``-restricted model.

    Raises:
        NotImplementedError: on a Quantifier / SortedQuantifier (first-order
            modal logic is out of scope for v1), a Łukasiewicz node, or a lambda
            node.
    """
    # --- atomic ---
    if isinstance(formula, Atom):
        return formula.to_unicode_str() in model.atoms_true_at(world)

    # --- hybrid: a nominal is true exactly at the world it names; @ jumps there ---
    if isinstance(formula, Nominal):
        return world == _nominal_world(model, formula.name)
    if isinstance(formula, At):
        return satisfies_modal(formula.formula, model,
                               _nominal_world(model, formula.nominal.name))

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
            for w2 in model.successors(_KNOWS_PREFIX + _agent_key(formula.agent), world)
        )
    if isinstance(formula, Believes):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_BELIEVES_PREFIX + _agent_key(formula.agent), world)
        )

    # --- assertive / bouletic (both universal K-modalities, no frame conditions:
    # Says is non-factive / non-doxastic, Wants is non-veridical) ---
    if isinstance(formula, Says):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_SAYS_PREFIX + _agent_key(formula.agent), world)
        )
    if isinstance(formula, Wants):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_WANTS_PREFIX + _agent_key(formula.agent), world)
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

    # --- past tense (over the CONVERSE of the one-step "temporal" relation) ---
    if isinstance(formula, Previous):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in _predecessors(model, _TEMPORAL, world)
        )
    if isinstance(formula, Historically):
        reverse = [(b, a) for (a, b) in model.relation(_TEMPORAL)]
        reachable = reflexive_transitive_closure(reverse, [world])
        return all(satisfies_modal(formula.formula, model, w2) for w2 in reachable)
    if isinstance(formula, Once):
        reverse = [(b, a) for (a, b) in model.relation(_TEMPORAL)]
        reachable = reflexive_transitive_closure(reverse, [world])
        return any(satisfies_modal(formula.formula, model, w2) for w2 in reachable)
    if isinstance(formula, Since):
        return _since_holds(formula.left, formula.right, model, world)

    # --- public announcement logic (PAL): a genuine MODEL UPDATE, not a fixed
    # accessibility relation — this is the ORACLE unicode_fol_kit.fol.pal
    # .reduce_announcements is differentially tested against (see that module's
    # docstring for the correctness argument relating the two). Both build the
    # restricted model M|announcement via
    # unicode_fol_kit.semantics.dynamic_epistemic.announce (imported lazily to
    # avoid a circular import: dynamic_epistemic imports THIS module at load
    # time) and recurse into ``formula.formula`` there, at the SAME world. ---
    if isinstance(formula, Announce):
        if not satisfies_modal(formula.announcement, model, world):
            return True  # untruthful announcement is not made: vacuously true
        from .dynamic_epistemic import announce  # lazy: avoid import cycle
        return satisfies_modal(formula.formula, announce(model, formula.announcement), world)
    if isinstance(formula, AnnounceDiamond):
        if not satisfies_modal(formula.announcement, model, world):
            return False  # dual of Announce: false whenever the announcement is
        from .dynamic_epistemic import announce  # lazy: avoid import cycle
        return satisfies_modal(formula.formula, announce(model, formula.announcement), world)

    # --- object quantifiers (actualist: range over the CURRENT world's domain D_w) ---
    if isinstance(formula, Quantifier):
        individuals = model.domain_at(world)
        instances = (
            satisfies_modal(substitute(formula.formula, formula.variable, Constant(d)),
                            model, world)
            for d in individuals
        )
        if formula.type in _FORALL:
            return all(instances)
        if formula.type in _EXISTS:
            return any(instances)
        raise ValueError(f"satisfies_modal: unknown quantifier type {formula.type!r}")

    # --- rejected: out-of-scope node kinds ---
    if isinstance(formula, SortedQuantifier):
        raise NotImplementedError(
            "satisfies_modal: SortedQuantifier is not supported in the modal "
            "evaluator; use a plain Quantifier with per-world domains."
        )
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
