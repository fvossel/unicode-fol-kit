"""Common knowledge and BMS action models (Dynamic Epistemic Logic).

Two independent extensions of the epistemic Kripke machinery in
:mod:`unicode_fol_kit.semantics.kripke` and
:mod:`unicode_fol_kit.semantics.dynamic_epistemic`:

1. **Common knowledge** — :func:`everybody_knows` (E_G φ, "everyone in G knows
   φ") and :func:`common_knowledge_holds` (C_G φ, "φ is common knowledge in
   G"), evaluated directly on an existing
   :class:`~unicode_fol_kit.semantics.kripke.KripkeModel` at a world, using the
   model's ``"K:" + agent`` relations (the SAME naming convention
   :mod:`kripke` itself uses for ``Knows`` — see that module's docstring for
   the contract).

2. **BMS action models** (Baltag, Moss & Solecki 1998, "The Logic of Public
   Announcements, Common Knowledge, and Private Suspicions", TARK; see also
   van Ditmarsch, van der Hoek & Kooi, *Dynamic Epistemic Logic*, Springer
   2007, ch. 6) — :class:`ActionModel` and :func:`product_update` generalise
   public announcement (:func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce`)
   to arbitrary epistemic EVENTS: private announcements, lies, and any other
   information-changing event that can be described by a set of events, a
   precondition per event, and per-agent indistinguishability between events.
   :func:`public_announcement_action` recovers plain PAL as the special case of
   a single event — the product update it induces agrees EXACTLY with
   :func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce` (see the
   module's own cross-check in ``tests/test_action_models.py``).

Both extensions build only on the PUBLIC interface of :mod:`kripke`
(``KripkeModel``, ``satisfies_modal``, ``model.relation``/``model.successors``,
``reflexive_transitive_closure``) — nothing here is wired into ``kripke.py``,
``dynamic_epistemic.py``, the parser, or ``semantics/__init__.py``; that
central wiring is a separate, later step. Import directly from this module:
``from unicode_fol_kit.semantics.action_models import ...``.

Scope: purely EPISTEMIC dynamics. BMS action models in general carry
POSTCONDITIONS (factual, non-epistemic change — e.g. an event that flips a
coin or updates a database), but :class:`ActionModel` here has no
postcondition parameter at all: an event has only a precondition and
per-agent accessibility edges to other events. :func:`product_update` always
copies the valuation of ``w`` unchanged onto ``(w, e)``. There is therefore no
postcondition argument to refuse — the omission itself is the scope boundary,
documented here rather than enforced by a runtime check.
"""

from typing import Dict, FrozenSet, Hashable, Iterable, Mapping, Optional, Set, Tuple

from ..fol.nodes import Node
from .kripke import KripkeModel, World, Edge, satisfies_modal, reflexive_transitive_closure

# Relation-key prefix for epistemic accessibility — MUST match the convention
# documented and used by unicode_fol_kit.semantics.kripke.KripkeModel /
# satisfies_modal (the private ``_KNOWS_PREFIX`` there). Kept as a literal
# here (rather than imported) because this module must not edit kripke.py,
# and the string itself — not the name it is bound to — is the actual
# contract between the two modules.
_KNOWS_PREFIX = "K:"

Event = Hashable


# ---------------------------------------------------------------------------
# Common knowledge
# ---------------------------------------------------------------------------

def _group_relation(model: KripkeModel, group: Iterable[str]) -> Set[Edge]:
    """Return the UNION of the ``"K:"+agent`` edge sets for every agent in ``group``.

    This is the accessibility relation ``R_G = ⋃_{a∈G} R_a`` that both
    :func:`everybody_knows` and :func:`common_knowledge_holds` are built from.
    An agent absent from ``model.relations`` contributes the empty relation
    (``KripkeModel``'s own "a missing name is the empty relation" convention).
    """
    union: Set[Edge] = set()
    for agent in group:
        union |= model.relation(_KNOWS_PREFIX + agent)
    return union


def everybody_knows(model: KripkeModel, world: World, group: Iterable[str], formula: Node) -> bool:
    """Return whether E_G φ ("everyone in ``group`` knows φ") holds at ``world``.

    E_G φ is, by definition, the finite conjunction ⋀_{a∈G} K_a φ (Fagin,
    Halpern, Moses & Vardi, *Reasoning About Knowledge*, MIT Press 1995, ch.
    2). Since ``Knows(a, φ)`` holds at ``world`` iff φ holds at every
    ``"K:"+a``-successor of ``world`` (universal quantification distributes
    over a union of successor sets), this is equivalent to — and computed
    here as — "φ holds at every world reachable from ``world`` by a SINGLE
    edge of the union relation ``⋃_{a∈G} R_a``" (no reflexive/transitive
    closure: this is the ONE-STEP operator, the first rung of the common-
    knowledge ladder — see :func:`common_knowledge_holds`).

    ``group`` is any iterable of agent name strings (consumed once, so a
    generator is safe here — it is materialised into the relation union
    immediately). An empty group makes E_∅ φ vacuously TRUE at every world
    (the union relation is empty, so "holds at every successor" holds
    vacuously) — the same convention an empty conjunction always gets.
    """
    successors = {w2 for (w1, w2) in _group_relation(model, group) if w1 == world}
    return all(satisfies_modal(formula, model, w2) for w2 in successors)


def common_knowledge_holds(model: KripkeModel, world: World, group: Iterable[str], formula: Node) -> bool:
    """Return whether C_G φ ("φ is common knowledge in ``group``") holds at ``world``.

    Common knowledge is standardly given TWO equivalent characterisations
    (Fagin, Halpern, Moses & Vardi, *Reasoning About Knowledge*, MIT Press
    1995, §2.4; also van Ditmarsch, van der Hoek & Kooi, *Dynamic Epistemic
    Logic*, Springer 2007, §2.3-2.4):

    1. **Fixpoint / ladder**: C_G φ is the (infinite) conjunction
       ``E_G φ ∧ E_G E_G φ ∧ E_G E_G E_G φ ∧ …`` — equivalently, the greatest
       fixpoint of ``X ↔ E_G(φ ∧ X)``. Everyone knows φ, everyone knows that
       everyone knows φ, and so on without end.
    2. **Reachability**: C_G φ holds at ``world`` iff φ holds at EVERY world
       reachable from ``world`` by a finite path of ONE OR MORE edges in the
       union relation ``R_G = ⋃_{a∈G} R_a`` (FHMV's Theorem 2.4.4-style
       reachability characterisation, which holds for arbitrary — not
       necessarily equivalence — relations).

    THIS FUNCTION IMPLEMENTS CHARACTERISATION 2, via
    :func:`~unicode_fol_kit.semantics.kripke.reflexive_transitive_closure` of
    ``R_G`` from ``world`` — REFLEXIVE, i.e. "zero or more edges" (``world``
    itself is always included), not FHMV's literal "one or more edges" (which
    would exclude ``world`` unless a path loops back to it).

    Why reflexive is the right choice here, not a deviation from FHMV: every
    individual epistemic relation ``"K:"+agent`` this kit ever builds for
    ``Knows`` is used with the reflexivity axiom T in mind (``K_a φ → φ``,
    tested directly in ``tests/test_kripke.py::test_reflexive_frame_gives_factivity_for_knows``)
    — i.e. the intended models are S5 (or at least reflexive), exactly the
    case FHMV themselves note collapses "one-or-more-steps" and "zero-or-more-
    steps" reachability into the same set, because a reflexive edge at
    ``world`` already puts ``world`` back into the "one-or-more-steps" set for
    free. Taking the reflexive closure directly (rather than requiring the
    caller's relations to already carry an explicit self-loop) makes
    ``common_knowledge_holds`` agree with FHMV on every model the caller is
    expected to build, and additionally makes ``C_G φ → φ`` a theorem here
    even on a model some caller forgot to add reflexive loops to (a
    permissive, not a silently-wrong, choice — the alternative, a strict
    "one-or-more-steps" closure, would make C_G φ fail to entail φ on such a
    model, which is not the standard reading anyone building an epistemic
    model here would expect).

    ``group`` is any iterable of agent name strings, consumed once into the
    union relation. An empty group makes ``common_knowledge_holds`` reduce
    to ``satisfies_modal(formula, model, world)`` (the reflexive closure of
    the empty relation from ``world`` is just ``{world}``) — consistent with
    :func:`everybody_knows`'s empty-group convention.
    """
    reachable = reflexive_transitive_closure(_group_relation(model, group), [world])
    return all(satisfies_modal(formula, model, w2) for w2 in reachable)


# ---------------------------------------------------------------------------
# BMS action models
# ---------------------------------------------------------------------------

class ActionModel:
    """A BMS (Baltag-Moss-Solecki) action model: events, preconditions, accessibility.

    Args:
        events: an iterable of hashable event tokens. Stored as a frozenset;
            duplicates collapse.
        pre: maps EVERY event to a kit :class:`Node` — the precondition that
            must hold at a world ``w`` for the event to be executable there
            (``M, w ⊨ pre(e)``). Every event named in ``events`` must have an
            entry (a missing precondition is a modelling error, not an
            implicit "always executable" default — this kit has no
            propositional-truth constant node that :func:`satisfies_modal`
            evaluates, so there is nothing sensible to default to; use an
            explicit tautology, e.g. ``Or(p, Not(p))`` over an atom already in
            the model's vocabulary, for an unconditionally executable event).
            An extra entry for an event not in ``events`` is equally rejected
            — ``pre`` and ``events`` must name exactly the same set.
        relations: maps a relation NAME (str) to a set of ``(e, e')`` event
            edges — the SAME naming convention :class:`KripkeModel` uses
            (``"K:" + agent`` for the epistemic accessibility
            :func:`product_update` combines with the base model's relation of
            the same name), so the two sides of the product line up by name
            without any translation step. A missing name is the empty
            relation — but note that "empty" is NOT "unchanged" and NOT
            "maximally informed" in any benign sense: an agent whose event
            relation is empty relates NO product worlds, so after the
            product `K_a φ` holds VACUOUSLY for every φ (factivity gone).
            :func:`product_update` therefore REFUSES an action that omits
            a relation name the base model carries; the empty default only
            matters for names the base model does not have either.
            Defaults to no relations at all.

    Every container is copied at construction time (frozensets / a plain
    dict), so later edits to the caller's structures never leak in — the same
    discipline :class:`KripkeModel` follows.
    """

    def __init__(
        self,
        events: Iterable[Event],
        pre: Mapping[Event, Node],
        relations: Optional[Mapping[str, Iterable[Tuple[Event, Event]]]] = None,
    ):
        self.events: FrozenSet[Event] = frozenset(events)
        pre = dict(pre)
        missing = self.events - pre.keys()
        if missing:
            raise ValueError(
                "ActionModel: no precondition given for event(s) "
                f"{sorted(missing, key=repr)!r} — every event needs an explicit "
                "pre[event] Node (BMS action models have no implicit "
                "'always true' default; see the class docstring for the "
                "tautology workaround for an unconditional event)."
            )
        extra = pre.keys() - self.events
        if extra:
            raise ValueError(
                "ActionModel: pre has precondition(s) for event(s) not in "
                f"events: {sorted(extra, key=repr)!r}."
            )
        self.pre: Dict[Event, Node] = pre
        self.relations: Dict[str, FrozenSet[Tuple[Event, Event]]] = {
            name: frozenset(edges) for name, edges in (relations or {}).items()
        }

    def __repr__(self) -> str:
        """Show the event set and relation table for inspection."""
        return (
            f"ActionModel(events={set(self.events)!r}, "
            f"pre={ {e: p.to_unicode_str() for e, p in self.pre.items()} !r}, "
            f"relations={ {k: set(v) for k, v in self.relations.items()} !r})"
        )

    def relation(self, name: str) -> FrozenSet[Tuple[Event, Event]]:
        """Return the edge set of a named relation (empty if undeclared)."""
        return self.relations.get(name, frozenset())

    def successors(self, name: str, event: Event) -> Set[Event]:
        """Return the set of ``e'`` with ``(event, e')`` in the named relation."""
        return {e2 for (e1, e2) in self.relation(name) if e1 == event}


def product_update(model: KripkeModel, action: "ActionModel") -> KripkeModel:
    """Return the BMS product update ``model ⊗ action`` (Baltag-Moss-Solecki 1998).

    The construction, verbatim from the standard definition (van Ditmarsch,
    van der Hoek & Kooi, *Dynamic Epistemic Logic*, Springer 2007, Def. 6.9,
    specialised to no postconditions — see the module docstring on scope):

    - **Worlds**: ``{(w, e) : w ∈ model.worlds, e ∈ action.events,
      model, w ⊨ action.pre[e]}`` — a world/event pair survives exactly when
      the event is executable at that world. Worlds of the product are
      LITERAL ``(w, e)`` tuples (so a caller can always recover the
      originating world/event by unpacking, no separate lookup needed).
    - **Accessibility**: for every relation NAME appearing in either
      ``model.relations`` or ``action.relations`` (their union — a name
      absent from one side is that side's empty relation, per each class's
      own convention), ``(w, e) R (w', e')`` in the product iff ``w R w'``
      in ``model`` AND ``e R e'`` in ``action`` — restricted to surviving
      product worlds on both ends. This is symmetric in model/action exactly
      because both use the identical ``"K:" + agent`` (etc.) naming
      convention for the relation being combined.
    - **Valuation**: purely epistemic events carry no factual change, so
      ``(w, e)`` gets EXACTLY ``model``'s valuation of ``w``, copied
      unchanged (no postcondition parameter exists on :class:`ActionModel` to
      do otherwise — see the module docstring).
    - **Domains**: if ``model`` carries per-world object domains, ``(w, e)``
      inherits ``model``'s domain of ``w`` unchanged (same "no factual
      change" reasoning as the valuation). ``Nominals`` are NOT propagated —
      neither does :func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce`,
      whose restricted model this function is a strict generalisation of, so
      the two stay consistent (see ``public_announcement_action`` /
      ``tests/test_action_models.py`` for the differential check against
      ``announce``).

    Neither ``model`` nor ``action`` is mutated.
    """
    worlds: FrozenSet[Tuple[World, Event]] = frozenset(
        (w, e)
        for w in model.worlds
        for e in action.events
        if satisfies_modal(action.pre[e], model, w)
    )

    # A relation the MODEL carries but the ACTION omits would intersect
    # with the empty event relation and silently WIPE the agent's epistemic
    # structure — after which K_a φ holds vacuously for every φ, breaking
    # factivity (adversarial-review reproduced: forgetting one agent in
    # public_announcement_action made K_c(¬P) true with P true everywhere).
    # BMS action models must specify every agent's event relation; refuse
    # loudly instead of manufacturing an omniscient agent.
    missing = sorted(set(model.relations.keys())
                     - set(action.relations.keys()))
    if missing:
        raise ValueError(
            "product_update: the action model omits relation name(s) "
            f"{missing!r} that the base model carries — an omitted agent "
            "would come out with an EMPTY product relation (vacuously "
            "omniscient), not an unchanged one. Give every such agent an "
            "explicit event relation (for a public announcement: include "
            "the agent in public_announcement_action's agents).")

    names = set(model.relations.keys()) | set(action.relations.keys())
    relations: Dict[str, Set[Tuple[Tuple[World, Event], Tuple[World, Event]]]] = {}
    for name in names:
        model_edges = model.relation(name)
        action_edges = action.relation(name)
        relations[name] = {
            ((w, e), (w2, e2))
            for (w, w2) in model_edges
            for (e, e2) in action_edges
            if (w, e) in worlds and (w2, e2) in worlds
        }

    valuation = {(w, e): set(model.atoms_true_at(w)) for (w, e) in worlds}

    domains = None
    if model.domains is not None:
        domains = {(w, e): set(model.domain_at(w)) for (w, e) in worlds}

    return KripkeModel(worlds, relations, valuation, domains=domains)


# The single event public_announcement_action uses, spelled with the kit's own
# announcement glyph "!" (as in "[φ!]ψ" / "⟨φ!⟩ψ", see fol._modal_nodes.Announce)
# so a repr of the resulting ActionModel or its product worlds reads naturally.
_ANNOUNCE_EVENT = "!"


def public_announcement_action(formula: Node, agents: Iterable[str]) -> ActionModel:
    """Return the 1-event :class:`ActionModel` whose product update IS a public announcement of ``formula``.

    The classic BMS special case (Baltag-Moss-Solecki 1998, §1; van Ditmarsch
    et al. 2007, Example 6.6): a SINGLE event ``"!"`` with precondition
    ``formula`` and, for every agent in ``agents``, the identity relation
    ``{("!", "!")}`` (an agent can only relate the one event to itself —
    vacuously true, since there IS only one event, but stated explicitly so
    the relation NAME ``"K:" + agent`` is populated and the product picks it
    up for every requested agent, not just the ones the base model happens to
    already have a ``"K:"+agent`` relation for).

    ``product_update(model, public_announcement_action(formula, agents))`` is
    then EXACTLY :func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce`
    up to the obvious relabelling ``(w, "!") ↦ w`` — PROVIDED ``agents``
    covers every ``"K:"+agent`` relation the base model carries (a shorter
    list no longer diverges silently: ``product_update`` refuses it, see
    its missing-relation check; ``announce`` itself restricts EVERY
    relation and needs no agent list at all):

    - worlds: ``{(w, "!") : M,w ⊨ formula}`` — the SAME survivor set as
      ``announce``'s ``{w : M,w ⊨ formula}``, just each tagged with the one
      event.
    - ``K:agent`` edges: ``(w,"!") R (w',"!")`` iff ``w R w'`` in ``model``
      (the action's identity relation on the single event never removes an
      edge — so the product restricts EXACTLY to survivor-to-survivor edges
      of ``model``'s own relation), matching ``announce``'s own relation
      restriction verbatim.
    - valuation/domains: copied from ``w`` unchanged on both sides.

    ``tests/test_action_models.py`` cross-checks this agreement explicitly
    (worlds, every relation, and valuation) rather than asserting it here —
    see ``test_public_announcement_action_agrees_with_announce``.
    """
    agents = list(agents)
    return ActionModel(
        events=[_ANNOUNCE_EVENT],
        pre={_ANNOUNCE_EVENT: formula},
        relations={
            _KNOWS_PREFIX + agent: {(_ANNOUNCE_EVENT, _ANNOUNCE_EVENT)}
            for agent in agents
        },
    )
