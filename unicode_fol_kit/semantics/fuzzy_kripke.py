"""Graded (fuzzy) Kripke semantics: a truth-DEGREE evaluator for propositional
modal logic over a t-norm, generalising :mod:`kripke`'s two-valued
satisfaction relation the way :mod:`fuzzy` generalises classical FOL.

A :class:`FuzzyKripkeModel` is the graded analogue of
:class:`~unicode_fol_kit.semantics.kripke.KripkeModel`: instead of a crisp
edge SET, each named accessibility relation is a ``Dict[(w, w'), float]`` of
edge WEIGHTS in ``[0, 1]`` (a missing pair reads as ``0.0``); instead of a
crisp atom-key SET, each world's valuation is a ``Dict[str, float]`` of
ground-atom DEGREES in ``[0, 1]`` (a missing key reads as ``0.0``). This is
exactly the "fuzzify every crisp component of the frame" move of Fitting's
many-valued modal logics (M. Fitting, "Many-valued modal logics",
*Fundamenta Informaticae* 15(3-4), 1991, 235-254, and its sequel "Many-valued
modal logics II", *Fundamenta Informaticae* 17(1-2), 1992, 55-73) and of the
residuated Kripke frames studied by Hájek (P. Hájek, *Metamathematics of
Fuzzy Logic*, Kluwer, 1998, ch. 8) and, for the specific residuated □ /
t-norm ◇ pair implemented here, by Bou, Esteva, Godo & Rodríguez ("On the
minimum many-valued modal logic over a finite residuated lattice", *Journal
of Logic and Computation* 21(5), 2011, 739-790).

:func:`satisfies_fuzzy_modal` returns a truth DEGREE in ``[0, 1]`` (mirroring
:func:`~unicode_fol_kit.semantics.fuzzy.evaluate`'s float-returning shape,
not :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`'s bool one):

- an ``Atom`` looks up its degree in the current world's valuation;
- the Łukasiewicz connectives (``LukNegation`` / ``WeakConjunction`` /
  ``WeakDisjunction`` / ``StrongConjunction`` / ``StrongDisjunction`` /
  ``LukImplication`` / ``LukEquivalence``) dispatch straight to
  ``model.tnorm``'s ``neg`` / weak min-max / ``conj`` / ``disj`` / ``impl`` /
  ``equiv`` — verbatim reuse of :mod:`tnorm`, no new connective semantics;
- ``Box φ`` is the RESIDUATED universal reading
  ``inf_{w'} tnorm.impl(R(w, w'), deg(φ, w'))`` — "every accessible world
  forces φ AT LEAST as much as it is accessible" — and ``Diamond φ`` is the
  T-NORM existential reading ``sup_{w'} tnorm.conj(R(w, w'), deg(φ, w'))`` —
  "some accessible world witnesses φ, discounted by how accessible it is".
  The aggregation domain at ``world`` is ``model.worlds`` UNIONED with every
  actual edge target ``w'`` for which ``(world, w') `` has a positive weight
  in the named relation — this matches
  :meth:`~unicode_fol_kit.semantics.kripke.KripkeModel.successors` exactly,
  which is never filtered by ``model.worlds`` either (a relation may name an
  edge to a world outside the declared ``worlds=`` set, and that edge must
  still be counted, not silently dropped). Because ``tnorm.impl(0, y) = 1``
  and ``tnorm.conj(0, y) = 0`` for all three t-norms in :mod:`tnorm` (0 is
  the residuum's right-identity and the t-norm's absorbing element), the
  ``model.worlds`` members that carry no edge to them contribute only the
  aggregate's neutral element, so folding them into the domain alongside the
  true successors is always safe. An empty aggregation domain (no worlds
  declared AND no successor edge from ``world`` in this relation) is the one
  place the aggregate set is genuinely empty; it is handled by the same
  convention :mod:`~unicode_fol_kit.semantics.kripke` uses for a vacuous
  crisp Box/Diamond: infimum over the empty set is ``1.0``, supremum is
  ``0.0``.
  ``Knows`` / ``Believes`` / ``Says`` / ``Wants`` get the same residuated
  UNIVERSAL reading as ``Box`` (matching
  :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`, where all four
  are ``all(...)``-quantified exactly like Box) over their own
  ``"K:"``/``"B:"``/``"Say:"``/``"Want:"``-prefixed relation, for free, via
  the same relation-name mechanism :mod:`kripke` documents.

**v1 scope** (deliberately narrow, matching
:mod:`~unicode_fol_kit.semantics.kripke`'s own "propositional / ground, v1"
discipline): exactly graded ``Box``/``Diamond``/``Knows``/``Believes``/
``Says``/``Wants``, single-step aggregation, no fixpoints, plus the
Łukasiewicz connectives. Every other node kind :mod:`kripke` interprets is
REJECTED here by name by design, not silently approximated:

- classical crisp connectives (``Not``/``And``/``Or``/``Implies``/``Iff``/
  ``Xor``) — a formula meant for graded evaluation must be built with fuzzy
  connective nodes, the same discipline :mod:`fuzzy` already enforces for
  non-modal formulas;
- ``Quantifier``/``SortedQuantifier`` and the lambda-calculus nodes, rejected
  via :mod:`_modal_reject`'s shared ``reject_quantifier``/``reject_lambda``
  (unchanged, so the message wording matches :mod:`kripke`'s own);
- temporal closure (``Next``/``Always``/``Eventually``/``Until``/
  ``Previous``/``Historically``/``Once``/``Since``), hybrid logic
  (``Nominal``/``At``), public announcement logic (``Announce``/
  ``AnnounceDiamond``), group-epistemic operators (``EverybodyKnows``/
  ``DistributedKnowledge``/``CommonKnowledge``), and Standard-Deontic-style
  serial-frame reasoning (``Obligatory``/``Permitted``) — a graded fixpoint,
  model update, or group-relation combinator over a CONTINUOUS t-norm is an
  open research question in its own right (what does "the least fixpoint of
  a residuated implication" even mean over ``[0, 1]``? how does public
  announcement restrict a model whose edges are weights, not a crisp
  subset?) and must not be silently approximated by, say, reusing the crisp
  fixpoint machinery over a 0/1-thresholded relation.

No parser change ships with this module: formulas are built via the Node API
directly (``Box(WeakConjunction(Atom("P", []), Atom("Q", [])))``), exactly
the precedent :mod:`~unicode_fol_kit.semantics.kripke` and
``docs/guide/quantified-modal.md`` already set for modal ASTs — "no parser
is involved" is a documented v1 limitation here too, not an oversight
(``MSFLParser`` still refuses ``modal=True, fuzzy=True`` together).
"""

from typing import Any, Dict, FrozenSet, Iterable, Mapping, NoReturn, Optional, Tuple
from types import MappingProxyType

from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Nominal, At,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)
from ..fol._modal_nodes import (
    Announce, AnnounceDiamond,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
)
from ._modal_reject import LAMBDA_TYPES, reject_quantifier, reject_lambda
from .tnorm import TNorm, LUKASIEWICZ

# Note on _modal_reject reuse: that module's FUZZY_TYPES / reject_fuzzy
# classify Łukasiewicz nodes as OUT OF SCOPE for the crisp Kripke evaluator —
# here they are exactly the nodes this module interprets, so only
# LAMBDA_TYPES / reject_lambda and reject_quantifier are reused from it.

# Relation-name prefixes, matching kripke.py's convention EXACTLY (the two
# modules must stay in sync on these strings so the same relations= dict
# shape reads the same way under both evaluators).
_ALETHIC = "alethic"
_KNOWS_PREFIX = "K:"
_BELIEVES_PREFIX = "B:"
_SAYS_PREFIX = "Say:"
_WANTS_PREFIX = "Want:"

World = Any
Edge = Tuple[World, World]


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic/assertive/bouletic agent term.

    Mirrors :func:`unicode_fol_kit.semantics.kripke._agent_key` exactly (kept
    as a small local copy rather than an import of that module's private
    helper, so this module stays self-contained the way its docstring
    promises), so a ``relations=`` dict built for one evaluator names its
    agent keys identically for the other.
    """
    return getattr(agent, "name", None) or agent.to_unicode_str()


def _clamp(x: float) -> float:
    """Defensively clamp a degree into the closed interval [0, 1]."""
    if x < 0.0:
        return 0.0
    if x > 1.0:
        return 1.0
    return x


class FuzzyKripkeModel:
    """A graded Kripke model: worlds, named WEIGHTED accessibility relations, and
    a graded valuation.

    Args:
        worlds: an iterable of worlds (any hashable values). Stored as a
            frozen set; duplicates collapse.
        relations: maps a relation NAME (str) to a ``Dict[(w, w'), float]`` of
            edge weights in ``[0, 1]`` — the graded generalisation of
            :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`'s crisp
            edge SETS. Recognised names follow the same convention:
            ``"alethic"`` (Box/Diamond), ``"K:"+agent`` (Knows),
            ``"B:"+agent`` (Believes), ``"Say:"+agent`` (Says),
            ``"Want:"+agent`` (Wants). A missing name is the everywhere-zero
            relation; within a named relation, a missing ``(w, w')`` pair
            reads as weight ``0.0``. Each weight is clamped into ``[0, 1]``.
        valuation: maps a world to a ``Dict[str, float]`` of GROUND-ATOM-KEY
            (``atom.to_unicode_str()``, the same convention as
            :mod:`~unicode_fol_kit.semantics.fuzzy`'s valuation and
            :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`'s atom
            keys) to a degree in ``[0, 1]``. A missing world, or a missing
            key within a world, reads as degree ``0.0``. Each degree is
            clamped into ``[0, 1]``.
        tnorm: a :class:`~unicode_fol_kit.semantics.tnorm.TNorm` instance
            (one of :data:`~unicode_fol_kit.semantics.tnorm.LUKASIEWICZ`,
            :data:`~unicode_fol_kit.semantics.tnorm.GODEL`,
            :data:`~unicode_fol_kit.semantics.tnorm.PRODUCT`, or a custom
            one) fixing the strong connectives AND the Box/Diamond residuum —
            reused UNMODIFIED from :mod:`tnorm`, never re-implemented here.
            Defaults to :data:`~unicode_fol_kit.semantics.tnorm.LUKASIEWICZ`.

    All mappings default to empty, so ``FuzzyKripkeModel({0, 1})`` is a valid
    (atom-free, relation-free, everywhere-0.0) frame. The constructor copies
    every container into an immutable ``MappingProxyType`` view, so later
    edits to the caller's structures never leak in.
    """

    def __init__(
        self,
        worlds: Iterable[World],
        relations: Optional[Mapping[str, Mapping[Edge, float]]] = None,
        valuation: Optional[Mapping[World, Mapping[str, float]]] = None,
        tnorm: TNorm = LUKASIEWICZ,
    ):
        if not isinstance(tnorm, TNorm):
            raise TypeError(
                f"FuzzyKripkeModel: tnorm must be a TNorm instance (e.g. "
                f"tnorm.LUKASIEWICZ / GODEL / PRODUCT), got {type(tnorm).__name__}."
            )
        self.worlds: FrozenSet[World] = frozenset(worlds)
        self.relations: Dict[str, Mapping[Edge, float]] = {
            name: MappingProxyType({edge: _clamp(float(w)) for edge, w in edges.items()})
            for name, edges in (relations or {}).items()
        }
        self.valuation: Dict[World, Mapping[str, float]] = {
            world: MappingProxyType({key: _clamp(float(d)) for key, d in degrees.items()})
            for world, degrees in (valuation or {}).items()
        }
        self.tnorm: TNorm = tnorm

    def __repr__(self) -> str:
        """Show world count and the relation / valuation tables for inspection."""
        return (
            f"FuzzyKripkeModel(worlds={set(self.worlds)!r}, "
            f"relations={ {k: dict(v) for k, v in self.relations.items()} !r}, "
            f"valuation={ {k: dict(v) for k, v in self.valuation.items()} !r}, "
            f"tnorm={self.tnorm.name!r})"
        )

    def relation_weight(self, name: str, w1: World, w2: World) -> float:
        """Return the ``(w1, w2)`` edge weight of the named relation (0.0 if absent)."""
        return self.relations.get(name, MappingProxyType({})).get((w1, w2), 0.0)

    def atom_degree(self, world: World, key: str) -> float:
        """Return the degree of ground-atom key ``key`` at ``world`` (0.0 if absent)."""
        return self.valuation.get(world, MappingProxyType({})).get(key, 0.0)


def _aggregation_domain(rel_name: str, model: FuzzyKripkeModel, world: World) -> FrozenSet[World]:
    """The set of ``w'`` a Box/Diamond aggregate at ``world`` must range over.

    ``model.worlds`` UNIONED with every actual edge target of the named
    relation from ``world`` (even one outside ``model.worlds``) — this
    matches :meth:`~unicode_fol_kit.semantics.kripke.KripkeModel.successors`
    exactly, which is never filtered by ``model.worlds`` either. A
    ``model.worlds`` member with no edge to it still appears here, but only
    ever contributes the aggregate's neutral element (see the module
    docstring), so including it is always safe.
    """
    edges = model.relations.get(rel_name, MappingProxyType({}))
    successors = {w2 for (w1, w2) in edges if w1 == world}
    return model.worlds | successors


def _residuated_box(rel_name: str, formula: Node, model: FuzzyKripkeModel, world: World) -> float:
    """``inf_{w'} tnorm.impl(R(rel_name)(world, w'), deg(formula, w'))`` over the
    aggregation domain (see :func:`_aggregation_domain`).

    The shared aggregator behind ``Box``/``Knows``/``Believes``/``Says``/
    ``Wants``, all of which read universally in the crisp evaluator.
    """
    domain = _aggregation_domain(rel_name, model, world)
    if not domain:
        return 1.0
    t = model.tnorm
    return min(
        t.impl(model.relation_weight(rel_name, world, w2),
               satisfies_fuzzy_modal(formula, model, w2))
        for w2 in domain
    )


def _tnorm_diamond(rel_name: str, formula: Node, model: FuzzyKripkeModel, world: World) -> float:
    """``sup_{w'} tnorm.conj(R(rel_name)(world, w'), deg(formula, w'))`` over the
    aggregation domain (see :func:`_aggregation_domain`).

    The existential counterpart of :func:`_residuated_box`; only ``Diamond``
    uses it (Knows/Believes/Says/Wants are all universal, per the module
    docstring).
    """
    domain = _aggregation_domain(rel_name, model, world)
    if not domain:
        return 0.0
    t = model.tnorm
    return max(
        t.conj(model.relation_weight(rel_name, world, w2),
               satisfies_fuzzy_modal(formula, model, w2))
        for w2 in domain
    )


# Classical connective classes that must not appear in fuzzy modal input —
# same discipline (and message shape) as fuzzy.py's _CLASSICAL_CONNECTIVES.
_CLASSICAL_CONNECTIVES = (Not, And, Or, Xor, Implies, Iff)

# Out-of-scope modal node families, rejected BY NAME with a category label
# (see the module docstring's "v1 scope" section for why each is excluded).
_TEMPORAL_TYPES = (Next, Always, Eventually, Until, Previous, Historically, Once, Since)
_HYBRID_TYPES = (Nominal, At)
_PAL_TYPES = (Announce, AnnounceDiamond)
_DEONTIC_TYPES = (Obligatory, Permitted)
_GROUP_EPISTEMIC_TYPES = (EverybodyKnows, DistributedKnowledge, CommonKnowledge)


def _reject_out_of_scope(formula: Node, caller: str, category: str) -> NoReturn:
    """Reject a modal node family the graded evaluator does not interpret in v1.

    Names both the offending node TYPE and the CATEGORY it belongs to, and
    states the reason (a graded fixpoint/model-update/group-combinator over a
    continuous t-norm is open research, not a silently-approximable detail) —
    see the module docstring's "v1 scope" section.
    """
    raise NotImplementedError(
        f"{caller}: {type(formula).__name__} ({category}) is not supported by "
        "the graded (fuzzy) Kripke evaluator — v1 covers exactly graded "
        "Box/Diamond/Knows/Believes/Says/Wants with single-step aggregation, "
        "no fixpoints; graded temporal closure, hybrid logic, public "
        "announcement model updates, group-epistemic combinators, and "
        "deontic serial-frame reasoning over a continuous t-norm are open "
        "research questions in their own right and must not be silently "
        "approximated. This is future work, tracked the same way "
        "kripke.py/_modal_reject.py track quantified/lambda modal logic."
    )


def satisfies_fuzzy_modal(formula: Node, model: FuzzyKripkeModel, world: World) -> float:
    """Compute the truth DEGREE in ``[0, 1]`` of ``formula`` at ``world`` in ``model``.

    Args:
        formula: a propositional/ground modal formula built from the Node API
            directly (no parser is involved — see the module docstring),
            using Łukasiewicz connective nodes (never classical And/Or/Not/
            Implies/Iff/Xor) under Box/Diamond/Knows/Believes/Says/Wants.
        model: the :class:`FuzzyKripkeModel` to evaluate against.
        world: the world to evaluate at (any hashable value; need not be a
            member of ``model.worlds``, exactly like
            :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`).

    Returns:
        The truth degree as a float clamped to ``[0, 1]``.

    Raises:
        NotImplementedError: on a Quantifier/SortedQuantifier, a lambda node,
            temporal/hybrid/PAL/group-epistemic/deontic node (all future
            work — see the module docstring), or an otherwise unsupported
            node type.
        TypeError: on a classical crisp connective (build the formula with
            fuzzy connective nodes instead).
    """
    t = model.tnorm

    # --- atomic ---
    if isinstance(formula, Atom):
        return _clamp(model.atom_degree(world, formula.to_unicode_str()))

    # --- Łukasiewicz connectives: verbatim dispatch into model.tnorm ---
    if isinstance(formula, LukNegation):
        return _clamp(t.neg(satisfies_fuzzy_modal(formula.formula, model, world)))
    if isinstance(formula, (WeakConjunction, WeakDisjunction,
                            StrongConjunction, StrongDisjunction,
                            LukImplication, LukEquivalence)):
        x = satisfies_fuzzy_modal(formula.left, model, world)
        y = satisfies_fuzzy_modal(formula.right, model, world)
        if isinstance(formula, WeakConjunction):
            return _clamp(min(x, y))
        if isinstance(formula, WeakDisjunction):
            return _clamp(max(x, y))
        if isinstance(formula, StrongConjunction):
            return _clamp(t.conj(x, y))
        if isinstance(formula, StrongDisjunction):
            return _clamp(t.disj(x, y))
        if isinstance(formula, LukImplication):
            return _clamp(t.impl(x, y))
        return _clamp(t.equiv(x, y))  # LukEquivalence

    # --- alethic: residuated universal Box, t-norm existential Diamond ---
    if isinstance(formula, Box):
        return _clamp(_residuated_box(_ALETHIC, formula.formula, model, world))
    if isinstance(formula, Diamond):
        return _clamp(_tnorm_diamond(_ALETHIC, formula.formula, model, world))

    # --- epistemic / doxastic / assertive / bouletic (all four residuated-universal,
    # matching kripke.py's satisfies_modal where all four are all(...)-quantified) ---
    if isinstance(formula, Knows):
        rel = _KNOWS_PREFIX + _agent_key(formula.agent)
        return _clamp(_residuated_box(rel, formula.formula, model, world))
    if isinstance(formula, Believes):
        rel = _BELIEVES_PREFIX + _agent_key(formula.agent)
        return _clamp(_residuated_box(rel, formula.formula, model, world))
    if isinstance(formula, Says):
        rel = _SAYS_PREFIX + _agent_key(formula.agent)
        return _clamp(_residuated_box(rel, formula.formula, model, world))
    if isinstance(formula, Wants):
        rel = _WANTS_PREFIX + _agent_key(formula.agent)
        return _clamp(_residuated_box(rel, formula.formula, model, world))

    # --- rejected: classical crisp connectives ---
    if isinstance(formula, _CLASSICAL_CONNECTIVES):
        raise TypeError(
            f"Classical connective {type(formula).__name__} is not valid in graded "
            "modal input; build the formula with Łukasiewicz connective nodes "
            "(LukNegation/WeakConjunction/WeakDisjunction/StrongConjunction/"
            "StrongDisjunction/LukImplication/LukEquivalence) instead — the same "
            "discipline unicode_fol_kit.semantics.fuzzy already enforces for "
            "non-modal formulas."
        )

    # --- rejected: quantifiers / lambda (shared with kripke.py's v1 discipline) ---
    if isinstance(formula, (Quantifier, SortedQuantifier)):
        reject_quantifier(formula, "satisfies_fuzzy_modal")
    if isinstance(formula, LAMBDA_TYPES):
        reject_lambda(formula, "satisfies_fuzzy_modal")

    # --- rejected: out-of-scope modal node families (see module docstring) ---
    if isinstance(formula, _TEMPORAL_TYPES):
        _reject_out_of_scope(formula, "satisfies_fuzzy_modal", "temporal")
    if isinstance(formula, _HYBRID_TYPES):
        _reject_out_of_scope(formula, "satisfies_fuzzy_modal", "hybrid")
    if isinstance(formula, _PAL_TYPES):
        _reject_out_of_scope(formula, "satisfies_fuzzy_modal", "public announcement logic")
    if isinstance(formula, _GROUP_EPISTEMIC_TYPES):
        _reject_out_of_scope(formula, "satisfies_fuzzy_modal", "group-epistemic")
    if isinstance(formula, _DEONTIC_TYPES):
        _reject_out_of_scope(formula, "satisfies_fuzzy_modal", "deontic")

    raise NotImplementedError(
        f"satisfies_fuzzy_modal: unsupported node type {type(formula).__name__}."
    )
