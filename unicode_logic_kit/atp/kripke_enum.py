"""Bounded enumeration of finite Kripke models — a semantic refutation oracle for
the modal fragment the labelled tableau cannot decide.

:mod:`unicode_logic_kit.atp.modal_tableau` has no proof rule for the temporal
*closure* operators (Always ``Ⓖ`` / Eventually ``Ⓕ`` / Until ``Ⓤ`` /
Historically ``⒣`` / Once ``⒫`` / Previous ``⒴`` / Since ``⒮`` — see
``modal_tableau._TEMPORAL_CLOSURE``): it marks a labelled formula built from one
of them INERT and reports ``"unknown"`` for any branch that only stays open
because of it. The quantified-modal-logic route (``fol.qml``) is sound but
proof-only (Z3 over the standard translation never REFUTES). Net effect: an
INVALID temporal formula such as ``Ⓕ P → P`` stays "unknown" — nothing in the
kit ever refutes it.

This module closes that gap for **refutation only**, the same way
:mod:`unicode_logic_kit.semantics.modelfinder` closes the analogous gap for plain
FOL: it exhaustively enumerates finite :class:`~unicode_logic_kit.semantics.kripke.KripkeModel`\\ s
of increasing world-count and hands each one to the EXISTING, already-tested
evaluator, :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal`, as an
oracle. Soundness is by construction: a returned countermodel is one
``satisfies_modal`` itself confirms falsifies the formula at world 0, so this
module contains no new semantic rule that could disagree with the one every
other Kripke-based route in the kit already relies on.

**What is enumerated.** For each relation family the formula actually uses
(``"alethic"`` for Box/Diamond, ``"K:"+agent`` / ``"B:"+agent`` /
``"Say:"+agent`` / ``"Want:"+agent`` for Knows/Believes/Says/Wants,
``"deontic"`` for Obligatory/Permitted, ``"temporal"`` for every temporal
operator — the exact naming convention documented in
:mod:`unicode_logic_kit.semantics.kripke`), every relation over ``{0, …, n-1}``
satisfying that family's frame condition is enumerated (the SAME frame-name
vocabulary as :mod:`unicode_logic_kit.atp.modal_tableau`: K/T/D/KD/B/KB/K4/K45/
S4/S5/KD45 for ``frame=``, plus per-family overrides via ``systems=``), crossed
with every valuation of the formula's ground atoms over those worlds. ``n``
ranges over ``1 .. max_worlds``. Each candidate model is checked with
``satisfies_modal(formula, model, 0)``; the first candidate where it comes back
``False`` is returned as the countermodel.

**Many-sorted ground formulas.** ``satisfies_modal`` relativizes a formula with a
sorted constant (``Mortal(socrates:Human)``) before it reads an atom, so the atom
it looks up is ``Mortal(socrates)``; the enumerator relativizes first too, and
varies THAT key. A sorted constant ``c:S`` is an element of ``S`` at every world
(``semantics.kripke``'s module docstring), so the guard atom ``S(c)`` is not
varied: it is true at every world of every candidate, and a countermodel this
search returns is therefore a model the many-sorted routes (``qml_is_valid``,
``api.prove``) would consider. A sorted QUANTIFIER still makes ``satisfies_modal``
ask for object domains, which these propositional models do not carry, and is
reported ``unsupported``.

**Predicate quantifiers.** ``satisfies_modal`` interprets ``∀P`` / ``∃P`` (a
bound predicate has an extension at each world), so a second-order modal formula
is searched like any other: the atoms headed by a bound predicate are not keys of
a candidate's valuation, and the evaluator ranges over their interpretations
itself, at ``2 ** (worlds * atoms)`` evaluations per quantifier. For propositional
quantifiers this is second-order propositional modal logic on the frames up to
``max_worlds`` worlds: ``∀P (□P → P)`` has a countermodel in ``K`` and none in
``T``. A formula whose bound predicates are applied to two different terms is
reported ``unsupported``: a candidate names an individual by its term, so no
candidate makes two terms name one individual, and ``∃P (P(a) ∧ ¬P(b))`` would be
given no countermodel although it has one.

**Three-way honesty, not two.** A search that finds no countermodel does NOT
mean the formula is valid — it means one of two different things, and
:class:`EnumSearchResult` keeps them apart instead of collapsing them into a
single ``None``:

- ``exhausted=True``  — EVERY candidate up to ``max_worlds`` was checked and
  none refuted the formula. This is a genuine, documentable statement ("no
  countermodel with ≤ ``max_worlds`` worlds, under this frame, exists"), but it
  is still **not a validity proof**: modal logic has no small-model property
  bounding countermodels to 3 worlds in general, so a larger, unexplored model
  might still refute the formula.
- ``exhausted=False`` (with ``model=None``) — the ``max_models`` candidate
  budget ran out before the ``max_worlds`` search space was fully covered, or
  ``max_atoms`` rejected the formula up front. Weaker than "exhausted": the
  small worlds were not even fully explored.
- ``timed_out=True`` (with ``model=None``) — the wall-clock ``timeout`` ran out
  first. The clock is read before every candidate model, while the relations
  and valuations of a world count are built, and while the next world count's
  relations are enumerated, so a search ends within the cost of one candidate
  (or of 256 edge sets of the relation enumeration) of its deadline however
  large the space is; a single evaluation of the formula in one model is not
  interrupted.

A formula outside the propositional/ground modal fragment ``satisfies_modal``
itself understands (a first-order quantifier with no per-world domain, an
unassigned hybrid nominal, a Lewis counterfactual, …) makes the evaluator raise
— caught here and reported as ``unsupported`` rather than silently skipped or
misreported as a bound. So is a formula in which two different atoms print alike (the
numeral ``1`` and a constant named ``1``, a free variable ``x`` and a constant named ``x``)
or two different agents are named alike: a valuation and a relation family are keyed by the
written form, so the pair would be ONE key of every candidate and "no countermodel" would be
said of a formula that has one.

**Determinism.** Every enumeration order (relations by bitmask over a
fixed, sorted pair list; valuations by bitmask over a fixed, sorted atom list;
worlds by increasing count) is fixed and free of hashing/set-iteration
nondeterminism, so two calls with identical arguments return bit-for-bit the
same model.

**Cost.** The candidate space is
``sum_{n=1..max_worlds} (worlds^worlds-per-family-relation-count) * 2^(atoms * n)``
— it grows fast in both the number of distinct relation families the formula
mixes and its atom count. ``max_atoms`` and ``max_models`` are the two knobs
that keep a pathological formula from hanging; both give an honest
``exhausted=False`` rather than either blocking forever or answering wrong. The
third, ``timeout`` (milliseconds), is the only one that bounds the TIME rather
than the size of the search; it gives ``timed_out=True``.

Public API: :class:`EnumSearchResult`, :func:`modal_enum_search`,
:func:`modal_enum_countermodel`, :class:`KripkeEnumBackend`, plus the witness
converters :func:`kripke_model_to_dict` / :func:`kripke_model_from_dict`
(the ``"data"`` payload of every ``"kripke"`` witness dict).
"""

import itertools
from dataclasses import dataclass
from functools import lru_cache
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from .._deadline import instant as _instant, passed as _passed
from ..fol.nodes import (
    Node, Atom,
    Box, Diamond, Knows, Believes, Says, Wants, Obligatory, Permitted,
    Next, Always, Eventually, Until, Historically, Once, Previous, Since,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    SecondOrderQuantifier,
    sort_axioms, sort_membership_axioms,
)
from ..fol._atom_keys import AtomKeys, refuse_alike_agents
from ..fol._msfl_nodes import key_text
from ..fol._truth_constants import truth_value as _truth_value
from ..semantics.kripke import KripkeModel, satisfies_modal
from ..fol.frames import (
    FRAMES as _FRAMES, resolve_frame, holds_on_finite_frame,
)
from .protocol import ProverBackend, Verdict, REFUTED, UNKNOWN

# Relation-name convention — must match semantics.kripke.KripkeModel exactly
# (see that module's docstring, "Relation-name convention").
_ALETHIC = "alethic"
_DEONTIC = "deontic"
_TEMPORAL = "temporal"
_KNOWS_PREFIX = "K:"
_BELIEVES_PREFIX = "B:"
_SAYS_PREFIX = "Say:"
_WANTS_PREFIX = "Want:"

#: Node types whose satisfaction is defined over the "temporal" relation.
_TEMPORAL_TYPES = (Next, Always, Eventually, Until, Historically, Once, Previous, Since)

#: Frame-condition-catching exceptions from satisfies_modal — anything here on
#: a candidate means the FORMULA (not the candidate model) is out of scope for
#: this propositional/ground enumerator; see the module docstring's "A formula
#: outside the propositional/ground modal fragment" paragraph.
_UNSUPPORTED_EXC = (NotImplementedError, ValueError, TypeError, KeyError)


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic/assertive/bouletic agent term.

    Mirrors the identically-named private helper in ``semantics.kripke`` and
    ``atp.modal_tableau`` (each module keeps its own copy rather than share a
    private cross-module import for a two-line function): the agent's
    ``.name`` if it has one (a Constant or Variable), else its rendered form.
    """
    return getattr(agent, "name", None) or key_text(agent)


def _collect(formula: Node) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
    """Scan ``formula`` for its ground-atom keys and the relation families it uses.

    Returns ``(atoms, families)``, both sorted tuples (deterministic order):
    ``atoms`` are the ``key_text`` keys (every constant written by its bare name) the
    valuation must cover;
    ``families`` are the relation NAMES (in the ``semantics.kripke`` convention)
    the enumerator must build a relation for — one entry per distinct alethic /
    epistemic-per-agent / doxastic-per-agent / assertive-per-agent /
    bouletic-per-agent / deontic / temporal operator family actually present.
    A formula with no modal operators at all yields an empty ``families``
    tuple (the propositional case: only world 0's valuation matters).

    An atom headed by a predicate that an enclosing ``∀P`` / ``∃P`` binds is not a
    key of the valuation: the evaluator ranges over its interpretations itself. An
    occurrence of the same name outside every such quantifier is a free atom and
    is listed, so ``P ∧ ∃P ¬P`` has the one atom ``P``.
    """
    atoms: set = set()
    families: set = set()
    stack: List[Tuple[Node, FrozenSet[str]]] = [(formula, frozenset())]
    while stack:
        node, bound = stack.pop()
        if isinstance(node, SecondOrderQuantifier):
            bound = bound | {node.predicate}
        stack.extend((child, bound) for child in node._child_nodes())
        if isinstance(node, Atom):
            # `$true` / `$false` are not varied
            if _truth_value(node) is None and node.predicate not in bound:
                atoms.add(key_text(node))
        elif isinstance(node, (Box, Diamond)):
            families.add(_ALETHIC)
        elif isinstance(node, Knows):
            families.add(_KNOWS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, (EverybodyKnows, DistributedKnowledge, CommonKnowledge)):
            # Every group member's "K:"+agent relation is searched and frame-
            # checked. Dropping it would fix the relation empty on every
            # candidate, which under e.g. S5 is not even a legal frame and
            # "refutes" the valid E_{a} P → P.
            families.update(_KNOWS_PREFIX + _agent_key(member) for member in node.group)
        elif isinstance(node, Believes):
            families.add(_BELIEVES_PREFIX + _agent_key(node.agent))
        elif isinstance(node, Says):
            families.add(_SAYS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, Wants):
            families.add(_WANTS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, (Obligatory, Permitted)):
            families.add(_DEONTIC)
        elif isinstance(node, _TEMPORAL_TYPES):
            families.add(_TEMPORAL)
    return tuple(sorted(atoms)), tuple(sorted(families))


def _terms_under_bound_predicates(formula: Node) -> Tuple[str, ...]:
    """The argument terms of the atoms headed by a bound predicate, by key, each once, sorted.

    A model of this search names an individual by its term, so two different terms are two
    individuals in every candidate. A formula without predicate quantifiers cannot tell: a
    model in which two terms name one individual is matched by one in which they name two
    and every atom keeps its value. A predicate quantifier can tell (``∃P (P(a) ∧ ¬P(b))``
    says that ``a`` and ``b`` are two), so with two different terms under bound predicates
    the candidates leave out models that matter. With at most one term they do not.
    """
    terms: set = set()
    stack: List[Tuple[Node, FrozenSet[str]]] = [(formula, frozenset())]
    while stack:
        node, bound = stack.pop()
        if isinstance(node, SecondOrderQuantifier):
            bound = bound | {node.predicate}
        elif isinstance(node, Atom) and node.predicate in bound:
            terms.update(key_text(arg) for arg in node.args)
        stack.extend((child, bound) for child in node._child_nodes())
    return tuple(sorted(terms))


def _check_frame(frame: str, systems: Optional[Dict[str, str]]) -> None:
    """Resolve every frame name this search will use, raising if any is unknown.

    The enumerator carries every condition in the shared registry that a
    FINITE frame check can decide — every first-order condition (a condition
    on a finite relation is directly checkable), and, via each one's finite
    structural characterisation (:func:`~unicode_logic_kit.fol.frames.holds_on_finite_frame`),
    Löb, McKinsey and Grz too — which is more than the labelled tableau's
    rule set, so it validates frames itself rather than borrowing the
    tableau's stricter check. There is nothing left for this function to
    refuse by condition: it only resolves each name, which still raises
    ``ValueError`` for one that names no known system or Geach spec.
    """
    names = [frame]
    for fam, sys in (systems or {}).items():
        if fam not in ("epistemic", "doxastic", "deontic", "temporal"):
            raise ValueError(
                f"kripke_enum: unknown system family {fam!r} (use epistemic / "
                "doxastic / deontic / temporal).")
        names.append(sys)
    for name in names:
        try:
            resolve_frame(name)
        except ValueError as exc:
            raise ValueError(f"kripke_enum: {exc}") from None


def _conditions_for(relname: str, frame: str, systems: Optional[Dict[str, str]]) -> Tuple[str, ...]:
    """Frame conditions for a relation name, mirroring ``modal_tableau._Ctx.conds``.

    ``"alethic"`` uses ``frame`` directly; ``"deontic"``/``"temporal"`` and the
    ``"K:"``/``"B:"`` families use their ``systems[...]`` override (default
    ``"KD"`` for deontic, ``"K"`` for the rest) — the exact same defaulting
    ``atp.modal_tableau`` applies, so a formula decided by both routes is
    decided over the SAME frame. ``"Say:"``/``"Want:"`` agents and any other
    family get no frame condition (plain K): Says/Wants are documented as
    non-factive/non-veridical K-modalities with no ``systems`` entry in
    ``modal_tableau`` either.
    """
    systems = systems or {}
    if relname == _ALETHIC:
        return resolve_frame(frame)
    if relname == _DEONTIC:
        return resolve_frame(systems.get("deontic", "KD"))
    if relname == _TEMPORAL:
        return resolve_frame(systems.get("temporal", "K"))
    if relname.startswith(_KNOWS_PREFIX):
        return resolve_frame(systems.get("epistemic", "K"))
    if relname.startswith(_BELIEVES_PREFIX):
        return resolve_frame(systems.get("doxastic", "K"))
    return ()


def _holds_conditions(edges: FrozenSet[Tuple[int, int]], n: int, conditions: Tuple[str, ...]) -> bool:
    """True iff the edge set ``edges`` over ``range(n)`` satisfies every condition.

    Delegates to :func:`unicode_logic_kit.fol.frames.holds_on_finite_frame`, the
    checker the correspondence tests use as well. Delegating matters for
    SOUNDNESS, not tidiness: this function used to test the five conditions it
    knew and IGNORE any other, so a frame class it did not recognise silently
    widened to the ones it did — and a countermodel the named system excludes
    would have been reported as if it refuted the formula. An unknown
    condition now raises instead — Löb/Grz/McKinsey are no exception: each
    is decided by its own finite structural characterisation, not raised.
    """
    return all(holds_on_finite_frame(cond, edges, n) for cond in conditions)


@lru_cache(maxsize=None)
def _valid_relations(n: int, conditions: Tuple[str, ...]) -> Tuple[FrozenSet[Tuple[int, int]], ...]:
    """Every edge set over ``range(n) x range(n)`` satisfying ``conditions``, in bitmask order.

    Deterministic and cached (families sharing the same conditions — e.g. two
    K-system epistemic agents — reuse the same enumeration and the same cache
    entry). Brute-force over ``2**(n*n)`` subsets, which is why callers keep
    ``max_worlds`` small (n=3 already means 512 subsets to filter per family).
    """
    pairs = [(a, b) for a in range(n) for b in range(n)]
    out = []
    for mask in range(1 << len(pairs)):
        edges = frozenset(p for i, p in enumerate(pairs) if (mask >> i) & 1)
        if _holds_conditions(edges, n, conditions):
            out.append(edges)
    return tuple(out)


#: The world counts up to which :func:`_valid_relations_until` uses :func:`_valid_relations`
#: even under a deadline: ``2 ** (n * n)`` masks are a few hundred, so it cannot overrun.
_UNTIMED_RELATION_WORLDS = 3

#: The relation sets that :func:`_valid_relations_until` completed under a deadline.
_TIMED_RELATIONS: Dict[Tuple[int, Tuple[str, ...]], Tuple[FrozenSet[Tuple[int, int]], ...]] = {}


def _valid_relations_until(n: int, conditions: Tuple[str, ...],
                           deadline: Optional[float]) -> Optional[Tuple[FrozenSet[Tuple[int, int]], ...]]:
    """:func:`_valid_relations`, or ``None`` if ``deadline`` (a ``perf_counter`` instant) passes first.

    Without a deadline, and for a world count too small to matter, this is
    :func:`_valid_relations` itself. Past that the ``2 ** (n * n)`` masks are enumerated here,
    reading the clock every 256 of them; a completed enumeration is kept, so a later call with
    the same ``n`` and ``conditions`` does not repeat it, and an interrupted one leaves nothing
    behind.
    """
    if deadline is None or n <= _UNTIMED_RELATION_WORLDS:
        return _valid_relations(n, conditions)
    key = (n, conditions)
    if key in _TIMED_RELATIONS:
        return _TIMED_RELATIONS[key]
    pairs = [(a, b) for a in range(n) for b in range(n)]
    out = []
    for mask in range(1 << len(pairs)):
        if not mask & 0xFF and _passed(deadline):
            return None
        edges = frozenset(p for i, p in enumerate(pairs) if (mask >> i) & 1)
        if _holds_conditions(edges, n, conditions):
            out.append(edges)
    _TIMED_RELATIONS[key] = tuple(out)
    return _TIMED_RELATIONS[key]


def _scan_sorted(formula: Node) -> Tuple[Node, Tuple[str, ...]]:
    """The formula the evaluator will read, and the atom keys a legal model fixes true.

    ``satisfies_modal`` relativizes a many-sorted formula before it reads an atom,
    so ``Mortal(socrates:Human)`` is looked up under the key ``Mortal(socrates)``
    — NOT under the key the unrelativized formula prints. The atoms the
    enumerator varies must be the atoms the evaluator reads, so a sorted formula
    is relativized HERE, once, before :func:`_collect` scans it.

    A sorted constant ``c:S`` also denotes an element of ``S`` at every world
    (it is a rigid designator; see the ``semantics.kripke`` module docstring), so
    the guard atom ``S(c)`` is not a free atom to enumerate: it is true in every
    world of every candidate. The second result lists those keys, sorted.

    A formula without any many-sorted node is returned UNCHANGED, with no fixed
    keys, so every unsorted caller sees exactly the search it always did.
    """
    if not sort_axioms(formula):
        return formula, ()
    fixed = tuple(sorted({key_text(atom)
                          for atom in sort_membership_axioms(formula)}))
    return formula._relativize([]), fixed


#: The number of valuations up to which one world count's valuations are held in a list
#: and reused for every relation choice (see :func:`modal_enum_search`).
_CACHED_VALUATIONS = 1 << 14


def _bitmask_tuples(count: int, n: int):
    """Yield every tuple of ``n`` integers of ``range(count)``, the first slowest.

    The order of ``itertools.product(range(count), repeat=n)``, produced one tuple at a time:
    ``product`` first copies its input into a tuple, which for the ``2 ** m`` bitmasks of ``m``
    atoms is more memory than a machine has long before ``m`` is large enough to matter.
    """
    if n == 0:
        yield ()
        return
    for head in range(count):
        for tail in _bitmask_tuples(count, n - 1):
            yield (head,) + tail


def _valuations(atoms: Tuple[str, ...], n: int, fixed: Tuple[str, ...] = ()):
    """Yield every valuation ``{world: frozenset(atoms true there)}`` over ``range(n)``.

    Deterministic bitmask order: for ``n`` worlds and ``m`` atoms, each of the
    ``(2**m)**n`` combinations is produced by ``itertools.product`` over a
    per-world bitmask in ``range(2**m)``, world 0 varying slowest — the same
    fixed order every call, so re-running a search reproduces the same model.
    The atom keys in ``fixed`` are true at every world of every valuation and are
    not enumerated.
    """
    m = len(atoms)
    for combo in _bitmask_tuples(1 << m, n):
        yield {
            w: frozenset(atoms[i] for i in range(m) if (bits >> i) & 1) | frozenset(fixed)
            for w, bits in enumerate(combo)
        }


@dataclass(frozen=True)
class EnumSearchResult:
    """The outcome of one :func:`modal_enum_search` call.

    Fields:

    ``model``
        a verified :class:`~unicode_logic_kit.semantics.kripke.KripkeModel`
        falsifying the searched formula at world 0, or ``None`` if none was
        found (whether because the space was exhausted, the budget ran out,
        or the formula is unsupported — see ``exhausted``/``unsupported``).
    ``exhausted``
        ``True`` iff ``model is None`` because EVERY candidate up to
        ``max_worlds`` was checked and none refuted the formula — a genuine
        "no countermodel with ≤ max_worlds worlds" statement, but NEVER a
        validity proof (see the module docstring). Always ``False`` when
        ``model`` is not ``None`` or ``unsupported`` is not ``None``.
    ``checked``
        the number of distinct candidate models actually run through
        ``satisfies_modal`` (informational; bounded by ``max_models``).
    ``unsupported``
        ``None`` if the formula is within the propositional/ground modal
        fragment ``satisfies_modal`` understands; otherwise the
        ``"ExceptionType: message"`` the evaluator raised on the formula,
        naming exactly why it is out of scope.
    ``detail``
        a short free-text explanation of which of the above happened.
    ``timed_out``
        ``True`` iff ``model is None`` because the ``timeout`` of the call
        passed before the search was complete. Always ``False`` for a search
        without a ``timeout``, for a model that was found and for
        ``exhausted=True``.
    """

    model: Optional[KripkeModel]
    exhausted: bool
    checked: int
    unsupported: Optional[str] = None
    detail: str = ""
    timed_out: bool = False

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (the model, if any, as worlds/relations/valuation)."""
        return {
            "found": self.model is not None,
            "exhausted": self.exhausted,
            "checked": self.checked,
            "unsupported": self.unsupported,
            "detail": self.detail,
            "timed_out": self.timed_out,
            "model": kripke_model_to_dict(self.model) if self.model is not None else None,
        }


def kripke_model_to_dict(model: KripkeModel) -> dict:
    """Render a :class:`KripkeModel` as a JSON-compatible dict.

    The shape is the structured ``"data"`` payload of every ``"kripke"``
    witness dict a :class:`~unicode_logic_kit.atp.protocol.Verdict` carries:
    ``{"worlds": [...], "relations": {name: [[w, w'], ...]}, "valuation":
    {str(world): [atom_key, ...]}}``, plus ``"nominals"`` / ``"domains"``
    keys ONLY when the model actually has them (the purely propositional
    models this module enumerates never do). Valuation/domain keys are
    ``str(world)`` because JSON object keys must be strings;
    :func:`kripke_model_from_dict` resolves them back against the typed
    ``"worlds"`` list.
    """
    data = {
        "worlds": sorted(model.worlds),
        "relations": {
            name: sorted([list(edge) for edge in edges])
            for name, edges in model.relations.items()
        },
        "valuation": {
            str(world): sorted(atoms) for world, atoms in model.valuation.items()
        },
    }
    if model.nominals:
        data["nominals"] = dict(sorted(model.nominals.items()))
    if model.domains is not None:
        data["domains"] = {
            str(world): sorted(individuals, key=repr)
            for world, individuals in model.domains.items()
        }
    return data


def kripke_model_from_dict(data: dict) -> KripkeModel:
    """Rebuild a :class:`KripkeModel` from :func:`kripke_model_to_dict` output.

    The inverse of :func:`kripke_model_to_dict` up to the container copying
    :class:`KripkeModel`'s constructor performs anyway: worlds, relations,
    valuation, and (when present) nominals and per-world domains all round
    trip. Valuation/domain keys arrive as ``str(world)`` and are mapped back
    to the typed world via the ``"worlds"`` list; a key matching no world is
    kept verbatim rather than guessed at (``KripkeModel`` treats an unknown
    valuation world as simply never queried).
    """
    worlds = list(data["worlds"])
    by_str = {str(world): world for world in worlds}
    relations = {
        name: [tuple(edge) for edge in edges]
        for name, edges in data.get("relations", {}).items()
    }
    valuation = {
        by_str.get(key, key): set(atoms)
        for key, atoms in data.get("valuation", {}).items()
    }
    domains = None
    if "domains" in data:
        domains = {
            by_str.get(key, key): set(individuals)
            for key, individuals in data["domains"].items()
        }
    return KripkeModel(worlds, relations, valuation,
                       domains=domains, nominals=data.get("nominals"))


def modal_enum_search(formula: Node, *, frame: str = "K",
                      systems: Optional[Dict[str, str]] = None,
                      max_worlds: int = 3, max_atoms: Optional[int] = None,
                      max_models: int = 200000,
                      timeout: Optional[float] = None) -> EnumSearchResult:
    """Exhaustively search finite Kripke models of increasing size for a countermodel.

    Enumerates every relation (per family, per the ``frame``/``systems`` frame
    conditions — see :func:`_conditions_for`) and every atom valuation over
    ``n = 1 .. max_worlds`` worlds, in a fixed deterministic order, and checks
    each candidate with :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal`
    (the existing, already-tested evaluator — this function adds no new
    semantic rule, only the search). The first candidate that falsifies
    ``formula`` at world 0 is returned immediately.

    Args:
        formula: the (already premise-folded, if applicable — see
            :class:`KripkeEnumBackend`) formula to search for a countermodel of.
        frame: the alethic frame name for ``"alethic"`` relations (Box/Diamond)
            — any name in :data:`unicode_logic_kit.fol.frames.FRAMES`, including
            ``"GL"``/``"S4.1"``/``"Grz"`` (decided via their finite structural
            characterisation — see the module docstring) and a Scott–Lemmon
            spec like ``"G(1,1,1,1)"``.
        systems: per-family frame overrides for deontic/temporal/epistemic/
            doxastic relations (``{"epistemic": "S5", ...}``), same convention
            and same defaults (KD for deontic, K for the rest) as
            ``modal_tableau``.
        max_worlds: the largest world-count searched (inclusive). Every ``n``
            from 1 up to this is tried in order, smallest countermodels first.
        max_atoms: if given, a formula using more than this many distinct
            ground atoms is rejected up front (``exhausted=False``,
            ``model=None``) rather than attempting a valuation space of
            ``2**(atoms*n)`` per world-count.
        max_models: the total number of candidate models actually evaluated
            (across every ``n``) before giving up. Bounds the worst case
            combinatorially, at the cost of an honest ``exhausted=False``
            instead of a complete search.
        timeout: a wall-clock limit in milliseconds, counted from the start of
            the call (default ``None``: no limit, the search is exactly the one
            it was without the argument). The clock is read before every
            candidate model and while the relations and valuations of a world
            count are built, so the search returns within the cost of one
            candidate of its deadline; the result has ``timed_out=True``,
            ``exhausted=False`` and no model.

    Returns:
        An :class:`EnumSearchResult` — see its docstring for how to read
        ``model``/``exhausted``/``unsupported`` together.

    Raises:
        ValueError: if ``frame`` or a ``systems`` entry names an unknown frame
            or system family. ``"GL"``/``"S4.1"``/``"Grz"`` are NOT refused —
            each has a finite structural characterisation
            (:func:`unicode_logic_kit.fol.frames.holds_on_finite_frame`) that
            this bounded enumerator decides directly, unlike the routes that
            emit a single first-order sentence over frames of every
            cardinality (``fol.qml``, ``fol.modal_translation``, ``atp.fitch``,
            the labelled tableau), which still refuse them.
    """
    _check_frame(frame, systems)
    try:
        scanned, fixed = _scan_sorted(formula)
    except _UNSUPPORTED_EXC + (RuntimeError,) as exc:
        # relativizing walks the whole tree and meets a node it has no rule for
        # (a Łukasiewicz operator under a sorted binder): the evaluator refuses
        # that formula too, so report it the way an evaluator refusal is reported.
        return EnumSearchResult(
            model=None, exhausted=False, checked=0,
            unsupported=f"{type(exc).__name__}: {exc}",
            detail=("a many-sorted formula could not be relativized — it is "
                    "outside the propositional/ground modal fragment this "
                    "enumerator supports"),
        )
    try:
        AtomKeys("modal_enum_search").letters([scanned])
        refuse_alike_agents([scanned], "modal_enum_search")
    except NotImplementedError as exc:
        # A valuation and a relation family are named by text: two different atoms (or two
        # different agents) that print alike would be ONE key of every candidate model, and a
        # search that read them as one would report "no countermodel" for a formula that has one.
        return EnumSearchResult(
            model=None, exhausted=False, checked=0,
            unsupported=f"{type(exc).__name__}: {exc}",
            detail=("two different atoms (or agents) of the formula are written alike, so a "
                    "model keyed by the written form could not tell them apart — the formula "
                    "is outside the fragment this enumerator supports"),
        )
    named = _terms_under_bound_predicates(scanned)
    if len(named) > 1:
        return EnumSearchResult(
            model=None, exhausted=False, checked=0,
            unsupported=(
                f"NotImplementedError: modal_enum_search: predicate quantifiers of the "
                f"formula apply their bound predicates to the different terms "
                f"{named[0]} and {named[1]}. Two terms may name one individual, and a "
                f"predicate quantifier can say that they do not; a model of this search "
                f"names an individual by its term, so it holds no model in which the two "
                f"are one. Export the formula with hol.ho_modal for a higher-order prover."),
            detail=("a bound predicate is applied to two different terms, and the models "
                    "of this search cannot make two terms name one individual — the "
                    "formula is outside the fragment this enumerator supports"),
        )
    atoms, families = _collect(scanned)
    # the membership keys are fixed true, not varied: they cost no search space
    atoms = tuple(a for a in atoms if a not in fixed)

    if max_atoms is not None and len(atoms) > max_atoms:
        return EnumSearchResult(
            model=None, exhausted=False, checked=0, unsupported=None,
            detail=(f"formula uses {len(atoms)} ground atoms, exceeding "
                    f"max_atoms={max_atoms}; search skipped rather than build "
                    "an oversized valuation space"),
        )

    conditions = {fam: _conditions_for(fam, frame, systems) for fam in families}
    checked = 0
    deadline = _instant(timeout)

    def out_of_time() -> EnumSearchResult:
        return EnumSearchResult(
            model=None, exhausted=False, checked=checked, unsupported=None,
            detail=(f"the {timeout} ms limit passed after {checked} models; the search "
                    f"up to max_worlds={max_worlds} did not complete"),
            timed_out=True)

    for n in range(1, max_worlds + 1):
        rel_lists = []
        for fam in families:
            family_relations = _valid_relations_until(n, conditions[fam], deadline)
            if family_relations is None:
                return out_of_time()
            rel_lists.append(family_relations)
        # A valuation list that is small is built once and reused for every relation
        # choice; a large one is generated again for each, instead of held in memory.
        valuations = (list(_valuations(atoms, n, fixed))
                      if (1 << len(atoms)) ** n <= _CACHED_VALUATIONS else None)
        rel_choices = itertools.product(*rel_lists) if rel_lists else [()]
        for rel_choice in rel_choices:
            relations = dict(zip(families, rel_choice))
            for valuation in (valuations if valuations is not None
                              else _valuations(atoms, n, fixed)):
                if _passed(deadline):
                    return out_of_time()
                if checked >= max_models:
                    return EnumSearchResult(
                        model=None, exhausted=False, checked=checked, unsupported=None,
                        detail=(f"candidate budget exhausted after {checked} models "
                                f"(max_models={max_models}); the search up to "
                                f"max_worlds={max_worlds} did not complete"),
                    )
                model = KripkeModel(worlds=range(n), relations=relations, valuation=valuation)
                try:
                    holds = satisfies_modal(formula, model, 0)
                except _UNSUPPORTED_EXC as exc:
                    return EnumSearchResult(
                        model=None, exhausted=False, checked=checked,
                        unsupported=f"{type(exc).__name__}: {exc}",
                        detail=("satisfies_modal has no rule for a construct in "
                                "this formula — it is outside the propositional/"
                                "ground modal fragment this enumerator supports"),
                    )
                checked += 1
                if not holds:
                    return EnumSearchResult(
                        model=model, exhausted=False, checked=checked, unsupported=None,
                        detail=(f"countermodel found with {n} world(s) after "
                                f"checking {checked} candidate(s)"),
                    )

    return EnumSearchResult(
        model=None, exhausted=True, checked=checked, unsupported=None,
        detail=(f"search space fully enumerated up to max_worlds={max_worlds} "
                f"({checked} candidates checked); no countermodel exists at or "
                "below that size — NOT a validity proof, larger models are "
                "unexplored"),
    )


def modal_enum_countermodel(formula: Node, *, frame: str = "K",
                            systems: Optional[Dict[str, str]] = None,
                            max_worlds: int = 3, max_atoms: Optional[int] = None,
                            max_models: int = 200000,
                            timeout: Optional[float] = None) -> Optional[KripkeModel]:
    """Return a verified Kripke countermodel for ``formula``, or ``None``.

    Thin convenience wrapper over :func:`modal_enum_search` for callers who
    only want the model (or its absence) and not the exhausted/unsupported/
    checked detail — e.g. a differential test against
    :func:`unicode_logic_kit.atp.modal_tableau.modal_countermodel`. ``None`` here
    conflates "exhausted" and "budget hit" and "timed out" and "unsupported";
    use :func:`modal_enum_search` directly to tell them apart (this is exactly
    what :class:`KripkeEnumBackend` does for its ``reason``/``detail`` fields).
    """
    return modal_enum_search(formula, frame=frame, systems=systems,
                             max_worlds=max_worlds, max_atoms=max_atoms,
                             max_models=max_models, timeout=timeout).model


class KripkeEnumBackend(ProverBackend):
    """Refutation-only semantic backend: bounded finite-Kripke-model enumeration.

    Fills exactly the gap ``modal-tableau`` and ``qml`` leave open: neither can
    REFUTE a temporal-closure formula (``modal-tableau`` has no rule for
    Ⓖ/Ⓕ/Ⓤ/⒣/⒫/⒴/⒮ and reports it ``UNKNOWN/unsupported``; ``qml`` is sound but
    proof-only). This backend decides such a formula by exhaustive finite-model
    search (:func:`modal_enum_search`) using the SAME evaluator
    (``satisfies_modal``) both of those routes ultimately answer to, so a
    REFUTED verdict here can never contradict a PROVED verdict from either.

    Like :class:`unicode_logic_kit.atp.protocol.ModelFinderBackend`, this is
    ONE-SIDED: finding a countermodel REFUTES; exhausting the search space
    proves NOTHING about validity (modal logic has no small-model property
    bounding countermodels to ``max_worlds``), so that case is reported
    ``UNKNOWN`` with ``reason="bound_hit"`` — the same reason
    ``ModelFinderBackend`` uses for "no countermodel up to the size bound",
    since ``max_worlds`` is exactly such a size bound (see
    ``atp.protocol``'s own reason-vocabulary docstring, which lists
    ``max_worlds`` as a ``bound_hit`` example). The ``detail`` field still says
    whether the bound was hit by a COMPLETE search (``exhausted``) or by the
    ``max_models``/``max_atoms`` budget cutting a search short — see
    :class:`EnumSearchResult`. The call's ``timeout`` is one more bound: a search
    it ended is ``UNKNOWN`` with ``reason="timeout"``.

    ``premises`` are folded into the LOCAL consequence goal
    ``(∧ premises) → formula``, exactly like ``ModalTableauBackend`` and
    ``QmlBackend``.
    """

    name = "kripke-enum"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        import time
        from .protocol import _implication

        goal = _implication(formula, premises)
        start = time.perf_counter()
        result = modal_enum_search(goal, timeout=timeout, **options)
        elapsed = time.perf_counter() - start

        if result.unsupported is not None:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="unsupported",
                           wall_time=elapsed,
                           detail=f"{result.detail} ({result.unsupported})")
        if result.model is not None:
            return Verdict(REFUTED, self.name, logic="modal", wall_time=elapsed,
                           countermodel={"kind": "kripke", "repr": repr(result.model),
                                        "data": kripke_model_to_dict(result.model)})
        if result.timed_out:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="timeout",
                           wall_time=elapsed, detail=result.detail)
        return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                       wall_time=elapsed, detail=result.detail)
