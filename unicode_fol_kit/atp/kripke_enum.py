"""Bounded enumeration of finite Kripke models — a semantic refutation oracle for
the modal fragment the labelled tableau cannot decide.

:mod:`unicode_fol_kit.atp.modal_tableau` has no proof rule for the temporal
*closure* operators (Always ``Ⓖ`` / Eventually ``Ⓕ`` / Until ``Ⓤ`` /
Historically ``⒣`` / Once ``⒫`` / Previous ``⒴`` / Since ``⒮`` — see
``modal_tableau._TEMPORAL_CLOSURE``): it marks a labelled formula built from one
of them INERT and reports ``"unknown"`` for any branch that only stays open
because of it. The quantified-modal-logic route (``fol.qml``) is sound but
proof-only (Z3 over the standard translation never REFUTES). Net effect: an
INVALID temporal formula such as ``Ⓕ P → P`` stays "unknown" — nothing in the
kit ever refutes it.

This module closes that gap for **refutation only**, the same way
:mod:`unicode_fol_kit.semantics.modelfinder` closes the analogous gap for plain
FOL: it exhaustively enumerates finite :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`\\ s
of increasing world-count and hands each one to the EXISTING, already-tested
evaluator, :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`, as an
oracle. Soundness is by construction: a returned countermodel is one
``satisfies_modal`` itself confirms falsifies the formula at world 0, so this
module contains no new semantic rule that could disagree with the one every
other Kripke-based route in the kit already relies on.

**What is enumerated.** For each relation family the formula actually uses
(``"alethic"`` for Box/Diamond, ``"K:"+agent`` / ``"B:"+agent`` /
``"Say:"+agent`` / ``"Want:"+agent`` for Knows/Believes/Says/Wants,
``"deontic"`` for Obligatory/Permitted, ``"temporal"`` for every temporal
operator — the exact naming convention documented in
:mod:`unicode_fol_kit.semantics.kripke`), every relation over ``{0, …, n-1}``
satisfying that family's frame condition is enumerated (the SAME frame-name
vocabulary as :mod:`unicode_fol_kit.atp.modal_tableau`: K/T/D/KD/B/KB/K4/K45/
S4/S5/KD45 for ``frame=``, plus per-family overrides via ``systems=``), crossed
with every valuation of the formula's ground atoms over those worlds. ``n``
ranges over ``1 .. max_worlds``. Each candidate model is checked with
``satisfies_modal(formula, model, 0)``; the first candidate where it comes back
``False`` is returned as the countermodel.

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

A formula outside the propositional/ground modal fragment ``satisfies_modal``
itself understands (a first-order quantifier with no per-world domain, an
unassigned hybrid nominal, a Lewis counterfactual, …) makes the evaluator raise
— caught here and reported as ``unsupported`` rather than silently skipped or
misreported as a bound.

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
``exhausted=False`` rather than either blocking forever or answering wrong.

Public API: :class:`EnumSearchResult`, :func:`modal_enum_search`,
:func:`modal_enum_countermodel`, :class:`KripkeEnumBackend`, plus the witness
converters :func:`kripke_model_to_dict` / :func:`kripke_model_from_dict`
(the ``"data"`` payload of every ``"kripke"`` witness dict).
"""

import itertools
from dataclasses import dataclass
from functools import lru_cache
from typing import Dict, FrozenSet, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom,
    Box, Diamond, Knows, Believes, Says, Wants, Obligatory, Permitted,
    Next, Always, Eventually, Until, Historically, Once, Previous, Since,
)
from ..semantics.kripke import KripkeModel, satisfies_modal
from ..fol.frames import (
    FRAME_CONDITIONS, FRAMES as _FRAMES, UnsupportedFrameCondition,
    resolve_frame, holds_on_finite_frame,
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
    return getattr(agent, "name", None) or agent.to_unicode_str()


def _collect(formula: Node) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
    """Scan ``formula`` for its ground-atom keys and the relation families it uses.

    Returns ``(atoms, families)``, both sorted tuples (deterministic order):
    ``atoms`` are the ``Atom.to_unicode_str()`` keys the valuation must cover;
    ``families`` are the relation NAMES (in the ``semantics.kripke`` convention)
    the enumerator must build a relation for — one entry per distinct alethic /
    epistemic-per-agent / doxastic-per-agent / assertive-per-agent /
    bouletic-per-agent / deontic / temporal operator family actually present.
    A formula with no modal operators at all yields an empty ``families``
    tuple (the propositional case: only world 0's valuation matters).
    """
    atoms: set = set()
    families: set = set()
    for node in formula.walk():
        if isinstance(node, Atom):
            atoms.add(node.to_unicode_str())
        elif isinstance(node, (Box, Diamond)):
            families.add(_ALETHIC)
        elif isinstance(node, Knows):
            families.add(_KNOWS_PREFIX + _agent_key(node.agent))
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


def _check_frame(frame: str, systems: Optional[Dict[str, str]]) -> None:
    """Resolve every frame this search will use, refusing what a FINITE frame
    check cannot decide.

    The enumerator carries every FIRST-ORDER condition in the shared registry
    (a condition on a finite relation is directly checkable), which is more
    than the labelled tableau's rule set — so it validates frames itself
    rather than borrowing the tableau's stricter check. The three
    non-first-order conditions (Löb, McKinsey, Grz) are refused by name: they
    are not properties of a frame's relation at all, and enumerating frames
    "satisfying" them would be enumerating nothing meaningful.
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
            conds = resolve_frame(name)
        except ValueError as exc:
            raise ValueError(f"kripke_enum: {exc}") from None
        for cond in conds:
            entry = FRAME_CONDITIONS.get(cond)
            if entry is not None and not entry.first_order:
                raise UnsupportedFrameCondition(
                    f"kripke_enum: the frame {name!r} needs the condition "
                    f"{cond!r} ({entry.description}), which no finite frame "
                    "check decides. Use the higher-order embeddings "
                    "hol.isabelle_modal / hol.thf_modal, which assert the "
                    "schema itself.")


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

    Delegates to :func:`unicode_fol_kit.fol.frames.holds_on_finite_frame`, the
    checker the correspondence tests use as well. Delegating matters for
    SOUNDNESS, not tidiness: this function used to test the five conditions it
    knew and IGNORE any other, so a frame class it did not recognise silently
    widened to the ones it did — and a countermodel the named system excludes
    would have been reported as if it refuted the formula. An unknown or
    non-first-order condition now raises instead.
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


def _valuations(atoms: Tuple[str, ...], n: int):
    """Yield every valuation ``{world: frozenset(atoms true there)}`` over ``range(n)``.

    Deterministic bitmask order: for ``n`` worlds and ``m`` atoms, each of the
    ``(2**m)**n`` combinations is produced by ``itertools.product`` over a
    per-world bitmask in ``range(2**m)``, world 0 varying slowest — the same
    fixed order every call, so re-running a search reproduces the same model.
    """
    m = len(atoms)
    for combo in itertools.product(range(1 << m), repeat=n):
        yield {
            w: frozenset(atoms[i] for i in range(m) if (bits >> i) & 1)
            for w, bits in enumerate(combo)
        }


@dataclass(frozen=True)
class EnumSearchResult:
    """The outcome of one :func:`modal_enum_search` call.

    Fields:

    ``model``
        a verified :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`
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
    """

    model: Optional[KripkeModel]
    exhausted: bool
    checked: int
    unsupported: Optional[str] = None
    detail: str = ""

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (the model, if any, as worlds/relations/valuation)."""
        return {
            "found": self.model is not None,
            "exhausted": self.exhausted,
            "checked": self.checked,
            "unsupported": self.unsupported,
            "detail": self.detail,
            "model": kripke_model_to_dict(self.model) if self.model is not None else None,
        }


def kripke_model_to_dict(model: KripkeModel) -> dict:
    """Render a :class:`KripkeModel` as a JSON-compatible dict.

    The shape is the structured ``"data"`` payload of every ``"kripke"``
    witness dict a :class:`~unicode_fol_kit.atp.protocol.Verdict` carries:
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
                      max_models: int = 200000) -> EnumSearchResult:
    """Exhaustively search finite Kripke models of increasing size for a countermodel.

    Enumerates every relation (per family, per the ``frame``/``systems`` frame
    conditions — see :func:`_conditions_for`) and every atom valuation over
    ``n = 1 .. max_worlds`` worlds, in a fixed deterministic order, and checks
    each candidate with :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`
    (the existing, already-tested evaluator — this function adds no new
    semantic rule, only the search). The first candidate that falsifies
    ``formula`` at world 0 is returned immediately.

    Args:
        formula: the (already premise-folded, if applicable — see
            :class:`KripkeEnumBackend`) formula to search for a countermodel of.
        frame: the alethic frame name for ``"alethic"`` relations (Box/Diamond)
            — one of K/T/D/KD/B/KB/K4/K45/S4/S5/KD45, the same vocabulary as
            :func:`unicode_fol_kit.atp.modal_tableau.is_modal_valid`.
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

    Returns:
        An :class:`EnumSearchResult` — see its docstring for how to read
        ``model``/``exhausted``/``unsupported`` together.

    Raises:
        NotImplementedError: if ``frame`` is ``"GL"`` (not finitely
            expressible — see ``modal_tableau._check_frame``).
        ValueError: if ``frame`` or a ``systems`` entry names an unknown frame
            or system family.
    """
    _check_frame(frame, systems)
    atoms, families = _collect(formula)

    if max_atoms is not None and len(atoms) > max_atoms:
        return EnumSearchResult(
            model=None, exhausted=False, checked=0, unsupported=None,
            detail=(f"formula uses {len(atoms)} ground atoms, exceeding "
                    f"max_atoms={max_atoms}; search skipped rather than build "
                    "an oversized valuation space"),
        )

    conditions = {fam: _conditions_for(fam, frame, systems) for fam in families}
    checked = 0

    for n in range(1, max_worlds + 1):
        rel_lists = [_valid_relations(n, conditions[fam]) for fam in families]
        valuations = list(_valuations(atoms, n))
        rel_choices = itertools.product(*rel_lists) if rel_lists else [()]
        for rel_choice in rel_choices:
            relations = dict(zip(families, rel_choice))
            for valuation in valuations:
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
                            max_models: int = 200000) -> Optional[KripkeModel]:
    """Return a verified Kripke countermodel for ``formula``, or ``None``.

    Thin convenience wrapper over :func:`modal_enum_search` for callers who
    only want the model (or its absence) and not the exhausted/unsupported/
    checked detail — e.g. a differential test against
    :func:`unicode_fol_kit.atp.modal_tableau.modal_countermodel`. ``None`` here
    conflates "exhausted" and "budget hit" and "unsupported"; use
    :func:`modal_enum_search` directly to tell them apart (this is exactly what
    :class:`KripkeEnumBackend` does for its ``reason``/``detail`` fields).
    """
    return modal_enum_search(formula, frame=frame, systems=systems,
                             max_worlds=max_worlds, max_atoms=max_atoms,
                             max_models=max_models).model


class KripkeEnumBackend(ProverBackend):
    """Refutation-only semantic backend: bounded finite-Kripke-model enumeration.

    Fills exactly the gap ``modal-tableau`` and ``qml`` leave open: neither can
    REFUTE a temporal-closure formula (``modal-tableau`` has no rule for
    Ⓖ/Ⓕ/Ⓤ/⒣/⒫/⒴/⒮ and reports it ``UNKNOWN/unsupported``; ``qml`` is sound but
    proof-only). This backend decides such a formula by exhaustive finite-model
    search (:func:`modal_enum_search`) using the SAME evaluator
    (``satisfies_modal``) both of those routes ultimately answer to, so a
    REFUTED verdict here can never contradict a PROVED verdict from either.

    Like :class:`unicode_fol_kit.atp.protocol.ModelFinderBackend`, this is
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
    :class:`EnumSearchResult`.

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
        result = modal_enum_search(goal, **options)
        elapsed = time.perf_counter() - start

        if result.unsupported is not None:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="unsupported",
                           wall_time=elapsed,
                           detail=f"{result.detail} ({result.unsupported})")
        if result.model is not None:
            return Verdict(REFUTED, self.name, logic="modal", wall_time=elapsed,
                           countermodel={"kind": "kripke", "repr": repr(result.model),
                                        "data": kripke_model_to_dict(result.model)})
        return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                       wall_time=elapsed, detail=result.detail)
