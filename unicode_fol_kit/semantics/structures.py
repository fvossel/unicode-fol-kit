"""Finite first-order structures — the interpretation side of model checking.

A :class:`FiniteStructure` is a concrete, finite interpretation: a domain of
named individuals plus an extension for every predicate symbol. It is what a
formula is *evaluated in* (model CHECKING — is this sentence true HERE?), as
opposed to what a model FINDER searches for. The kit already had the finder
(:mod:`unicode_fol_kit.atp.modelfinder`); this module supplies the other
direction, which is what structured real-world data actually needs: a
molecule, a knowledge-graph neighbourhood, a scene graph is *given*, and the
question is whether a definition holds of it.

Design decisions and why
-------------------------
**Extensions are keyed by (name, arity).** Predicate symbols in this kit live
in an arity-aware namespace (see :mod:`unicode_fol_kit.eval.validate`), so
``P/1`` and ``P/2`` are different symbols and must be able to coexist. A
0-ary predicate's extension is either ``frozenset()`` (false) or
``frozenset({()})`` (true) — the standard model-theoretic uniformity, which
means global molecule properties like ``net_charge_neutral`` need no special
case anywhere downstream.

**Computed predicates are first-class.** Some properties of a finite
structure are perfectly decidable ON the structure while being inexpressible
IN first-order logic over it — connectivity and ring membership are the
canonical examples (they need transitive closure). ChemLog (Flügel et al.,
2025) hits exactly this and resolves it by computing such a predicate
externally in Python and injecting its extension. This module makes that
pattern explicit and general: a ``computed`` entry maps a symbol to a
callable that decides it on demand, so a definition may *use* ``in_ring(x)``
without the structure having to materialise the whole extension up front. The
honest reading: a structure with computed predicates is still a completely
ordinary finite structure — the callable is just a lazy representation of an
extension, not an escape into a stronger logic.

**Indexing is part of the contract, not an optimisation detail.**
:meth:`individuals_with` and :meth:`neighbors` exist because the difference
between iterating a quantifier over the whole domain and iterating it over
"the oxygens double-bonded to the carbon we already fixed" is the difference
between a timeout and a millisecond on real data. Evaluators are expected to
use them; see :mod:`unicode_fol_kit.semantics.model_eval`.

Serialisation round-trips through :meth:`to_dict` / :func:`structure_from_dict`
EXCEPT for computed predicates: a Python callable has no JSON image. They are
listed by name in the dict under ``"computed"`` so a consumer can see what is
missing rather than silently receiving a weaker structure, and
:func:`structure_from_dict` refuses to rebuild one unless the caller supplies
the callables again.
"""

from dataclasses import dataclass, field
from typing import (
    Callable, Dict, FrozenSet, Iterable, Mapping, Optional, Sequence, Tuple,
)

__all__ = [
    "FiniteStructure", "structure_from_dict", "graph_to_structure",
]

Individual = str
Tuple_ = Tuple[Individual, ...]
Key = Tuple[str, int]


def _freeze(pairs: Mapping[Key, Iterable[Sequence[Individual]]]
            ) -> Dict[Key, FrozenSet[Tuple_]]:
    """Normalise an extension mapping to frozensets of tuples of str."""
    out: Dict[Key, FrozenSet[Tuple_]] = {}
    for key, rows in pairs.items():
        if (not isinstance(key, tuple) or len(key) != 2
                or not isinstance(key[0], str) or not isinstance(key[1], int)):
            raise ValueError(
                f"FiniteStructure: extension key must be (name, arity), got {key!r}")
        name, arity = key
        frozen = set()
        for row in rows:
            row_t = tuple(row)
            if len(row_t) != arity:
                raise ValueError(
                    f"FiniteStructure: {name}/{arity} has a {len(row_t)}-tuple "
                    f"{row_t!r} in its extension")
            frozen.add(row_t)
        out[key] = frozenset(frozen)
    return out


@dataclass(frozen=True)
class FiniteStructure:
    """A finite first-order interpretation: domain + predicate extensions.

    ``domain`` is the tuple of individual NAMES (order is presentational but
    kept stable so evaluation is deterministic). ``extensions`` maps
    ``(predicate_name, arity)`` to the frozenset of satisfying tuples;
    ``computed`` maps such a key to a callable ``(*individuals) -> bool``
    consulted on demand for predicates whose extension is decided
    algorithmically rather than stored (see the module docstring).
    ``constants`` optionally names distinguished individuals so a formula may
    mention them as terms.

    A symbol may appear in ``extensions`` or in ``computed``, never both —
    two sources of truth for one predicate is exactly the kind of silent
    disagreement this kit refuses.
    """

    domain: Tuple[Individual, ...]
    extensions: Mapping[Key, FrozenSet[Tuple_]] = field(default_factory=dict)
    computed: Mapping[Key, Callable[..., bool]] = field(default_factory=dict)
    constants: Mapping[str, Individual] = field(default_factory=dict)

    def __post_init__(self):
        object.__setattr__(self, "domain", tuple(self.domain))
        if len(set(self.domain)) != len(self.domain):
            raise ValueError("FiniteStructure: domain has duplicate individuals")
        object.__setattr__(self, "extensions", _freeze(dict(self.extensions)))
        object.__setattr__(self, "computed", dict(self.computed))
        object.__setattr__(self, "constants", dict(self.constants))

        members = set(self.domain)
        for (name, arity), rows in self.extensions.items():
            for row in rows:
                unknown = [i for i in row if i not in members]
                if unknown:
                    raise ValueError(
                        f"FiniteStructure: {name}/{arity} mentions individuals "
                        f"outside the domain: {sorted(unknown)}")
        clash = set(self.extensions) & set(self.computed)
        if clash:
            raise ValueError(
                "FiniteStructure: these symbols have BOTH a stored extension "
                f"and a computed one: {sorted(clash)} — a predicate needs one "
                "source of truth")
        for name, individual in self.constants.items():
            if individual not in members:
                raise ValueError(
                    f"FiniteStructure: constant {name!r} denotes {individual!r}, "
                    "which is not in the domain")
        object.__setattr__(self, "_index", {})

    # -- querying ---------------------------------------------------------

    def holds(self, name: str, args: Sequence[Individual]) -> bool:
        """Is ``name(args)`` true in this structure?

        An UNINTERPRETED symbol (neither stored nor computed) raises
        ``KeyError`` rather than defaulting to false: a definition mentioning
        a predicate this structure knows nothing about is a vocabulary error
        the caller must see, not a silent falsehood that would make the
        definition look merely unsatisfied.
        """
        args_t = tuple(args)
        key = (name, len(args_t))
        if key in self.extensions:
            return args_t in self.extensions[key]
        if key in self.computed:
            return bool(self.computed[key](*args_t))
        raise KeyError(
            f"FiniteStructure: no interpretation for {name}/{len(args_t)} "
            f"(known: {sorted(n for n, _ in self.signature())})")

    def interprets(self, name: str, arity: int) -> bool:
        """Whether ``name/arity`` has an interpretation here (stored or computed)."""
        return (name, arity) in self.extensions or (name, arity) in self.computed

    def signature(self) -> Tuple[Key, ...]:
        """Every interpreted ``(name, arity)``, sorted — stored and computed."""
        return tuple(sorted(set(self.extensions) | set(self.computed)))

    def individuals_with(self, name: str) -> Tuple[Individual, ...]:
        """The individuals satisfying the UNARY predicate ``name``, in domain order.

        The candidate-set primitive for quantifier evaluation: iterating
        ``∃x (o(x) ∧ …)`` over the oxygens instead of over every atom is what
        keeps evaluation tractable on real structures. A computed unary
        predicate is materialised here by asking it about every individual
        (unavoidable, and still linear).
        """
        key = (name, 1)
        if key in self.extensions:
            members = {row[0] for row in self.extensions[key]}
        elif key in self.computed:
            decide = self.computed[key]
            members = {i for i in self.domain if decide(i)}
        else:
            raise KeyError(f"FiniteStructure: no interpretation for {name}/1")
        return tuple(i for i in self.domain if i in members)

    def neighbors(self, name: str, individual: Individual) -> Tuple[Individual, ...]:
        """The ``y`` with ``name(individual, y)`` true, in domain order.

        Forward index over a BINARY relation, built once per relation and
        cached (the structure is frozen, so the cache can never go stale).
        This is the second candidate-set primitive: once a variable is bound,
        the variables related to it should range over its neighbourhood, not
        the domain.
        """
        key = (name, 2)
        if key in self.computed:
            decide = self.computed[key]
            return tuple(y for y in self.domain if decide(individual, y))
        if key not in self.extensions:
            raise KeyError(f"FiniteStructure: no interpretation for {name}/2")
        index = self._index.get(key)            # type: ignore[attr-defined]
        if index is None:
            index = {}
            for a, b in self.extensions[key]:
                index.setdefault(a, set()).add(b)
            self._index[key] = index            # type: ignore[attr-defined]
        members = index.get(individual, ())
        return tuple(y for y in self.domain if y in members)

    # -- serialisation ----------------------------------------------------

    def to_dict(self) -> dict:
        """JSON-compatible dict. Computed predicates appear by NAME only.

        They cannot be serialised (a callable has no JSON image); listing
        them under ``"computed"`` keeps the loss visible instead of handing
        out a structure that quietly lost predicates.
        """
        return {
            "domain": list(self.domain),
            "extensions": {
                f"{name}/{arity}": sorted(list(row) for row in rows)
                for (name, arity), rows in sorted(self.extensions.items())
            },
            "computed": [f"{name}/{arity}"
                         for name, arity in sorted(self.computed)],
            "constants": dict(sorted(self.constants.items())),
        }

    def __repr__(self) -> str:
        return (f"FiniteStructure(|D|={len(self.domain)}, "
                f"symbols={len(self.signature())}, "
                f"computed={len(self.computed)})")


def structure_from_dict(
    data: dict, *,
    computed: Optional[Mapping[Key, Callable[..., bool]]] = None,
) -> FiniteStructure:
    """Rebuild a :class:`FiniteStructure` from :meth:`FiniteStructure.to_dict`.

    ``computed`` must supply a callable for every symbol the dict lists under
    ``"computed"`` — otherwise the rebuild is REFUSED (``ValueError``) rather
    than silently producing a structure in which those predicates are simply
    absent, which would turn every definition using them into a vocabulary
    error at best and a wrong verdict at worst.
    """
    def split(label: str) -> Key:
        name, _, arity = label.rpartition("/")
        return name, int(arity)

    needed = {split(label) for label in data.get("computed", [])}
    supplied = dict(computed or {})
    missing = needed - set(supplied)
    if missing:
        raise ValueError(
            "structure_from_dict: the serialised structure uses computed "
            f"predicates {sorted(missing)}; supply them via computed= "
            "(a callable has no JSON image, so they cannot be restored "
            "automatically)")
    return FiniteStructure(
        domain=tuple(data["domain"]),
        extensions={split(label): frozenset(tuple(r) for r in rows)
                    for label, rows in data.get("extensions", {}).items()},
        computed={k: v for k, v in supplied.items() if k in needed},
        constants=dict(data.get("constants", {})),
    )


def graph_to_structure(
    nodes: Mapping[Individual, Iterable[str]],
    edges: Mapping[str, Iterable[Tuple[Individual, Individual]]],
    *,
    globals_: Optional[Mapping[str, bool]] = None,
    computed: Optional[Mapping[Key, Callable[..., bool]]] = None,
    constants: Optional[Mapping[str, Individual]] = None,
) -> FiniteStructure:
    """Build a structure from a LABELLED GRAPH — the generic shape behind
    molecules, knowledge-graph neighbourhoods, scene graphs, and dependency
    parses.

    ``nodes`` maps each individual to the unary labels holding of it;
    ``edges`` maps a relation name to its pairs; ``globals_`` maps 0-ary
    property names to their truth value. Nothing here is domain-specific —
    :mod:`unicode_fol_kit.chem` is one caller among possible others.
    """
    domain = tuple(nodes)
    unary: Dict[Key, set] = {}
    for individual, labels in nodes.items():
        for label in labels:
            unary.setdefault((label, 1), set()).add((individual,))
    extensions: Dict[Key, Iterable[Sequence[Individual]]] = dict(unary)
    for relation, pairs in edges.items():
        extensions[(relation, 2)] = {tuple(p) for p in pairs}
    for name, value in (globals_ or {}).items():
        extensions[(name, 0)] = {()} if value else set()
    return FiniteStructure(
        domain=domain, extensions=extensions,
        computed=dict(computed or {}), constants=dict(constants or {}))
