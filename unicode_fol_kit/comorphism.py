"""A composable registry of the kit's logic-to-logic translations.

The kit has long owned a family of translation functions — the modal standard
translation, ALC→FOL / ALC→modal-K, dependence→ESO — each living in its home
module as a bare function. This module catalogues them as first-class
:class:`Comorphism` edges in a graph keyed by logic labels, with BFS path
composition: ``translate(term, "alc", "fol")`` works whether the registry has
a direct edge or has to compose ``alc→modal→fol``. (The name and the idea —
logic translations as first-class objects — are HETS'; the machinery here is
deliberately lightweight and native Python.)

Logic labels used by the default registry: ``"modal"`` (propositional modal
family), ``"fol"`` (classical FOL), ``"alc"`` (description-logic concepts),
``"team"`` (dependence/team-semantic sentences), ``"eso"`` (existential
second-order formulas). Third-party edges register with
:func:`register_comorphism` and become reachable from
:func:`unicode_fol_kit.api.translate` immediately.

A comorphism's ``apply`` maps a SOURCE-logic term to a TARGET-logic term; the
term type is whatever the source logic's AST is (``Node`` for the formula
families, ``Concept`` for ALC). Fragment restrictions of the underlying
functions (e.g. ``concept_to_modal`` accepts only single-role concepts)
surface as their own exceptions, unchanged.
"""

from collections import deque
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Tuple

__all__ = [
    "Comorphism", "TranslationResult", "ComorphismRegistry",
    "DEFAULT_REGISTRY", "register_comorphism",
]


@dataclass(frozen=True)
class Comorphism:
    """One directed translation edge between two logic labels.

    ``lossy`` marks edges that do not preserve the full source semantics
    (none of the default edges are lossy; the flag exists so future edges —
    e.g. a fuzzy→classical collapse — must declare it). ``note`` documents
    conventions a consumer must know (free anchors, fragment limits).
    """

    name: str
    source: str
    target: str
    apply: Callable[[Any], Any]
    lossy: bool = False
    note: str = ""


@dataclass(frozen=True)
class TranslationResult:
    """Outcome of a (possibly composed) translation.

    ``path`` names the comorphisms applied, in order; ``lossy`` is True iff
    any edge on the path is. ``note`` concatenates the edge notes so the
    conventions travel with the result.
    """

    result: Any
    source: str
    target: str
    path: Tuple[str, ...]
    lossy: bool
    note: str = ""

    def to_dict(self) -> dict:
        """JSON-compatible dict; the result serialises via its own ``to_dict``
        when it has one, else via ``repr``."""
        if hasattr(self.result, "to_dict"):
            rendered = self.result.to_dict()
        else:
            rendered = repr(self.result)
        return {
            "result": rendered,
            "source": self.source,
            "target": self.target,
            "path": list(self.path),
            "lossy": self.lossy,
            "note": self.note,
        }


class ComorphismRegistry:
    """A graph of :class:`Comorphism` edges with BFS path composition."""

    def __init__(self):
        self._edges: Dict[Tuple[str, str], Comorphism] = {}

    def register(self, comorphism: Comorphism, replace: bool = False) -> None:
        """Add an edge; refuses to silently overwrite an existing one.

        One edge per (source, target) pair keeps ``translate`` deterministic —
        pass ``replace=True`` to intentionally swap an edge out.
        """
        key = (comorphism.source, comorphism.target)
        if key in self._edges and not replace:
            raise ValueError(
                f"register: an edge {key[0]}→{key[1]} is already registered "
                f"({self._edges[key].name!r}); pass replace=True to swap it.")
        self._edges[key] = comorphism

    def unregister(self, name: str) -> bool:
        """Remove the edge registered under ``name``; True iff one existed.

        The inverse of :meth:`register`, added for DYNAMIC edge providers
        (the Hets bridge re-binds its ``hets:<Name>`` edges on every
        re-registration and must be able to drop edges the new server no
        longer offers — leaving them would keep stale closures pointing at
        a dead URL). Removing an unknown name is a no-op returning False,
        not an error: refresh code calls this speculatively.
        """
        for key, edge in list(self._edges.items()):
            if edge.name == name:
                del self._edges[key]
                return True
        return False

    def edges(self) -> Tuple[Comorphism, ...]:
        """All registered edges, sorted by (source, target) for determinism."""
        return tuple(self._edges[k] for k in sorted(self._edges))

    def find_path(self, source: str, target: str) -> List[Comorphism]:
        """Shortest edge sequence from ``source`` to ``target`` (BFS).

        Deterministic: neighbours are explored in sorted label order, so equal
        length paths always resolve the same way. Raises ``ValueError`` when no
        path exists — with the known labels in the message, because a typo in a
        logic label should fail loudly.
        """
        if source == target:
            return []
        labels = sorted({l for k in self._edges for l in k})
        if source not in labels or target not in labels:
            raise ValueError(
                f"find_path: unknown logic label in {source!r}→{target!r} "
                f"(known: {labels})")
        # BFS over labels; predecessors remember the edge that reached a label.
        seen = {source}
        queue = deque([source])
        via: Dict[str, Comorphism] = {}
        while queue:
            here = queue.popleft()
            for (s, t), edge in sorted(self._edges.items()):
                if s != here or t in seen:
                    continue
                via[t] = edge
                if t == target:
                    path = [edge]
                    while path[0].source != source:
                        path.insert(0, via[path[0].source])
                    return path
                seen.add(t)
                queue.append(t)
        raise ValueError(
            f"find_path: no comorphism path {source!r}→{target!r} "
            f"(edges: {[f'{c.source}→{c.target}' for c in self.edges()]})")

    def translate(self, term: Any, source: str, target: str) -> TranslationResult:
        """Apply the (composed) translation ``source``→``target`` to ``term``."""
        path = self.find_path(source, target)
        result = term
        for edge in path:
            result = edge.apply(result)
        notes = "; ".join(e.note for e in path if e.note)
        return TranslationResult(
            result=result, source=source, target=target,
            path=tuple(e.name for e in path),
            lossy=any(e.lossy for e in path), note=notes)


def _build_default_registry() -> ComorphismRegistry:
    """The default edges: exactly the kit's existing translation functions.

    Note what is deliberately NOT an edge: ``circumscription_entails_so`` is an
    entailment decision, not a term-to-term translation, and ``qml_translate``
    shares modal→fol with the standard translation (it becomes selectable when
    the registry grows per-edge selection; until then the propositional
    standard translation owns that pair).
    """
    from .fol.modal_translation import standard_translation
    from .dl.translate import concept_to_fol, concept_to_modal
    from .semantics.team_translation import dependence_to_eso

    registry = ComorphismRegistry()
    registry.register(Comorphism(
        name="standard_translation", source="modal", target="fol",
        apply=standard_translation,
        note="anchored at the FREE world variable 'w' — universally close it "
             "(∀w …) for validity questions",
    ))
    registry.register(Comorphism(
        name="concept_to_modal", source="alc", target="modal",
        apply=concept_to_modal,
        note="single-role concepts only (ALC with one role = modal K); "
             "multi-role concepts raise",
    ))
    registry.register(Comorphism(
        name="concept_to_fol", source="alc", target="fol",
        apply=concept_to_fol,
        note="one free individual variable 'x' — close existentially for "
             "satisfiability questions",
    ))
    registry.register(Comorphism(
        name="dependence_to_eso", source="team", target="eso",
        apply=dependence_to_eso,
        note="sentences only (no free variables)",
    ))
    return registry


DEFAULT_REGISTRY = _build_default_registry()


def register_comorphism(comorphism: Comorphism, replace: bool = False) -> None:
    """Register an edge in the DEFAULT registry (see :class:`ComorphismRegistry`)."""
    DEFAULT_REGISTRY.register(comorphism, replace=replace)
