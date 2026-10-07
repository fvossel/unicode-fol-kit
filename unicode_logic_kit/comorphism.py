"""A composable registry of the kit's logic-to-logic translations.

The kit has long owned a family of translation functions — the modal standard
translation, ALC→FOL / ALC→modal-K, dependence→ESO — each living in its home
module as a bare function. This module catalogues them as first-class
:class:`Comorphism` edges in a graph keyed by logic labels, with BFS path
composition: ``translate(term, "alc", "fol")`` works whether the registry has
a direct edge or has to compose ``alc→modal→fol``. (The name and the idea —
logic translations as first-class objects — are HETS'; the machinery here is
deliberately lightweight and native Python.)

Logic labels used by the default registry: ``"fol"`` (classical FOL),
``"msfol"`` (many-sorted FOL, whose sorts are non-empty), ``"modal"`` (the
propositional modal / temporal / deontic / hybrid family), ``"qml"``
(quantified modal logic with a domain regime), ``"alc"`` (description-logic
concepts), ``"drs"`` (discourse representation structures), ``"team"``
(dependence / team-semantic sentences), ``"eso"`` (existential second-order
formulas) and ``"fuzzy"`` (Łukasiewicz many-valued logic, whose single edge is
lossy). :mod:`unicode_logic_kit.logic` is the typed surface over these labels:
``FOL(MODAL(f))`` converts and keeps the side axioms with the term.
Third-party edges register with
:func:`register_comorphism` and become reachable from
:func:`unicode_logic_kit.api.translate` immediately.

A comorphism's ``apply`` maps a SOURCE-logic term to a TARGET-logic term; the
term type is whatever the source logic's AST is (``Node`` for the formula
families, ``Concept`` for ALC). Fragment restrictions of the underlying
functions (e.g. ``concept_to_modal`` accepts only single-role concepts)
surface as their own exceptions, unchanged.

STABILITY POLICY (:data:`DEFAULT_REGISTRY`): within a minor release line
(0.N.x) no edge — identified by its ``name`` — is removed, renamed, or has
its ``source``/``target``/``lossy`` changed; only new edges are added.
This mirrors :mod:`unicode_logic_kit.api`'s own STABILITY POLICY (see that
module's docstring) applied to the registry surface rather than the
result dataclasses, and it is what lets a caller compose
``translate(term, a, b)`` across a minor line without re-checking that the
path it found last time still exists. ``tests/test_mcp_stability.py``
pins ``(name, source, target, lossy)`` for the current edges as a
baseline-subset check.
"""

from collections import deque
from dataclasses import dataclass
from inspect import Parameter, signature
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Tuple

__all__ = [
    "Comorphism", "TranslationResult", "ComorphismRegistry",
    "DEFAULT_REGISTRY", "GUARANTEES", "register_comorphism", "weakest_guarantee",
]

# What a translation preserves, strongest first. An edge DECLARES one; a path
# gets the weakest on it (:func:`weakest_guarantee`).
#
# EVERY level is a statement about the PAIR (image, ``axioms``), never about the
# bare image: a translation with side conditions is faithful to its source only
# in the models that satisfy them. ``to_fol`` is the plain case — the unsorted
# image of ``(∀x:Human M(x)) → ∃x:Human M(x)`` has a model the sorted formula
# has none of (``Human`` empty), and the non-emptiness axiom is exactly what
# rules it out. So "with the axioms as separate premises" is the premise of all
# four readings below, and what distinguishes them is WHICH questions transfer:
#
#   "faithful"        the model classes correspond in both directions on the
#                     edge's own fragment (pointwise, for an edge with a free
#                     anchor), so every question transfers.
#   "validity"        a validity / entailment question transfers, but the model
#                     classes do not correspond (e.g. the image is a closed
#                     sentence that only ENCODES validity of the source).
#   "satisfiability"  only satisfiability transfers; a validity answer does NOT
#                     (e.g. a free anchor that has to be closed existentially).
#   "lossy"           none of the above; ``note`` must say what is dropped.
#
# ``None`` means the edge has not declared one — then a path's guarantee is
# None as well. It is NOT a synonym for "faithful": an undeclared edge makes no
# promise, and a caller that needs one must look at the edge.
#: The guarantee vocabulary, strongest first (see the comment above).
GUARANTEES: Tuple[str, ...] = ("faithful", "validity", "satisfiability", "lossy")


def weakest_guarantee(values) -> Optional[str]:
    """The weakest guarantee among ``values`` (``None`` if any is undeclared).

    The order is :data:`GUARANTEES`. This is what a composed path can promise:
    a faithful edge after a satisfiability-only one does not repair the latter.
    """
    values = list(values)
    if not values or any(v is None for v in values):
        return None
    return max(values, key=GUARANTEES.index)


@dataclass(frozen=True)
class Comorphism:
    """One directed translation edge between two logic labels.

    ``lossy`` marks edges that do not preserve the full source semantics; it
    must agree with ``guarantee == "lossy"`` (checked in ``__post_init__``).
    The one lossy default edge is ``to_msfol``, the two-valued projection of
    Łukasiewicz logic. ``note`` documents conventions a consumer must know
    (free anchors, fragment limits), and ``axioms`` / ``options`` are the
    side-condition producer and the option names this edge reads — see
    :meth:`side_axioms`.
    """

    name: str
    source: str
    target: str
    apply: Callable[[Any], Any]
    lossy: bool = False
    note: str = ""
    guarantee: Optional[str] = None
    axioms: Optional[Callable[..., Tuple[Any, ...]]] = None
    options: FrozenSet[str] = frozenset()

    def __post_init__(self):
        if self.guarantee is not None and self.guarantee not in GUARANTEES:
            raise ValueError(
                f"Comorphism {self.name!r}: guarantee {self.guarantee!r} is not "
                f"one of {GUARANTEES}")
        # The flag and the declaration must agree, or a consumer that reads only
        # one of them gets a different answer than one reading the other.
        if self.lossy and self.guarantee not in (None, "lossy"):
            raise ValueError(
                f"Comorphism {self.name!r}: lossy=True but guarantee="
                f"{self.guarantee!r} — a lossy edge preserves nothing")
        if self.guarantee == "lossy" and not self.lossy:
            raise ValueError(
                f"Comorphism {self.name!r}: guarantee='lossy' but lossy=False")
        object.__setattr__(self, "options", frozenset(self.options))

    def _for(self, fn: Callable, options: Dict[str, Any]) -> Dict[str, Any]:
        """The subset of ``options`` that ``fn`` itself accepts.

        An edge declares its option NAMES once in :attr:`options`; which of the
        two callables reads them is a detail of the edge (a frame system, say,
        changes the side axioms but not the translation itself). The subset is
        read off the signature — ``**kwargs`` takes everything — so neither
        callable is ever handed a keyword it cannot name.
        """
        try:
            params = signature(fn).parameters
        except (TypeError, ValueError):            # builtins without signatures
            return {}
        if any(p.kind is Parameter.VAR_KEYWORD for p in params.values()):
            return dict(options)
        return {k: v for k, v in options.items() if k in params}

    def side_axioms(self, term: Any, **options) -> Tuple[Any, ...]:
        """The axioms a caller must add for this edge, computed from ``term``.

        Empty when the edge declares none. The axioms are TARGET-logic terms and
        are never folded into the translated term: folding them in breaks every
        validity question through the edge (0.28.0 shipped exactly that bug for
        subsort axioms — ``api.prove(to_fol(f, signature=sig))`` then had to
        prove the axiom itself and valid formulas came back REFUTED).
        """
        if self.axioms is None:
            return ()
        return tuple(self.axioms(term, **self._for(self.axioms, options)))


@dataclass(frozen=True)
class TranslationResult:
    """Outcome of a (possibly composed) translation.

    ``path`` names the comorphisms applied, in order; ``lossy`` is True iff
    any edge on the path is. ``note`` concatenates the edge notes so the
    conventions travel with the result.

    ``axioms`` are the side conditions of the whole path, already expressed in
    the TARGET logic (an upstream edge's axioms are translated by the remaining
    edges, because they are terms of the intermediate logic). They are SEPARATE
    PREMISES, never conjoined onto ``result``::

        t = api.translate(f, "msfol", "fol")
        api.prove(t.result, [*premises, *t.axioms])

    ``guarantee`` is the weakest one on the path (see :data:`GUARANTEES`), or
    ``None`` when some edge on it declares none.
    """

    result: Any
    source: str
    target: str
    path: Tuple[str, ...]
    lossy: bool
    note: str = ""
    axioms: Tuple[Any, ...] = ()
    guarantee: Optional[str] = None

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
            "axioms": [a.to_dict() if hasattr(a, "to_dict") else repr(a)
                       for a in self.axioms],
            "guarantee": self.guarantee,
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

    def carry(self, term: Any, source: str, target: str, **options) -> Any:
        """Translate ``term`` along the path WITHOUT collecting side axioms.

        For a term that IS a side axiom: it has to be expressed in the target
        logic like any other term, but the edges' own axioms were already
        collected once by the :meth:`translate` call that produced it, and
        collecting them again per axiom would multiply them.
        """
        path = self.find_path(source, target)
        accepted = {name for edge in path for name in edge.options}
        unknown = sorted(set(options) - accepted)
        if unknown:
            raise ValueError(
                f"carry: option(s) {unknown} are accepted by no edge on "
                f"{source!r}→{target!r} (path {[e.name for e in path]}, "
                f"accepted: {sorted(accepted)})")
        for edge in path:
            mine = {k: v for k, v in options.items() if k in edge.options}
            term = edge.apply(term, **edge._for(edge.apply, mine))
        return term

    def translate(self, term: Any, source: str, target: str,
                  **options) -> TranslationResult:
        """Apply the (composed) translation ``source``→``target`` to ``term``.

        ``options`` are forwarded to the edges on the path that DECLARE them in
        :attr:`Comorphism.options` (e.g. a frame system for a modal edge). An
        option no edge on the path declares raises ``ValueError`` naming the
        path and what it does accept — a silently ignored option would answer a
        different question than the caller asked.

        Side axioms accumulate along the path: each edge contributes its own
        (computed from the term it is handed), and the axioms collected so far
        are carried through the edge as well, since they are terms of its source
        logic. An edge that cannot carry an axiom raises; the path is then not
        usable for that term, rather than quietly dropping the condition.
        """
        path = self.find_path(source, target)
        accepted = {name for edge in path for name in edge.options}
        unknown = sorted(set(options) - accepted)
        if unknown:
            raise ValueError(
                f"translate: option(s) {unknown} are accepted by no edge on "
                f"{source!r}→{target!r} (path "
                f"{[e.name for e in path]}, accepted: {sorted(accepted)})")
        result = term
        axioms: Tuple[Any, ...] = ()
        for edge in path:
            mine = {k: v for k, v in options.items() if k in edge.options}
            fresh = edge.side_axioms(result, **mine)
            for_apply = edge._for(edge.apply, mine)
            try:
                carried = tuple(edge.apply(a, **for_apply) for a in axioms)
            except Exception as exc:                 # pragma: no cover - guard
                raise ValueError(
                    f"translate: edge {edge.name!r} cannot carry a side axiom "
                    f"of an earlier edge on {source!r}→{target!r}; this path "
                    f"cannot answer the question for this term") from exc
            result = edge.apply(result, **for_apply)
            axioms = carried + fresh
        notes = "; ".join(e.note for e in path if e.note)
        return TranslationResult(
            result=result, source=source, target=target,
            path=tuple(e.name for e in path),
            lossy=any(e.lossy for e in path), note=notes,
            axioms=axioms,
            # The empty path (source == target) is the identity translation.
            guarantee=("faithful" if not path
                       else weakest_guarantee([e.guarantee for e in path])))


def _build_default_registry() -> ComorphismRegistry:
    """The default edges: exactly the kit's existing translation functions.

    Note what is deliberately NOT an edge: ``circumscription_entails_so`` is an
    entailment decision rather than a term-to-term translation; the Isabelle /
    THF / TPTP / CASL writers are serialisers into text, not into another
    logic's AST, so a path never runs through them; and ``eliminate_lambdas``
    and the ChemLog renamings stay inside one logic. ``qml_translate`` has its
    own ``qml → fol`` edge (the propositional standard translation keeps
    ``modal → fol``), because the two differ in more than the source language:
    the quantified one sorts the domain into worlds and objects and needs the
    sort discipline among its side axioms.
    """
    from .fol.modal_translation import frame_axioms, standard_translation
    from .fol.qml import qml_axioms, qml_translate
    from .fol._msfl_nodes import sort_axioms, subsort_axioms, to_fol
    from .dl.translate import concept_to_fol, concept_to_modal, _reject_data_concept
    from .drt.export import drs_to_fol
    from .drt.reverse import fol_to_drs
    from .semantics.team_translation import dependence_to_eso

    def alc_to_fol(concept):
        # Faithful with no side axioms is true of a concept WITHOUT a data
        # restriction; with one the sorts and the datatype lattice are axioms
        # of a knowledge base (dl.kb_to_fol(..., query=[concept])), so the edge
        # refuses it by name instead of answering for a weaker theory.
        _reject_data_concept(concept, "alc→fol (dl.concept_to_fol)")
        return concept_to_fol(concept)

    registry = ComorphismRegistry()
    registry.register(Comorphism(
        name="standard_translation", source="modal", target="fol",
        apply=standard_translation,
        guarantee="faithful",
        # frame_axioms returns a list; an edge's axioms producer returns a
        # tuple, because TranslationResult.axioms accumulates along a path.
        axioms=lambda term, **options: tuple(frame_axioms(term, **options)),
        options=frozenset({"frame", "systems", "temporal_closure"}),
        note="anchored at the FREE world variable 'w' — universally close it "
             "(∀w …) for validity questions, existentially for satisfiability; "
             "the frame conditions of every relation the image mentions are in "
             ".axioms (pass frame=/systems= to choose the systems), and so is "
             "the membership of every sorted constant c:S of the formula in S "
             "at every world, ∀v0 S(c, v0) — a constant is a rigid designator, "
             "and without that axiom the image has a countermodel in which c "
             "is no S. Take them as SEPARATE premises, never conjoined onto "
             "the image",
    ))
    registry.register(Comorphism(
        name="qml_translate", source="qml", target="fol",
        apply=qml_translate,
        guarantee="faithful",
        # qml_axioms takes the formula as a KEYWORD and gates its output on the
        # relations and sorts occurring in it, so the adapter passes it there.
        axioms=lambda term, **options: tuple(qml_axioms(formula=term, **options)),
        options=frozenset({"mode", "frame", "systems", "bridges",
                           "temporal_closure"}),
        note="quantified modal logic: sorted into World/Object with the "
             "existence predicate E; anchored at the free world variable 'w'. "
             ".axioms carries the sort discipline, the domain regime of mode= "
             "and the frame conditions — the image answers nothing without "
             "them (fol.qml.qml_validity_formula bundles all of it into one "
             "closed sentence instead)",
    ))
    registry.register(Comorphism(
        name="to_fol", source="msfol", target="fol",
        apply=to_fol,
        guarantee="faithful",
        # Sort non-emptiness and the membership of every sorted constant in its
        # sort are read off the sentence (to_fol drops both: ``c:S`` becomes the
        # plain ``c``); a SUBSORT hierarchy is not in the term at all, so it has
        # to come from the signature.
        axioms=lambda term, signature=None: (
            tuple(sort_axioms(term))
            + (tuple(subsort_axioms(signature)) if signature is not None else ())),
        options=frozenset({"signature"}),
        note="many-sorted → unsorted: sorts become unary guards and a sorted "
             "constant c:S becomes the plain c. .axioms has one non-emptiness "
             "sentence per sort (the kit's MSFOL convention), one membership "
             "atom S(c) per sorted constant (without it the image forgets that "
             "c is in S) and, with signature=, one implication per declared "
             "subsort edge; all of them are SEPARATE premises — conjoining "
             "them onto the image makes a prover prove the axiom and valid "
             "formulas come back REFUTED. Take .axioms of the premises AND of "
             "the conclusion",
    ))
    registry.register(Comorphism(
        name="to_msfol", source="fuzzy", target="msfol",
        apply=lambda term: term.to_msfol(),
        lossy=True, guarantee="lossy",
        note="Łukasiewicz → classical is a TWO-VALUED PROJECTION: weak and "
             "strong conjunction get the same image, so it is sound only on "
             "crisp {0,1} valuations and is not a validity-preserving route "
             "for fuzzy logic (use semantics.fuzzy / the fuzzy Kripke route)",
    ))
    registry.register(Comorphism(
        name="drs_to_fol", source="drs", target="fol",
        apply=drs_to_fol,
        guarantee="faithful",
        note="a DRS is a closed box: the image is a sentence, no anchor",
    ))
    registry.register(Comorphism(
        name="fol_to_drs", source="fol", target="drs",
        apply=fol_to_drs,
        guarantee="faithful",
        note="the inverse of drs_to_fol ON ITS IMAGE; a formula outside that "
             "image is refused by name (FolToDrsError), never approximated",
    ))
    registry.register(Comorphism(
        name="concept_to_modal", source="alc", target="modal",
        apply=concept_to_modal,
        guarantee="faithful",
        note="single-role concepts only (ALC with one role = modal K); "
             "multi-role concepts raise",
    ))
    registry.register(Comorphism(
        name="concept_to_fol", source="alc", target="fol",
        apply=alc_to_fol,
        guarantee="faithful",
        note="one free individual variable 'x' — close existentially for "
             "satisfiability questions; read against the EMPTY knowledge base. "
             "A concept with a data restriction is refused by name "
             "(UnsupportedDatatypeError): its sort and datatype axioms belong "
             "to a knowledge base — ask dl.kb_to_fol(..., query=[concept])",
    ))
    registry.register(Comorphism(
        name="dependence_to_eso", source="team", target="eso",
        apply=dependence_to_eso,
        guarantee="faithful",
        note="sentences only (no free variables)",
    ))
    return registry


DEFAULT_REGISTRY = _build_default_registry()


def register_comorphism(comorphism: Comorphism, replace: bool = False) -> None:
    """Register an edge in the DEFAULT registry (see :class:`ComorphismRegistry`)."""
    DEFAULT_REGISTRY.register(comorphism, replace=replace)
