"""TBox classification: the named-concept subsumption hierarchy, as a pure reduction
to :func:`unicode_fol_kit.dl.tableau.subsumes`.

Given a TBox, :func:`classify` collects every named (:class:`~unicode_fol_kit.dl.concepts.Atomic`)
concept mentioned in it, decides the full pairwise subsumption matrix over those names
with the already-tested ``subsumes``, and turns that matrix into the structure an OWL
reasoner's classifier reports: equivalence classes (for concepts a TBox happens to make
synonyms), a transitively-reduced Hasse diagram of direct parents/children, and the
free transitive closure (``ancestors``). No new tableau completion rules are added —
correctness rides entirely on ``subsumes``'s existing soundness and completeness for ALC.

Public API: :class:`Classification`, :func:`classify`.
"""

from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, List, Optional, Set

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DATA_CONCEPTS,
)
from .tableau import TBox, subsumes, _reject_beyond_alc, _reject_inputs, _reject_role_box


@dataclass(frozen=True)
class Classification:
    """The named-concept subsumption hierarchy of a TBox (see :func:`classify`).

    Every key and every member of every value is a *canonical name*: the
    lexicographically smallest name in its mutual-subsumption equivalence class, so
    that a TBox with synonyms (``Bachelor ≡ Man ⊓ ¬Married``) still reports one node
    per distinct concept rather than one per name.
    """

    equivalents: Dict[str, FrozenSet[str]]
    """Canonical name -> its full synonym set (itself included)."""

    parents: Dict[str, FrozenSet[str]]
    """Canonical name -> its *direct* super-concept names (the Hasse diagram)."""

    children: Dict[str, FrozenSet[str]]
    """Canonical name -> its *direct* sub-concept names (the Hasse diagram)."""

    ancestors: Dict[str, FrozenSet[str]]
    """Canonical name -> ALL (transitively closed) super-concept names."""


def _atomic_names(concept: Concept, names: Set[str]) -> None:
    """Recursively collect every :class:`Atomic` name occurring in ``concept`` into ``names``.

    Refuses — through the tableau's own concept guard, with
    :class:`~unicode_fol_kit.dl.tableau.UnsupportedConceptError`, the refusal every
    other entry point gives — a :class:`~unicode_fol_kit.dl.concepts.Nominal`
    (caught directly: it is not "atomic-shaped" enough to fall through the
    isinstance chain below, so it hits the final ``else`` on its own) or an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole`-valued ``role`` field
    (checked EXPLICITLY in the ``Exists``/``ForAll``/``AtLeast``/``AtMost``
    branch below, unlike :func:`unicode_fol_kit.dl.concepts.nnf`'s matching
    branches, which leave ``role`` untyped on purpose — see that function's
    docstring): without this explicit check, an ``InverseRole``-only axiom
    would silently contribute NO names to :func:`classify`'s vocabulary
    (``Exists``/``ForAll`` only ever recurse into ``.concept``, never inspect
    ``.role``), so a TBox whose ONLY axiom uses one would classify as an empty,
    vacuously "fine" hierarchy instead of raising — the one shape in this
    module where :func:`unicode_fol_kit.dl.tableau.subsumes`'s own
    ``_reject_beyond_alc`` guard would never even get called to catch it (see
    :func:`classify`'s docstring: it never calls ``subsumes`` at all when its
    collected vocabulary is empty).

    A :class:`~unicode_fol_kit.dl.concepts.HasValue` and a data restriction are
    refused through the tableau's own concept guard, with
    :class:`~unicode_fol_kit.dl.tableau.UnsupportedConceptError`.
    """
    if isinstance(concept, Atomic):
        names.add(concept.name)
    elif isinstance(concept, (Top, Bottom)):
        pass
    elif isinstance(concept, DATA_CONCEPTS):
        # A data restriction names a DATA property and a data range, never a
        # class, so it contributes no name -- but it is outside the fragment the
        # reduction to ``subsumes`` decides, and with a one-name vocabulary
        # ``subsumes`` is never called to say so. The tableau's own concept
        # guard raises the SAME refusal every other entry point gives.
        _reject_beyond_alc(concept)
    elif isinstance(concept, HasValue):
        # Contributes NO class name -- a value restriction names a ROLE and an
        # INDIVIDUAL, neither of which belongs in a subsumption hierarchy over
        # named CONCEPTS -- but it is a nominal in disguise, which the reduction
        # to ``subsumes`` does not decide, and with a one-name vocabulary
        # ``subsumes`` is never called to say so. The tableau's own concept
        # guard raises the SAME refusal every other entry point gives.
        _reject_beyond_alc(concept)
    elif isinstance(concept, Not):
        _atomic_names(concept.concept, names)
    elif isinstance(concept, (And, Or)):
        _atomic_names(concept.left, names)
        _atomic_names(concept.right, names)
    elif isinstance(concept, (Exists, ForAll, AtLeast, AtMost)):
        if isinstance(concept.role, InverseRole):
            # An inverse role contributes no class name either, and with a
            # one-name vocabulary ``subsumes`` is never called to refuse it. The
            # tableau's own concept guard raises the SAME refusal every other
            # entry point gives (UnsupportedConceptError, which the MCP tools
            # return as a structured error; a bare TypeError escaped them).
            _reject_beyond_alc(concept)
        _atomic_names(concept.concept, names)
    else:
        # A bare Nominal lands here: refused by the same guard, by name.
        _reject_beyond_alc(concept)
        raise TypeError(f"classify: unsupported concept {type(concept).__name__}")


def _equivalence_classes(names: List[str], holds) -> List[Set[str]]:
    """Connected components of the mutual-subsumption graph over ``names``."""
    adjacency: Dict[str, Set[str]] = {n: set() for n in names}
    for a in names:
        for b in names:
            if a != b and holds[(a, b)] and holds[(b, a)]:
                adjacency[a].add(b)
                adjacency[b].add(a)
    seen: Set[str] = set()
    classes: List[Set[str]] = []
    for n in names:
        if n in seen:
            continue
        stack, component = [n], set()
        while stack:
            x = stack.pop()
            if x in component:
                continue
            component.add(x)
            stack.extend(adjacency[x] - component)
        seen |= component
        classes.append(component)
    return classes


def classify(tbox: TBox, concepts: Optional[Iterable[Concept]] = None) -> Classification:
    """Classify every named concept of ``tbox`` into a subsumption hierarchy.

    The vocabulary is every :class:`Atomic` name reachable from ``tbox.inclusions``
    (walked through ``And``/``Or``/``Not``/``Exists``/``ForAll``), extended with the
    names occurring in ``concepts`` when given — useful for a name of interest that
    never appears in an axiom (and so would otherwise be invisible, an isolated node
    with no parents/children/ancestors and a singleton equivalence class).

    Raises:
        ~unicode_fol_kit.dl.tableau.UnsupportedAxiomError:
            ``tbox`` carries an axiom KIND no in-house rule
            decides, exactly as ``subsumes`` would raise -- including for a
            TBox with ONE named concept, where the pair loop below never calls
            ``subsumes`` at all (its only ordered pair is ``(A, A)``, answered
            ``True`` without a tableau), so without the up-front guard that one
            shape returned a hierarchy for a knowledge base every other entry
            point refuses.
        ~unicode_fol_kit.dl.tableau.UnsupportedConceptError:
            a stored class expression (or one of
            ``concepts``) contains a value restriction (``HasValue``, a
            nominal in disguise) or a data restriction -- raised by the
            tableau's concept guard whatever the vocabulary's size.
    """
    # The axiom-level guard, once, before anything is decided -- the same call
    # concept_satisfiable/abox_consistent open with. A TBox with zero or one
    # named concept never reaches `subsumes`, so inheriting it was not enough.
    _reject_role_box(tbox, None)
    names: Set[str] = set()
    for sub, sup in tbox.inclusions:
        _atomic_names(sub, names)
        _atomic_names(sup, names)
    extra = list(concepts) if concepts is not None else []
    for c in extra:
        _atomic_names(c, names)
    # The concept-level half of the same guard, over EVERY class expression the
    # TBox stores (a domain or range filler included -- `_atomic_names` above
    # reads inclusions only) and over the extra concepts. `subsumes` runs it per
    # pair, but a vocabulary of fewer than two names makes no such call, and a
    # knowledge base that every other entry point refuses (an OWL 2 built-in
    # property name as a restriction's role, a nominal in a domain filler) got a
    # hierarchy here.
    _reject_inputs(tbox, None, extra)
    ordered = sorted(names)

    # The O(n^2) reduction: decide sub/sup for every ordered pair with `subsumes`.
    holds = {}
    for a in ordered:
        for b in ordered:
            holds[(a, b)] = True if a == b else subsumes(Atomic(a), Atomic(b), tbox)

    classes = _equivalence_classes(ordered, holds)
    canon_of: Dict[str, str] = {}
    equivalents: Dict[str, FrozenSet[str]] = {}
    for component in classes:
        canon = min(component)
        equivalents[canon] = frozenset(component)
        for member in component:
            canon_of[member] = canon
    canon_names = sorted(equivalents)

    # Free byproduct: the un-reduced transitive closure, at the canonical-name level
    # (equivalence-class members all agree on what they subsume/are subsumed by, so one
    # representative pairwise lookup per class is enough).
    ancestors: Dict[str, Set[str]] = {c: set() for c in canon_names}
    for a in canon_names:
        for b in canon_names:
            if a != b and holds[(a, b)]:
                ancestors[a].add(b)

    # Transitive reduction (Hasse diagram): drop a -> b when some c also ancestor of a
    # already reaches b, i.e. a -> c -> b makes a -> b redundant.
    parents: Dict[str, FrozenSet[str]] = {}
    for a in canon_names:
        direct = set(ancestors[a])
        for c in ancestors[a]:
            direct -= ancestors[c]
        parents[a] = frozenset(direct)

    children: Dict[str, Set[str]] = {c: set() for c in canon_names}
    for a, ps in parents.items():
        for p in ps:
            children[p].add(a)

    return Classification(
        equivalents=equivalents,
        parents=parents,
        children={c: frozenset(s) for c, s in children.items()},
        ancestors={c: frozenset(s) for c, s in ancestors.items()},
    )
