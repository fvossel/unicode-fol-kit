"""An ALC tableau reasoner: concept satisfiability, subsumption, ABox consistency.

Decides the core description-logic reasoning tasks for **ALC** with *general* TBoxes
by the standard tableau algorithm. A tableau builds a tree of individuals, each
carrying a *label* (a set of concepts it must satisfy), and applies completion rules:

- ``⊓``: ``x : C ⊓ D``  ⇒  add ``x : C`` and ``x : D`` (deterministic);
- ``⊔``: ``x : C ⊔ D``  ⇒  branch on ``x : C`` | ``x : D`` (nondeterministic);
- ``∃``: ``x : ∃r.C``   ⇒  create a fresh ``r``-successor ``y`` with ``y : C``;
- ``∀``: ``x : ∀r.C`` and ``x —r→ y``  ⇒  add ``y : C``.

A **clash** is ``x : ⊥`` or ``{x : A, x : ¬A}``. A concept is satisfiable iff some
branch saturates without a clash. **General TBoxes** ``C ⊑ D`` are *internalised*: the
concept ``¬C ⊔ D`` is forced on every individual. Termination with such axioms relies
on **subset blocking** — a generated individual whose label is contained in that of an
earlier individual is not expanded (its successors are reused), which is sound and
complete for ALC (no inverse roles or number restrictions).

Public API: :class:`TBox`, :class:`ABox`, :func:`concept_satisfiable`,
:func:`subsumes`, :func:`equivalent`, :func:`concept_unsatisfiable`,
:func:`abox_consistent`.
"""

from dataclasses import dataclass, field
from typing import List, Optional, Tuple

from .concepts import Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, nnf

MAX_STEPS = 1_000_000


@dataclass
class TBox:
    """A general TBox: concept inclusions ``C ⊑ D`` and equivalences ``C ≡ D``."""

    inclusions: List[Tuple[Concept, Concept]] = field(default_factory=list)

    def add(self, sub: Concept, sup: Concept) -> "TBox":
        """Add a general concept inclusion ``sub ⊑ sup`` and return self (chainable)."""
        self.inclusions.append((sub, sup))
        return self

    def add_equivalence(self, c: Concept, d: Concept) -> "TBox":
        """Add an equivalence ``c ≡ d`` (as the two inclusions ``c ⊑ d``, ``d ⊑ c``)."""
        self.inclusions.append((c, d))
        self.inclusions.append((d, c))
        return self

    def internalized(self) -> List[Concept]:
        """The concepts ``nnf(¬C ⊔ D)`` every individual must satisfy (one per GCI)."""
        return [nnf(Or(Not(sub), sup)) for sub, sup in self.inclusions]


@dataclass
class ABox:
    """An ABox: concept assertions ``a : C`` and role assertions ``(a, b) : r``."""

    concept_assertions: List[Tuple[str, Concept]] = field(default_factory=list)
    role_assertions: List[Tuple[str, str, str]] = field(default_factory=list)

    def assert_concept(self, individual: str, concept: Concept) -> "ABox":
        """Add a concept assertion ``individual : concept`` (chainable)."""
        self.concept_assertions.append((individual, concept))
        return self

    def assert_role(self, a: str, b: str, role: str) -> "ABox":
        """Add a role assertion ``(a, b) : role`` (chainable)."""
        self.role_assertions.append((a, b, role))
        return self


class _Branch:
    """A single open tableau branch: per-individual labels, role edges, order."""

    __slots__ = ("label", "edges", "order", "counter")

    def __init__(self):
        self.label = {}                  # node -> set of concepts
        self.edges = set()               # (src, role, dst)
        self.order = []                  # nodes in creation order (for blocking)
        self.counter = 0

    def copy(self) -> "_Branch":
        b = _Branch.__new__(_Branch)
        b.label = {k: set(v) for k, v in self.label.items()}
        b.edges = set(self.edges)
        b.order = list(self.order)
        b.counter = self.counter
        return b

    def add_node(self, node: str) -> None:
        if node not in self.label:
            self.label[node] = set()
            self.order.append(node)

    def fresh(self) -> str:
        self.counter += 1
        node = f"_x{self.counter}"
        self.add_node(node)
        return node


class _Ctx:
    def __init__(self, max_steps: int):
        self.steps = max_steps

    def tick(self) -> None:
        self.steps -= 1
        if self.steps <= 0:
            raise RuntimeError("dl tableau: step budget exhausted (raise dl.tableau.MAX_STEPS).")


def _clash(branch: _Branch) -> bool:
    """True iff some individual's label contains ⊥ or a complementary atomic pair."""
    for concepts in branch.label.values():
        if Bottom() in concepts:
            return True
        for c in concepts:
            if isinstance(c, Not) and isinstance(c.concept, Atomic) and c.concept in concepts:
                return True
    return False


def _saturate(branch: _Branch) -> bool:
    """Apply the deterministic ⊓ and ∀ rules once over the branch; return True if changed."""
    changed = False
    for node in list(branch.label):
        for c in list(branch.label[node]):
            if isinstance(c, And):
                for part in (c.left, c.right):
                    if part not in branch.label[node]:
                        branch.label[node].add(part)
                        changed = True
            elif isinstance(c, ForAll):
                for (s, role, d) in branch.edges:
                    if s == node and role == c.role and c.concept not in branch.label[d]:
                        branch.label[d].add(c.concept)
                        changed = True
    return changed


def _find_disjunction(branch: _Branch):
    """An unresolved ``x : C ⊔ D`` (neither disjunct present yet), or None."""
    for node in branch.order:
        for c in branch.label[node]:
            if isinstance(c, Or) and c.left not in branch.label[node] \
                    and c.right not in branch.label[node]:
                return node, c
    return None


def _blocked(branch: _Branch, node: str) -> bool:
    """Subset blocking: a generated node subsumed by an earlier node is not expanded."""
    if not node.startswith("_x"):
        return False                     # named / root individuals are never blocked
    idx = branch.order.index(node)
    lbl = branch.label[node]
    return any(branch.label[other] >= lbl for other in branch.order[:idx])


def _find_exists(branch: _Branch):
    """An unsatisfied, unblocked ``x : ∃r.C`` to generate a witness for, or None."""
    for node in branch.order:
        if _blocked(branch, node):
            continue
        for c in branch.label[node]:
            if isinstance(c, Exists):
                if not any(s == node and role == c.role and c.concept in branch.label[d]
                           for (s, role, d) in branch.edges):
                    return node, c
    return None


def _solve(branch: _Branch, tbox_concepts: List[Concept], ctx: _Ctx) -> bool:
    """Return True iff the branch can be completed without a clash (i.e. is consistent)."""
    while True:
        ctx.tick()
        if _clash(branch):
            return False
        if _saturate(branch):
            continue
        if _clash(branch):
            return False

        disjunction = _find_disjunction(branch)
        if disjunction is not None:
            node, c = disjunction
            for option in (c.left, c.right):
                child = branch.copy()
                child.label[node].add(option)
                if _solve(child, tbox_concepts, ctx):
                    return True
            return False

        existential = _find_exists(branch)
        if existential is not None:
            node, c = existential
            witness = branch.fresh()
            branch.edges.add((node, c.role, witness))
            branch.label[witness].update(tbox_concepts)
            branch.label[witness].add(c.concept)
            continue

        return True                      # saturated and clash-free → consistent


def _new_branch(tbox: Optional[TBox]):
    """Return ``(branch, tbox_concepts)`` for a fresh tableau under ``tbox``."""
    tbox_concepts = tbox.internalized() if tbox else []
    return _Branch(), tbox_concepts


def concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox``.

    Satisfiable means some model places an individual in the concept while obeying
    every TBox axiom. ``tbox=None`` is the empty TBox (pure concept satisfiability).
    """
    branch, tbox_concepts = _new_branch(tbox)
    branch.add_node("a")
    branch.label["a"].update(tbox_concepts)
    branch.label["a"].add(nnf(concept))
    return _solve(branch, tbox_concepts, _Ctx(MAX_STEPS))


def concept_unsatisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is unsatisfiable with respect to ``tbox``."""
    return not concept_satisfiable(concept, tbox)


def subsumes(sub: Concept, sup: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``tbox`` entails ``sub ⊑ sup`` (every model puts ``sub`` in ``sup``).

    Decided by the standard reduction: ``sub ⊑ sup`` holds iff ``sub ⊓ ¬sup`` is
    unsatisfiable with respect to the TBox.
    """
    return not concept_satisfiable(And(sub, Not(sup)), tbox)


def equivalent(c: Concept, d: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``tbox`` entails ``c ≡ d`` (mutual subsumption)."""
    return subsumes(c, d, tbox) and subsumes(d, c, tbox)


def abox_consistent(abox: ABox, tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` is consistent (has a model)."""
    branch, tbox_concepts = _new_branch(tbox)
    individuals = {a for a, _ in abox.concept_assertions}
    for a, b, _ in abox.role_assertions:
        individuals.add(a)
        individuals.add(b)
    if not individuals:
        individuals = {"a"}
    for ind in sorted(individuals):
        branch.add_node(ind)
        branch.label[ind].update(tbox_concepts)
    for ind, concept in abox.concept_assertions:
        branch.label[ind].add(nnf(concept))
    for a, b, role in abox.role_assertions:
        branch.edges.add((a, role, b))
    return _solve(branch, tbox_concepts, _Ctx(MAX_STEPS))
