"""An ALCHQ tableau reasoner: concept satisfiability, subsumption, ABox consistency.

Decides the core description-logic reasoning tasks for **ALC**, extended with role
hierarchies/transitive roles (**H**, **S** — see "Role hierarchies and transitive
roles (RBox)" below) and qualified number restrictions (**Q** — see "Qualified
number restrictions" below), with *general* TBoxes, by the standard tableau
algorithm. A tableau builds a tree (more precisely, once **Q** is in play, a DAG —
see "Qualified number restrictions") of individuals, each carrying a *label* (a set
of concepts it must satisfy), and applies completion rules:

- ``⊓``: ``x : C ⊓ D``  ⇒  add ``x : C`` and ``x : D`` (deterministic);
- ``⊔``: ``x : C ⊔ D``  ⇒  branch on ``x : C`` | ``x : D`` (nondeterministic);
- ``∃``: ``x : ∃r.C``   ⇒  create a fresh ``r``-successor ``y`` with ``y : C``;
- ``∀``: ``x : ∀r.C`` and ``x —r→ y``  ⇒  add ``y : C``;
- ``≥``, ``≤``, choose: the **Q** number-restriction rules — see "Qualified number
  restrictions" below.

A **clash** is ``x : ⊥``, ``{x : A, x : ¬A}``, or (with **Q**) ``x : ≤n r.C`` together
with ``n+1`` PAIRWISE-DISTINCT ``r``-neighbours of ``x`` all in ``C`` — see below. A
concept is satisfiable iff some branch saturates without a clash. **General TBoxes**
``C ⊑ D`` are *internalised*: the concept ``¬C ⊔ D`` is forced on every individual.
Termination with such axioms relies on **subset blocking** — a generated individual
whose label is contained in that of an earlier individual is not expanded (its
successors are reused) — sound and complete for plain ALC(H+S) (no inverse roles or
number restrictions); see "Qualified number restrictions" below for why it remains
sound and complete once **Q** (still without inverse roles) is added on top.

The instance/realization family are pure reductions to :func:`abox_consistent`
(``instance_check``) and to that in turn (``instance_retrieval``, ``realize``,
``realize_all``) — no new tableau completion rules, so they inherit the same
soundness/completeness as the rest of the reasoner without adding to its burden. The
same is true of :func:`unicode_fol_kit.dl.classification.classify`, which reduces to
:func:`subsumes` alone; consequently every RBox extension below (role hierarchies,
transitive roles) is automatically respected by ``instance_check``, ``classify``, and
the rest of that family with no change to their own code — they only ever call back
into :func:`concept_satisfiable`/:func:`abox_consistent`, which are where the RBox
lives.

Role hierarchies and transitive roles (RBox)
---------------------------------------------
On top of the TBox, :class:`TBox` also carries an **RBox**: role inclusions
``r ⊑ s`` (:meth:`TBox.add_role_inclusion`) and transitivity declarations
``Trans(r)`` (:meth:`TBox.add_transitive_role`). Together with the ALC concept
language this gives **ALCH** (role hierarchies) plus transitive roles, i.e. the
DL usually written **SH** once inverse roles are added on top — this kit
deliberately stops short of inverses and of qualified number restrictions,
which is what keeps the algorithm below (and its blocking argument) simple.

Both axiom kinds are precomputed once per :func:`_solve` call into an
``_RBox`` helper (see ``_new_branch``): ``ancestors(r)`` is the
reflexive-transitive closure of ``⊑`` over role names (``s ∈ ancestors(r)``
iff ``r ⊑* s``), and ``transitive`` is the declared set of transitive role
names. A cycle in the inclusions (``r ⊑ s ⊑ r``) is not rejected — it simply
makes ``ancestors(r) == ancestors(s)``, i.e. the two roles become semantically
synonymous, which is sound (every model where ``r ⊑ s`` and ``s ⊑ r`` both
hold has ``r`` and ``s`` denote the same relation anyway).

Two changes to :func:`_saturate`'s ∀-rule realise the RBox semantics, confined
entirely to that one branch:

1. **H (role hierarchy).** The exact-match edge/restriction test
   ``role == c.role`` is generalised to ``c.role ∈ ancestors(role)`` (i.e.
   ``role ⊑* c.role``): an ``r``-edge is also an ``s``-edge for every
   declared ``r ⊑ s``, so ``x : ∀s.C`` together with an ``r``-successor
   still forces that successor into ``C``. This is exactly Horrocks &
   Sattler's treatment of role hierarchies for **ALCH** ("A Description
   Logic with Transitive and Inverse Roles and Role Hierarchies", *DL'99*).

2. **S (transitive roles, the "∀+"-rule).** Whenever rule 1 fires across an
   edge labelled ``role`` and there exists SOME transitive role ``R`` with
   ``role ⊑* R ⊑* c.role`` (``R`` may equal ``role`` itself, ``c.role``
   itself, or an intermediate declared-transitive role strictly between the
   two), the *whole* restriction ``∀R.C`` — not just ``C`` — is also copied
   onto the successor's label, so the restriction is still active for that
   successor's own ``R``-neighbours, and so on along the entire chain. This
   is the standard ∀+-rule from the same paper (their "R-neighbour" notion,
   restricted here to the non-inverse fragment). Concretely this is what
   makes ``hasChild ⊑ hasDescendant`` plus ``Trans(hasDescendant)`` propagate
   ``∀hasDescendant.C`` down an arbitrarily long chain of ``hasChild`` edges
   (``R = hasDescendant``, transitive, reachable from every ``hasChild``
   edge and equal to the restriction's own role), and equally what makes
   ``Trans(hasChild)`` alone (no hierarchy at all, ``R = role = c.role``)
   propagate along a ``hasChild``-only chain — both are the same rule, just
   different choices of the witnessing ``R``.

**Soundness.** Neither rule ever adds a concept that every model of the role
axioms does not already force onto the successor. Rule 1: ``r ⊑ s`` is
exactly ``∀x,y (r(x,y) → s(x,y))`` (see :func:`unicode_fol_kit.dl.translate.rbox_to_fol`),
so an ``r``-edge already witnesses an ``s``-edge in any model — copying
``C`` across it is just using that fact. Rule 2: chaining rule-1 facts along
``role ⊑* R`` shows every ``role``-edge is also an ``R``-edge, and
``Trans(R)`` (``∀x,y,z (R(x,y) ∧ R(y,z) → R(x,z))``) then makes any further
``R``-neighbour of the successor an ``R``-neighbour of the *original* node
too — exactly the FOL image :func:`rbox_to_fol` renders and the differential
test battery checks the tableau against directly. Everything else (⊓, ⊔, ∃,
the clash condition) is untouched, so soundness elsewhere in the reasoner
carries over unchanged.

**Termination.** Only the ∀-rule changed, and both new cases remain purely
LABEL-GROWING: they add elements to ``branch.label[successor]`` and never
touch an edge or look at (let alone modify) a predecessor's label — exactly
like the pre-existing plain ∀-rule. The role language has no inverse roles,
so a node's label still depends only on what was pushed forward from its
ancestors along the (fixed, ∃-rule-built) tree structure; nothing added by
rule 1 or 2 ever needs to look backward across an edge. That is precisely
the property subset blocking's soundness/completeness proof relies on
(Horrocks & Sattler 1999): a blocked node's label is a SUBSET of its
blocker's, so reusing the blocker's already-expanded subtree instead of
re-expanding remains model-correct regardless of how that label came to
contain what it does. Since rule 2 only ever adds ``ForAll(R, C)`` for an
``R`` drawn from the FINITE set of role names mentioned in the RBox, paired
with a ``C`` that already occurs somewhere in the branch (never a fresh
one), the set of concepts able to appear in any one label stays finite —
bounded by the same subconcept/RBox-role closure the ALC case already
blocks on — so blocking is still guaranteed to trigger within a bounded
number of successor generations, and termination follows exactly as before;
``_blocked`` itself is untouched.

Qualified number restrictions (ALCQ)
-------------------------------------
On top of ALC(H+S), :mod:`unicode_fol_kit.dl.concepts` also has
:class:`~unicode_fol_kit.dl.concepts.AtLeast` (≥n r.C) and
:class:`~unicode_fol_kit.dl.concepts.AtMost` (≤n r.C) — *qualified number
restrictions*. This is the **Q** in ALCHQ (Hollunder & Baader 1991 for the
core ALCQ algorithm; Horrocks, Sattler & Tobies 1999/2000 for the SHQ/SHIQ
extension this kit's role-hierarchy/transitivity combination follows).

**No unique name assumption.** DL semantics never assumes two individuals
(named or generated) denote different domain elements unless something
forces it, so counting "n distinct r-successors" needs an explicit notion of
FORCED distinctness, tracked in ``_Branch.distinct``: a set of node-name
pairs. Two nodes start distinct only when the ≥-rule (below) generates them
TOGETHER as witnesses of the same restriction, or when :meth:`ABox.assert_distinct`
records it explicitly; every other pair (two ABox individuals in particular)
is *not* assumed distinct, exactly per the mandate above — so an ABox with
two named ``r``-successors that are never asserted distinct can always be
read as ONE individual wearing two names, and a ``≤1 r.⊤`` restriction over
them is satisfiable (see ``tests/test_dl_alcq.py``'s ABox-merge cases).

**Simple roles only.** A qualified number restriction may not target a
NON-SIMPLE role — one that is itself transitive, or has a transitive
sub-role reachable via the RBox (``r' ⊑* r`` for some ``Trans(r')``, ``r'``
possibly ``= r``). Combining unrestricted transitivity with counting makes
satisfiability UNDECIDABLE (Horrocks, Sattler & Tobies 1999, "A Description
Logic with Transitive and Inverse Roles and Role Hierarchies", *DL'99*; the
"simple roles" restriction is standard in every DL from SHQ onward). This
kit refuses the combination outright rather than silently mistranslating or
looping forever: :func:`_check_simple_roles` walks every ``AtLeast``/
``AtMost`` reachable from the query concept, the TBox, and the ABox once per
:func:`concept_satisfiable`/:func:`abox_consistent` call and raises
:class:`NonSimpleRoleError`, naming the offending role, before the tableau
ever starts.

**Role-hierarchy-aware neighbour counting.** Exactly like the ∀-rule's rule H
(see above), an ``r``-edge counts as an ``s``-neighbour of its source for
EVERY ``s`` with ``r ⊑* s`` — so ``≥n s.C``/``≤n s.C`` at ``x`` are decided
over ``_role_neighbours(x, s)`` = every DISTINCT ``y`` with an edge ``x —r→ y``
and ``s ∈ ancestors(r)``, not just literal ``s``-edges. "Distinct" matters: a
number restriction counts NEIGHBOURS, so a ``y`` reached by more than one
entailing edge out of ``x`` (e.g. both a literal ``s``-edge and an ``r``-edge
with ``r ⊑ s``, or two sibling sub-roles of ``s``) must be counted exactly
ONCE, not once per edge — ``_role_neighbours`` deduplicates by destination for
exactly this reason (see its own docstring for the branch-corrupting crash an
undeduplicated count used to cause once two entailing edges landed on the same
node, since a self-pair then looks "mergeable" to the ≤-rule below). ``⊤`` as
the qualifying concept is handled specially (``_in_concept``): every
individual is trivially "in ⊤" whether or not the literal concept ``Top()``
was ever added to its label, matching how the rest of the tableau treats ⊤ as
inert.

**The three new completion rules**, all confined to their own functions and
consulted from :func:`_solve` in the same nondeterministic-then-generating
order the ⊔-rule and ∃-rule already use:

1. **≥-rule** (:func:`_find_atleast`, deterministic *generation*, mirrors the
   ∃-rule): if ``x : ≥n r.C`` and ``x`` does not already have ``n``
   pairwise-distinct ``r``-neighbours in ``C``, generate ``n`` FRESH nodes,
   each an ``r``-edge from ``x`` labelled ``C`` (plus the internalised TBox
   concepts, like the ∃-rule), and mark them PAIRWISE distinct from each
   other (never from anyone else). Marking them distinct is what protects an
   already-satisfied ``≥``-restriction from ever being undone by a later
   merge: the ≤-rule (below) only merges NON-distinct pairs, so two
   witnesses generated together for the same restriction can never be
   collapsed back into one.
2. **≤-rule** (:func:`_find_mergeable` + :func:`_merge`, NONDETERMINISTIC —
   this is the mandatory nondeterminism the ≤-rule needs, see below): if
   ``x : ≤n r.C`` and ``x`` has more than ``n`` ``r``-neighbours in ``C``,
   then — since :func:`_clash` has already ruled out ``n+1`` of them being
   pairwise distinct (that is the clash condition itself) — pigeonhole
   guarantees some pair among them is NOT marked distinct; merging THAT pair
   is sound (nothing forces them apart) but WHICH non-distinct pair to merge
   is not determined by the branch alone, so every candidate pair is tried
   as a separate branch, backtracking on failure (this is the "which pair to
   merge" nondeterminism the ≤-rule is known for). A merge redirects every
   edge and re-parents every distinctness pair from the discarded node onto
   the survivor, and unions their labels; the survivor is chosen to be the
   NON-blockable (named/root) node when exactly one of the pair is blockable
   (a generated node can always be discarded — see "Termination" below —
   but a named individual should not be, since :func:`abox_consistent` and
   friends only ever report a boolean, never inspect *which* name survived,
   so the choice is safe either way, but keeping named nodes stable matches
   the standard presentation and avoids surprising a caller who traces the
   branch by hand).
3. **choose-rule** (:func:`_find_choose`, NONDETERMINISTIC, needed for the
   ≤-rule's COMPLETENESS): for ``x : ≥n r.C`` or ``x : ≤n r.C`` and an
   ``r``-neighbour ``y`` of ``x`` with NEITHER ``C`` nor ``¬C`` decided in
   its label, branch on adding ``C`` or ``¬C`` to ``y``. Without this rule
   the ≥-rule's "already satisfied?" check can only see neighbours with ``C``
   LITERALLY in their label, so an undetermined pre-existing neighbour that
   *could* have been reused as a witness gets ignored and a brand-new one
   generated instead — inflating the neighbour count and risking a spurious
   clash against an unrelated ``≤`` restriction that a complete algorithm
   would have avoided by reusing the undetermined neighbour. This is exactly
   the standard DL-handbook justification for the choose-rule (Baader &
   Sattler, "An Overview of Tableau Algorithms for Description Logics",
   *Studia Logica* 2001).

**Termination.** ``_find_atleast``/``_find_choose``/``_find_mergeable`` all
skip blocked nodes exactly like ``_find_exists`` (a blocked node's
consistency is guaranteed by its blocker's, so no rule — old or new — is
ever applied to one). The ≥-rule's generated labels are drawn from the same
finite subconcept/RBox-role closure ``AtLeast``/``AtMost`` are themselves
members of, so blocking triggers within a bounded number of generations
exactly as in the ALC(H+S) case. Merging never threatens this: the ≤-rule
only ever merges two ``r``-NEIGHBOURS OF THE SAME NODE ``x`` (both reached
by a forward edge out of ``x``), so it can only fold sibling subtrees
together, never create a back-edge toward an ancestor of ``x`` — the graph
built by ∃/≥-generation plus ≤-merging stays acyclic with strictly
non-decreasing "distance from a root", which is exactly the structural
property subset blocking's soundness/completeness proof needs (Horrocks &
Sattler 1999; Hollunder & Baader 1991 for the ALCQ-specific merge case):
merging never turns a blocked node's blocker into its own descendant, so
the blocker relationship a blocked node relies on stays valid. (A role
CYCLE among purely NAMED ABox individuals, e.g. ``a —r→ b —r→ a``, needs no
blocking argument at all: named individuals are never blocked in the first
place — see ``_blocked`` — and the branch they live on is finite by
construction, so saturation over it is a plain finite fixed-point
computation, exactly as in pre-Q ALC ABox reasoning.) This is deliberately
the *simplest* sufficient condition, not the most permissive one this
fragment could support (a tighter analysis could shrink the search space by
recognising DAG-equal nodes sooner), which is an appropriate trade for a
tool that must stay auditable, per this kit's own design principles.

Inverse roles and nominals (I, O) — refused, not decided
-----------------------------------------------------------
:mod:`unicode_fol_kit.dl.concepts` also has
:class:`~unicode_fol_kit.dl.concepts.InverseRole` (``r⁻``, a role EXPRESSION
usable wherever a plain role name is) and
:class:`~unicode_fol_kit.dl.concepts.Nominal` (``{a}``) — the **I** and **O**
of SHIQ/SHOIQ. This tableau does NOT decide either: inverse roles break the
subset-blocking argument above (blocking needs a node's label to depend only
on what was pushed FORWARD from its ancestors — see "Termination" above — and
an inverse role lets a successor's label depend on what lies BACKWARD across
an edge, which subset blocking's soundness/completeness proof does not cover;
this is exactly why C45, an in-house SHIQ/SHOIQ tableau rewrite, was
rejected), and nominals need an equality/merging machinery over NAMED
individuals this tableau has none of (``_Branch`` has no notion that two
DIFFERENT node names might denote the SAME nominal-forced individual).
Rather than attempt either and risk an unsound or silently-incomplete result,
:func:`_reject_beyond_alc` walks every concept :func:`concept_satisfiable`/
:func:`abox_consistent` are about to reason over — the query concept (or
every ABox concept assertion) plus every TBox inclusion — and raises
:class:`UnsupportedConceptError`, NAMING the exact construct, before the
tableau starts. :func:`~unicode_fol_kit.dl.concepts.nnf`'s own top-level
dispatch independently refuses a bare ``Nominal`` too (see its docstring) —
belt-and-suspenders, not redundant: ``_reject_beyond_alc`` is the guard that
actually runs first and produces the precise :class:`UnsupportedConceptError`
message; ``nnf``'s refusal is what stops a ``Nominal`` from ever being
silently treated as an ordinary :class:`~unicode_fol_kit.dl.concepts.Atomic`
concept if ``_reject_beyond_alc`` is ever bypassed (a future call site, a
missed nested occurrence) — see ``tests/test_dl_alc.py``'s dedicated
regression test, which calls ``nnf`` directly to prove this second line of
defense still holds on its own. Use
:mod:`unicode_fol_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner —
which DOES decide the full ALCHQ **+ I + O** fragment — for a concept that
genuinely needs either construct.

Public API: :class:`TBox`, :class:`ABox`, :func:`concept_satisfiable`,
:func:`subsumes`, :func:`equivalent`, :func:`concept_unsatisfiable`,
:func:`abox_consistent`, :func:`instance_check`, :func:`instance_retrieval`,
:func:`realize`, :func:`realize_all`, :class:`NonSimpleRoleError`,
:class:`UnsupportedConceptError`.
"""

from dataclasses import dataclass, field
from itertools import combinations
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, nnf,
)

MAX_STEPS = 1_000_000


class NonSimpleRoleError(ValueError):
    """Raised when an ``AtLeast``/``AtMost`` (qualified number restriction) targets a
    NON-SIMPLE role — one that is transitive, or has a transitive sub-role via the
    RBox. Number restrictions on non-simple roles make the logic undecidable (see
    "Qualified number restrictions" in the module docstring), so this kit refuses the
    combination by name rather than risk an unsound or non-terminating result.
    """


class UnsupportedConceptError(ValueError):
    """Raised when a concept reachable from a :func:`concept_satisfiable`/
    :func:`abox_consistent` call contains a :class:`~unicode_fol_kit.dl.concepts.Nominal`
    or an :class:`~unicode_fol_kit.dl.concepts.InverseRole`-valued role — the **I**
    (inverse roles) and **O** (nominals) beyond this tableau's **ALCHQ** fragment
    (see "Inverse roles and nominals (I, O) — refused, not decided" in the module
    docstring). Raised by :func:`_reject_beyond_alc`, named for the exact offending
    construct, before the tableau ever runs — never a silent, too-permissive
    approximation. Use :mod:`unicode_fol_kit.dl.owl_reasoner`'s external,
    HermiT-backed reasoner to decide a concept that needs either construct.
    """


@dataclass
class TBox:
    """A general TBox with an RBox on top: concept inclusions ``C ⊑ D`` and
    equivalences ``C ≡ D`` (the concept-level TBox), plus role inclusions ``r ⊑ s``
    and transitivity declarations ``Trans(r)`` (the RBox — see "Role hierarchies and
    transitive roles (RBox)" in the module docstring for the algorithm and its
    soundness/termination argument).
    """

    inclusions: List[Tuple[Concept, Concept]] = field(default_factory=list)
    role_inclusions: List[Tuple[str, str]] = field(default_factory=list)
    transitive_roles: Set[str] = field(default_factory=set)

    def add(self, sub: Concept, sup: Concept) -> "TBox":
        """Add a general concept inclusion ``sub ⊑ sup`` and return self (chainable)."""
        self.inclusions.append((sub, sup))
        return self

    def add_equivalence(self, c: Concept, d: Concept) -> "TBox":
        """Add an equivalence ``c ≡ d`` (as the two inclusions ``c ⊑ d``, ``d ⊑ c``)."""
        self.inclusions.append((c, d))
        self.inclusions.append((d, c))
        return self

    def add_role_inclusion(self, sub_role: str, super_role: str) -> "TBox":
        """Add a role inclusion ``sub_role ⊑ super_role`` and return self (chainable).

        Every ``sub_role``-edge is then also treated as a ``super_role``-edge by the
        tableau's ∀-rule (RBox rule "H"; see the module docstring).
        """
        self.role_inclusions.append((sub_role, super_role))
        return self

    def add_transitive_role(self, role: str) -> "TBox":
        """Declare ``role`` transitive (``Trans(role)``) and return self (chainable).

        The tableau's ∀+-rule then propagates a ``∀role.C`` restriction along the
        whole chain of ``role``-successors, not just the immediate one (RBox rule
        "S"; see the module docstring).
        """
        self.transitive_roles.add(role)
        return self

    def internalized(self) -> List[Concept]:
        """The concepts ``nnf(¬C ⊔ D)`` every individual must satisfy (one per GCI).

        RBox axioms (``role_inclusions``, ``transitive_roles``) are NOT part of this
        list — they are not concepts forced on every individual, but a separate role
        constraint the tableau's ∀-rule consults directly via ``_RBox`` (see
        ``_new_branch``), so they only ever change how existing labels propagate
        across edges, never what gets internalised onto a label up front.
        """
        return [nnf(Or(Not(sub), sup)) for sub, sup in self.inclusions]


@dataclass
class ABox:
    """An ABox: concept assertions ``a : C``, role assertions ``(a, b) : r``, and
    (for **Q**, since there is no unique name assumption — see "Qualified number
    restrictions" in :mod:`unicode_fol_kit.dl.tableau`'s module docstring)
    ``a ≠ b`` distinctness assertions.
    """

    concept_assertions: List[Tuple[str, Concept]] = field(default_factory=list)
    role_assertions: List[Tuple[str, str, str]] = field(default_factory=list)
    distinct_assertions: List[Tuple[str, str]] = field(default_factory=list)

    def assert_concept(self, individual: str, concept: Concept) -> "ABox":
        """Add a concept assertion ``individual : concept`` (chainable)."""
        self.concept_assertions.append((individual, concept))
        return self

    def assert_role(self, a: str, b: str, role: str) -> "ABox":
        """Add a role assertion ``(a, b) : role`` (chainable)."""
        self.role_assertions.append((a, b, role))
        return self

    def assert_distinct(self, a: str, b: str) -> "ABox":
        """Add a distinctness assertion ``a ≠ b`` (chainable).

        Without a unique name assumption, two ABox individuals may otherwise denote
        the SAME domain element as far as the reasoner is concerned (see the module
        docstring) — this is how to rule that out explicitly, e.g. to make a
        qualified number restriction like ``≤1 r.⊤`` genuinely forbid two named
        ``r``-successors rather than letting them collapse into one.
        """
        self.distinct_assertions.append((a, b))
        return self


class _Branch:
    """A single open tableau branch: per-individual labels, role edges, order, and
    (for **Q**) a pairwise-distinctness relation — see "Qualified number
    restrictions" in the module docstring.
    """

    __slots__ = ("label", "edges", "order", "counter", "distinct")

    def __init__(self):
        self.label = {}                  # node -> set of concepts
        self.edges = set()               # (src, role, dst)
        self.order = []                  # nodes in creation order (for blocking)
        self.counter = 0
        self.distinct = set()            # frozenset({a, b}) pairs forced distinct

    def copy(self) -> "_Branch":
        b = _Branch.__new__(_Branch)
        b.label = {k: set(v) for k, v in self.label.items()}
        b.edges = set(self.edges)
        b.order = list(self.order)
        b.counter = self.counter
        b.distinct = set(self.distinct)
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

    def mark_distinct(self, a: str, b: str) -> None:
        """Force ``a`` and ``b`` (already-added nodes) pairwise distinct."""
        if a != b:
            self.distinct.add(frozenset((a, b)))


class _Ctx:
    def __init__(self, max_steps: int):
        self.steps = max_steps

    def tick(self) -> None:
        self.steps -= 1
        if self.steps <= 0:
            raise RuntimeError("dl tableau: step budget exhausted (raise dl.tableau.MAX_STEPS).")


class _RBox:
    """The role hierarchy/transitivity view of a ``TBox``'s RBox, precomputed once
    per :func:`_solve` call (see ``_new_branch``) and consulted read-only from
    :func:`_saturate`'s ∀-rule (see "Role hierarchies and transitive roles (RBox)"
    in the module docstring for the algorithm this implements and its
    soundness/termination argument).
    """

    __slots__ = ("_ancestors", "transitive")

    def __init__(self, role_inclusions: List[Tuple[str, str]], transitive_roles: Set[str]):
        direct: Dict[str, Set[str]] = {}
        for sub, sup in role_inclusions:
            direct.setdefault(sub, set()).add(sup)
            direct.setdefault(sup, set())
        for role in transitive_roles:
            direct.setdefault(role, set())
        # Reflexive-transitive closure of ⊑ per role, by BFS. A ⊑-cycle just merges
        # the roles on it into one ancestor set (sound — see the module docstring).
        ancestors: Dict[str, FrozenSet[str]] = {}
        for start in direct:
            seen = {start}
            frontier = [start]
            while frontier:
                cur = frontier.pop()
                for nxt in direct[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        frontier.append(nxt)
            ancestors[start] = frozenset(seen)
        self._ancestors = ancestors
        # Public: the declared-transitive role names, read directly by the ∀+-rule
        # (RBox rule S) in _saturate, which iterates it rather than testing
        # membership one role at a time.
        self.transitive: FrozenSet[str] = frozenset(transitive_roles)

    def ancestors(self, role: str) -> FrozenSet[str]:
        """Every role ``role`` entails via ⊑* (``role`` itself included).

        A role that never occurs in any RBox axiom falls back to the reflexive
        singleton ``{role}`` — so a plain ALC ``TBox`` with an empty RBox degrades
        every lookup here to exactly the pre-RBox exact-match behaviour.
        """
        return self._ancestors.get(role, frozenset((role,)))


_EMPTY_RBOX = _RBox([], set())


def _clash(branch: _Branch, rbox: _RBox) -> bool:
    """True iff some individual's label contains ⊥, a complementary atomic pair, or
    (for **Q**) a ``≤n r.C`` together with ``n+1`` PAIRWISE-DISTINCT ``r``-neighbours
    all in ``C`` (see "Qualified number restrictions" in the module docstring).
    """
    for node, concepts in branch.label.items():
        if Bottom() in concepts:
            return True
        for c in concepts:
            if isinstance(c, Not) and isinstance(c.concept, Atomic) and c.concept in concepts:
                return True
            if isinstance(c, AtMost):
                witnesses = _concept_neighbours(branch, rbox, node, c.role, c.concept)
                if _has_pairwise_distinct_subset(branch, witnesses, c.n + 1):
                    return True
    return False


def _saturate(branch: _Branch, rbox: _RBox) -> bool:
    """Apply the deterministic ⊓ and ∀ rules once over the branch; return True if changed.

    The ∀-rule implements both RBox extensions in place (see "Role hierarchies and
    transitive roles (RBox)" in the module docstring): rule H generalises the
    edge/restriction match from ``role == c.role`` to ``c.role ∈ rbox.ancestors(role)``
    (``role ⊑* c.role``), and rule S (the "∀+"-rule) additionally re-adds the whole
    restriction ``ForAll(R, c.concept)`` for every transitive role ``R`` reachable
    from ``role`` and itself reaching ``c.role`` in the role hierarchy, so the
    restriction keeps firing along further ``R``-chains out of the successor.
    """
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
                    if s != node:
                        continue
                    role_ancestors = rbox.ancestors(role)
                    if c.role not in role_ancestors:
                        continue                      # rule H: role ⊑* c.role fails
                    if c.concept not in branch.label[d]:
                        branch.label[d].add(c.concept)
                        changed = True
                    for trans_role in rbox.transitive:          # rule S: ∀+-rule
                        if trans_role not in role_ancestors:
                            continue                  # role ⊑* trans_role fails
                        if c.role not in rbox.ancestors(trans_role):
                            continue                  # trans_role ⊑* c.role fails
                        propagated = ForAll(trans_role, c.concept)
                        if propagated not in branch.label[d]:
                            branch.label[d].add(propagated)
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


# --------------------------------------------------------------------------- #
# Qualified number restrictions (ALCQ) — see "Qualified number restrictions" in
# the module docstring for the algorithm these implement.
# --------------------------------------------------------------------------- #

def _role_neighbours(branch: _Branch, rbox: _RBox, x: str, role: str) -> List[str]:
    """Every DISTINCT ``y`` reached from ``x`` by an edge whose OWN role entails
    ``role`` via the role hierarchy (``r' ⊑* role`` — RBox rule H, generalised from
    the ∀-rule to number restrictions; see the module docstring).

    A number restriction counts NEIGHBOURS, not edges: ``x`` can be linked to the
    same ``y`` by more than one entailing edge (e.g. a direct ``hasChild``-edge and
    an ``hasSon``-edge with ``hasSon ⊑ hasChild``, or simply two role names ``r``,
    ``s`` both declared ``⊑ role``), and ``y`` must still be counted ONCE. Without
    this dedup, ``y`` would appear twice in the returned list; downstream, that
    degenerate self-pair ``(y, y)`` looks to :func:`_find_mergeable` like two
    distinct witnesses eligible to be merged into each other, and :func:`_merge`
    would then delete ``y`` from the branch while edges/labels/distinctness still
    reference it as the survivor too — corrupting the branch (a dangling label
    lookup crashes the very next step). ``dict.fromkeys`` dedups while preserving
    the (branch-``edges``-set-determined) enumeration order.
    """
    return list(dict.fromkeys(d for (s, r, d) in branch.edges if s == x and role in rbox.ancestors(r)))


def _in_concept(branch: _Branch, node: str, concept: Concept) -> bool:
    """True iff ``node`` is (syntactically) known to be in ``concept`` — ``concept``
    is ⊤ (trivially true for everyone, whether or not ``Top()`` was ever literally
    added to a label) or ``concept`` is literally in ``node``'s label.
    """
    return isinstance(concept, Top) or concept in branch.label[node]


def _concept_neighbours(branch: _Branch, rbox: _RBox, x: str, role: str,
                         concept: Concept) -> List[str]:
    """Every ``role``-neighbour of ``x`` (role-hierarchy-aware) that is in ``concept``."""
    return [y for y in _role_neighbours(branch, rbox, x, role) if _in_concept(branch, y, concept)]


def _marked_distinct(branch: _Branch, a: str, b: str) -> bool:
    """True iff ``a`` and ``b`` are FORCED distinct on this branch."""
    return a != b and frozenset((a, b)) in branch.distinct


def _has_pairwise_distinct_subset(branch: _Branch, nodes: List[str], k: int) -> bool:
    """True iff some size-``k`` subset of ``nodes`` is pairwise FORCED-distinct.

    Brute-force over ``C(len(nodes), k)`` combinations — deciding "is there a
    pairwise-distinct k-subset" is a clique-existence question in general, but the
    node sets this reasoner ever builds stay small at the scale it targets (see the
    module docstring's "Qualified number restrictions" section), so this is fine in
    practice; it is not meant for adversarially large ``n``.
    """
    if k <= 0:
        return True
    if len(nodes) < k:
        return False
    for combo in combinations(nodes, k):
        if all(_marked_distinct(branch, a, b) for a, b in combinations(combo, 2)):
            return True
    return False


def _find_atleast(branch: _Branch, rbox: _RBox):
    """An unsatisfied, unblocked ``x : ≥n r.C`` needing fresh witnesses, or None
    (mirrors :func:`_find_exists`; the ≥-rule itself is applied in :func:`_solve`).
    """
    for node in branch.order:
        if _blocked(branch, node):
            continue
        for c in branch.label[node]:
            if isinstance(c, AtLeast) and c.n > 0:
                witnesses = _concept_neighbours(branch, rbox, node, c.role, c.concept)
                if not _has_pairwise_distinct_subset(branch, witnesses, c.n):
                    return node, c
    return None


def _find_choose(branch: _Branch, rbox: _RBox):
    """An ``r``-neighbour of a number-restricted node with neither ``C`` nor ``¬C``
    decided, or None — the choose-rule's trigger (see the module docstring; needed
    for the ≤-rule's completeness). Returns ``(neighbour, C, ¬C)``.
    """
    for node in branch.order:
        if _blocked(branch, node):
            continue
        for c in branch.label[node]:
            if isinstance(c, (AtLeast, AtMost)) and not isinstance(c.concept, Top):
                neg_concept = nnf(Not(c.concept))
                for neighbour in _role_neighbours(branch, rbox, node, c.role):
                    lbl = branch.label[neighbour]
                    if c.concept not in lbl and neg_concept not in lbl:
                        return neighbour, c.concept, neg_concept
    return None


def _find_mergeable(branch: _Branch, rbox: _RBox):
    """An ``x : ≤n r.C`` with more than ``n`` ``r``-neighbours in ``C``, together
    with every candidate NON-distinct pair among them, or None. By this point
    :func:`_clash` has already ruled out ``n+1`` of them being pairwise distinct, so
    (pigeonhole) at least one non-distinct pair is guaranteed to exist whenever this
    returns non-None — see the module docstring for why WHICH pair to merge must be
    tried as separate branches rather than picked once.
    """
    for node in branch.order:
        if _blocked(branch, node):
            continue
        for c in branch.label[node]:
            if isinstance(c, AtMost):
                witnesses = _concept_neighbours(branch, rbox, node, c.role, c.concept)
                if len(witnesses) <= c.n:
                    continue
                # ``a != b`` is defense in depth: ``_role_neighbours`` already
                # dedups by destination, so ``witnesses`` should never contain the
                # same node twice, but a future duplicate-producing path (here or
                # in a caller) must fail safe by skipping the degenerate self-pair
                # rather than handing it to ``_merge`` (see ``_role_neighbours``'s
                # docstring for what a self-merge does to the branch).
                pairs = [(a, b) for i, a in enumerate(witnesses)
                         for b in witnesses[i + 1:]
                         if a != b and not _marked_distinct(branch, a, b)]
                if pairs:
                    return node, c, pairs
    return None


def _merge_order(branch: _Branch, a: str, b: str) -> Tuple[str, str]:
    """Return ``(keep, drop)`` for merging ``a``, ``b``: keep the NON-blockable
    (named/root) node when exactly one of the two is blockable, else keep whichever
    was added to the branch first (see the module docstring's ≤-rule description).
    """
    a_blockable, b_blockable = a.startswith("_x"), b.startswith("_x")
    if a_blockable != b_blockable:
        return (b, a) if a_blockable else (a, b)
    return (a, b) if branch.order.index(a) < branch.order.index(b) else (b, a)


def _merge(branch: _Branch, keep: str, drop: str) -> None:
    """Merge ``drop`` into ``keep`` in place: redirect every edge, union the labels,
    re-parent every distinctness pair, and remove ``drop``. The caller must already
    have confirmed ``keep``/``drop`` are not marked pairwise distinct.

    A no-op when ``keep == drop`` — defense in depth against a degenerate
    self-pair reaching this far (see ``_role_neighbours``'s docstring): merging a
    node into itself has nothing to redirect and must NOT fall through to
    ``del branch.label[drop]``, which would delete a node that ``keep`` (the same
    node) still needs.
    """
    if keep == drop:
        return
    branch.label[keep] |= branch.label[drop]
    branch.edges = {(keep if s == drop else s, r, keep if d == drop else d)
                     for (s, r, d) in branch.edges}
    new_distinct = set()
    for pair in branch.distinct:
        a, b = tuple(pair)
        a2, b2 = (keep if a == drop else a), (keep if b == drop else b)
        if a2 != b2:
            new_distinct.add(frozenset((a2, b2)))
    branch.distinct = new_distinct
    del branch.label[drop]
    branch.order.remove(drop)


def _solve(branch: _Branch, tbox_concepts: List[Concept], rbox: _RBox, ctx: _Ctx) -> bool:
    """Return True iff the branch can be completed without a clash (i.e. is consistent)."""
    while True:
        ctx.tick()
        if _clash(branch, rbox):
            return False
        if _saturate(branch, rbox):
            continue
        if _clash(branch, rbox):
            return False

        disjunction = _find_disjunction(branch)
        if disjunction is not None:
            node, c = disjunction
            for option in (c.left, c.right):
                child = branch.copy()
                child.label[node].add(option)
                if _solve(child, tbox_concepts, rbox, ctx):
                    return True
            return False

        choose = _find_choose(branch, rbox)
        if choose is not None:
            neighbour, concept, neg_concept = choose
            for option in (concept, neg_concept):
                child = branch.copy()
                child.label[neighbour].add(option)
                if _solve(child, tbox_concepts, rbox, ctx):
                    return True
            return False

        mergeable = _find_mergeable(branch, rbox)
        if mergeable is not None:
            _node, _c, pairs = mergeable
            for (a, b) in pairs:
                keep, drop = _merge_order(branch, a, b)
                child = branch.copy()
                _merge(child, keep, drop)
                if _solve(child, tbox_concepts, rbox, ctx):
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

        atleast = _find_atleast(branch, rbox)
        if atleast is not None:
            node, c = atleast
            witnesses = [branch.fresh() for _ in range(c.n)]
            for w in witnesses:
                branch.edges.add((node, c.role, w))
                branch.label[w].update(tbox_concepts)
                branch.label[w].add(c.concept)
            for i in range(len(witnesses)):
                for j in range(i + 1, len(witnesses)):
                    branch.mark_distinct(witnesses[i], witnesses[j])
            continue

        return True                      # saturated and clash-free → consistent


def _collect_number_restriction_roles(concept: Concept, roles: Set[str]) -> None:
    """Recursively gather every role name used in an ``AtLeast``/``AtMost`` anywhere
    inside ``concept`` into ``roles`` (see :func:`_check_simple_roles`).
    """
    if isinstance(concept, (Top, Bottom, Atomic)):
        return
    if isinstance(concept, Not):
        _collect_number_restriction_roles(concept.concept, roles)
    elif isinstance(concept, (And, Or)):
        _collect_number_restriction_roles(concept.left, roles)
        _collect_number_restriction_roles(concept.right, roles)
    elif isinstance(concept, (Exists, ForAll)):
        _collect_number_restriction_roles(concept.concept, roles)
    elif isinstance(concept, (AtLeast, AtMost)):
        roles.add(concept.role)
        _collect_number_restriction_roles(concept.concept, roles)
    else:
        raise TypeError(
            f"_collect_number_restriction_roles: unsupported concept {type(concept).__name__}")


def _is_simple_role(role: str, rbox: _RBox) -> bool:
    """A role is SIMPLE iff no transitive role (itself included) entails it via ⊑*."""
    return not any(role in rbox.ancestors(trans_role) for trans_role in rbox.transitive)


def _check_simple_roles(concepts: List[Concept], rbox: _RBox) -> None:
    """Raise :class:`NonSimpleRoleError` if any ``AtLeast``/``AtMost`` anywhere in
    ``concepts`` restricts a NON-SIMPLE role (see "Qualified number restrictions" in
    the module docstring for why this is refused rather than silently accepted).
    """
    roles: Set[str] = set()
    for concept in concepts:
        _collect_number_restriction_roles(concept, roles)
    for role in sorted(roles):
        if not _is_simple_role(role, rbox):
            raise NonSimpleRoleError(
                f"qualified number restriction on role {role!r} is not allowed: "
                f"{role!r} is NON-SIMPLE — it is transitive, or has a transitive "
                "sub-role via the RBox (a role inclusion into it from a declared-"
                "transitive role). Number restrictions on non-simple roles make the "
                "logic undecidable (Horrocks, Sattler & Tobies 1999/2000: SHQ/SHIQ "
                "restrict AtLeast/AtMost to SIMPLE roles for exactly this reason), so "
                "this kit refuses the combination outright rather than risk an "
                "unsound or non-terminating result.")


def _reject_beyond_alc(concept: Concept) -> None:
    """Raise :class:`UnsupportedConceptError` if ``concept`` (recursively) contains
    a :class:`~unicode_fol_kit.dl.concepts.Nominal` or an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole`-valued ``role`` field — the
    **I**/**O** beyond this tableau's **ALCHQ** fragment (see "Inverse roles and
    nominals (I, O)" in the module docstring). Called on the query concept plus
    every TBox inclusion by :func:`concept_satisfiable`, and on every ABox concept
    assertion plus every TBox inclusion by :func:`abox_consistent` — BEFORE either
    builds a branch, so the tableau never even starts on an unsupported concept.
    ``instance_check``/``instance_retrieval``/``realize``/``realize_all``/
    ``subsumes``/``equivalent`` need no call of their own: they are pure
    reductions to these two (see the module docstring's opening paragraph), so
    they inherit this guard automatically through whichever one they call.
    """
    if isinstance(concept, Nominal):
        raise UnsupportedConceptError(
            f"dl.tableau: Nominal concepts ({{{concept.individual}}}) are outside "
            "ALCHQ (this kit's in-house DL fragment) — no in-house tableau rule "
            "decides them. Use dl.owl_reasoner's external, HermiT-backed reasoner "
            "instead.")
    if isinstance(concept, (Top, Bottom, Atomic)):
        return
    if isinstance(concept, Not):
        _reject_beyond_alc(concept.concept)
    elif isinstance(concept, (And, Or)):
        _reject_beyond_alc(concept.left)
        _reject_beyond_alc(concept.right)
    elif isinstance(concept, (Exists, ForAll, AtLeast, AtMost)):
        if isinstance(concept.role, InverseRole):
            raise UnsupportedConceptError(
                f"dl.tableau: an InverseRole ({concept.role.role}⁻) is outside "
                "ALCHQ (this kit's in-house DL fragment) — no in-house tableau "
                "rule decides it (see the module docstring's 'Inverse roles and "
                "nominals (I, O)' section for why: it breaks subset blocking's "
                "soundness/completeness argument). Use dl.owl_reasoner's "
                "external, HermiT-backed reasoner instead.")
        _reject_beyond_alc(concept.concept)
    else:
        raise TypeError(f"_reject_beyond_alc: unsupported concept {type(concept).__name__}")


def _new_branch(tbox: Optional[TBox]):
    """Return ``(branch, tbox_concepts, rbox)`` for a fresh tableau under ``tbox``.

    ``rbox`` is precomputed once here (not per completion-rule application) because
    it derives entirely from the static ``TBox.role_inclusions``/``transitive_roles``
    and is invariant across the whole tableau expansion — see ``_RBox``.
    """
    tbox_concepts = tbox.internalized() if tbox else []
    rbox = _RBox(tbox.role_inclusions, tbox.transitive_roles) if tbox else _EMPTY_RBOX
    return _Branch(), tbox_concepts, rbox


def concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox``.

    Satisfiable means some model places an individual in the concept while obeying
    every TBox axiom (including its RBox — role hierarchy and transitivity
    declarations, see "Role hierarchies and transitive roles (RBox)" in the module
    docstring). ``tbox=None`` is the empty TBox (pure concept satisfiability).

    Raises:
        UnsupportedConceptError: ``concept`` or a TBox inclusion contains a
            Nominal or an InverseRole-valued role — see "Inverse roles and
            nominals (I, O)" in the module docstring.
    """
    _reject_beyond_alc(concept)
    if tbox is not None:
        for sub, sup in tbox.inclusions:
            _reject_beyond_alc(sub)
            _reject_beyond_alc(sup)
    branch, tbox_concepts, rbox = _new_branch(tbox)
    _check_simple_roles([concept] + tbox_concepts, rbox)
    branch.add_node("a")
    branch.label["a"].update(tbox_concepts)
    branch.label["a"].add(nnf(concept))
    return _solve(branch, tbox_concepts, rbox, _Ctx(MAX_STEPS))


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


def _individuals(abox: ABox) -> Set[str]:
    """The individual names mentioned in ``abox`` (either assertion list).

    An ABox with no named individuals at all falls back to the single anonymous
    individual ``"a"``, matching :func:`abox_consistent`'s own convention that an
    empty ABox is trivially consistent (some individual exists, it just carries
    no assertions).
    """
    individuals = {a for a, _ in abox.concept_assertions}
    for a, b, _ in abox.role_assertions:
        individuals.add(a)
        individuals.add(b)
    for a, b in abox.distinct_assertions:
        individuals.add(a)
        individuals.add(b)
    if not individuals:
        individuals = {"a"}
    return individuals


def abox_consistent(abox: ABox, tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` is consistent (has a model).

    Raises:
        UnsupportedConceptError: an ABox concept assertion or a TBox inclusion
            contains a Nominal or an InverseRole-valued role — see "Inverse
            roles and nominals (I, O)" in the module docstring.
    """
    for _, concept in abox.concept_assertions:
        _reject_beyond_alc(concept)
    if tbox is not None:
        for sub, sup in tbox.inclusions:
            _reject_beyond_alc(sub)
            _reject_beyond_alc(sup)
    branch, tbox_concepts, rbox = _new_branch(tbox)
    abox_concepts = [c for _, c in abox.concept_assertions]
    _check_simple_roles(tbox_concepts + abox_concepts, rbox)
    for ind in sorted(_individuals(abox)):
        branch.add_node(ind)
        branch.label[ind].update(tbox_concepts)
    for ind, concept in abox.concept_assertions:
        branch.label[ind].add(nnf(concept))
    for a, b, role in abox.role_assertions:
        branch.edges.add((a, role, b))
    for a, b in abox.distinct_assertions:
        branch.mark_distinct(a, b)
    return _solve(branch, tbox_concepts, rbox, _Ctx(MAX_STEPS))


def instance_check(abox: ABox, individual: str, concept: Concept,
                    tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` entails ``individual : concept``.

    Decided by the ABox-level mirror of :func:`subsumes`'s reduction: entailment
    holds iff asserting the *complement* ``individual : ¬concept`` alongside the
    existing assertions makes the knowledge base inconsistent (every model of the
    KB already puts ``individual`` in ``concept``, so adding ``¬concept`` cannot be
    satisfied). This is open-world: a False result means the KB does not entail
    membership, not that it entails non-membership.
    """
    abox2 = ABox(
        concept_assertions=abox.concept_assertions + [(individual, Not(concept))],
        role_assertions=list(abox.role_assertions),
        distinct_assertions=list(abox.distinct_assertions),
    )
    return not abox_consistent(abox2, tbox)


def instance_retrieval(abox: ABox, concept: Concept, tbox: Optional[TBox] = None) -> Set[str]:
    """Return every individual of ``abox`` that ``(tbox, abox)`` entails is a ``concept``.

    Sweeps :func:`instance_check` over every individual named in ``abox`` — including
    one that appears only inside a role assertion, never a concept assertion.
    """
    return {ind for ind in _individuals(abox) if instance_check(abox, ind, concept, tbox)}


def realize(abox: ABox, individual: str, vocabulary: List[Concept],
            tbox: Optional[TBox] = None) -> List[Concept]:
    """Return ``individual``'s most-specific concepts from ``vocabulary``.

    ``vocabulary`` is the caller-supplied list of concepts to classify against —
    realization needs a fixed vocabulary since this reasoner has no persistent
    TBox-signature registry to draw one from automatically (see
    :func:`unicode_fol_kit.dl.classify` for that, over named TBox concepts).

    First keeps only the ``C`` in ``vocabulary`` with ``instance_check(abox,
    individual, C, tbox)``, then drops any ``C`` for which some other kept ``D``
    strictly subsumes it (``D ⊑ C`` holds but ``C ⊑ D`` does not) — the remaining
    antichain is what every OWL reasoner reports as "the" (most specific) types.
    """
    candidates = [c for c in vocabulary if instance_check(abox, individual, c, tbox)]
    return [c for c in candidates
            if not any(subsumes(d, c, tbox) and not subsumes(c, d, tbox) for d in candidates)]


def realize_all(abox: ABox, vocabulary: List[Concept],
                 tbox: Optional[TBox] = None) -> Dict[str, List[Concept]]:
    """Return :func:`realize` for every individual named in ``abox``, keyed by name."""
    return {ind: realize(abox, ind, vocabulary, tbox) for ind in sorted(_individuals(abox))}
