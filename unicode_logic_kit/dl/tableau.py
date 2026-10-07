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

The instance/realization family are reductions to :func:`abox_consistent`
(``instance_check``) and to that in turn (``instance_retrieval``, ``realize``,
``realize_all``) — they add no tableau completion rule, so they inherit the same
soundness/completeness as the rest of the reasoner without adding to its burden (the
guard they run first is the one thing they do add: see "The axiom-kind table"
below). The same is true of :func:`unicode_logic_kit.dl.classification.classify`, which
reduces to
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
exactly ``∀x,y (r(x,y) → s(x,y))`` (see :func:`unicode_logic_kit.dl.translate.rbox_to_fol`),
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

The rest of the OWL 2 role box: characteristics, disjointness, chains
----------------------------------------------------------------------
OWL 2 has nine more object-property axiom kinds, and a :class:`TBox` carries
every one of them (builders never refuse — see "The axiom-kind table" below).
Three of them this tableau DECIDES, six it REFUSES BY NAME, and the split is
not a matter of effort: it follows from one property of the completion graph.

**The three decided: irreflexivity, asymmetry, role disjointness.** Each
forbids an edge PATTERN and forces no concept on anybody, so each is ONE new
clash condition in :func:`_clash` and nothing else:

* ``IrreflexiveObjectProperty(P)`` (:meth:`TBox.add_irreflexive_role`) — clash
  if some edge ``x —R→ x`` has ``R ⊑* P``.
* ``AsymmetricObjectProperty(P)`` (:meth:`TBox.add_asymmetric_role`) — clash if
  edges ``x —R→ y`` and ``y —R'→ x`` both have ``R ⊑* P`` and ``R' ⊑* P``. The
  degenerate ``x = y`` is included, which is right: asymmetry ENTAILS
  irreflexivity (instantiate ``y := x`` in ``P(x,y) → ¬P(y,x)``).
* ``DisjointObjectProperties(P, Q)`` (:meth:`TBox.add_disjoint_roles`) — clash
  if edges ``x —R→ y`` and ``x —R'→ y`` with the SAME source and the SAME
  destination have ``R ⊑* P`` and ``R' ⊑* Q``. The degenerate ``P = Q`` falls
  out of this with ``R' = R``, correctly making ``P`` empty.

All three are read off one per-``_solve``-iteration index of the branch's edges
(:func:`_edge_closure`: ``(source, destination) -> every role the edges between
them entail via ⊑*``), and all three are skipped outright unless
``_RBox.has_edge_constraints`` says the role box declares one — ``_clash`` is
the innermost loop of the whole reasoner and a plain ALC/ALCQ TBox must not pay
for a feature it does not use.

**Soundness** of the three is the same one-line argument: each condition is
strictly SUBTRACTIVE. It adds no concept, adds no edge, changes no rule, and
closes a branch only where two edges the branch itself entails contradict the
axiom in EVERY model — so ``_saturate``, ``_blocked``, ``_merge``,
``_find_*`` and the termination argument above are untouched, and the only
branches lost were unsatisfiable anyway.

**Completeness** rests on two things, and the second is the one an implementer
must not get wrong.

1. *The roles are SIMPLE.* OWL 2 (Structural Specification §11) restricts these
   three axioms — and ``FunctionalObjectProperty``/
   ``InverseFunctionalObjectProperty``, and every number restriction — to
   SIMPLE roles, and :func:`_check_simple_role_box` enforces exactly that
   condition, by name, before the tableau starts. A role is COMPOSITE iff it is
   declared transitive or is the super-role of a property chain, and NON-SIMPLE
   iff some composite role entails it via ``⊑*`` (``r' ⊑* r`` for composite
   ``r'``, ``r'`` possibly ``= r``). That direction matters: a composite
   SUB-role is what makes the super-role non-simple, and reading it the other
   way round silently readmits an undecidable combination (Horrocks, Sattler &
   Tobies 1999). With simplicity in hand, the ``P``-relation a saturated branch
   entails is EXACTLY the one-step ``⊑*``-closure of ``branch.edges`` — no
   transitive closure and no chain closure can manufacture a pair the one-step
   check missed — so the edge-pattern tests above are exact rather than merely
   sound.
2. *The model is read off the UNRAVELLED tree*, not the looped finite model the
   usual subset-blocking presentation builds. Concretely: with ``⊤ ⊑ ∃r.⊤`` and
   ``Asym(r)``, the looped model (a blocked node's edge bent back to its
   blocker) contains both ``r(a, _x1)`` and ``r(_x1, a)`` and so violates
   asymmetry, while the INFINITE unravelled tree model does not. The tableau's
   answer (satisfiable) is correct and only the completeness proof's model
   CONSTRUCTION needs the unravelling; an implementer who checks the rule
   against the looped model will wrongly conclude it is unsound and weaken it.
   The generated part of a branch is a tree, so it never contains a converse
   pair or a self-loop at all; the only sources are ABox role assertions
   (finite, possibly cyclic, checked literally) and the ≤-rule's merges — and
   ``_clash`` runs at the TOP of every :func:`_solve` iteration, hence after
   every merge, with ``_solve`` backtracking over the other candidate pairs, so
   a merge choice that violates one of the three is rejected and another is
   tried. ``tests/test_dl_rbox.py``'s unbounded-chain case is this argument's
   regression, and its at-most-one merge case proves the condition is consulted
   after a merge rather than only at branch setup.

**Functionality is not a new rule at all.** ``FunctionalObjectProperty(P)``
(:meth:`TBox.add_functional_role`) IS the GCI ``⊤ ⊑ ≤1 P.⊤``, and
``AtMost(1, P, Top())`` on a simple role is already decided by the **Q**
machinery below. So it is INTERNALISED, in :func:`_new_branch` rather than in
:meth:`TBox.internalized` (which stays exactly the GCI list — a guard worth
keeping, see ``tests/test_dl_rbox.py::test_internalized_unaffected_by_rbox``).
``_new_branch`` is the single place both :func:`concept_satisfiable` and
:func:`abox_consistent` take ``tbox_concepts`` from, and the ∃- and ≥-rules
already copy that list onto every freshly generated node, so functionality
applies to generated individuals too, for free. Soundness, completeness and
termination are the existing ALCQ argument, unchanged.

**The six refused**, each by name from :func:`_reject_unsupported` (the shared
axiom-level guard) with its own remedy in the message:

* ``InverseObjectProperties(P Q)``, and an :class:`~unicode_logic_kit.dl.concepts.InverseRole`
  on either side of a role inclusion (``r ⊑ s⁻``) — the **I** of SHIQ, refused
  for exactly the reason given under "Inverse roles and nominals (I, O)" below:
  a back-edge makes a node's label depend on what lies BACKWARD across an edge,
  which subset blocking's soundness/completeness argument does not cover.
* ``SymmetricObjectProperty(P)`` — this IS the inverse-role inclusion
  ``P ⊑ P⁻``. The tempting shortcut, materialising the converse edge whenever
  ``(x, P, y)`` is added, puts a CYCLE into the completion graph, so a blocked
  node's blocker can become its own descendant; same failure, same refusal.
* ``InverseFunctionalObjectProperty(P)`` — the number restriction
  ``≤1 P⁻.⊤``, which counts P-PREDECESSORS. The **I** again; the message points
  at :meth:`TBox.add_functional_role` in case functionality on ``P`` itself was
  meant.
* ``ReflexiveObjectProperty(P)`` — the only one refused for a COUNTING reason
  rather than a blocking one. The ∀ half would be cheap (a reflexive ``P``
  makes every node its own ``P``-neighbour, so ``x : ∀Q.C`` with ``P ⊑* Q``
  forces ``C`` onto ``x`` itself: a purely local label rule from the existing
  finite closure). What kills it is that OWL 2 does NOT restrict Reflexive to
  simple roles and does allow ``≤n P.C`` alongside it, and a correct ``≤``/``≥``
  answer then needs :func:`_role_neighbours` to include ``x`` itself — at which
  point :func:`_find_mergeable` can hand :func:`_merge` the pair ``(x, one of
  x's own successors)``, the back-edge case the ≤-rule's termination argument
  explicitly excludes. One unconditional refusal is a smaller and more
  auditable surface than a second, conditional refusal mechanism, and matches
  this module's stated preference for the simplest sufficient condition. (A
  consequence worth recording so it is not re-derived: a role that is both
  reflexive and irreflexive — or both reflexive and asymmetric, which entails
  irreflexivity — is an inconsistent ROLE BOX, since the domain is never empty.
  With Reflexive refused, that combination can never reach the tableau, so no
  RBox-level clash condition is needed for it.)
* ``SubObjectPropertyOf(ObjectPropertyChain(P1 … Pn) Q)`` — complex role
  inclusions, the **R** of SROIQ. Deferred, not impossible, and the rule is
  recorded here so a future session does not have to re-derive it: it would be
  a purely LOCAL label rule — whenever ``∀Q.C`` is in a label and a chain
  ``P1…Pn ⊑ Q'`` exists with ``Q' ⊑* Q``, add ``∀P1.∀P2.…∀Pn.C`` to the SAME
  label, plus ``∀P1.…∀Pn.(C ⊓ ∀Q.C)`` when ``Q`` is transitive — which adds no
  edge and no backward dependency, and whose concept closure is finite exactly
  when the chain dependency graph is ACYCLIC. What that does not give for free
  is (a) the counting side, since a chain-derived ``Q``-edge must count as a
  ``Q``-neighbour — disposed of by the simple-role restriction above, because a
  chain super-role is COMPOSITE and so may carry no number restriction,
  asymmetry, irreflexivity or role disjointness — and (b) the REGULARITY
  restriction a general chain set needs: an irregular set such as
  ``{R∘S ⊑ S, S∘R ⊑ S}`` makes satisfiability undecidable, and deciding
  regularity needs the role-automaton construction of Horrocks, Kutz & Sattler
  2006 ("The Even More Irresistible SROIQ"). (b) is a second piece of work, so
  the honest answer today is a refusal that says so. Ignoring the chain instead
  would report "not subsumed" for a subsumption the FOL image PROVES, which is
  precisely the two-routes-disagree failure this module exists to prevent.

The OWL 2 built-in roles (``owl:topObjectProperty`` and friends)
-----------------------------------------------------------------
``(owl:topObjectProperty)^OP`` is the whole of ``Δ^I × Δ^I`` and
``(owl:bottomObjectProperty)^OP`` is ``∅``. ALCHQ has neither the universal nor
the empty role, and carrying such a name as an ORDINARY role would ship a
weaker theory under a name that looks like a built-in — so no role-box field of
any :class:`TBox` may contain one. Every ``add_*`` method refuses the four
built-ins, in both the abbreviated and the full-IRI spelling
(:data:`RESERVED_ROLE_SPELLINGS`), by name and with the rewrite to use instead.
The ONE way such an axiom may enter is
:func:`~unicode_logic_kit.dl.owl_functional.parse_owl_functional`, which consumes
a TAUTOLOGICAL inclusion (a reserved TOP name as the super-role, or a reserved
BOTTOM name as the sub-role) as a documented no-op — a tautology carries no
truth to lose, which is the same precedent that module already sets and argues
for ``Declaration(...)``/``Annotation(...)``. Consequence to state plainly: the
kit does not gain the universal role, so ``∃owl:topObjectProperty.C`` ("C is
non-empty") remains inexpressible, and ``P ⊑ owl:bottomObjectProperty`` ("P is
empty") must be written as the concept inclusion ``⊤ ⊑ ∀P.⊥``.

Qualified number restrictions (ALCQ)
-------------------------------------
On top of ALC(H+S), :mod:`unicode_logic_kit.dl.concepts` also has
:class:`~unicode_logic_kit.dl.concepts.AtLeast` (≥n r.C) and
:class:`~unicode_logic_kit.dl.concepts.AtMost` (≤n r.C) — *qualified number
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
computation, exactly as in pre-Q ALC ABox reasoning. Since 0.30.0 a named
individual may not BLOCK either, which is a strictly smaller set of eligible
blockers and so leaves this argument untouched; ``_blocked``'s own docstring
says what that restriction protects.) This is deliberately
the *simplest* sufficient condition, not the most permissive one this
fragment could support (a tighter analysis could shrink the search space by
recognising DAG-equal nodes sooner), which is an appropriate trade for a
tool that must stay auditable, per this kit's own design principles.

Value restrictions (ObjectHasValue) — refused, and why no value-rule is sound here
-----------------------------------------------------------------------------------
:class:`~unicode_logic_kit.dl.concepts.HasValue` (``∃r.{a}``, OWL's
``ObjectHasValue(r a)``) names an INDIVIDUAL inside a concept: it is a
NOMINAL, the **O** of SHOIQ, in the one shape that looks harmless. This
tableau does NOT decide it. :func:`_reject_beyond_alc` refuses it, by name,
with :class:`UnsupportedConceptError`, through the same code path that refuses
a bare :class:`~unicode_logic_kit.dl.concepts.Nominal` — wherever it occurs: in
the queried concept, in a TBox inclusion, in a domain or range filler, in an
ABox concept assertion, positive or negated. Everything that reduces to
:func:`concept_satisfiable`/:func:`abox_consistent` refuses with it. The
construct itself is kept as a concept (its FOL image, the Manchester and
Functional-Syntax readers and writers and the external route all handle it);
only the in-house DECISION is gone.

An in-house **value-rule** was built for 0.30.0 and removed again, for the
reason below. It is recorded here so that a later session neither rebuilds it
nor has to rediscover the counterexample.

**The value-rule.** For an unblocked ``x`` with ``∃r.{a}`` in its label and no
entailed ``r``-edge to ``a``: add the NAMED node ``a`` (seeded with the
internalised TBox) and the edge ``x —r→ a``; ``¬∃r.{a}`` clashes with an
entailed ``r``-edge from ``x`` to ``a``. Two defects were found by a
differential fuzz of the tableau against the FOL image, and only the first can
be patched:

1. After a merge (``SameIndividual``, or the ≤-rule identifying two named
   individuals) a concept still mentions the merged-away node by name, and the
   rule re-created that node: ``a : ∃r.{c}``, ``a = c``, ``¬r(c, c)`` was
   reported consistent. An alias map repaired it.
2. **A hole in the method.** Two axioms::

       Asym(s)                       s is asymmetric
       range(s) = ∃s.∃s.{b}          ⊤ ⊑ ∀s.∃s.∃s.{b}

   Hand-derived, in ANY model: take an ``s``-edge ``x → y``. The range axiom
   puts ``y`` in ``∃s.∃s.{b}``, so there are ``y → z`` and ``z → b`` (``z`` is
   in ``∃s.{b}``). The edge ``z → b`` is an ``s``-edge too, so the range axiom
   puts its target ``b`` in ``∃s.∃s.{b}`` as well: ``b → w`` and ``w → b``.
   That is ``s(b, w)`` together with ``s(w, b)``, which asymmetry forbids
   (``w = b`` would be the loop ``s(b, b)``, which asymmetry entails to be
   absent). So NO ``s``-edge can exist, and ``∃s.⊤`` is UNSATISFIABLE with
   respect to the two axioms. The FOL image proves it (``api.prove`` over
   :func:`~unicode_logic_kit.dl.translate.kb_to_fol`) and so does HermiT; the
   tableau with the value-rule answered *satisfiable*. Among what it built
   (traced on the 0.30.0 code) was the chain
   ``_root —s→ _x1 —s→ _x2 —s→ b —s→ _x3``: ``_x2 : ∃s.{b}`` got its edge to
   ``b``; the range axiom put ``∃s.∃s.{b}`` on ``b`` over that edge, which
   generated ``_x3 : ∃s.{b}`` — and ``_x3``'s label equals ``_x2``'s, so
   ``_x3`` is BLOCKED. The value-rule never fires on a blocked node, so the
   edge ``_x3 —s→ b`` was never added and the asymmetry clash
   ``s(b, _x3), s(_x3, b)`` was never seen.

   This is not a bug in one function. A value restriction is the one construct
   that gives a GENERATED node an edge BACK to a NAMED one, and two things in
   this module assume that never happens: subset blocking (a blocked node is
   interpreted by its blocker, so it needs no edges of its own — which is only
   true while no rule has to add one), and the argument above that the role
   box's clash conditions are EXACT because the model is read off the
   unravelled tree (whose generated part has no edge back to anything already
   in it). No patch to the rule restores either assumption.

**The rule that would repair this one case, and what has NOT been shown.**
Fire the value-rule on BLOCKED nodes too, so that ``_x3 —s→ b`` is added and
the clash is seen. It is written down here and deliberately NOT built, because
no soundness and completeness argument for it has been given in this module:
a blocked node that carries edges of its own is no longer interpreted purely
by its blocker, which is the premise of the blocking argument, and the same
question has to be answered for every other condition that reads the edges at
a named node (irreflexivity, role disjointness, negative role assertions, ``≤n``
counting at ``b``). Until that argument exists, the sound answer is the one
given: refuse.

**What decides a value restriction instead:** the FOL image
(:func:`~unicode_logic_kit.dl.translate.kb_to_fol`, then ``api.prove``), and the
external, HermiT-backed reasoner — all nine ``dl.external_*`` entry points
translate it (as owlready2's ``prop.value(individual)``).

**What this module keeps from that work:** ``SameIndividual`` merging
(:func:`_apply_same_assertions` — the ≤-rule's own merge, sound without any
nominal), negative role assertions and their clash condition, the rule that
only a GENERATED node may block (see :func:`_blocked`), and the anonymous
root's name ``"_root"`` (see :func:`concept_satisfiable`). Nothing reads an
individual name out of a concept any more, so a merge needs no alias map on the
branch: :func:`_apply_same_assertions` keeps the one it needs, locally.

Domain and range axioms — ordinary GCIs, a direct FOL image
--------------------------------------------------------------
``ObjectPropertyDomain(P C)`` IS the GCI ``∃P.⊤ ⊑ C`` and
``ObjectPropertyRange(P C)`` is ``⊤ ⊑ ∀P.C``, so both are internalised (in
``_new_branch``, where the functional-role GCI already lives) and decided by
the existing ⊓/⊔/∃/∀ rules with NO new machinery and no change to the
termination argument. The ∀-rule's sub-role closure gives the right
propagation for free: a sub-``P`` edge IS a ``P`` edge, so its target must be
in a range axiom's ``C``.

Worth one line in passing: a RANGE axiom is a pure label-growing
internalisation (cheap), while a DOMAIN axiom is a genuine disjunction
(``∀P.⊥ ⊔ C``) and costs one extra ⊔ branch per node.

The FOL image is deliberately NOT the GCI rewrite: see
:meth:`TBox.add_role_domain`.

Same-individual assertions — decided by merging
--------------------------------------------------
``SameIndividual(a b)`` is decided by genuine node MERGING, not approximated:
:func:`abox_consistent` applies the assertions after the whole branch is set
up and before any completion rule runs, closed under the equivalence they
generate (see :func:`_apply_same_assertions`), reusing the ≤-rule's own
:func:`_merge`. ``instance_check`` then works with no further change, because
``a = b`` with ``a : C`` puts both ``C`` and ``¬C`` in the survivor's label,
which is the existing atomic clash.

Negative role assertions — a clash condition over forbidden edges
--------------------------------------------------------------------
``NegativeObjectPropertyAssertion(r a b)`` is seeded into
``_Branch.negative_edges`` (copied in :meth:`_Branch.copy`, and re-mapped by
:func:`_merge` exactly like a real edge, so ``assert_same(b, c)`` with
``r(a, c)`` and ``¬r(a, b)`` clashes after the merge), and :func:`_clash`
reports a clash when the branch has an entailed edge between the two. Refused
by name on a non-simple role, for the reason
:func:`_non_simple_edge_message` gives.

Inverse roles and nominals (I, O) — refused, not decided
-----------------------------------------------------------
:mod:`unicode_logic_kit.dl.concepts` also has
:class:`~unicode_logic_kit.dl.concepts.InverseRole` (``r⁻``, a role EXPRESSION
usable wherever a plain role name is) and
:class:`~unicode_logic_kit.dl.concepts.Nominal` (``{a}``) — the **I** and **O**
of SHIQ/SHOIQ. (:class:`~unicode_logic_kit.dl.concepts.HasValue` is the nominal in
its disguise as a value restriction; see "Value restrictions (ObjectHasValue)"
above for why it is refused too.)
This tableau does NOT decide either: inverse roles break the
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
tableau starts. :func:`~unicode_logic_kit.dl.concepts.nnf`'s own top-level
dispatch independently refuses a bare ``Nominal`` too (see its docstring) —
belt-and-suspenders, not redundant: ``_reject_beyond_alc`` is the guard that
actually runs first and produces the precise :class:`UnsupportedConceptError`
message; ``nnf``'s refusal is what stops a ``Nominal`` from ever being
silently treated as an ordinary :class:`~unicode_logic_kit.dl.concepts.Atomic`
concept if ``_reject_beyond_alc`` is ever bypassed (a future call site, a
missed nested occurrence) — see ``tests/test_dl_alc.py``'s dedicated
regression test, which calls ``nnf`` directly to prove this second line of
defense still holds on its own. Use
:mod:`unicode_logic_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner —
which DOES decide the full ALCHQ **+ I + O** fragment — for a concept that
genuinely needs either construct.

The data layer — refused here, translated by the FOL image
------------------------------------------------------------
OWL 2's DATA half (data properties, datatypes, literals and facets — see
:mod:`unicode_logic_kit.dl.datatypes`) is NOT decided by this tableau. It has no
data domain: deciding ``∃d.xsd:integer[≥ 5] ⊓ ∀d.xsd:integer[≤ 3]`` needs the
interval algebra of the datatype, deciding ``≥2 d.xsd:boolean`` needs the
CARDINALITY of its value space (exactly 2), and two literals of one datatype
denote different data values, so no ≤-rule may ever merge two data nodes. None
of that is a rule this module has, and a tableau that skipped it would answer
for a WEAKER knowledge base. So it refuses, by name, at both levels:

* every data AXIOM kind (``SubDataPropertyOf``, ``DisjointDataProperties``,
  ``FunctionalDataProperty``, ``DataPropertyDomain``, ``DataPropertyRange``,
  ``DatatypeDefinition``, ``DataPropertyAssertion``,
  ``NegativeDataPropertyAssertion``) is a ``"refused"`` row of
  :data:`_AXIOM_KINDS`, so :func:`_reject_unsupported` raises
  :class:`UnsupportedAxiomError` for it;
* every data CONCEPT (``DataExists``, ``DataForAll``, ``DataHasValue``,
  ``DataAtLeast``, ``DataAtMost``), in a query or in an inclusion, makes
  :func:`_reject_beyond_alc` raise :class:`UnsupportedConceptError` — and
  :func:`~unicode_logic_kit.dl.concepts.nnf` refuses it too, independently,
  exactly as it refuses a bare ``Nominal``.

The FOL image translates all of it (guarded ONE-sorted first-order logic over
the reserved predicates ``OwlThing``/``OwlData``; the sorts are side axioms of
:func:`~unicode_logic_kit.dl.translate.kb_to_fol`), so for the data layer the
route that answers is ``api.prove`` over that image. The cross-check that
usually runs tableau-against-prover runs the other way here: the image against
hand-derived verdicts, and the facet arithmetic against ``atp.z3_arith``.

The axiom-kind table: what each route does with each axiom kind
----------------------------------------------------------------
This kit answers a question about a knowledge base by TWO routes — this
tableau, and the FOL image :mod:`unicode_logic_kit.dl.translate` builds for
``api.prove``. The two must never answer the same question differently, and
"the FOL route handles it while the tableau quietly ignores it" is the shape
that failure takes. :data:`_AXIOM_KINDS` is what makes that impossible to do
by accident: ONE row per axiom kind a :class:`TBox`/:class:`ABox` can hold,
and the row carries four facts.

* ``field`` — the :class:`TBox`/:class:`ABox` attribute that stores it, plus
  the ``builder`` method that fills it.
* ``tableau`` — what THIS module does with it: ``"internalised"`` (it IS a
  general concept inclusion — written as one, or exactly equivalent to one —
  turned into a label concept every node carries, so no new rule and subset
  blocking's termination argument is untouched. ``SubClassOf`` and
  ``EquivalentClasses`` are turned by :meth:`TBox.internalized`;
  ``FunctionalObjectProperty`` (``⊤ ⊑ ≤1 P.⊤``) and
  ``ObjectPropertyDomain``/``ObjectPropertyRange`` (``∃P.⊤ ⊑ C``, ``⊤ ⊑ ∀P.C``)
  by :func:`_new_branch`, which :meth:`TBox.internalized` deliberately leaves
  to it),
  ``"rule"`` (dedicated machinery — a completion rule, a clash condition, or
  initial-branch seeding — whose termination argument is written in this
  docstring), or ``"refused"`` (:func:`_reject_unsupported` raises
  :class:`UnsupportedAxiomError`, naming it).
* ``fol`` — what the FOL image does with it: ``"fol"``
  (:func:`~unicode_logic_kit.dl.translate.kb_to_fol` renders it),
  ``"two-sorted"`` (only the two-sorted entry point renders it) or ``"none"``.
* ``part`` — WHERE in the FOL image it lands: ``"concepts"`` (the
  concept-inclusion image :func:`~unicode_logic_kit.dl.translate.tbox_to_fol`
  builds), ``"side"`` (a side axiom, a premise and never a conjunct of the
  knowledge-base formula), ``"assertions"`` (the ABox image) or ``"none"``.
  :meth:`TBox.has_side_axioms` reads this column, which is how
  ``tbox_to_fol``'s "you are dropping half the TBox" guard is DERIVED from the
  table rather than hand-written over whichever fields existed that week.

Two consequences follow mechanically, and they are the whole point of the
table. First, builders NEVER refuse: :meth:`TBox.add` and friends accept every
kind, because a builder that refuses cannot hold an ontology read from a file
(and the honest answer to "is this knowledge base consistent?" is an answer,
not a constructor exception — see :meth:`ABox.assert_distinct`). The refusal
is raised at QUERY time and at RENDER time. Second, at query time there is ONE
axiom-level guard, :func:`_reject_unsupported`. It is reached through
:func:`_reject_role_box` (which adds the value-level checks) as the first
statement of :func:`concept_satisfiable`, of :func:`abox_consistent` and of
:func:`~unicode_logic_kit.dl.classification.classify`, and through
:func:`_reject_inputs` (the same call plus the concept guard over every stored
class expression) at the top of :func:`instance_retrieval`, :func:`realize`,
:func:`realize_all` and, again, ``classify``. :func:`instance_check`,
:func:`subsumes`, :func:`equivalent` and :func:`concept_unsatisfiable` have no
guard of their own: each reduces to :func:`abox_consistent` or
:func:`concept_satisfiable` with something to decide, and inherits it, for the
reason :func:`_reject_beyond_alc`'s docstring already gives. Inheriting is only
a guard WHEN THERE IS SOMETHING TO REDUCE, which is why the other four carry
their own: ``realize`` with an empty vocabulary, ``realize_all`` and
``instance_retrieval`` on an empty ABox and ``classify`` with fewer than two
names make no call to either function, and so would return before any guard
had run.

``tests/test_dl_route_agreement.py`` enforces the table. Its meta-test
``test_every_tbox_and_abox_field_has_a_row`` goes red the moment a field is
added to :class:`TBox` or :class:`ABox` without a row, so a new axiom kind
cannot be shipped with the two routes silently disagreeing about it.

Search order
------------
Every choice the completion rules leave open is made by a fixed rule that depends
on the order things were INSERTED into the branch and on nothing else — not on a
hash, not on a random number — so a run is reproducible and a step count
(:data:`MAX_STEPS` counts them) means something. The rules are complete under any
order, so the order never changes a verdict; it changes how much of the search
space is visited before the branch closes.

* **Which disjunction is split** (:func:`_find_disjunction`). A disjunction is
  FORCED when at most one of its alternatives (the leaves of the nested ``⊔``) is
  not already contradicted by its node's label — ``⊥``, or an atom whose
  complement is in the label. Splitting a forced disjunction costs one step: the
  branch of a contradicted alternative closes at once and the other alternative
  is the only way on. So the first forced disjunction is split first, and when none
  is forced, the first unresolved one. "First" is in node creation order and, in a
  label, in the order the label received its concepts. The pigeonhole concept
  PHP(n+1, n) (n+1 pigeons, n holes, every pigeon in some hole, no two in one
  hole) shows the difference: splitting the "no two share hole k" clauses in the
  order they were inserted needs about 9 000 steps for four pigeons and does not
  finish within the default budget for five, while splitting a forced disjunction
  first propagates each pigeon's hole into the clauses of that hole and needs about
  500 and 25 000.
* **Which rule fires.** Disjunction, choose, merge, ∃, ≥ — in that order, the
  deterministic ⊓ / ∀ rules first. Within a rule, nodes are taken oldest first
  and a node's concepts in insertion order.
* **Which pair a ≤-restriction merges first.** The ≤-rule tries EVERY candidate
  pair as a branch of its own (see "Qualified number restrictions"), so on a
  branch that closes the order of the pairs changes nothing; the pairs are in
  neighbour order.

Public API: :class:`TBox`, :class:`ABox`, :func:`concept_satisfiable`,
:func:`subsumes`, :func:`equivalent`, :func:`concept_unsatisfiable`,
:func:`abox_consistent`, :func:`instance_check`, :func:`instance_retrieval`,
:func:`realize`, :func:`realize_all`, :class:`NonSimpleRoleError`,
:class:`UnsupportedConceptError`, :class:`UnsupportedAxiomError`,
:class:`RoleExpressionError`.
"""

from collections.abc import Set as _AbstractSet
from dataclasses import dataclass, field
from dataclasses import fields as dataclass_fields
from itertools import combinations
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple, Union

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DATA_CONCEPTS, DataHasValue, DataForAll,
    DataAtLeast, DataAtMost, nnf,
)
from .datatypes import (
    BUILTIN_DATATYPES, DataRange, Datatype, Literal, UnsupportedDatatypeError,
    canonical_datatype_name, datarange_datatypes,
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
    :func:`abox_consistent` call contains a :class:`~unicode_logic_kit.dl.concepts.Nominal`,
    a :class:`~unicode_logic_kit.dl.concepts.HasValue` (a nominal in disguise) or an
    :class:`~unicode_logic_kit.dl.concepts.InverseRole`-valued role — the **I**
    (inverse roles) and **O** (nominals) beyond this tableau's **ALCHQ** fragment
    (see "Inverse roles and nominals (I, O) — refused, not decided" and "Value
    restrictions (ObjectHasValue)" in the module docstring). Raised by
    :func:`_reject_beyond_alc`, named for the exact offending construct, before
    the tableau ever runs — never a silent, too-permissive approximation. Use
    :mod:`unicode_logic_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner, or
    the FOL image (:func:`~unicode_logic_kit.dl.translate.kb_to_fol` with
    ``api.prove``), to decide a concept that needs any of these constructs.
    """


class UnsupportedAxiomError(ValueError):
    """Raised by :func:`concept_satisfiable`/:func:`abox_consistent` when the
    :class:`TBox`/:class:`ABox` they were handed carries an axiom KIND no
    in-house tableau rule decides — a ``"refused"`` row of
    :data:`_AXIOM_KINDS` (see "The axiom-kind table" in the module docstring).

    Deliberately NOT a reuse of :class:`UnsupportedConceptError`, which is
    about a CONCEPT reachable from the query (a nominal, an inverse role): the
    two have different remedies, and a caller that catches the concept-level
    refusal should not silently start catching axiom-level ones as well.

    The message names EVERY refused kind present, with its count, in one go —
    a real ontology hits several at once and a one-at-a-time loop is a bad
    experience — and points at the two routes that DO answer: the external,
    HermiT-backed reasoner (``dl.external_*``) and the FOL image
    (:func:`~unicode_logic_kit.dl.translate.kb_to_fol` + ``api.prove``).
    """


class RoleExpressionError(ValueError):
    """Raised when a role-box builder (``TBox.add_role_inclusion`` and the rest)
    is handed something that is not a usable role in that POSITION — and, as a
    second line of defence behind the builders, by the ONE validation of a
    stored role box (:func:`_validate_role_box`) that BOTH the tableau's shared
    guard and :func:`~unicode_logic_kit.dl.translate.rbox_to_fol` run, so a
    ``TBox`` built through the dataclass constructor or mutated in place fails
    loudly on either route instead of answering (tableau) or rendering a
    nonsense atom (FOL). It is also what the query-time and translation-time
    guards raise for an OWL 2 built-in property name inside a class expression
    or an ABox assertion, which no builder sees (builders never refuse).

    Four cases, each named in the message with the spelling to use instead:

    * a value that is not a role at all — a tuple or list (a caller reaching for
      a property chain: :meth:`TBox.add_role_chain`), or any other type;
    * an :class:`~unicode_logic_kit.dl.concepts.InverseRole` in a position that
      takes a plain role NAME. What to write instead depends on the axiom, and
      the message says it: ``Trans(r⁻)``, ``Sym(r⁻)``, ``Asym(r⁻)``,
      ``Irr(r⁻)`` and ``Refl(r⁻)`` ARE the plain-name axioms (each is preserved
      by taking the converse); ``Func(r⁻)`` is ``InvFunc(r)`` and the other way
      round, a range axiom on ``r⁻`` is the domain axiom on ``r``, and for
      disjointness and chains no plain-name spelling exists. (An
      ``InverseRole`` on either side of a role INCLUSION is accepted, and
      rendered correctly, since ``r ⊑ s⁻`` is a genuinely different axiom from
      ``r ⊑ s``.)
    * one of the four OWL 2 built-in role names (:data:`RESERVED_ROLE_SPELLINGS`)
      — see "The OWL 2 built-in roles" in the module docstring;
    * a role called ``=`` or ``≠``, which the FOL image would render as the
      equality atom.

    This is NOT the "builders never refuse" rule being broken (see "The
    axiom-kind table"): that rule is about axiom KINDS, every one of which a
    ``TBox`` must be able to hold because a parser fills it from a file. These
    three are malformed ARGUMENTS — there is no axiom to hold — and the
    exception landing on the call that is wrong is the whole point.
    """


#: Every spelling of an OWL 2 built-in property name, mapped to its canonical
#: abbreviated form. All four built-ins (top/bottom x object/data) in both the
#: abbreviated and the full-IRI form, in ONE table: the data-property pair is
#: shared with the data-property layer, and two tables would drift.
RESERVED_ROLE_SPELLINGS: Dict[str, str] = {
    "owl:topObjectProperty": "owl:topObjectProperty",
    "http://www.w3.org/2002/07/owl#topObjectProperty": "owl:topObjectProperty",
    "owl:bottomObjectProperty": "owl:bottomObjectProperty",
    "http://www.w3.org/2002/07/owl#bottomObjectProperty": "owl:bottomObjectProperty",
    "owl:topDataProperty": "owl:topDataProperty",
    "http://www.w3.org/2002/07/owl#topDataProperty": "owl:topDataProperty",
    "owl:bottomDataProperty": "owl:bottomDataProperty",
    "http://www.w3.org/2002/07/owl#bottomDataProperty": "owl:bottomDataProperty",
}

#: The two built-ins denoting the UNIVERSAL property (every pair), canonical
#: spelling. An inclusion INTO one of these is a tautology.
RESERVED_TOP_ROLES: FrozenSet[str] = frozenset(
    {"owl:topObjectProperty", "owl:topDataProperty"})

#: The two built-ins denoting the EMPTY property, canonical spelling. An
#: inclusion OUT OF one of these is a tautology.
RESERVED_BOTTOM_ROLES: FrozenSet[str] = frozenset(
    {"owl:bottomObjectProperty", "owl:bottomDataProperty"})


def reserved_role(name) -> Optional[str]:
    """The canonical built-in name ``name`` spells, or None if it is an ordinary
    role name (or not a name at all).
    """
    if not isinstance(name, str):
        return None
    # Both OWL readers store an IRI without its angle brackets; a hand-built
    # name may still carry one pair, and it is the same built-in property.
    if len(name) > 2 and name.startswith("<") and name.endswith(">"):
        name = name[1:-1]
    return RESERVED_ROLE_SPELLINGS.get(name)


def is_tautological_role_inclusion(sub_role, super_role) -> bool:
    """True iff ``sub_role ⊑ super_role`` is valid in EVERY interpretation
    because of a built-in role name: a reserved TOP name as the super-role
    (everything is included in the universal property), or a reserved BOTTOM
    name as the sub-role (the empty property is included in everything).

    ``owl:topObjectProperty ⊑ P`` ("P is universal") and
    ``P ⊑ owl:bottomObjectProperty`` ("P is empty") are deliberately NOT in
    this class: both are genuine constraints, and both are refused by name
    (see "The OWL 2 built-in roles" in the module docstring).
    """
    return (reserved_role(super_role) in RESERVED_TOP_ROLES
            or reserved_role(sub_role) in RESERVED_BOTTOM_ROLES)


#: Role names the FOL image cannot carry as ordinary predicates: it renders an
#: atom named ``=`` / ``≠`` as the equality / disequality of its two arguments
#: (that is how ``⊤`` and ``⊥`` are spelled), so a role called that would be
#: silently read as a different axiom. No OWL source can produce such a name.
_EQUALITY_ROLE_NAMES: FrozenSet[str] = frozenset({"=", "≠"})


def _inverse_advice(kind: Optional[str], role: str) -> str:
    """What to write INSTEAD of ``r⁻`` where an axiom of OWL keyword ``kind``
    takes a plain role name — and only what is TRUE of that axiom.

    Five characteristics are preserved by taking the converse
    (``Trans(r⁻) ⇔ Trans(r)``, and the same for symmetric, asymmetric,
    irreflexive and reflexive), so for those the plain spelling IS the same
    axiom. The others are NOT: ``Func(r⁻)`` says an element has at most one
    r-PREDECESSOR, which is ``InvFunc(r)``, and the other way round; a range
    axiom on ``r⁻`` is the domain axiom on ``r``. For disjointness and chains
    no plain-name spelling exists, and saying "pass r instead" would silently
    build a DIFFERENT axiom — the defect this table replaces.
    """
    r = repr(role)
    same = {
        "TransitiveObjectProperty": "Trans", "SymmetricObjectProperty": "Sym",
        "AsymmetricObjectProperty": "Asym", "IrreflexiveObjectProperty": "Irr",
        "ReflexiveObjectProperty": "Refl",
    }
    if kind in same:
        return (f"{same[kind]}(r⁻) holds exactly when {same[kind]}(r) does "
                f"(this characteristic is preserved by taking the converse), "
                f"so the plain spelling is the same axiom: pass {r} instead.")
    if kind == "FunctionalObjectProperty":
        return (f"Functional(r⁻) is NOT Functional(r): it says an element has "
                f"at most one r-PREDECESSOR, which is InverseFunctional(r). "
                f"Use dl.TBox.add_inverse_functional_role({r}).")
    if kind == "InverseFunctionalObjectProperty":
        return (f"InverseFunctional(r⁻) is NOT InverseFunctional(r): it says "
                f"an element has at most one r-SUCCESSOR, which is "
                f"Functional(r). Use dl.TBox.add_functional_role({r}).")
    if kind == "ObjectPropertyDomain":
        return (f"Domain(r⁻, C) is the RANGE axiom on r, not the domain axiom: "
                f"use dl.TBox.add_role_range({r}, C).")
    if kind == "ObjectPropertyRange":
        return (f"Range(r⁻, C) is the DOMAIN axiom on r, not the range axiom: "
                f"use dl.TBox.add_role_domain({r}, C).")
    if kind == "DisjointObjectProperties":
        return (f"Disjoint(p, q⁻) is NOT Disjoint(p, q) — it forbids p(x, y) "
                f"together with q(y, x) — and no spelling over plain role "
                f"names states it, so this kit cannot hold it as an axiom. "
                f"Pass it to api.prove as the FOL premise "
                f"∀x ∀y ¬(p(x, y) ∧ q(y, x)).")
    if kind == "InverseObjectProperties":
        return (f"Inverses cancel: an inverse role on exactly ONE side of "
                f"InverseObjectProperties makes it the equality p ≡ q (use "
                f"dl.TBox.add_equivalent_roles(p, q)), and on BOTH sides "
                f"InverseObjectProperties(p⁻, q⁻) is InverseObjectProperties"
                f"(p, q) over the plain names.")
    if kind == "EquivalentObjectProperties":
        return (f"State each direction with dl.TBox.add_role_inclusion, which "
                f"does accept an inverse role: add_role_inclusion(p, r⁻) and "
                f"add_role_inclusion(r⁻, p).")
    if kind == "ObjectPropertyChain":
        return (f"An inverse role inside a property chain has no spelling over "
                f"plain role names, so this kit cannot hold it as an axiom. "
                f"Pass it to api.prove as the FOL premise, e.g. "
                f"p ∘ q⁻ ⊑ s is ∀x ∀y ∀z (p(x, y) ∧ q(z, y) → s(x, z)).")
    if kind in ("ObjectPropertyAssertion", "NegativeObjectPropertyAssertion"):
        return (f"r⁻(a, b) is r(b, a): swap the two individuals and pass "
                f"{r}.")
    if kind is not None and "Data" in kind:
        return ("A DATA property has no inverse (only an object property "
                "does); pass the data property's own name.")
    return ("This position takes a plain role name, and no rewrite is offered "
            "because the right one depends on which axiom is meant — it is "
            "NOT always the plain name (Functional(r⁻) is InverseFunctional(r), "
            "for one).")


def _equality_name_message(where: str, name: str) -> str:
    """The refusal for a role (or property) called ``=`` or ``≠`` — see
    :data:`_EQUALITY_ROLE_NAMES`."""
    return (f"{where}: {name!r} is the name of the "
            f"{'EQUALITY' if name == '=' else 'DISEQUALITY'} atom the FOL image "
            f"renders (it is how ⊤ and ⊥ are spelled), not a role name: every "
            f"image of an axiom over it would be printed as "
            f"{'x = y' if name == '=' else 'x ≠ y'}, a different axiom, and no "
            f"OWL ontology can produce such a name. Give the role an ordinary "
            f"name.")


def _kind_of_builder(where: str) -> Optional[str]:
    """The OWL keyword of the axiom a ``where`` like
    ``"dl.TBox.add_functional_role"`` builds, read off :data:`_AXIOM_KINDS`'
    ``builder`` column (plus the two equivalence builders, which store
    inclusions and so have no row of their own). ``None`` when ``where`` is not
    a builder — the caller then passes ``kind=`` itself, or gets the generic
    advice."""
    builder = where.rsplit(".", 1)[-1]
    extra = {"add_equivalent_roles": "EquivalentObjectProperties",
             "add_equivalent_data_properties": "EquivalentDataProperties",
             "assert_role": "ObjectPropertyAssertion",
             "assert_negative_role": "NegativeObjectPropertyAssertion"}
    if builder in extra:
        return extra[builder]
    for row in _AXIOM_KINDS:
        if row.builder == builder:
            return row.kind
    return None


def _check_role_name(value, *, where: str, allow_inverse: bool = False,
                     kind: Optional[str] = None) -> None:
    """Raise :class:`RoleExpressionError` unless ``value`` is a usable role in
    this position: a plain role name that is not an OWL 2 built-in and not the
    name of an equality atom, or — when ``allow_inverse`` — an
    :class:`~unicode_logic_kit.dl.concepts.InverseRole` over one.

    ``where`` names the function the caller actually called, so the message
    points at the call that is wrong rather than at this guard. ``kind`` is the
    OWL keyword of the axiom the role sits in; it picks the advice given for an
    ``InverseRole`` (see :func:`_inverse_advice`) and is read off ``where`` when
    ``where`` names a builder.
    """
    if isinstance(value, InverseRole):
        if allow_inverse:
            _check_role_name(value.role, where=where, kind=kind)
            return
        raise RoleExpressionError(
            f"{where}: an InverseRole ({value.role}⁻) is not a role NAME, and "
            f"this position takes one. "
            f"{_inverse_advice(kind or _kind_of_builder(where), value.role)} "
            f"An InverseRole IS accepted on either side of "
            f"dl.TBox.add_role_inclusion, where r ⊑ s⁻ is a genuinely "
            f"different axiom from r ⊑ s.")
    if isinstance(value, (tuple, list)):
        raise RoleExpressionError(
            f"{where}: expected a role NAME (str), got a "
            f"{type(value).__name__} {value!r}. A sequence of roles is a "
            f"PROPERTY CHAIN — use dl.TBox.add_role_chain(chain, super_role), "
            f"whose FOL image is ∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z)). "
            f"Storing it as a role name instead silently builds an axiom about "
            f"an atomic role nobody named.")
    if not isinstance(value, str):
        raise RoleExpressionError(
            f"{where}: expected a role NAME (str), got "
            f"{type(value).__name__} {value!r}.")
    if value in _EQUALITY_ROLE_NAMES:
        raise RoleExpressionError(_equality_name_message(where, value))
    builtin = reserved_role(value)
    if builtin is None:
        return
    if builtin in RESERVED_TOP_ROLES:
        what = ("the universal property: it relates every pair of individuals")
        remedy = ("An inclusion INTO it is a tautology, and "
                  "dl.parse_owl_functional consumes that shape as a documented "
                  "no-op; 'P is universal' (an inclusion OUT OF it) is the "
                  "universal role of SROIQ, which breaks the tree-model "
                  "property ALCHQ relies on and this kit does not have.")
    else:
        what = "the empty property: it relates no pair at all"
        remedy = ("An inclusion OUT OF it is a tautology, and "
                  "dl.parse_owl_functional consumes that shape as a documented "
                  "no-op; 'P is empty' is the concept inclusion ⊤ ⊑ ∀P.⊥, "
                  "which this kit does decide.")
    raise RoleExpressionError(
        f"{where}: {value!r} is an OWL 2 BUILT-IN property ({builtin} — "
        f"{what}), not an ordinary role name: ALCHQ (this kit's in-house DL "
        f"fragment) has neither the universal nor the empty role, so no role "
        f"box entry may carry it. {remedy}")


def _check_chain_shape(chain, *, where: str, stored: bool = False) -> Tuple:
    """The property chain ``chain`` as a ``tuple`` of role names, or a
    :class:`RoleExpressionError` when it is not an ORDERED collection of them.

    Two inputs are refused by what they are. A plain ``str`` (or ``bytes``) is
    not a chain: it is a sequence of one-character strings, so ``tuple("rs")``
    is ``("r", "s")`` and ``add_role_chain("rs", "t")`` was accepted and stored
    the two roles ``r`` and ``s`` nobody named, and ``add_role_chain("PartOf",
    "R")`` the six single-letter roles of ``P, a, r, t, O, f``. A set-like
    collection (``set``, ``frozenset``, a dict's key view) has no order to
    preserve, and the order of a chain is its meaning.

    Any other iterable — a list, a tuple, a generator, an iterator, ``map`` — is
    ordered, and is MATERIALISED with ``tuple()``: a generator of role names
    worked before the shape guard and still does. The length and the element
    types are checked by the callers on the tuple that comes back.

    ``stored=True`` is the second line of defence over an entry a hand-built
    ``TBox`` already holds: there a chain must BE a tuple or a list, since
    materialising a stored iterator would consume it.
    """
    if isinstance(chain, (str, bytes)):
        reason = ("A str would be split into its CHARACTERS, so 'rs' would "
                  "silently become the two roles 'r' and 's'. "
                  if isinstance(chain, str) else
                  "A bytes value would be split into its integers. ")
    elif isinstance(chain, _AbstractSet):
        reason = ("A chain is ordered, and an unordered collection has no "
                  "order to preserve. ")
    elif stored and not isinstance(chain, Sequence):
        reason = ("A stored chain is a tuple (or list) of role names. ")
    else:
        try:
            return tuple(chain)
        except TypeError:
            reason = "It is not a collection of role names at all. "
    raise RoleExpressionError(
        f"{where}: a property chain is a SEQUENCE of role names — a tuple "
        f"or a list such as ('r', 's') — got {type(chain).__name__} "
        f"{chain!r}. {reason}Write dl.TBox.add_role_chain(['r', 's'], 't').")


def _builtin_family_note(builtin: str, concept_is_data: bool) -> str:
    """A sentence naming a type mismatch — a DATA built-in in an object
    restriction, or an object one in a data restriction — or ``""``."""
    builtin_is_data = "Data" in builtin
    if builtin_is_data == concept_is_data:
        return ""
    return (f" It is also ill-typed OWL 2: {builtin} is a "
            f"{'data' if builtin_is_data else 'object'} property, and this is "
            f"a {'data' if concept_is_data else 'object'}-property "
            f"restriction.")


def _builtin_in_concept_message(where: str, concept, name: str, builtin: str) -> str:
    """The refusal for an OWL 2 built-in property name as the ROLE of a class
    expression (``∃owl:topObjectProperty.A`` and the like), with what to write
    instead — and only what is TRUE of that shape.

    The universal property relates every pair, so a restriction over it talks
    about the WHOLE domain: that is a global statement (the **U** of SROIQ),
    which no ALCHQ concept makes; a global "every element is in C" is the
    general concept inclusion ``⊤ ⊑ C``. ``HasValue`` is the exception —
    ``∃U.{a}`` holds of every element (each is related to ``a``), so it is
    ``⊤``. The empty property relates no pair, so ``∃``/``≥n`` (n ≥ 1) over it
    and ``HasValue`` are unsatisfiable (``⊥``) and ``∀``/``≤n`` (and ``≥0``)
    hold of everything (``⊤``).
    """
    shown = concept.to_unicode()
    if builtin in RESERVED_TOP_ROLES:
        what = "the universal property: it relates every pair of elements"
        if isinstance(concept, (HasValue, DataHasValue)):
            remedy = ("Every element is related to the individual by it, so "
                      "the restriction holds of EVERY element: write dl.Top().")
        else:
            remedy = ("A restriction over it talks about the WHOLE domain — a "
                      "global statement, the universal role of SROIQ, which "
                      "ALCHQ (this kit's in-house DL fragment) does not have "
                      "and no concept can make. A global 'every element is in "
                      "C' is the general concept inclusion ⊤ ⊑ C "
                      "(dl.TBox.add(dl.Top(), C)).")
    else:
        what = "the empty property: it relates no pair at all"
        vacuous = (isinstance(concept, (ForAll, AtMost, DataForAll, DataAtMost))
                   or (isinstance(concept, (AtLeast, DataAtLeast)) and concept.n == 0))
        remedy = ("The restriction holds of every element, so it is ⊤: write "
                  "dl.Top()." if vacuous else
                  "No element can satisfy the restriction, so it is ⊥: write "
                  "dl.Bottom().")
    return (f"{where}: the OWL 2 BUILT-IN property {name!r} ({builtin} — "
            f"{what}) is the role of {type(concept).__name__} ({shown}), and "
            f"it would be read as an ORDINARY role of that name — a different "
            f"restriction, with a different verdict. {remedy}"
            f"{_builtin_family_note(builtin, isinstance(concept, DATA_CONCEPTS))}")


#: The concept classes whose ``role`` field names an OBJECT property.
_OBJECT_ROLE_CONCEPTS = (Exists, ForAll, AtLeast, AtMost, HasValue)


def _reject_concept_role(concept, *, where: str) -> None:
    """Refuse, by name, a role that is not usable as the role of ``concept``
    ITSELF (not its sub-concepts: the caller walks) — an OWL 2 built-in
    property name, the name of an equality atom, or a value that is no role at
    all.

    One function for the three places a concept's role is read — the
    tableau's concept guard (:func:`_reject_beyond_alc`), the standard
    translation (:func:`~unicode_logic_kit.dl.translate.concept_to_fol` and
    friends) and the external route — so the SAME expression is refused with
    the SAME words wherever it is asked. The builders and the glyph/Manchester
    parsers never reach it for a concept built directly, which is exactly why
    it has to be a QUERY-time and TRANSLATION-time check ("builders never
    refuse").

    A data restriction's ``prop`` is read the same way: the four built-in names
    include the two data ones.
    """
    if isinstance(concept, _OBJECT_ROLE_CONCEPTS):
        role = concept.role
    elif isinstance(concept, DATA_CONCEPTS):
        role = concept.prop
    else:
        return
    plain = role.role if isinstance(role, InverseRole) else role
    if isinstance(plain, str):
        if plain in _EQUALITY_ROLE_NAMES:
            raise RoleExpressionError(_equality_name_message(where, plain))
        builtin = reserved_role(plain)
        if builtin is not None:
            raise RoleExpressionError(
                _builtin_in_concept_message(where, concept, plain, builtin))
        return
    _check_role_name(role, where=where, allow_inverse=True)


def _reject_concept_roles_deep(concept: Concept, *, where: str) -> None:
    """:func:`_reject_concept_role` over ``concept`` and every sub-concept —
    for a route (the external one) that has no recursive guard of its own over
    the whole fragment, the way :func:`_reject_beyond_alc` is the tableau's."""
    stack = [concept]
    while stack:
        node = stack.pop()
        _reject_concept_role(node, where=where)
        for attribute in ("concept", "left", "right"):
            child = getattr(node, attribute, None)
            if isinstance(child, Concept):
                stack.append(child)


def _builtin_in_assertion_message(where: str, kind: str, entry, name: str,
                                  builtin: str) -> str:
    """The refusal for an OWL 2 built-in property name in an ABOX assertion,
    with the consequence in OWL 2's own semantics: asserting the universal
    property (or denying the empty one) states nothing, and asserting the empty
    property (or denying the universal one) makes the knowledge base
    inconsistent."""
    negative = kind.startswith("Negative")
    universal = builtin in RESERVED_TOP_ROLES
    holds_always = universal != negative
    first = entry[0]
    if holds_always:
        consequence = ("The assertion holds in EVERY interpretation, so it "
                       "constrains nothing: drop it.")
    else:
        consequence = (f"The assertion holds in NO interpretation, so it makes "
                       f"the knowledge base INCONSISTENT: state that with "
                       f"abox.assert_concept({first!r}, dl.Bottom()) if it is "
                       f"what you mean.")
    what = ("the universal property: it relates every pair"
            if universal else "the empty property: it relates no pair at all")
    return (f"{where}: the OWL 2 BUILT-IN property {name!r} ({builtin} — "
            f"{what}) occurs in the {kind} {entry!r}, and it would be read as an "
            f"ORDINARY role of that name — an uninterpreted relation, which "
            f"answers a different question. {consequence}"
            f"{_builtin_family_note(builtin, kind.startswith(('Data', 'NegativeData')))}")


#: ``(ABox field, OWL keyword, index of the property in the stored tuple)`` for
#: every assertion that names a property.
_ABOX_PROPERTY_FIELDS: Tuple[Tuple[str, str, int], ...] = (
    ("role_assertions", "ObjectPropertyAssertion", 2),
    ("negative_role_assertions", "NegativeObjectPropertyAssertion", 2),
    ("data_assertions", "DataPropertyAssertion", 1),
    ("negative_data_assertions", "NegativeDataPropertyAssertion", 1),
)


def _reject_abox_roles(abox: Optional["ABox"], *, where: str) -> None:
    """Refuse, by name, an ABox assertion whose property is an OWL 2 built-in
    name, the name of an equality atom, an inverse role or no name at all.

    The ABox builders accept every ``str`` (builders never refuse), so this is
    where the assertion is first CHECKED: at query time by the shared guard
    and at translation time by :func:`~unicode_logic_kit.dl.translate.abox_to_fol`.
    ``r⁻(a, b)`` is refused with the true remedy (swap the individuals); a
    built-in is refused with its OWL 2 consequence, because the two readings —
    an ordinary uninterpreted role, and the universal/empty property — give
    different verdicts (``a`` related to ``b`` by the EMPTY property is
    inconsistent; by an ordinary role it is not).
    """
    if abox is None:
        return
    for field_name, kind, index in _ABOX_PROPERTY_FIELDS:
        for entry in getattr(abox, field_name):
            name = entry[index]
            if isinstance(name, str) and name not in _EQUALITY_ROLE_NAMES:
                builtin = reserved_role(name)
                if builtin is not None:
                    raise RoleExpressionError(_builtin_in_assertion_message(
                        where, kind, entry, name, builtin))
            _check_role_name(name, where=where, kind=kind)


def _stored_pair(entry, kind: str, where: str) -> Tuple[object, object]:
    """``entry`` as the two-element pair a TBox list of ``kind`` stores, or a
    :class:`RoleExpressionError` — never the bare ``ValueError`` that unpacking
    a 3-tuple raises, which names no axiom and no call."""
    if not (isinstance(entry, (tuple, list)) and len(entry) == 2):
        raise RoleExpressionError(
            f"{where}: a stored {kind} entry is a PAIR of two values, got "
            f"{entry!r}. Build the TBox with the builder that stores {kind} "
            f"instead of assembling its list by hand.")
    return entry[0], entry[1]


#: ``(TBox field, OWL keyword)`` of every object-role axiom that stores plain
#: role NAMES, set-valued.
_NAME_SET_FIELDS: Tuple[Tuple[str, str], ...] = (
    ("transitive_roles", "TransitiveObjectProperty"),
    ("symmetric_roles", "SymmetricObjectProperty"),
    ("asymmetric_roles", "AsymmetricObjectProperty"),
    ("reflexive_roles", "ReflexiveObjectProperty"),
    ("irreflexive_roles", "IrreflexiveObjectProperty"),
    ("functional_roles", "FunctionalObjectProperty"),
    ("inverse_functional_roles", "InverseFunctionalObjectProperty"),
)


def _validate_role_box(tbox: "TBox", *, where: str) -> None:
    """Raise :class:`RoleExpressionError` unless every value STORED in ``tbox``'s
    object role box is usable: a role name (an inverse role only on either side
    of a role inclusion), a pair where a pair is stored, a chain that is a
    sequence of at least two role names.

    The ONE validation of a stored role box, called by BOTH routes — the
    tableau's shared guard (:func:`_reject_role_box`) and the FOL image
    (:func:`~unicode_logic_kit.dl.translate.rbox_to_fol`) — so that a ``TBox``
    built through the dataclass constructor, or mutated in place, is refused
    the same way by both. Until 0.30.0 only the FOL route had this second line
    of defence behind the builders, and the tableau ANSWERED, silently, for a
    role inclusion between two tuples that the FOL route rejected — the two
    routes disagreeing about whether there was a question.
    """
    for entry in tbox.role_inclusions:
        sub, sup = _stored_pair(entry, "SubObjectPropertyOf", where)
        _check_role_name(sub, where=where, allow_inverse=True,
                         kind="SubObjectPropertyOf")
        _check_role_name(sup, where=where, allow_inverse=True,
                         kind="SubObjectPropertyOf")
    for field_name, kind in _NAME_SET_FIELDS:
        for role in sorted(getattr(tbox, field_name), key=repr):
            _check_role_name(role, where=where, kind=kind)
    for field_name, kind in (("inverse_role_pairs", "InverseObjectProperties"),
                             ("disjoint_role_pairs", "DisjointObjectProperties")):
        for entry in getattr(tbox, field_name):
            for role in _stored_pair(entry, kind, where):
                _check_role_name(role, where=where, kind=kind)
    for chain_entry in tbox.role_chains:
        stored_chain, super_role = _stored_pair(chain_entry, "ObjectPropertyChain", where)
        chain = _check_chain_shape(stored_chain, where=where, stored=True)
        if len(chain) < 2:
            raise RoleExpressionError(
                f"{where}: a stored property chain needs at least 2 roles, "
                f"got {len(chain)} ({tuple(chain)!r}). OWL 2's grammar is "
                f"ObjectPropertyChain(OPE OPE+); a single role on the left is "
                f"an ordinary role inclusion (dl.TBox.add_role_inclusion).")
        for role in chain:
            _check_role_name(role, where=where, kind="ObjectPropertyChain")
        _check_role_name(super_role, where=where, kind="ObjectPropertyChain")
    for field_name, kind in (("role_domains", "ObjectPropertyDomain"),
                             ("role_ranges", "ObjectPropertyRange")):
        for entry in getattr(tbox, field_name):
            role, _filler = _stored_pair(entry, kind, where)
            _check_role_name(role, where=where, kind=kind)


def _validate_data_box(tbox: "TBox", *, where: str) -> None:
    """:func:`_validate_role_box`'s counterpart for the DATA box: every stored
    data property name is a plain name (a data property has no inverse), and
    every stored pair is a pair."""
    for field_name, kind in (("data_property_inclusions", "SubDataPropertyOf"),
                             ("disjoint_data_property_pairs",
                              "DisjointDataProperties")):
        for entry in getattr(tbox, field_name):
            for prop in _stored_pair(entry, kind, where):
                _check_role_name(prop, where=where, kind=kind)
    for prop in sorted(tbox.functional_data_properties, key=repr):
        _check_role_name(prop, where=where, kind="FunctionalDataProperty")
    for field_name, kind in (("data_property_domains", "DataPropertyDomain"),
                             ("data_property_ranges", "DataPropertyRange")):
        for entry in getattr(tbox, field_name):
            prop, _filler = _stored_pair(entry, kind, where)
            _check_role_name(prop, where=where, kind=kind)
    _check_datatype_definitions(tbox.datatype_definitions, where=where)


def _definition_references(datarange: DataRange, defined: Iterable[str]) -> List[str]:
    """The DEFINED datatype names ``datarange`` mentions, in order, once each."""
    seen: List[str] = []
    for name in datarange_datatypes(datarange):
        if name in defined and name not in seen:
            seen.append(name)
    return seen


def _definition_cycle(start: str, definitions: Dict[str, DataRange]) -> Optional[List[str]]:
    """A path ``start → … → start`` through the DEFINED datatype names, or
    ``None``: the cycle OWL 2 (Structural Specification §9.4) forbids a set of
    datatype definitions to have, found by a depth-first walk from ``start``."""
    path: List[str] = [start]
    visiting: Set[str] = set()

    def walk(name: str) -> Optional[List[str]]:
        visiting.add(name)
        for ref in _definition_references(definitions[name], definitions):
            if ref == start:
                return path + [start]
            if ref in visiting:
                continue
            path.append(ref)
            found = walk(ref)
            if found is not None:
                return found
            path.pop()
        return None

    return walk(start)


def _duplicate_definition_error(name: str, first: DataRange, second: DataRange,
                                where: str) -> "UnsupportedDatatypeError":
    return UnsupportedDatatypeError(
        f"{where}: the datatype {name!r} has two DatatypeDefinitions "
        f"({first.to_unicode()} and {second.to_unicode()}). OWL 2 (Structural "
        f"Specification §9.4) gives a datatype ONE definition, and the image of "
        f"two would be two biconditionals that force the two data ranges to be "
        f"equal — a constraint nobody wrote. Merge them into one data range, or "
        f"name one of the datatypes differently.")


def _cyclic_definition_error(path: List[str], where: str) -> "UnsupportedDatatypeError":
    return UnsupportedDatatypeError(
        f"{where}: the datatype definitions are cyclic ({' → '.join(path)}), "
        f"and OWL 2 (Structural Specification §9.4) requires them to be "
        f"acyclic: a datatype may not be defined in terms of itself, directly "
        f"or through other defined datatypes. The image of a cycle "
        f"(∀v (P(v) ↔ Q(v)) with ∀v (Q(v) ↔ OwlData(v) ∧ ¬P(v))) has no model "
        f"once the data domain is non-empty, so it would make the knowledge "
        f"base inconsistent.")


def _check_datatype_definitions(entries, *, where: str) -> None:
    """The shared validation of the stored ``DatatypeDefinition`` entries — the
    one every route runs on a TBox that may have been assembled by hand (the
    builder :meth:`TBox.add_datatype_definition` runs the same three tests on
    the entry it is handed): the name is not a built-in datatype, no name has
    two DIFFERENT definitions (an identical repeat is the same axiom), and the
    definitions are acyclic. Raises :class:`UnsupportedDatatypeError`."""
    definitions: Dict[str, DataRange] = {}
    for entry in entries:
        name, datarange = _stored_pair(entry, "DatatypeDefinition", where)
        if not isinstance(name, str) or not isinstance(datarange, DataRange):
            raise UnsupportedDatatypeError(
                f"{where}: a stored DatatypeDefinition is (datatype name, data "
                f"range), got {entry!r}. Build the TBox with "
                f"TBox.add_datatype_definition instead of assembling its list "
                f"by hand.")
        name = canonical_datatype_name(name)
        if name in BUILTIN_DATATYPES:
            raise UnsupportedDatatypeError(
                f"{where}: {name!r} is a built-in datatype of the OWL 2 "
                f"datatype map, and OWL 2 does not allow redefining one. Name "
                f"the new datatype something else.")
        if name in definitions and definitions[name] != datarange:
            raise _duplicate_definition_error(name, definitions[name], datarange, where)
        definitions[name] = datarange
    for name in definitions:
        cycle = _definition_cycle(name, definitions)
        if cycle is not None:
            raise _cyclic_definition_error(cycle, where)


#: A role in a role-box position: a plain role name, or (only where the module
#: docstring says so — on either side of a role inclusion) an inverse role.
RoleExpr = Union[str, InverseRole]


def _as_datarange(value, where: str) -> DataRange:
    """``value`` as a :class:`~unicode_logic_kit.dl.datatypes.DataRange`: a data
    range is returned as is and a ``str`` is the datatype of that name; anything
    else is a caller mistake, named at the call that made it."""
    if isinstance(value, DataRange):
        return value
    if isinstance(value, str):
        return Datatype(value)
    raise TypeError(
        f"{where}: expected a data range (dl.Datatype, dl.DatatypeRestriction, "
        f"dl.DataOneOf, …) or a datatype name (str), got "
        f"{type(value).__name__} {value!r}.")


@dataclass
class TBox:
    """A general TBox with an RBox on top: concept inclusions ``C ⊑ D`` and
    equivalences ``C ≡ D`` (the concept-level TBox), plus the whole OWL 2 object
    property box — role inclusions ``r ⊑ s``, transitivity declarations
    ``Trans(r)``, inverse-property pairs, property chains, role disjointness and
    the six remaining role characteristics.

    See "Role hierarchies and transitive roles (RBox)" and "The rest of the OWL 2
    role box" in the module docstring for which of them this tableau decides,
    which it refuses by name, and the soundness/termination argument for each.
    Every kind is accepted here regardless: a ``TBox`` is what a parser fills
    from a file, so a builder that refused a KIND could not hold an ontology the
    kit is supposed to report on (the refusal is at query time, from
    :func:`_reject_unsupported`). Malformed ARGUMENTS are a different matter and
    are refused on the spot — see :class:`RoleExpressionError`.
    """

    inclusions: List[Tuple[Concept, Concept]] = field(default_factory=list)
    role_inclusions: List[Tuple[RoleExpr, RoleExpr]] = field(default_factory=list)
    transitive_roles: Set[str] = field(default_factory=set)
    inverse_role_pairs: List[Tuple[str, str]] = field(default_factory=list)
    role_chains: List[Tuple[Tuple[str, ...], str]] = field(default_factory=list)
    disjoint_role_pairs: List[Tuple[str, str]] = field(default_factory=list)
    symmetric_roles: Set[str] = field(default_factory=set)
    asymmetric_roles: Set[str] = field(default_factory=set)
    reflexive_roles: Set[str] = field(default_factory=set)
    irreflexive_roles: Set[str] = field(default_factory=set)
    functional_roles: Set[str] = field(default_factory=set)
    inverse_functional_roles: Set[str] = field(default_factory=set)
    role_domains: List[Tuple[str, Concept]] = field(default_factory=list)
    role_ranges: List[Tuple[str, Concept]] = field(default_factory=list)
    # The data half of the property box (see "The data layer" in the module
    # docstring): stored, and rendered by the FOL image, but REFUSED by the
    # tableau, which has no data domain.
    data_property_inclusions: List[Tuple[str, str]] = field(default_factory=list)
    disjoint_data_property_pairs: List[Tuple[str, str]] = field(default_factory=list)
    functional_data_properties: Set[str] = field(default_factory=set)
    data_property_domains: List[Tuple[str, Concept]] = field(default_factory=list)
    data_property_ranges: List[Tuple[str, DataRange]] = field(default_factory=list)
    datatype_definitions: List[Tuple[str, DataRange]] = field(default_factory=list)

    def add(self, sub: Concept, sup: Concept) -> "TBox":
        """Add a general concept inclusion ``sub ⊑ sup`` and return self (chainable)."""
        self.inclusions.append((sub, sup))
        return self

    def add_equivalence(self, c: Concept, d: Concept) -> "TBox":
        """Add an equivalence ``c ≡ d`` (as the two inclusions ``c ⊑ d``, ``d ⊑ c``)."""
        self.inclusions.append((c, d))
        self.inclusions.append((d, c))
        return self

    def add_role_inclusion(self, sub_role: RoleExpr, super_role: RoleExpr) -> "TBox":
        """Add a role inclusion ``sub_role ⊑ super_role`` and return self (chainable).

        Every ``sub_role``-edge is then also treated as a ``super_role``-edge by the
        tableau's ∀-rule (RBox rule "H"; see the module docstring).

        Either side may be an :class:`~unicode_logic_kit.dl.concepts.InverseRole`:
        ``r ⊑ s⁻`` is a genuinely different axiom from ``r ⊑ s``, and
        :func:`~unicode_logic_kit.dl.translate.rbox_to_fol` renders it correctly
        (``∀x ∀y (r(x, y) → s(y, x))``). The TABLEAU refuses such a role box by
        name, as the **I** of SHIQ — see the module docstring.

        Raises:
            RoleExpressionError: a side is not a role name or inverse role, or
                is an OWL 2 built-in property name.
        """
        _check_role_name(sub_role, where="dl.TBox.add_role_inclusion",
                         allow_inverse=True)
        _check_role_name(super_role, where="dl.TBox.add_role_inclusion",
                         allow_inverse=True)
        self.role_inclusions.append((sub_role, super_role))
        return self

    def add_role_chain(self, chain: Sequence[str], super_role: str) -> "TBox":
        """Add the complex role inclusion ``P1 ∘ … ∘ Pn ⊑ super_role``
        (``SubObjectPropertyOf(ObjectPropertyChain(P1 … Pn) Q)``), ``n ≥ 2``, and
        return self (chainable).

        ``chain`` is stored as a ``tuple``. The FOL image is
        ``∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z))`` for ``n = 2``, with further
        positions taking minted variables; the tableau refuses it by name (the
        **R** of SROIQ — see the module docstring, which also records the rule
        that would decide it and the regularity problem that defers it).

        Raises:
            RoleExpressionError: ``chain`` is not an ordered collection of role
                names (a plain ``str`` or ``bytes`` is refused: it would be
                split into its CHARACTERS, ``"rs"`` into the roles ``r`` and
                ``s``; a set-like collection has no order; any other iterable,
                such as a generator, is read in order), has fewer than two
                roles (a length-1 "chain" is an ordinary role inclusion — the
                message says so), or a role is not a usable role name.
        """
        chain = _check_chain_shape(chain, where="dl.TBox.add_role_chain")
        if len(chain) < 2:
            raise RoleExpressionError(
                f"dl.TBox.add_role_chain: a property chain needs at least 2 "
                f"roles, got {len(chain)} ({chain!r}). OWL 2's own grammar is "
                f"ObjectPropertyChain(OPE OPE+); a single role on the left is "
                f"the ordinary role inclusion dl.TBox.add_role_inclusion"
                + (f"({chain[0]!r}, {super_role!r})" if chain else "(sub, sup)")
                + ", which this tableau decides.")
        for role in chain:
            _check_role_name(role, where="dl.TBox.add_role_chain")
        _check_role_name(super_role, where="dl.TBox.add_role_chain")
        self.role_chains.append((chain, super_role))
        return self

    def add_equivalent_roles(self, *roles: str) -> "TBox":
        """Declare ``roles`` pairwise equivalent
        (``EquivalentObjectProperties(P1 … Pk)``, ``k ≥ 2``) and return self.

        Stored as the role INCLUSIONS it abbreviates — both ways round for each
        CONSECUTIVE pair — exactly as :meth:`add_equivalence` stores a concept
        equivalence as the pair of inclusions. Consecutive suffices because
        ``⊑`` is transitive, so ``P1 ≡ P2 ≡ P3`` already entails ``P1 ≡ P3``;
        contrast :meth:`add_disjoint_roles`, where disjointness has no such
        closure and ALL pairs are needed. So there is no new field and nothing
        new in the tableau: ``_RBox`` already treats a ⊑-cycle as one synonym
        class.

        Raises:
            RoleExpressionError: fewer than two roles, or a role is not a usable
                role name.
        """
        if len(roles) < 2:
            raise RoleExpressionError(
                f"dl.TBox.add_equivalent_roles: expected at least 2 roles, got "
                f"{len(roles)} ({roles!r}) — OWL 2's own grammar is "
                f"EquivalentObjectProperties(OPE OPE+), and one role is "
                f"equivalent to itself in every interpretation (nothing to add).")
        for role in roles:
            _check_role_name(role, where="dl.TBox.add_equivalent_roles")
        for left, right in zip(roles, roles[1:]):
            self.add_role_inclusion(left, right)
            self.add_role_inclusion(right, left)
        return self

    def add_inverse_roles(self, p: str, q: str) -> "TBox":
        """Declare ``p`` and ``q`` mutually inverse
        (``InverseObjectProperties(p q)``, W3C arity exactly 2) and return self.

        The FOL image is the single biconditional
        ``∀x ∀y (p(x, y) ↔ q(y, x))`` — the axiom is an EQUALITY of relations,
        not two separate inclusions. The tableau refuses it by name (the **I**
        of SHIQ).

        Raises:
            RoleExpressionError: a side is not a usable role name.
        """
        _check_role_name(p, where="dl.TBox.add_inverse_roles")
        _check_role_name(q, where="dl.TBox.add_inverse_roles")
        self.inverse_role_pairs.append((p, q))
        return self

    def add_disjoint_roles(self, *roles: str) -> "TBox":
        """Declare ``roles`` pairwise disjoint
        (``DisjointObjectProperties(P1 … Pk)``, ``k ≥ 2``) and return self.

        Expanded at BUILD time into every unordered pair, each stored with its
        two names SORTED (so ``(r, s)`` and ``(s, r)`` are one entry and ``TBox``
        equality is spelling-independent), exactly as ``DisjointClasses`` and
        ``DifferentIndividuals`` are expanded by the parser. ALL ``C(k, 2)``
        pairs, never a consecutive chain: disjointness has no transitive
        shortcut — ``P1 ∩ P2 = ∅`` and ``P2 ∩ P3 = ∅`` say nothing about
        ``P1 ∩ P3`` — so ``k - 1`` axioms would be a STRICTLY WEAKER theory.
        A repeated name gives the degenerate pair ``(P, P)``, i.e.
        ``∀x ∀y ¬P(x, y)`` ("P is empty"), which is kept rather than dropped.

        Raises:
            RoleExpressionError: fewer than two roles, or a role is not a usable
                role name.
        """
        if len(roles) < 2:
            raise RoleExpressionError(
                f"dl.TBox.add_disjoint_roles: expected at least 2 roles, got "
                f"{len(roles)} ({roles!r}) — OWL 2's own grammar is "
                f"DisjointObjectProperties(OPE OPE+). To say a single role is "
                f"EMPTY, pass it twice (the degenerate pair (P, P) is "
                f"∀x ∀y ¬P(x, y)) or write the concept inclusion ⊤ ⊑ ∀P.⊥.")
        for role in roles:
            _check_role_name(role, where="dl.TBox.add_disjoint_roles")
        for i, left in enumerate(roles):
            for right in roles[i + 1:]:
                first, second = sorted((left, right))
                pair = (first, second)
                if pair not in self.disjoint_role_pairs:
                    self.disjoint_role_pairs.append(pair)
        return self

    def add_transitive_role(self, role: str) -> "TBox":
        """Declare ``role`` transitive (``Trans(role)``) and return self (chainable).

        The tableau's ∀+-rule then propagates a ``∀role.C`` restriction along the
        whole chain of ``role``-successors, not just the immediate one (RBox rule
        "S"; see the module docstring).

        Raises:
            RoleExpressionError: ``role`` is not a usable role name (an
                ``InverseRole`` is refused here, naming the plain spelling:
                ``Trans(r⁻)`` is logically ``Trans(r)``).
        """
        _check_role_name(role, where="dl.TBox.add_transitive_role")
        self.transitive_roles.add(role)
        return self

    def add_symmetric_role(self, role: str) -> "TBox":
        """Declare ``role`` symmetric (``SymmetricObjectProperty``): image
        ``∀x ∀y (role(x, y) → role(y, x))``. Refused by the tableau by name —
        symmetry IS the inverse-role inclusion ``P ⊑ P⁻`` (see the module
        docstring).
        """
        _check_role_name(role, where="dl.TBox.add_symmetric_role")
        self.symmetric_roles.add(role)
        return self

    def add_asymmetric_role(self, role: str) -> "TBox":
        """Declare ``role`` asymmetric (``AsymmetricObjectProperty``): image
        ``∀x ∀y (role(x, y) → ¬role(y, x))``, which also ENTAILS irreflexivity.
        Decided by the tableau, as one clash condition (see the module
        docstring); OWL 2 §11 requires ``role`` SIMPLE and
        :func:`_check_simple_role_box` enforces it.
        """
        _check_role_name(role, where="dl.TBox.add_asymmetric_role")
        self.asymmetric_roles.add(role)
        return self

    def add_reflexive_role(self, role: str) -> "TBox":
        """Declare ``role`` reflexive (``ReflexiveObjectProperty``): image
        ``∀x role(x, x)``. Refused by the tableau by name — a reflexive role
        makes every individual its own neighbour, and counting a node among its
        own neighbours lets the ≤-rule merge a node with its own successor (see
        the module docstring).
        """
        _check_role_name(role, where="dl.TBox.add_reflexive_role")
        self.reflexive_roles.add(role)
        return self

    def add_irreflexive_role(self, role: str) -> "TBox":
        """Declare ``role`` irreflexive (``IrreflexiveObjectProperty``): image
        ``∀x ¬role(x, x)`` — ONE variable, not two. Decided by the tableau, as
        one clash condition (see the module docstring); OWL 2 §11 requires
        ``role`` SIMPLE.
        """
        _check_role_name(role, where="dl.TBox.add_irreflexive_role")
        self.irreflexive_roles.add(role)
        return self

    def add_functional_role(self, role: str) -> "TBox":
        """Declare ``role`` functional (``FunctionalObjectProperty``): image
        ``∀x ∀y ∀z (role(x, y) ∧ role(x, z) → y = z)``.

        Decided by the tableau WITHOUT a new rule: this is exactly the GCI
        ``⊤ ⊑ ≤1 role.⊤``, internalised in ``_new_branch`` (see the module
        docstring). OWL 2 §11 requires ``role`` SIMPLE.
        """
        _check_role_name(role, where="dl.TBox.add_functional_role")
        self.functional_roles.add(role)
        return self

    def add_inverse_functional_role(self, role: str) -> "TBox":
        """Declare ``role`` inverse-functional
        (``InverseFunctionalObjectProperty``): image
        ``∀x ∀y ∀z (role(y, x) ∧ role(z, x) → y = z)`` — the argument order of
        the two body atoms is the whole content of the axiom.

        Refused by the tableau by name: it is ``≤1 role⁻.⊤``, so it counts
        role-PREDECESSORS and needs inverse roles. For functionality on ``role``
        itself use :meth:`add_functional_role`, which the tableau does decide.
        """
        _check_role_name(role, where="dl.TBox.add_inverse_functional_role")
        self.inverse_functional_roles.add(role)
        return self

    def add_role_domain(self, role: str, concept: Concept) -> "TBox":
        """Add the domain axiom ``ObjectPropertyDomain(role concept)`` — "anything
        with a ``role``-successor is a ``concept``" — and return self (chainable).

        Stored NATIVELY, beside the rest of the role box, rather than desugared
        into the equivalent GCI ``∃role.⊤ ⊑ concept``. Three reasons, all of
        which the requesting OEO project hit:

        * the FOL image must be the direct-semantics sentence
          ``∀x ∀y (role(x, y) → π(concept, x))``, and no GCI can produce it —
          :func:`~unicode_logic_kit.dl.translate.subsumption_to_fol` would emit
          ``∀x (∃x0 (role(x, x0) ∧ x0 = x0) → π(concept, x))``, carrying a
          tautological ``x0 = x0`` filler the reader has to decode;
        * :func:`~unicode_logic_kit.dl.owl_functional.to_owl_functional` must
          round-trip the axiom back to ``ObjectPropertyDomain(…)``, and a
          desugared GCI cannot be re-detected reliably (the same reason that
          module does not re-fold ``DisjointClasses``);
        * it is an axiom ABOUT A ROLE, like a role inclusion or a transitivity
          declaration, so it belongs in the role box — which also puts its FOL
          image in :attr:`~unicode_logic_kit.dl.translate.KnowledgeBaseFOL.axioms`
          (a premise) rather than inside the knowledge-base formula.

        The TABLEAU, by contrast, does treat it as the GCI it is equivalent to:
        ``_new_branch`` internalises it as ``∀role.⊥ ⊔ concept``, so no new
        completion rule and no change to the termination argument (see
        "Domain and range axioms" in the module docstring).

        Raises:
            RoleExpressionError: ``role`` is not a usable role name.
        """
        _check_role_name(role, where="dl.TBox.add_role_domain")
        self.role_domains.append((role, concept))
        return self

    def add_role_range(self, role: str, concept: Concept) -> "TBox":
        """Add the range axiom ``ObjectPropertyRange(role concept)`` — "every
        ``role``-successor is a ``concept``" — and return self (chainable).

        Stored natively for the same three reasons as :meth:`add_role_domain`;
        its FOL image is ``∀x ∀y (role(x, y) → π(concept, y))``, the filler
        translated at the SECOND variable, which is the only difference.

        Raises:
            RoleExpressionError: ``role`` is not a usable role name.
        """
        _check_role_name(role, where="dl.TBox.add_role_range")
        self.role_ranges.append((role, concept))
        return self

    # -- the data half of the property box ------------------------------- #

    def add_data_property_inclusion(self, sub_prop: str, super_prop: str) -> "TBox":
        """Add ``SubDataPropertyOf(sub_prop super_prop)`` and return self.

        FOL image ``∀x ∀v (sub_prop(x, v) → super_prop(x, v))``. Kept apart from
        :attr:`role_inclusions`, not merged into them: a data property and an
        object role of the same name are different things in OWL 2, and one
        shared list would let either be read as the other. Refused by the
        tableau (no data domain).

        Raises:
            RoleExpressionError: a side is not a usable property name (an
                inverse role is refused — a data property has no inverse — and
                so is an OWL 2 built-in property name).
        """
        _check_role_name(sub_prop, where="dl.TBox.add_data_property_inclusion")
        _check_role_name(super_prop, where="dl.TBox.add_data_property_inclusion")
        self.data_property_inclusions.append((sub_prop, super_prop))
        return self

    def add_equivalent_data_properties(self, *props: str) -> "TBox":
        """Declare ``props`` pairwise equivalent
        (``EquivalentDataProperties(P1 … Pk)``, ``k ≥ 2``) and return self.

        Stored as the data property inclusions it abbreviates — both ways round
        for each CONSECUTIVE pair, which suffices because ⊑ is transitive — so
        there is no field and no table row of its own, exactly like
        :meth:`add_equivalent_roles`.

        Raises:
            RoleExpressionError: fewer than two properties, or a name is not usable.
        """
        if len(props) < 2:
            raise RoleExpressionError(
                f"dl.TBox.add_equivalent_data_properties: expected at least 2 "
                f"properties, got {len(props)} ({props!r}) — OWL 2's own grammar "
                f"is EquivalentDataProperties(DPE DPE+).")
        for prop in props:
            _check_role_name(prop, where="dl.TBox.add_equivalent_data_properties")
        for left, right in zip(props, props[1:]):
            self.add_data_property_inclusion(left, right)
            self.add_data_property_inclusion(right, left)
        return self

    def add_disjoint_data_properties(self, *props: str) -> "TBox":
        """Declare ``props`` pairwise disjoint
        (``DisjointDataProperties(P1 … Pk)``, ``k ≥ 2``) and return self.

        Expanded at BUILD time into every unordered pair, each stored sorted —
        ALL ``C(k, 2)`` pairs, never a consecutive chain, for the reason
        :meth:`add_disjoint_roles` gives. Image ``∀x ∀v ¬(p(x, v) ∧ q(x, v))``.

        Raises:
            RoleExpressionError: fewer than two properties, or a name is not usable.
        """
        if len(props) < 2:
            raise RoleExpressionError(
                f"dl.TBox.add_disjoint_data_properties: expected at least 2 "
                f"properties, got {len(props)} ({props!r}) — OWL 2's own grammar "
                f"is DisjointDataProperties(DPE DPE+).")
        for prop in props:
            _check_role_name(prop, where="dl.TBox.add_disjoint_data_properties")
        for i, left in enumerate(props):
            for right in props[i + 1:]:
                first, second = sorted((left, right))
                pair = (first, second)
                if pair not in self.disjoint_data_property_pairs:
                    self.disjoint_data_property_pairs.append(pair)
        return self

    def add_functional_data_property(self, prop: str) -> "TBox":
        """Declare ``prop`` functional (``FunctionalDataProperty``): image
        ``∀x ∀v ∀w (prop(x, v) ∧ prop(x, w) → v = w)``. Refused by the tableau.

        Raises:
            RoleExpressionError: ``prop`` is not a usable property name.
        """
        _check_role_name(prop, where="dl.TBox.add_functional_data_property")
        self.functional_data_properties.add(prop)
        return self

    def add_data_property_domain(self, prop: str, concept: Concept) -> "TBox":
        """Add ``DataPropertyDomain(prop concept)`` — "anything with a
        ``prop``-value is a ``concept``" — and return self.

        Stored NATIVELY, for the reasons :meth:`add_role_domain` gives (the
        image must be the direct sentence ``∀x ∀v (prop(x, v) → π(concept, x))``,
        and the writer must round-trip the axiom). Refused by the tableau.

        Raises:
            RoleExpressionError: ``prop`` is not a usable property name.
        """
        _check_role_name(prop, where="dl.TBox.add_data_property_domain")
        self.data_property_domains.append((prop, concept))
        return self

    def add_data_property_range(self, prop: str, datarange: Union[DataRange, str]) -> "TBox":
        """Add ``DataPropertyRange(prop datarange)`` — "every ``prop``-value is in
        ``datarange``" — and return self. A bare string is a datatype name.

        Image ``∀x ∀v (prop(x, v) → δ(datarange, v))``. NOT rewritten as the GCI
        ``⊤ ⊑ ∀prop.datarange``, whose image would carry the ``x = x`` filler of
        an ``⊤`` antecedent. Refused by the tableau.

        Raises:
            RoleExpressionError: ``prop`` is not a usable property name.
            TypeError: ``datarange`` is not a data range or a datatype name.
        """
        _check_role_name(prop, where="dl.TBox.add_data_property_range")
        self.data_property_ranges.append(
            (prop, _as_datarange(datarange, "dl.TBox.add_data_property_range")))
        return self

    def add_datatype_definition(self, name: str,
                                datarange: Union[DataRange, str]) -> "TBox":
        """Add ``DatatypeDefinition(name datarange)`` — the named datatype IS the
        data range — and return self.

        Image ``∀v (name(v) ↔ δ(datarange, v))``: a definition, so a ``↔`` and
        not a pair of inclusions read one way. The datatype keeps its own guard
        predicate in the image rather than being inlined, so the image stays
        the size of the ontology. Refused by the tableau.

        Raises:
            ~unicode_logic_kit.dl.datatypes.UnsupportedDatatypeError:
                ``name`` is a built-in datatype (OWL 2
                forbids redefining one), occurs in its own definition, closes a
                cycle through the definitions already stored (``P ≡ Q`` then
                ``Q ≡ ¬P``), or already has a DIFFERENT definition (OWL 2 §9.4:
                definitions are acyclic and a datatype has one; an identical
                repeat is the same axiom and is accepted). A hand-built
                ``TBox`` is held to the same three rules by the shared
                validation every route runs.
            TypeError: ``datarange`` is not a data range or a datatype name.
        """
        name = canonical_datatype_name(name)
        datarange = _as_datarange(datarange, "dl.TBox.add_datatype_definition")
        if name in BUILTIN_DATATYPES:
            raise UnsupportedDatatypeError(
                f"dl.TBox.add_datatype_definition: {name!r} is a built-in "
                f"datatype of the OWL 2 datatype map, and OWL 2 does not allow "
                f"redefining one. Name the new datatype something else.")
        if name in datarange_datatypes(datarange):
            raise UnsupportedDatatypeError(
                f"dl.TBox.add_datatype_definition: {name!r} occurs in its own "
                f"definition ({datarange.to_unicode()}), and OWL 2 requires "
                f"datatype definitions to be acyclic.")
        where = "dl.TBox.add_datatype_definition"
        stored = {canonical_datatype_name(other): other_range
                  for other, other_range in self.datatype_definitions}
        if name in stored and stored[name] != datarange:
            raise _duplicate_definition_error(name, stored[name], datarange, where)
        stored[name] = datarange
        cycle = _definition_cycle(name, stored)
        if cycle is not None:
            raise _cyclic_definition_error(cycle, where)
        self.datatype_definitions.append((name, datarange))
        return self

    def internalized(self) -> List[Concept]:
        """The concepts ``nnf(¬C ⊔ D)`` every individual must satisfy (one per GCI).

        Role-box axioms are NOT part of this list — they are not concepts forced
        on every individual, but a separate role constraint the tableau consults
        through ``_RBox`` (see ``_new_branch``), so they only ever change how
        existing labels propagate across edges, or which edge patterns clash,
        never what gets internalised onto a label up front.

        ``FunctionalObjectProperty`` is the one that LOOKS like an exception and
        is not: it is the GCI ``⊤ ⊑ ≤1 P.⊤``, and the concept it contributes is
        added in ``_new_branch`` rather than here, so this method stays exactly
        the GCI list (``tests/test_dl_rbox.py::test_internalized_unaffected_by_rbox``
        is that guard, and it is worth keeping: ``internalized()`` is documented
        as the image of ``inclusions`` and callers read it that way).
        ``ObjectPropertyDomain``/``ObjectPropertyRange`` are the same case and
        are internalised in the same place, for the same reason.
        """
        return [nnf(Or(Not(sub), sup)) for sub, sup in self.inclusions]

    def has_side_axioms(self) -> bool:
        """True iff this TBox carries an axiom that is NOT part of the
        concept-inclusion image — any ``part == "side"`` row of
        :data:`_AXIOM_KINDS`: a role-box axiom (role inclusion, transitivity,
        disjointness, the other characteristics, inverse pairs, chains, domain
        and range) or a data-box axiom.

        DERIVED from :data:`_AXIOM_KINDS`' ``part`` column rather than written
        out over whichever fields happened to exist, which is what
        :func:`~unicode_logic_kit.dl.translate.tbox_to_fol` reads to decide
        whether rendering only the concept inclusions would silently hand the
        caller a WEAKER theory than the TBox (see
        :class:`~unicode_logic_kit.dl.translate.RoleBoxOmittedError`). A new
        axiom kind is covered by adding its table row, and nothing else.
        """
        return any(getattr(self, field)
                   for field in _holder_fields("tbox", part="side"))


def _check_literal(value, where: str) -> None:
    if not isinstance(value, Literal):
        raise TypeError(
            f"{where}: expected a dl.Literal (e.g. dl.Literal('400', 'xsd:integer')), "
            f"got {type(value).__name__} {value!r}.")


@dataclass
class ABox:
    """An ABox: concept assertions ``a : C``, role assertions ``(a, b) : r``, and
    (for **Q**, since there is no unique name assumption — see "Qualified number
    restrictions" in :mod:`unicode_logic_kit.dl.tableau`'s module docstring)
    ``a ≠ b`` distinctness assertions.
    """

    concept_assertions: List[Tuple[str, Concept]] = field(default_factory=list)
    role_assertions: List[Tuple[str, str, str]] = field(default_factory=list)
    distinct_assertions: List[Tuple[str, str]] = field(default_factory=list)
    same_assertions: List[Tuple[str, str]] = field(default_factory=list)
    negative_role_assertions: List[Tuple[str, str, str]] = field(default_factory=list)
    # Data assertions: stored and rendered by the FOL image, REFUSED by the
    # tableau (see "The data layer" in the module docstring).
    data_assertions: List[Tuple[str, str, Literal]] = field(default_factory=list)
    negative_data_assertions: List[Tuple[str, str, Literal]] = field(default_factory=list)

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

        ``assert_distinct(a, a)`` is ACCEPTED and makes the ABox inconsistent, the
        way ``DifferentIndividuals(a a)`` does in OWL and ``a ≠ a`` does in the FOL
        rendering :func:`~unicode_logic_kit.dl.translate.abox_to_fol` produces. It is
        not refused here, because an ABox assembled from a real ontology may well
        contain it and the honest answer to "is this knowledge base consistent?" is
        no — not an exception from the constructor.
        """
        self.distinct_assertions.append((a, b))
        return self

    def assert_same(self, a: str, b: str) -> "ABox":
        """Add a same-individual assertion ``a = b`` (``SameIndividual(a b)``,
        chainable).

        The mirror of :meth:`assert_distinct`: there is no unique name
        assumption here (see the module docstring), so two names MAY denote one
        element — this is how to say that they DO. The tableau decides it by
        genuine node MERGING, closed under the equivalence the assertions
        generate, before any completion rule runs (see "Same-individual
        assertions" in the module docstring); the FOL image is the atom
        ``a = b``.

        ``assert_same(a, a)`` is ACCEPTED and is a no-op — ``a = a`` holds in
        every model — the way ``assert_distinct(a, a)`` is accepted and makes
        the ABox inconsistent: an ABox assembled from a real ontology may
        contain either, and the honest answer is the consistency verdict, not
        an exception from the constructor.
        """
        self.same_assertions.append((a, b))
        return self

    def assert_negative_role(self, a: str, b: str, role: str) -> "ABox":
        """Add a negative role assertion ``¬role(a, b)``
        (``NegativeObjectPropertyAssertion(role a b)``, chainable).

        Argument order matches :meth:`assert_role`'s — the two individuals
        first, the role last. A ground FACT about two individuals, so it is
        stored natively rather than as the concept assertion
        ``a : ¬∃role.{b}``: its FOL image must be the ground literal
        ``¬role(a, b)``, and
        :func:`~unicode_logic_kit.dl.owl_functional.to_owl_functional` must
        round-trip the axiom back to itself.

        The tableau decides it by a clash condition over the branch's edges,
        closed under the role hierarchy, and REFUSES by name the one fragment
        it cannot see: a negative assertion on a NON-SIMPLE role (see
        "Negative role assertions" in the module docstring).
        """
        self.negative_role_assertions.append((a, b, role))
        return self

    def assert_data(self, individual: str, prop: str, value: Literal) -> "ABox":
        """Add ``DataPropertyAssertion(prop individual value)`` — the ground
        atom ``prop(individual, t)`` for the literal's term ``t`` — and return
        self (chainable).

        Individual first, to match :meth:`assert_concept`, and not OWL's
        property-first order. Only the individual is an INDIVIDUAL
        (:data:`_AXIOM_KINDS`' ``individual_positions``): the literal's term is
        a data value and is never reported in ``KnowledgeBaseFOL.individuals``.
        Refused by the tableau (no data domain).

        Raises:
            TypeError: ``value`` is not a :class:`~unicode_logic_kit.dl.datatypes.Literal`.
        """
        _check_literal(value, "dl.ABox.assert_data")
        self.data_assertions.append((individual, prop, value))
        return self

    def assert_negative_data(self, individual: str, prop: str, value: Literal) -> "ABox":
        """Add ``NegativeDataPropertyAssertion(prop individual value)`` — the
        ground literal ``¬prop(individual, t)`` — and return self (chainable).
        Same argument order as :meth:`assert_data`. Refused by the tableau.

        Raises:
            TypeError: ``value`` is not a :class:`~unicode_logic_kit.dl.datatypes.Literal`.
        """
        _check_literal(value, "dl.ABox.assert_negative_data")
        self.negative_data_assertions.append((individual, prop, value))
        return self

    def copy(self) -> "ABox":
        """A shallow copy with FRESH lists: same assertions, independent
        storage, so mutating the copy's lists (every ``assert_*`` mutates in
        place) cannot reach back into the original.

        ONE place, so an ABox field added later is carried over by
        construction. :func:`instance_check` built its probe ABox field by
        field until 0.30.0, which meant every assertion kind added to
        :class:`ABox` had to be remembered there as well — and forgetting it
        was SILENT: ``instance_check``/``instance_retrieval``/``realize``/
        ``realize_all`` would all answer about a strictly WEAKER knowledge base
        than :func:`abox_consistent` sees on the same ABox, which is the two-
        routes-disagree bug in its purest form.

        ``dataclasses.replace`` is not used because it SHARES the lists it does
        not replace, which is exactly what the explicit ``list(...)`` calls
        here exist to avoid.
        """
        return ABox(**{f.name: list(getattr(self, f.name))
                       for f in dataclass_fields(ABox)})

    def is_empty(self) -> bool:
        """True iff this ABox carries no assertion of ANY kind.

        DERIVED from :data:`_AXIOM_KINDS` (every ``holder == "abox"`` row's
        field), not from a hand-written ``or`` over three attributes — which is
        what :func:`~unicode_logic_kit.dl.translate.kb_to_fol` reads to decide
        whether the knowledge-base formula has an ABox half at all. A new
        assertion kind that escaped a hand-written condition there would be a
        SILENT loss (the ABox half dropped from the formula entirely), not an
        error; a missing table row is caught by
        ``tests/test_dl_route_agreement.py``'s meta-test instead.
        """
        return not any(getattr(self, field) for field in _holder_fields("abox"))


# --------------------------------------------------------------------------- #
# The axiom-kind table: one row per axiom kind a TBox/ABox can hold, carrying
# what each of the kit's two routes does with it. See "The axiom-kind table"
# in the module docstring for the policy this table makes mechanical.
# --------------------------------------------------------------------------- #

_TABLEAU_EFFECTS = ("internalised", "rule", "refused")
_FOL_EFFECTS = ("fol", "two-sorted", "none")
_IMAGE_PARTS = ("concepts", "side", "assertions", "none")


@dataclass(frozen=True)
class _AxiomKind:
    """One row of :data:`_AXIOM_KINDS`.

    Fields:

    * ``kind`` — the OWL 2 keyword, e.g. ``"SubObjectPropertyOf"``. The OWL
      name rather than an internal one, so a caller can census an ontology's
      image per axiom kind (:meth:`KnowledgeBaseFOL.axioms_of_kind`) without a
      second translation table.
    * ``holder`` — ``"tbox"`` or ``"abox"``: which of the two classes stores it.
    * ``field`` — the attribute on that class. Two kinds MAY share a field
      (``SubClassOf`` and ``EquivalentClasses`` both live in
      ``TBox.inclusions``, because an equivalence is stored as the pair of
      inclusions it abbreviates).
    * ``builder`` — the ``add_*``/``assert_*`` method that fills it. Builders
      never refuse; see the module docstring.
    * ``tableau`` — one of :data:`_TABLEAU_EFFECTS`.
    * ``fol`` — one of :data:`_FOL_EFFECTS`.
    * ``part`` — one of :data:`_IMAGE_PARTS`.
    * ``individual_positions`` — for an ABox row, the indices of the stored
      tuple that hold INDIVIDUAL names (``concept_assertions`` stores
      ``(individual, concept)`` so ``(0,)``; ``role_assertions`` stores
      ``(a, b, role)`` so ``(0, 1)``). :func:`_abox_individual_names` and
      :func:`~unicode_logic_kit.dl.translate._abox_individuals` both read this,
      so a new assertion kind contributes its individuals to
      ``KnowledgeBaseFOL.individuals`` by declaring positions here rather than
      by being remembered in two scans.
    * ``layer`` — ``"object"`` (the default) or ``"data"``: which half of OWL 2
      the kind belongs to. The data half is the one NO in-house route here
      decides, and :func:`_reject_unsupported` words its pointer accordingly
      (the external HermiT route is not wired to it either); the other
      consumers that must refuse it by name read this column.
    * ``refusal_note`` — for a ``"refused"`` row, one sentence saying WHY this
      particular kind has no rule and what to write instead, appended to
      :func:`_reject_unsupported`'s message. The shared guard names the kind
      and its count for every refused row alike; the remedy is per construct
      (``InverseFunctionalObjectProperty`` points at
      :meth:`TBox.add_functional_role`, ``ReflexiveObjectProperty`` at
      ``⊤ ⊑ ∀r.C``), and a generic message cannot carry that. Empty for a
      decided kind.
    """

    kind: str
    holder: str
    field: str
    builder: str
    tableau: str
    fol: str
    part: str
    individual_positions: Tuple[int, ...] = ()
    refusal_note: str = ""
    layer: str = "object"


#: The refusal note every DATA row carries: one reason, because it is one
#: reason (the tableau has no data domain), plus the route that answers.
_DATA_NOTE = (
    "the in-house tableau has no data domain: it cannot decide datatype "
    "membership, facet arithmetic, the cardinality of a value space, or that "
    "two literals of one datatype denote DIFFERENT values (so no ≤-rule may "
    "ever merge two data nodes), and skipping the axiom would answer for a "
    "weaker knowledge base. The FOL image carries the data layer — "
    "dl.kb_to_fol renders it, with the OwlThing/OwlData and datatype-lattice "
    "side axioms, for api.prove")


_AXIOM_KINDS: Tuple[_AxiomKind, ...] = (
    # --- the concept-level TBox: ordinary GCIs, internalised onto every label
    _AxiomKind("SubClassOf", "tbox", "inclusions", "add",
               tableau="internalised", fol="fol", part="concepts"),
    _AxiomKind("EquivalentClasses", "tbox", "inclusions", "add_equivalence",
               tableau="internalised", fol="fol", part="concepts"),
    # --- the RBox: not internalised (TBox.internalized leaves it out on
    #     purpose) but read by _saturate's ∀-rule through _RBox — rules H and
    #     S of "Role hierarchies and transitive roles (RBox)" above, whose
    #     termination argument is written there. The FOL image renders them as
    #     SIDE axioms, never as conjuncts of the knowledge-base formula.
    _AxiomKind("SubObjectPropertyOf", "tbox", "role_inclusions", "add_role_inclusion",
               tableau="rule", fol="fol", part="side"),
    _AxiomKind("TransitiveObjectProperty", "tbox", "transitive_roles", "add_transitive_role",
               tableau="rule", fol="fol", part="side"),
    # --- the rest of the OWL 2 object property box. See "The rest of the OWL 2
    #     role box" in the module docstring for the derivation of every
    #     "rule"/"internalised"/"refused" below; each of them renders as a SIDE
    #     axiom.
    #     Decided, each by one clash condition over the edge closure (_clash):
    _AxiomKind("DisjointObjectProperties", "tbox", "disjoint_role_pairs",
               "add_disjoint_roles", tableau="rule", fol="fol", part="side"),
    _AxiomKind("AsymmetricObjectProperty", "tbox", "asymmetric_roles",
               "add_asymmetric_role", tableau="rule", fol="fol", part="side"),
    _AxiomKind("IrreflexiveObjectProperty", "tbox", "irreflexive_roles",
               "add_irreflexive_role", tableau="rule", fol="fol", part="side"),
    #     Decided by INTERNALISATION, not by a rule: ⊤ ⊑ ≤1 P.⊤ (see
    #     _new_branch), so the existing ALCQ argument covers it unchanged. The
    #     row says "internalised" for that reason; it said "rule" while this
    #     very comment said the opposite.
    _AxiomKind("FunctionalObjectProperty", "tbox", "functional_roles",
               "add_functional_role", tableau="internalised", fol="fol",
               part="side"),
    #     Refused by name, with the construct's own remedy:
    _AxiomKind("InverseObjectProperties", "tbox", "inverse_role_pairs",
               "add_inverse_roles", tableau="refused", fol="fol", part="side",
               refusal_note=(
                   "InverseObjectProperties(P Q) is the I of SHIQ: with P ≡ Q⁻, "
                   "an edge x —P→ y makes y —Q→ x hold, so y : ∀Q.C forces C "
                   "onto x — a node's label would depend on what lies BACKWARD "
                   "across an edge, which subset blocking's soundness/"
                   "completeness argument does not cover (see the module "
                   "docstring's 'Inverse roles and nominals (I, O)' section, "
                   "the same reason a bare InverseRole concept is refused)")),
    _AxiomKind("SymmetricObjectProperty", "tbox", "symmetric_roles",
               "add_symmetric_role", tableau="refused", fol="fol", part="side",
               refusal_note=(
                   "a symmetric role IS the inverse-role inclusion P ⊑ P⁻: "
                   "materialising the converse edge would put a cycle in the "
                   "completion graph, so a blocked node's blocker can become "
                   "its own descendant and subset blocking no longer applies")),
    _AxiomKind("ReflexiveObjectProperty", "tbox", "reflexive_roles",
               "add_reflexive_role", tableau="refused", fol="fol", part="side",
               refusal_note=(
                   "a reflexive role makes every individual its OWN neighbour, "
                   "and counting a node among its own neighbours lets the "
                   "≤-rule merge a node with its own successor — the back-edge "
                   "case this tableau's termination argument excludes (see the "
                   "module docstring's 'Qualified number restrictions'). The "
                   "restriction ⊤ ⊑ ∀r.C is the concept-level way to spell what "
                   "a reflexive r would propagate")),
    _AxiomKind("InverseFunctionalObjectProperty", "tbox",
               "inverse_functional_roles", "add_inverse_functional_role",
               tableau="refused", fol="fol", part="side",
               refusal_note=(
                   "InverseFunctionalObjectProperty(P) is the number "
                   "restriction ≤1 P⁻.⊤, so it counts P-PREDECESSORS and needs "
                   "inverse roles (the I of SHIQ). If you meant functionality "
                   "on P itself, use dl.TBox.add_functional_role, which this "
                   "tableau does decide")),
    _AxiomKind("ObjectPropertyChain", "tbox", "role_chains", "add_role_chain",
               tableau="refused", fol="fol", part="side",
               refusal_note=(
                   "a complex role inclusion P1 ∘ … ∘ Pn ⊑ Q is the R of "
                   "SROIQ: deciding it needs the role automaton and the "
                   "regularity restriction of Horrocks, Kutz & Sattler 2006, "
                   "which this tableau does not implement (the local label "
                   "rule that would cover an acyclic chain set is written out "
                   "in the module docstring). Ignoring the chain instead would "
                   "report 'not subsumed' for a subsumption the FOL image "
                   "proves, so this refuses")),
    #     Decided by INTERNALISATION as well, and the only role-box kinds whose
    #     axiom carries a CLASS EXPRESSION: a domain axiom is the GCI
    #     ∃P.⊤ ⊑ C and a range axiom is ⊤ ⊑ ∀P.C (see "Domain and range
    #     axioms" in the module docstring), so the existing ⊓/⊔/∃/∀ rules
    #     decide them with no new machinery. Their FOL image is nevertheless
    #     the direct ∀x ∀y (P(x, y) → C(x/y)) sentence, not the GCI rewrite.
    _AxiomKind("ObjectPropertyDomain", "tbox", "role_domains", "add_role_domain",
               tableau="internalised", fol="fol", part="side"),
    _AxiomKind("ObjectPropertyRange", "tbox", "role_ranges", "add_role_range",
               tableau="internalised", fol="fol", part="side"),
    # --- the ABox: seeded into the initial branch by abox_consistent and
    #     decided by the clash conditions (_clash), which is the "rule"
    #     column's third form.
    _AxiomKind("ClassAssertion", "abox", "concept_assertions", "assert_concept",
               tableau="rule", fol="fol", part="assertions",
               individual_positions=(0,)),
    _AxiomKind("ObjectPropertyAssertion", "abox", "role_assertions", "assert_role",
               tableau="rule", fol="fol", part="assertions",
               individual_positions=(0, 1)),
    _AxiomKind("DifferentIndividuals", "abox", "distinct_assertions", "assert_distinct",
               tableau="rule", fol="fol", part="assertions",
               individual_positions=(0, 1)),
    #     Decided by node MERGING at setup, closed under the equivalence the
    #     assertions generate (see "Same-individual assertions" in the module
    #     docstring) -- the ≤-rule's own _merge, reused.
    _AxiomKind("SameIndividual", "abox", "same_assertions", "assert_same",
               tableau="rule", fol="fol", part="assertions",
               individual_positions=(0, 1)),
    #     Decided by a clash condition over _Branch.negative_edges, closed
    #     under the role hierarchy (see "Negative role assertions").
    _AxiomKind("NegativeObjectPropertyAssertion", "abox",
               "negative_role_assertions", "assert_negative_role",
               tableau="rule", fol="fol", part="assertions",
               individual_positions=(0, 1)),
    # --- the DATA layer: every kind REFUSED by the tableau (it has no data
    #     domain -- see "The data layer" in the module docstring) and rendered
    #     by the FOL image as an ordinary side axiom / ABox conjunct. The
    #     two-sorted discipline around them (OwlThing/OwlData, the datatype
    #     lattice) is NOT a row: it is derived from the vocabulary by
    #     dl.translate.data_sort_axioms, not stored.
    _AxiomKind("SubDataPropertyOf", "tbox", "data_property_inclusions",
               "add_data_property_inclusion", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("DisjointDataProperties", "tbox", "disjoint_data_property_pairs",
               "add_disjoint_data_properties", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("FunctionalDataProperty", "tbox", "functional_data_properties",
               "add_functional_data_property", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("DataPropertyDomain", "tbox", "data_property_domains",
               "add_data_property_domain", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("DataPropertyRange", "tbox", "data_property_ranges",
               "add_data_property_range", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("DatatypeDefinition", "tbox", "datatype_definitions",
               "add_datatype_definition", tableau="refused", fol="fol",
               part="side", refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("DataPropertyAssertion", "abox", "data_assertions", "assert_data",
               tableau="refused", fol="fol", part="assertions",
               individual_positions=(0,), refusal_note=_DATA_NOTE, layer="data"),
    _AxiomKind("NegativeDataPropertyAssertion", "abox",
               "negative_data_assertions", "assert_negative_data",
               tableau="refused", fol="fol", part="assertions",
               individual_positions=(0,), refusal_note=_DATA_NOTE, layer="data"),
)


def _validate_axiom_kinds(rows: Optional[Tuple[_AxiomKind, ...]] = None) -> None:
    """Check :data:`_AXIOM_KINDS`' own well-formedness at import time.

    A typo in a vocabulary word (``"refuse"`` for ``"refused"``) would make
    every guard derived from the column silently fall through, which is the
    one failure mode the table exists to prevent — so it is caught here, when
    the module is imported, rather than by whichever test happens to notice.
    """
    rows = _AXIOM_KINDS if rows is None else rows
    seen = set()
    for row in rows:
        if row.kind in seen:
            raise ValueError(f"_AXIOM_KINDS: duplicate kind {row.kind!r}")
        seen.add(row.kind)
        if row.holder not in ("tbox", "abox"):
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: holder {row.holder!r}")
        if row.tableau not in _TABLEAU_EFFECTS:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: tableau {row.tableau!r} "
                             f"is not one of {_TABLEAU_EFFECTS}")
        if row.fol not in _FOL_EFFECTS:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: fol {row.fol!r} "
                             f"is not one of {_FOL_EFFECTS}")
        if row.part not in _IMAGE_PARTS:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: part {row.part!r} "
                             f"is not one of {_IMAGE_PARTS}")
        holder = TBox if row.holder == "tbox" else ABox
        if row.field not in {f.name for f in dataclass_fields(holder)}:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: {holder.__name__} has "
                             f"no field {row.field!r}")
        if not callable(getattr(holder, row.builder, None)):
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: {holder.__name__} has "
                             f"no builder method {row.builder!r}")
        if row.holder == "tbox" and row.individual_positions:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: individual_positions "
                             "is for ABox rows only")
        if (row.fol == "none") != (row.part == "none"):
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: fol={row.fol!r} and "
                             f"part={row.part!r} disagree about whether the FOL "
                             "image renders this kind")
        if row.layer not in ("object", "data"):
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: layer {row.layer!r} "
                             "is not one of ('object', 'data')")
        if row.tableau != "refused" and row.refusal_note:
            raise ValueError(f"_AXIOM_KINDS[{row.kind}]: tableau={row.tableau!r} "
                             "but a refusal_note is set — a decided kind has "
                             "nothing to refuse")


_validate_axiom_kinds()


def _holder_fields(holder: str, *, part: Optional[str] = None,
                   tableau: Optional[str] = None,
                   layer: Optional[str] = None) -> Tuple[str, ...]:
    """The distinct ``field`` names of :data:`_AXIOM_KINDS`' rows for ``holder``,
    optionally narrowed to one ``part``, one ``tableau`` effect and/or one
    ``layer`` (``"object"`` or ``"data"``).

    De-duplicated and in table order, because two kinds may share a field and
    a caller counting a field twice would report an axiom twice.
    """
    names = []
    for row in _AXIOM_KINDS:
        if row.holder != holder:
            continue
        if part is not None and row.part != part:
            continue
        if tableau is not None and row.tableau != tableau:
            continue
        if layer is not None and row.layer != layer:
            continue
        if row.field not in names:
            names.append(row.field)
    return tuple(names)


def _concept_individual_names(concept) -> Set[str]:
    """Every individual a class expression names, at any depth: the filler of a
    :class:`~unicode_logic_kit.dl.concepts.Nominal` or of a
    :class:`~unicode_logic_kit.dl.concepts.HasValue`. Generic over the dataclass
    fields, so a new concept kind with a nested concept is reached without being
    named here (the ``individual`` field is the one thing this must know)."""
    names: Set[str] = set()
    stack = [concept]
    while stack:
        node = stack.pop()
        if isinstance(node, (Nominal, HasValue)):
            names.add(node.individual)
        for fld in dataclass_fields(node) if hasattr(node, "__dataclass_fields__") else ():
            value = getattr(node, fld.name)
            if isinstance(value, Concept):
                stack.append(value)
    return names


def _abox_individual_names(abox: "ABox") -> Set[str]:
    """Every individual name ``abox`` mentions, read off :data:`_AXIOM_KINDS`'
    ``individual_positions`` rather than by scanning three fields by hand —
    plus the individuals named INSIDE an asserted class expression: an
    individual in an ABox assertion is an individual of the ABox wherever in the
    assertion it stands, so ``a : ∃r.{b}`` (a value restriction or a nominal, at
    any depth) makes ``b`` one as well. The fillers of a TBox's class expressions
    stay out, as :attr:`~unicode_logic_kit.dl.translate.KnowledgeBaseFOL.individuals`
    documents.
    """
    names: Set[str] = set()
    for row in _AXIOM_KINDS:
        if row.holder != "abox" or not row.individual_positions:
            continue
        for stored in getattr(abox, row.field):
            for position in row.individual_positions:
                names.add(stored[position])
    for _individual, concept in abox.concept_assertions:
        names |= _concept_individual_names(concept)
    return names


def _data_layer_kinds(tbox: Optional["TBox"], abox: Optional["ABox"]) -> List[str]:
    """The ``layer == "data"`` kinds ``(tbox, abox)`` actually carries, in table
    order — every one of them, refused by the tableau or not (today they are the
    same set). What the OTHER consumers that must refuse the data layer by
    name (``dl.owl_reasoner``) ask.
    """
    found: List[str] = []
    for row in _AXIOM_KINDS:
        if row.layer != "data":
            continue
        obj = tbox if row.holder == "tbox" else abox
        if obj is not None and getattr(obj, row.field):
            found.append(row.kind)
    return found


def _refused_axioms(tbox: Optional["TBox"],
                    abox: Optional["ABox"]) -> List[Tuple[str, int, Tuple[str, ...]]]:
    """``(kind-name, count, notes)`` for every ``"refused"`` row of
    :data:`_AXIOM_KINDS` that ``(tbox, abox)`` actually carries, in table order.

    Kinds that share a storing field are reported as one entry naming both
    (``"A/B"``), since the field's length is the only count there is; ``notes``
    then carries each of their ``refusal_note``s.
    """
    found: List[Tuple[str, int, Tuple[str, ...]]] = []
    for holder, obj in (("tbox", tbox), ("abox", abox)):
        if obj is None:
            continue
        for field in _holder_fields(holder, tableau="refused"):
            count = len(getattr(obj, field))
            if not count:
                continue
            rows = [row for row in _AXIOM_KINDS
                    if row.holder == holder and row.field == field
                    and row.tableau == "refused"]
            found.append(("/".join(row.kind for row in rows), count,
                          tuple(row.refusal_note for row in rows if row.refusal_note)))
    return found


def _reject_unsupported(tbox: Optional["TBox"], abox: Optional["ABox"]) -> None:
    """Raise :class:`UnsupportedAxiomError` if ``(tbox, abox)`` carries an axiom
    kind this tableau has no rule for — every such kind at once, with counts.

    THE single shared axiom-level guard — it has ONE caller, :func:`_reject_role_box`,
    which is the first statement of :func:`concept_satisfiable`,
    :func:`abox_consistent` and ``classify``, and which :func:`_reject_inputs`
    calls for the entry points that can return WITHOUT reaching either
    (``realize`` on an empty vocabulary, ``realize_all``/``instance_retrieval``
    on an empty ABox, ``classify`` on fewer than two names).
    ``instance_check``/``subsumes``/``equivalent``/``concept_unsatisfiable``
    hold no guard of their own: each reduces to one of the two deciding
    functions with something to decide, and inherits it, exactly as they
    inherit :func:`_reject_beyond_alc`.

    Each refused kind's own ``refusal_note`` is appended, so the message says
    not only WHICH construct has no rule but why and what to write instead —
    the remedy differs per construct (``InverseFunctionalObjectProperty``
    points at :meth:`TBox.add_functional_role`, ``ReflexiveObjectProperty`` at
    ``⊤ ⊑ ∀r.C``), and the kind name alone cannot carry that.
    """
    refused = _refused_axioms(tbox, abox)
    if not refused:
        return
    listing = ", ".join(f"{kind} x{count}" for kind, count, _ in refused)
    # De-duplicated, in order: the eight data kinds share one reason, and a
    # knowledge base carrying several of them should read it once.
    notes = list(dict.fromkeys(
        note for _, _, kind_notes in refused for note in kind_notes))
    detail = ("".join(f" Why {note}." for note in notes)) if notes else ""
    object_kinds = [name for name, _, _ in refused
                    if any(row.layer == "object" and row.kind in name.split("/")
                           for row in _AXIOM_KINDS)]
    if object_kinds:
        remedy = (f"Use dl.owl_reasoner's external, HermiT-backed reasoner "
                  f"(dl.external_abox_consistent, dl.external_subsumes, …) to "
                  f"decide them, or ask the same question of the FOL image with "
                  f"dl.kb_to_fol(tbox, abox) and api.prove.")
        if len(object_kinds) < len(refused):
            remedy += (" (The data kinds among them are decided by neither "
                       "tableau nor HermiT — dl.owl_reasoner refuses the data "
                       "layer by name too — only by the FOL image.)")
    else:
        remedy = (f"dl.owl_reasoner's external, HermiT-backed reasoner is not "
                  f"wired to the data layer either (it refuses it by name), so "
                  f"ask the FOL image: kb = dl.kb_to_fol(tbox, abox, "
                  f"query=[...the concepts you will ask about]), then api.prove "
                  f"with kb.premises or kb.tbox_premises and the goal from "
                  f"kb.subsumption_goal, kb.unsatisfiability_goal or "
                  f"kb.instance_goal. 'proved' transfers to OWL 2 and 'refuted' "
                  f"does not (kb.refutation_is_decisive: the image is sound, not "
                  f"complete). A facet entailment over the data ranges alone is "
                  f"decided by atp.z3_arith.is_valid_arith.")
    raise UnsupportedAxiomError(
        f"dl.tableau: this knowledge base carries axiom kinds that are outside "
        f"ALCHQ (this kit's in-house DL fragment) — no in-house tableau rule "
        f"decides them: {listing}. Refusing by name is the only honest answer: "
        f"a tableau that ignored them would report a verdict about a WEAKER "
        f"knowledge base than the one it was handed.{detail} {remedy}")


def _reject_inverse_role_inclusions(tbox: "TBox") -> None:
    """Raise :class:`UnsupportedAxiomError` if any role inclusion has an
    :class:`~unicode_logic_kit.dl.concepts.InverseRole` on either side.

    Not a ``"refused"`` ROW of :data:`_AXIOM_KINDS`, because
    ``SubObjectPropertyOf`` as a KIND is decided: this is a condition on the
    stored VALUE, and ``r ⊑ s⁻`` is the **I** of SHIQ exactly as
    ``InverseObjectProperties`` is (see that row's ``refusal_note``). The FOL
    image renders it correctly, so this is the entry that makes the two routes
    agree about it rather than letting the tableau answer a question about a
    role box it silently read as atomic.
    """
    for sub_role, super_role in tbox.role_inclusions:
        for side, value in (("sub-role", sub_role), ("super-role", super_role)):
            if isinstance(value, InverseRole):
                raise UnsupportedAxiomError(
                    f"dl.tableau: the role box declares the role inclusion "
                    f"{_role_text(sub_role)} ⊑ {_role_text(super_role)}, whose "
                    f"{side} is an INVERSE role ({value.role}⁻) — the I of "
                    f"SHIQ, outside ALCHQ (this kit's in-house DL fragment): no "
                    f"in-house tableau rule decides it, because a successor's "
                    f"label would then depend on what lies BACKWARD across an "
                    f"edge, which subset blocking's soundness/completeness "
                    f"argument does not cover (see the module docstring's "
                    f"'Inverse roles and nominals (I, O)' section). "
                    f"dl.rbox_to_fol DOES render this axiom correctly, so ask "
                    f"the question of the FOL image with dl.kb_to_fol(tbox, "
                    f"abox) and api.prove, or decide the knowledge base with "
                    f"dl.owl_reasoner's external, HermiT-backed reasoner "
                    f"(dl.external_subsumes, dl.external_abox_consistent).")


def _role_text(role) -> str:
    """``role`` as it should read in a message: ``'r'`` or ``'r'⁻``."""
    if isinstance(role, InverseRole):
        return f"{role.role!r}⁻"
    return repr(role)


#: ``(TBox field, OWL keyword, how the stored entries name roles)`` for every
#: axiom kind OWL 2 (Structural Specification §11) restricts to SIMPLE roles.
#: :func:`_check_simple_role_box` is driven by this, so a kind added later is
#: covered by one line rather than by being remembered inside a loop.
_SIMPLE_ROLE_AXIOMS: Tuple[Tuple[str, str, str], ...] = (
    ("asymmetric_roles", "AsymmetricObjectProperty", "name"),
    ("irreflexive_roles", "IrreflexiveObjectProperty", "name"),
    ("functional_roles", "FunctionalObjectProperty", "name"),
    ("inverse_functional_roles", "InverseFunctionalObjectProperty", "name"),
    ("disjoint_role_pairs", "DisjointObjectProperties", "pair"),
)


class _OrderedSet(dict):
    """A set that iterates in the order its members were first added.

    What the search order of the tableau is made of. A branch's labels and
    edges were plain ``set`` s, and a ``set`` of strings iterates in an order
    that depends on ``PYTHONHASHSEED``: the completion rules each take "the
    first" unresolved disjunction, existential, ≥-restriction, choice or merge
    they meet, so the SAME knowledge base was searched in a different order
    — and used a different number of steps, near the step budget a verdict on
    one run and "step budget exhausted" on the next — from one process to the
    next. Here iteration order is a function of the sequence of insertions
    alone, and every insertion the tableau makes is itself driven by an
    ordered traversal (the TBox lists, the sorted individuals, this
    container), so a run is reproducible whatever the hash seed.

    A ``dict`` subclass, so that membership, iteration and ``len`` stay at the
    speed of the built-in container; only the set operations the tableau uses
    are spelled out (``add``, ``update``, ``|=``, ``>=`` and ``copy``).
    """

    __slots__ = ()

    def __init__(self, members=()):
        dict.__init__(self, dict.fromkeys(members))

    def add(self, member) -> None:
        self[member] = None

    def update(self, members) -> None:  # type: ignore[override]  # a set stored as a dict: takes members, not entries
        dict.update(self, dict.fromkeys(members))

    def __ior__(self, members):  # type: ignore[misc]  # set union in place, not dict's merge of entries
        self.update(members)
        return self

    def __ge__(self, other) -> bool:
        """Superset test, as for a ``set`` (``other`` may be any set-like)."""
        return self.keys() >= (other.keys() if isinstance(other, dict) else other)

    def copy(self) -> "_OrderedSet":
        duplicate = _OrderedSet()
        dict.update(duplicate, self)
        return duplicate

    def __repr__(self) -> str:
        return f"_OrderedSet({list(self)!r})"


class _Generated:
    """A node the tableau itself created: the witness of an ``∃`` or a ``≥``
    restriction.

    Whether a node is generated or named is a property of the node — its CLASS —
    and never of how a name is spelled. A named individual is a ``str``, a
    generated node is a ``_Generated``, and the two are never equal, so a
    knowledge base may call an individual anything at all (``_x1`` and ``x0``
    included) without it ever being merged with a witness, blocked as one, or
    blocking one. Only a generated node may be blocked or block
    (:func:`_blocked`), and only a named node is kept when a merge has the
    choice (:func:`_merge_order`).

    Two generated nodes are equal iff they carry the same serial number, which
    is unique within a branch. The hash is that of the serial, so the order a
    container of nodes iterates in never depends on ``PYTHONHASHSEED``.
    """

    __slots__ = ("serial",)

    def __init__(self, serial: int) -> None:
        self.serial = serial

    def __eq__(self, other: object) -> bool:
        return isinstance(other, _Generated) and other.serial == self.serial

    def __hash__(self) -> int:
        return hash(self.serial)

    def __repr__(self) -> str:
        return f"<generated node {self.serial}>"


#: A node of a branch: a named individual (or the anonymous root) is a ``str``, a
#: generated one a :class:`_Generated`.
_Node = Union[str, _Generated]


class _Branch:
    """A single open tableau branch: per-individual labels, role edges, order, and
    (for **Q**) a pairwise-distinctness relation — see "Qualified number
    restrictions" in the module docstring.
    """

    __slots__ = ("label", "edges", "order", "counter", "distinct",
                 "self_distinct", "negative_edges")

    def __init__(self):
        self.label = {}                  # node -> ordered set of concepts
        self.edges = _OrderedSet()       # (src, role, dst), in insertion order
        self.order = []                  # nodes in creation order (for blocking)
        self.counter = 0
        self.distinct = set()            # frozenset({a, b}) pairs forced distinct
        self.self_distinct = False       # an individual asserted distinct from ITSELF
        self.negative_edges = set()      # (src, role, dst) FORBIDDEN by a
                                         # NegativeObjectPropertyAssertion

    def copy(self) -> "_Branch":
        b = _Branch.__new__(_Branch)
        b.label = {k: v.copy() for k, v in self.label.items()}
        b.edges = self.edges.copy()
        b.order = list(self.order)
        b.counter = self.counter
        b.distinct = set(self.distinct)
        b.self_distinct = self.self_distinct
        b.negative_edges = set(self.negative_edges)
        return b

    def add_node(self, node: "_Node") -> None:
        if node not in self.label:
            self.label[node] = _OrderedSet()
            self.order.append(node)

    def fresh(self) -> "_Generated":
        """A new GENERATED node, added to the branch.

        It is a :class:`_Generated`, not a name: it equals no string, so it can
        be neither a named individual nor merged with one by accident, whatever
        the individuals are called.
        """
        self.counter += 1
        node = _Generated(self.counter)
        self.add_node(node)
        return node

    def mark_distinct(self, a: _Node, b: _Node) -> None:
        """Force ``a`` and ``b`` (already-added nodes) pairwise distinct.

        ``a`` and ``b`` being the SAME node is recorded in ``self_distinct``, which
        :func:`_clash` reads: ``a ≠ a`` has no model. Dropping it instead — which
        this method did until 0.30.0 — made ``abox_consistent`` report True for an
        ABox whose own FOL rendering ``a ≠ a`` is refutable, so the tableau and the
        FOL cross-check disagreed. The ≥-rule's own witnesses can never reach this:
        it marks FRESH nodes distinct from each other, pairwise, never from
        themselves.
        """
        if a == b:
            self.self_distinct = True
        else:
            self.distinct.add(frozenset((a, b)))


class _Ctx:
    def __init__(self, max_steps: int):
        self.steps = max_steps

    def tick(self) -> None:
        self.steps -= 1
        if self.steps <= 0:
            raise RuntimeError("dl tableau: step budget exhausted (raise dl.tableau.MAX_STEPS).")


class _RBox:
    """The role-box view of a ``TBox``, precomputed once per :func:`_solve` call
    (see ``_new_branch``) and consulted read-only from :func:`_saturate`'s
    ∀-rule and from :func:`_clash`.

    See "Role hierarchies and transitive roles (RBox)" and "The rest of the OWL 2
    role box" in the module docstring for the algorithm this implements and its
    soundness/termination argument.

    Every parameter after the first two is KEYWORD-ONLY with a default, so the
    two-positional form ``_RBox(role_inclusions, transitive_roles)`` keeps
    working; :meth:`from_tbox` is the one real call site.
    """

    __slots__ = ("_ancestors", "transitive", "transitive_in_order", "disjoint_pairs",
                 "asymmetric", "irreflexive", "reflexive", "composite",
                 "has_edge_constraints")

    def __init__(self, role_inclusions: List[Tuple[str, str]],
                 transitive_roles: Set[str], *,
                 disjoint_pairs: Iterable[Tuple[str, str]] = (),
                 asymmetric: Iterable[str] = (),
                 irreflexive: Iterable[str] = (),
                 reflexive: Iterable[str] = (),
                 chain_super_roles: Iterable[str] = ()):
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
        # Public: the declared-transitive role names, as a set to test
        # membership against. The ∀+-rule (RBox rule S) in _saturate iterates
        # ``transitive_in_order`` instead, below.
        self.transitive: FrozenSet[str] = frozenset(transitive_roles)
        # The same roles in a fixed order: the ∀+-rule adds one restriction per
        # qualifying role to a label, and the order of those additions is part of
        # the search order, so it must not follow the hash of the role names.
        self.transitive_in_order: Tuple[str, ...] = tuple(
            sorted(self.transitive, key=repr))
        # The three EDGE-PATTERN constraints _clash decides (see "The rest of
        # the OWL 2 role box" in the module docstring).
        self.disjoint_pairs: FrozenSet[Tuple[str, str]] = frozenset(disjoint_pairs)
        self.asymmetric: FrozenSet[str] = frozenset(asymmetric)
        self.irreflexive: FrozenSet[str] = frozenset(irreflexive)
        # Carried for completeness of the view (and for the external routes);
        # the clash rules never read it, because a reflexive role box is
        # refused before the tableau starts.
        self.reflexive: FrozenSet[str] = frozenset(reflexive)
        # COMPOSITE in OWL 2's sense (Structural Specification §11): declared
        # transitive, or the super-role of a property chain. `_is_simple_role`
        # reads this, so adding chains to the tableau later needs no second
        # definition of "simple".
        self.composite: FrozenSet[str] = frozenset(transitive_roles) | frozenset(chain_super_roles)
        # The short-circuit `_clash` tests before touching the edge set at all:
        # `_clash` is the innermost loop of the reasoner and a plain ALC/ALCQ
        # TBox must not pay for a feature it does not use.
        self.has_edge_constraints: bool = bool(
            self.disjoint_pairs or self.asymmetric or self.irreflexive)

    @classmethod
    def from_tbox(cls, tbox: "TBox") -> "_RBox":
        """The role-box view of ``tbox`` — the one real construction site.

        Only inclusions between PLAIN role names enter the view. An inclusion
        with an :class:`~unicode_logic_kit.dl.concepts.InverseRole` on a side is
        the **I** of SHIQ: the in-house tableau refuses it before it builds a
        branch (:func:`_reject_inverse_role_inclusions`), and the one other
        caller, the external route, reads this view only for the simple-role
        check, which asks whether a role reaches a NAMED composite role. An
        inverse-role node was never one, so leaving it out changes no verdict.
        """
        plain_inclusions = [
            (sub_role, super_role)
            for sub_role, super_role in tbox.role_inclusions
            if isinstance(sub_role, str) and isinstance(super_role, str)]
        return cls(plain_inclusions, tbox.transitive_roles,
                   disjoint_pairs=tbox.disjoint_role_pairs,
                   asymmetric=tbox.asymmetric_roles,
                   irreflexive=tbox.irreflexive_roles,
                   reflexive=tbox.reflexive_roles,
                   chain_super_roles=[super_role for _, super_role in tbox.role_chains])

    def ancestors(self, role: str) -> FrozenSet[str]:
        """Every role ``role`` entails via ⊑* (``role`` itself included).

        A role that never occurs in any RBox axiom falls back to the reflexive
        singleton ``{role}`` — so a plain ALC ``TBox`` with an empty RBox degrades
        every lookup here to exactly the pre-RBox exact-match behaviour.
        """
        return self._ancestors.get(role, frozenset((role,)))


_EMPTY_RBOX = _RBox([], set())


def _edge_closure(branch: _Branch,
                  rbox: _RBox) -> Dict[Tuple[_Node, _Node], Set[str]]:
    """``(source, destination) -> every role the branch's edges between them
    entail via ⊑*`` — the one index the three edge-pattern clash conditions read.

    Built once per :func:`_clash` call rather than per condition, and only when
    ``rbox.has_edge_constraints``. On a SIMPLE role box this closure is exactly
    the entailed relation (see the module docstring's completeness argument),
    which is what makes the three conditions exact and not merely sound.
    """
    closure: Dict[Tuple[_Node, _Node], Set[str]] = {}
    for (source, role, destination) in branch.edges:
        closure.setdefault((source, destination), set()).update(rbox.ancestors(role))
    return closure


def _edge_pattern_clash(branch: _Branch, rbox: _RBox) -> bool:
    """True iff the branch's edges violate an irreflexivity, asymmetry or role
    disjointness declaration (see "The rest of the OWL 2 role box" in the module
    docstring for the derivation of all three, and for why they are strictly
    SUBTRACTIVE and so change nothing else about the algorithm).
    """
    closure = _edge_closure(branch, rbox)
    for (source, destination), roles in closure.items():
        if source == destination and rbox.irreflexive & roles:
            return True                              # IrreflexiveObjectProperty
        if rbox.asymmetric & roles:                  # AsymmetricObjectProperty
            converse = closure.get((destination, source))
            if converse is not None and rbox.asymmetric & roles & converse:
                return True                          # (x == y included: entailed
                                                     #  irreflexivity)
        for left, right in rbox.disjoint_pairs:      # DisjointObjectProperties
            if left in roles and right in roles:
                return True
    return False


def _has_entailed_edge(branch: _Branch, rbox: _RBox, source: _Node, role,
                       destination: _Node) -> bool:
    """True iff the branch has an edge from ``source`` to ``destination`` whose
    OWN role entails ``role`` via ⊑* — i.e. iff the branch already says
    ``role(source, destination)``.

    Hierarchy-aware for the reason the ∀-rule's rule H is (see the module
    docstring): an ``r``-edge with ``r ⊑* role`` IS a ``role``-edge in every
    model, so it VIOLATES the negative role assertion ``¬role(source,
    destination)`` — the one reader of this function.
    """
    ancestors_of = rbox.ancestors
    return any(s == source and d == destination and role in ancestors_of(r)
               for (s, r, d) in branch.edges)


def _clash(branch: _Branch, rbox: _RBox) -> bool:
    """True iff some individual's label contains ⊥, a complementary atomic pair, an
    individual asserted distinct from ITSELF, or (for **Q**) a ``≤n r.C`` together
    with ``n+1`` PAIRWISE-DISTINCT ``r``-neighbours all in ``C`` (see "Qualified
    number restrictions" in the module docstring) — or the branch's EDGES violate
    an irreflexivity/asymmetry/role-disjointness declaration (see "The rest of the
    OWL 2 role box") or a negative role assertion (see "Negative role
    assertions").
    """
    if branch.self_distinct:
        # ``a ≠ a`` has no model, whatever else the branch says — and unlike every
        # other clash condition here it needs no label or neighbour to look at.
        return True
    if rbox.has_edge_constraints and _edge_pattern_clash(branch, rbox):
        return True
    for (source, role, destination) in branch.negative_edges:
        # NegativeObjectPropertyAssertion(role a b) says <a, b> ∉ role^I, so an
        # entailed edge between the two is a direct contradiction.
        if _has_entailed_edge(branch, rbox, source, role, destination):
            return True
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
                    for trans_role in rbox.transitive_in_order:  # rule S: ∀+-rule
                        if trans_role not in role_ancestors:
                            continue                  # role ⊑* trans_role fails
                        if c.role not in rbox.ancestors(trans_role):
                            continue                  # trans_role ⊑* c.role fails
                        propagated = ForAll(trans_role, c.concept)
                        if propagated not in branch.label[d]:
                            branch.label[d].add(propagated)
                            changed = True
    return changed


def _contradicted(label: "_OrderedSet", c: Concept) -> bool:
    """True iff ``c`` cannot hold at a node carrying ``label``: it is ⊥, or its
    complement is in the label (``A`` against ``¬A``, either way round)."""
    if isinstance(c, Bottom):
        return True
    if isinstance(c, Atomic):
        return Not(c) in label
    if isinstance(c, Not):
        return c.concept in label
    return False


def _is_forced(label: "_OrderedSet", disjunction: Concept) -> bool:
    """True iff at most ONE alternative of ``disjunction`` can still hold at a node
    carrying ``label``. The alternatives are the leaves of the (nested) ``⊔``;
    one is out when :func:`_contradicted`."""
    alive = 0
    stack = [disjunction]
    while stack:
        alternative = stack.pop()
        if isinstance(alternative, Or):
            stack.append(alternative.right)
            stack.append(alternative.left)
        elif not _contradicted(label, alternative):
            alive += 1
            if alive > 1:
                return False
    return True


def _find_disjunction(branch: _Branch):
    """An unresolved ``x : C ⊔ D`` (neither disjunct present yet), or None.

    Which one is a fixed rule, because the ⊔-rule may be applied to any of them and
    the verdict never depends on the choice, while the size of the search does
    ("Search order" in the module docstring): the first unresolved disjunction
    that is FORCED comes first (:func:`_is_forced`: at most one alternative is not
    already contradicted by its node's label, so one branch of the split dies at
    once and the other is the only way on), and if there is none, the first
    unresolved disjunction. "First" is in node creation order, then in the order
    a label received its concepts: a function of the insertion order alone.
    """
    first: Optional[Tuple[_Node, Concept]] = None
    for node in branch.order:
        label = branch.label[node]
        for c in label:
            if not isinstance(c, Or) or c.left in label or c.right in label:
                continue
            if first is None:
                first = (node, c)
            if _is_forced(label, c):
                return node, c
    return first


def _blocked(branch: _Branch, node: _Node) -> bool:
    """Subset blocking: a GENERATED node subsumed by an earlier GENERATED node
    is not expanded.

    Both occurrences of "generated" matter, and the second one is a 0.30.0
    restriction. Until then any earlier node could block — including a NAMED
    ABox individual, which ``abox_consistent`` adds first, so a generated node
    with a small label was routinely blocked by a named one. That is
    legitimate only as long as no formula can distinguish two elements that
    satisfy the same concepts: subset blocking's soundness argument (Horrocks
    & Sattler 1999) is a statement about the UNRAVELLING, in which a blocked
    node is interpreted by its blocker. A negative role assertion ``¬r(a, b)``
    is such a formula — it refers to elements BY NAME. Collapsing a generated
    ``r``-successor of ``a`` onto the NAMED node ``b`` would give ``a`` an
    ``r``-edge to ``b`` in the model that the assertion forbids, and no clash
    would fire, because no such edge was ever added to the graph. So a named
    node may not block. (The value restriction ``∃r.{a}``, which names an
    element too, is what exposed this; it is refused now — see "Value
    restrictions (ObjectHasValue)" in the module docstring — but a negative
    role assertion still needs the restriction.)

    Collapsing a generated node onto an earlier GENERATED node is the standard
    case the module docstring's termination argument covers: the generated
    part of a branch is a tree whose labels are pushed forward from the
    ancestors, so a blocker whose label is a superset of the blocked node's has
    every obligation the blocked node has.

    Unconditional, not gated on "does this knowledge base contain a negative
    role assertion": a flag that changes the blocking condition is right in the
    commit that adds it and wrong three releases later. The restriction only
    ever makes the search space LARGER, never a verdict different, and
    termination is untouched, because the finite subconcept/RBox-role label
    closure still forces a repeat among generated nodes within a bounded
    number of generations, which is the whole content of the existing
    argument; only the set of eligible blockers shrinks.
    """
    if not isinstance(node, _Generated):
        return False                     # named / root individuals are never blocked
    idx = branch.order.index(node)
    lbl = branch.label[node]
    return any(branch.label[other] >= lbl
               for other in branch.order[:idx] if isinstance(other, _Generated))


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

def _role_neighbours(branch: _Branch, rbox: _RBox, x: _Node, role: str) -> List[_Node]:
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


def _in_concept(branch: _Branch, node: _Node, concept: Concept) -> bool:
    """True iff ``node`` is (syntactically) known to be in ``concept`` — ``concept``
    is ⊤ (trivially true for everyone, whether or not ``Top()`` was ever literally
    added to a label) or ``concept`` is literally in ``node``'s label.
    """
    return isinstance(concept, Top) or concept in branch.label[node]


def _concept_neighbours(branch: _Branch, rbox: _RBox, x: _Node, role: str,
                         concept: Concept) -> List[_Node]:
    """Every ``role``-neighbour of ``x`` (role-hierarchy-aware) that is in ``concept``."""
    return [y for y in _role_neighbours(branch, rbox, x, role) if _in_concept(branch, y, concept)]


def _marked_distinct(branch: _Branch, a: _Node, b: _Node) -> bool:
    """True iff ``a`` and ``b`` are FORCED distinct on this branch."""
    return a != b and frozenset((a, b)) in branch.distinct


def _has_pairwise_distinct_subset(branch: _Branch, nodes: List[_Node], k: int) -> bool:
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


def _merge_order(branch: _Branch, a: _Node, b: _Node) -> Tuple[_Node, _Node]:
    """Return ``(keep, drop)`` for merging ``a``, ``b``: keep the NON-blockable
    (named/root) node when exactly one of the two is blockable, else keep whichever
    was added to the branch first (see the module docstring's ≤-rule description).
    """
    a_blockable, b_blockable = isinstance(a, _Generated), isinstance(b, _Generated)
    if a_blockable != b_blockable:
        return (b, a) if a_blockable else (a, b)
    return (a, b) if branch.order.index(a) < branch.order.index(b) else (b, a)


def _merge(branch: _Branch, keep: _Node, drop: _Node) -> None:
    """Merge ``drop`` into ``keep`` in place: redirect every edge (positive and
    negative), union the labels, re-parent every distinctness pair, and remove
    ``drop``.

    A no-op when ``keep == drop`` — defense in depth against a degenerate
    self-pair reaching this far (see ``_role_neighbours``'s docstring): merging a
    node into itself has nothing to redirect and must NOT fall through to
    ``del branch.label[drop]``, which would delete a node that ``keep`` (the same
    node) still needs.

    A distinctness pair that COLLAPSES onto one node (both endpoints become
    ``keep``) sets ``branch.self_distinct``, which :func:`_clash` already reads:
    the branch now says one element is distinct from itself, and ``a ≠ a`` has
    no model. Until 0.30.0 the pair was DROPPED instead. That was unreachable
    from the ≤-rule — which only ever merges a pair it has already checked is
    NOT marked distinct, and ``a2 == b2`` can then only happen for the merged
    pair itself — but :func:`abox_consistent`'s same-individual merging is a
    second caller that does not check, so ``assert_same(a, b)`` together with
    ``assert_distinct(a, b)`` would otherwise be reported CONSISTENT while its
    own FOL image ``a = b ∧ a ≠ b`` is refutable. (Exactly the asymmetry
    :meth:`_Branch.mark_distinct` was given in 0.30.0, for the same reason.)
    ``tests/test_dl_abox_identity.py`` has both halves: the new verdict, and a
    ≤-rule control proving this branch is still not reachable from there.
    """
    if keep == drop:
        return
    branch.label[keep] |= branch.label[drop]
    branch.edges = _OrderedSet((keep if s == drop else s, r, keep if d == drop else d)
                               for (s, r, d) in branch.edges)
    # The FORBIDDEN edges travel with the node exactly as the real ones do, so
    # `assert_same(b, c)` + `r(a, c)` + `¬r(a, b)` clashes after the merge.
    branch.negative_edges = {
        (keep if s == drop else s, r, keep if d == drop else d)
        for (s, r, d) in branch.negative_edges}
    new_distinct = set()
    for pair in branch.distinct:
        a, b = tuple(pair)
        a2, b2 = (keep if a == drop else a), (keep if b == drop else b)
        if a2 != b2:
            new_distinct.add(frozenset((a2, b2)))
        else:
            branch.self_distinct = True
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
    """A role is SIMPLE iff no COMPOSITE role (itself included) entails it via ⊑*.

    COMPOSITE is OWL 2's own notion (Structural Specification §11): a role
    declared transitive, or the super-role of a property chain. The ⊑*
    direction is the one to get right — a composite SUB-role is what makes the
    super-role non-simple (``r' ⊑* role`` for composite ``r'``), and reading it
    the other way round silently readmits a combination that is undecidable
    (Horrocks, Sattler & Tobies 1999). See the module docstring.
    """
    return not any(role in rbox.ancestors(composite) for composite in rbox.composite)


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


def _check_simple_role_box(tbox: TBox, rbox: _RBox) -> None:
    """Raise :class:`NonSimpleRoleError` if a role-box axiom OWL 2 restricts to
    SIMPLE roles targets a NON-SIMPLE one (see :data:`_SIMPLE_ROLE_AXIOMS` for
    the kinds and the module docstring for why simplicity is what makes the
    three edge-pattern clash conditions EXACT).

    Runs BEFORE :func:`_check_simple_roles` so that, for instance,
    ``FunctionalObjectProperty(P)`` on a transitive ``P`` is refused with a
    message naming ``FunctionalObjectProperty`` rather than with the generic
    "qualified number restriction on role 'P'" — the caller never wrote a
    number restriction, the internalisation in ``_new_branch`` did.
    """
    for field_name, kind, shape in _SIMPLE_ROLE_AXIOMS:
        stored = getattr(tbox, field_name)
        roles = sorted({role for entry in stored for role in entry}
                       if shape == "pair" else set(stored))
        for role in roles:
            if _is_simple_role(role, rbox):
                continue
            raise NonSimpleRoleError(
                f"dl.tableau: {kind}({role!r}) is not allowed: {role!r} is "
                f"NON-SIMPLE — it is COMPOSITE (declared transitive, or the "
                f"super-role of a property chain), or a composite role entails "
                f"it via the role hierarchy. OWL 2 (Structural Specification "
                f"§11) restricts {kind} — and every other axiom in "
                f"{', '.join(k for _, k, _ in _SIMPLE_ROLE_AXIOMS if k != kind)}, "
                f"and every qualified number restriction — to SIMPLE roles, "
                f"because the combination with transitivity is undecidable "
                f"(Horrocks, Sattler & Tobies 1999). This tableau's clash "
                f"conditions are also only EXACT on a simple role, where the "
                f"relation a saturated branch entails is the one-step "
                f"⊑*-closure of its own edges. Declare the characteristic on a "
                f"SIMPLE sub-role instead, or decide this knowledge base with "
                f"dl.owl_reasoner's external, HermiT-backed reasoner or with "
                f"dl.kb_to_fol(tbox, abox) + api.prove.")


def _non_simple_edge_message(what: str, role: str) -> str:
    """The refusal for the construct that needs to SEE a forbidden edge: a
    negative role assertion.

    It is decided by a clash condition over the branch's own edges, and the
    tableau never MATERIALISES a transitive role's derived edges — the ∀+-rule
    propagates the restriction along the chain instead (see "Role hierarchies
    and transitive roles (RBox)"). So on a non-simple role a two-step path
    ``x —r→ m —r→ y`` entails ``r(x, y)`` in every model while leaving the
    branch with no edge for the condition to find, and the verdict would be
    "consistent" for a knowledge base with no model. Refusing by name is the
    only honest answer.
    """
    return (
        f"dl.tableau: {what} is not allowed: {role!r} is NON-SIMPLE — it is "
        f"COMPOSITE (declared transitive, or the super-role of a property "
        f"chain), or a composite role entails it via the role hierarchy. This "
        f"refusal is about SEEING a forbidden edge: the tableau never "
        f"materialises a transitive role's derived edges (its ∀+-rule "
        f"propagates the RESTRICTION along the chain instead — see 'Role "
        f"hierarchies and transitive roles (RBox)' in dl.tableau's module "
        f"docstring), so a two-step {role!r}-path x → m → y entails "
        f"{role!r}(x, y) in every model while leaving the branch with no edge "
        f"for the clash condition to find, and the verdict would be "
        f"'consistent' for a knowledge base with no model. An ordinary "
        f"(positive) role assertion stays supported on a transitive role — one "
        f"edge is all it needs. "
        f"Declare the axiom on a SIMPLE sub-role instead, or ask the question "
        f"of the FOL image with dl.kb_to_fol(tbox, abox) and api.prove, or "
        f"decide the knowledge base with dl.owl_reasoner's external, "
        f"HermiT-backed reasoner.")


def _check_simple_negative_role_assertions(abox: Optional[ABox],
                                           rbox: _RBox) -> None:
    """Raise :class:`NonSimpleRoleError` if a negative role assertion in ``abox``
    targets a non-simple role (see :func:`_non_simple_edge_message`).
    """
    if abox is None:
        return
    for role in sorted({role for _, _, role in abox.negative_role_assertions}):
        if not _is_simple_role(role, rbox):
            raise NonSimpleRoleError(_non_simple_edge_message(
                f"NegativeObjectPropertyAssertion({role!r} a b)", role))


def _reject_role_box(tbox: Optional[TBox], abox: Optional[ABox]) -> None:
    """The axiom-level half of both entry points' preamble, in ONE place:
    refuse every axiom KIND no in-house rule decides, then refuse an inverse
    role inside a role inclusion (a condition on the stored VALUE, which no
    table row can express).

    Called as the FIRST statement of :func:`concept_satisfiable`,
    :func:`abox_consistent` and ``classify``, and by :func:`_reject_inputs` for
    the entry points that can return without reaching either; the rest of the
    reasoning API reduces to those two and inherits it (see
    :func:`_reject_unsupported`).

    Deliberately does NOT build the branch: ``_new_branch`` calls
    :meth:`TBox.internalized`, which calls ``nnf`` — and ``nnf`` refuses a
    bare :class:`~unicode_logic_kit.dl.concepts.Nominal` with its own
    ``TypeError``. :func:`_reject_beyond_alc` has to run over the TBox
    inclusions first, so it is the one that produces the precise
    :class:`UnsupportedConceptError` (see ``tests/test_dl_alc.py``'s
    I/O-refusal battery, which covers a nominal nested in an inclusion).

    It starts with the VALUE-level checks, so that a knowledge base that is not
    well-formed is refused as such before anything is said about its kinds:
    every stored role-box and data-box entry is a usable name
    (:func:`_validate_role_box` — the SAME validation
    :func:`~unicode_logic_kit.dl.translate.rbox_to_fol` runs, so a ``TBox`` built
    through the dataclass constructor or mutated in place is refused by both
    routes and not answered by one) and every ABox assertion's property is one
    (:func:`_reject_abox_roles`: an OWL 2 built-in name is NOT an ordinary
    role, and treating it as one — which every route did for an ABox
    assertion — answers a different question).
    """
    if tbox is not None:
        _validate_role_box(tbox, where="dl.tableau")
        _validate_data_box(tbox, where="dl.tableau")
    _reject_abox_roles(abox, where="dl.tableau")
    _reject_unsupported(tbox, abox)
    if tbox is not None:
        _reject_inverse_role_inclusions(tbox)


def _tbox_class_expressions(tbox: Optional[TBox]) -> List[Concept]:
    """Every class expression ``tbox`` stores — both sides of each concept
    inclusion and the filler of each domain and range axiom — which is what
    :func:`_reject_beyond_alc` has to see for the tableau to be allowed to
    start (a data-property domain filler is left out: the data box is refused
    as a whole by :func:`_reject_unsupported`)."""
    if tbox is None:
        return []
    found: List[Concept] = []
    for sub, sup in tbox.inclusions:
        found += [sub, sup]
    for _role, filler in tbox.role_domains + tbox.role_ranges:
        found.append(filler)
    return found


def _reject_inputs(tbox: Optional[TBox], abox: Optional[ABox],
                   concepts: Iterable[Concept] = ()) -> None:
    """The WHOLE shared guard, for an entry point that may never reach
    :func:`concept_satisfiable`/:func:`abox_consistent`: :func:`_reject_role_box`,
    then :func:`_reject_beyond_alc` over ``concepts`` and over every class
    expression ``tbox`` and ``abox`` store.

    Two entry points reduce to the two guarded ones only WHEN THERE IS
    SOMETHING TO REDUCE: ``realize`` with an empty vocabulary, ``realize_all``
    and ``instance_retrieval`` on an empty ABox, ``classify`` with fewer than
    two names all return without a single ``instance_check``/``subsumes`` call,
    and so without the guard having run — a knowledge base carrying a refused
    kind got a quiet ``[]`` where every other entry point raised. Those call
    this at their top instead of relying on the reduction.
    """
    _reject_role_box(tbox, abox)
    for concept in concepts:
        _reject_beyond_alc(concept)
    for concept in _tbox_class_expressions(tbox):
        _reject_beyond_alc(concept)
    if abox is not None:
        for _individual, concept in abox.concept_assertions:
            _reject_beyond_alc(concept)


def _has_value_message(concept: HasValue) -> str:
    """The refusal for a value restriction ``∃r.{a}`` (OWL's ``ObjectHasValue``),
    worded like the :class:`~unicode_logic_kit.dl.concepts.Nominal` refusal it
    shares :func:`_reject_beyond_alc` with: it names the construct, says why it
    is outside what subset blocking decides, and names the routes that DO decide
    it — only ones that work (the FOL image, and every ``dl.external_*`` entry
    point, which translates a value restriction as owlready2's
    ``prop.value(individual)``).
    """
    inverse = ""
    if isinstance(concept.role, InverseRole):
        inverse = (f" Its role is also an InverseRole ({concept.role.role}⁻) — "
                   "the I of SHIQ, a second reason it is outside ALCHQ (see "
                   "the module docstring's 'Inverse roles and nominals (I, O)' "
                   "section).")
    return (
        f"dl.tableau: the value restriction HasValue ({concept.to_unicode()}, "
        f"OWL's ObjectHasValue) is outside ALCHQ (this kit's in-house DL "
        f"fragment) — no in-house tableau rule decides it. It is a NOMINAL: it "
        f"names the individual {concept.individual!r} inside a concept, and a "
        f"nominal gives a generated node an edge BACK to a named one, which the "
        f"subset blocking this tableau terminates by does not cover — a "
        f"blocked node never receives that edge, so a clash the edge would "
        f"complete (asymmetry, irreflexivity, …) is never seen and the "
        f"verdict could be 'satisfiable' for a knowledge base with no model "
        f"(see 'Value restrictions (ObjectHasValue)' in the module docstring "
        f"for the two-axiom counterexample). Decide it with the FOL image — "
        f"dl.kb_to_fol(tbox, abox) and api.prove — or with dl.owl_reasoner's "
        f"external, HermiT-backed reasoner (dl.external_*).{inverse}")


def _reject_beyond_alc(concept: Concept) -> None:
    """Raise :class:`UnsupportedConceptError` if ``concept`` (recursively) contains
    a :class:`~unicode_logic_kit.dl.concepts.Nominal`, a
    :class:`~unicode_logic_kit.dl.concepts.HasValue` (a nominal in disguise — see
    "Value restrictions (ObjectHasValue)" in the module docstring) or an
    :class:`~unicode_logic_kit.dl.concepts.InverseRole`-valued ``role`` field — the
    **I**/**O** beyond this tableau's **ALCHQ** fragment (see "Inverse roles and
    nominals (I, O)" in the module docstring). Called on the query concept plus
    every TBox inclusion by :func:`concept_satisfiable`, and on every ABox concept
    assertion plus every TBox inclusion by :func:`abox_consistent` — BEFORE either
    builds a branch, so the tableau never even starts on an unsupported concept.
    ``instance_check``/``subsumes``/``equivalent`` need no call of their own:
    they reduce to these two, so they inherit this guard through whichever one
    they call. ``instance_retrieval``/``realize``/``realize_all``/``classify``
    reach it through :func:`_reject_inputs` instead, because with nothing to
    reduce (an empty ABox, vocabulary or name list) there is no call to inherit
    it from.
    """
    if isinstance(concept, Nominal):
        raise UnsupportedConceptError(
            f"dl.tableau: Nominal concepts ({{{concept.individual}}}) are outside "
            "ALCHQ (this kit's in-house DL fragment) — no in-house tableau rule "
            "decides them. Use dl.owl_reasoner's external, HermiT-backed reasoner "
            "instead.")
    if not isinstance(concept, DATA_CONCEPTS):
        # An OWL 2 built-in property name (or an equality name, or no name at
        # all) as the role of THIS node. A data restriction is refused as a
        # whole below, with its own, more fundamental message.
        _reject_concept_role(concept, where="dl.tableau")
    if isinstance(concept, (Top, Bottom, Atomic)):
        return
    if isinstance(concept, Not):
        _reject_beyond_alc(concept.concept)
    elif isinstance(concept, HasValue):
        # A nominal in disguise: refused exactly as a bare Nominal is (see
        # "Value restrictions (ObjectHasValue)" in the module docstring for the
        # counterexample). Reached AFTER _reject_concept_role above, so a
        # value restriction over an OWL 2 built-in property keeps its more
        # specific refusal.
        raise UnsupportedConceptError(_has_value_message(concept))
    elif isinstance(concept, (And, Or)):
        _reject_beyond_alc(concept.left)
        _reject_beyond_alc(concept.right)
    elif isinstance(concept, (Exists, ForAll, AtLeast, AtMost)):
        _reject_inverse_role_field(concept.role)
        _reject_beyond_alc(concept.concept)
    elif isinstance(concept, DATA_CONCEPTS):
        raise UnsupportedConceptError(
            f"dl.tableau: the data restriction {type(concept).__name__} "
            f"({concept.to_unicode()}) is outside ALCHQ (this kit's in-house DL "
            f"fragment): {_DATA_NOTE}. Ask the FOL image — "
            f"kb = dl.kb_to_fol(tbox, abox, query=[concept]), then "
            f"api.prove(kb.unsatisfiability_goal(concept), kb.tbox_premises) "
            f"(kb.subsumption_goal and kb.instance_goal ask the other two "
            f"questions). 'proved' transfers to OWL 2 and 'refuted' does not "
            f"(see kb.refutation_is_decisive: the image is sound, not "
            f"complete). A facet entailment over the data ranges alone is "
            f"decided by atp.z3_arith.")
    else:
        raise TypeError(f"_reject_beyond_alc: unsupported concept {type(concept).__name__}")


def _reject_inverse_role_field(role) -> None:
    """Raise :class:`UnsupportedConceptError` if a concept's ``role`` field holds
    an :class:`~unicode_logic_kit.dl.concepts.InverseRole` — the **I** of SHIQ.

    One function rather than the same four lines in each branch of
    :func:`_reject_beyond_alc`, so a concept kind that gains a ``role`` field
    later refuses it with the SAME message rather than a near-copy.
    """
    if isinstance(role, InverseRole):
        raise UnsupportedConceptError(
            f"dl.tableau: an InverseRole ({role.role}⁻) is outside "
            "ALCHQ (this kit's in-house DL fragment) — no in-house tableau "
            "rule decides it (see the module docstring's 'Inverse roles and "
            "nominals (I, O)' section for why: it breaks subset blocking's "
            "soundness/completeness argument). Use dl.owl_reasoner's "
            "external, HermiT-backed reasoner instead.")


def _new_branch(tbox: Optional[TBox]):
    """Return ``(branch, tbox_concepts, rbox)`` for a fresh tableau under ``tbox``.

    ``rbox`` is precomputed once here (not per completion-rule application) because
    it derives entirely from the static role box and is invariant across the whole
    tableau expansion — see ``_RBox``.

    ``tbox_concepts`` is ``TBox.internalized()`` PLUS one ``≤1 P.⊤`` per
    functional role: ``FunctionalObjectProperty(P)`` is exactly the GCI
    ``⊤ ⊑ ≤1 P.⊤``, and this is the single place both
    :func:`concept_satisfiable` and :func:`abox_consistent` take the
    internalised list from — and the one the ∃- and ≥-rules copy onto every
    freshly generated node, so functionality reaches generated individuals too
    with no further edit. Added HERE rather than in :meth:`TBox.internalized`,
    which stays exactly the image of ``inclusions`` (see its docstring).
    Sorted, so the list is deterministic despite ``functional_roles`` being a
    ``set``.

    The domain and range axioms join it here for the same reason, and are the
    same kind of thing: ``ObjectPropertyDomain(P C)`` IS the GCI ``∃P.⊤ ⊑ C``,
    whose internalisation ``nnf(¬∃P.⊤ ⊔ C)`` reduces to ``∀P.⊥ ⊔ C`` — "either
    no ``P``-successor at all, or in ``C``". ``ObjectPropertyRange(P C)`` is
    ``⊤ ⊑ ∀P.C``, internalised as ``nnf(∀P.C)`` directly rather than as
    ``nnf(¬⊤ ⊔ ∀P.C)``: the two are semantically identical (both force the
    concept on every element, which is what this list means), but the literal
    ``Or`` form produces ``⊥ ⊔ ∀P.C``, and the ⊔-rule would then open a dead
    branch on the ``⊥`` disjunct at every node for every range axiom — 108
    pointless binary branchings per node on the OEO ontology. The DOMAIN form
    keeps its genuine disjunction, which is unavoidable.

    Neither needs a completion rule, so subset blocking's termination argument
    is untouched, and neither introduces an ``AtLeast``/``AtMost``, so
    ``_check_simple_role_box`` is unaffected and a domain or range axiom on a
    transitive role stays legal.
    """
    if not tbox:
        return _Branch(), [], _EMPTY_RBOX
    tbox_concepts = tbox.internalized()
    tbox_concepts += [nnf(AtMost(1, role, Top()))
                      for role in sorted(tbox.functional_roles)]
    tbox_concepts += [nnf(Or(Not(Exists(role, Top())), concept))
                      for role, concept in tbox.role_domains]
    tbox_concepts += [nnf(ForAll(role, concept))
                      for role, concept in tbox.role_ranges]
    return _Branch(), tbox_concepts, _RBox.from_tbox(tbox)


def concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox``.

    Satisfiable means some model places an individual in the concept while obeying
    every TBox axiom (including its RBox — role hierarchy and transitivity
    declarations, see "Role hierarchies and transitive roles (RBox)" in the module
    docstring). ``tbox=None`` is the empty TBox (pure concept satisfiability).

    Raises:
        UnsupportedAxiomError: ``tbox`` carries an axiom KIND no in-house rule
            decides — see "The axiom-kind table" in the module docstring. This
            guard runs first, before any concept is even looked at.
        UnsupportedConceptError: ``concept``, a TBox inclusion or a domain/range
            filler contains a Nominal, a HasValue (a nominal in disguise) or an
            InverseRole-valued role — see "Inverse roles and nominals (I, O)" and
            "Value restrictions (ObjectHasValue)" in the module docstring.
        NonSimpleRoleError: a role-box axiom OWL 2 restricts to simple roles, or a
            number restriction, targets a non-simple role.
        RoleExpressionError: a stored role-box entry is not a usable role (a
            ``TBox`` assembled by hand), or ``concept`` / an inclusion uses an
            OWL 2 built-in property name (``owl:topObjectProperty`` …) or a role
            called ``=`` as the role of a restriction — an ordinary role of that
            name would be a different restriction, with a different verdict.

    The anonymous root node is called ``"_root"``, not ``"a"``: it stands for
    "SOME element", existentially quantified, whereas an individual name denotes
    a FIXED one, so a root that carried such a name would add an equation the
    query never stated. (No concept of this fragment names an individual — a
    :class:`~unicode_logic_kit.dl.concepts.HasValue` is refused — so no collision
    is reachable here; the name is kept, and is not ``"a"``, so that none can
    become reachable by accident.) The root is a named node (a ``str``), not a
    :class:`_Generated` one, so :func:`_blocked` never blocks it and it never
    blocks, exactly as it never did under the old name.
    """
    _reject_role_box(tbox, None)
    _reject_beyond_alc(concept)
    if tbox is not None:
        for sub, sup in tbox.inclusions:
            _reject_beyond_alc(sub)
            _reject_beyond_alc(sup)
        # A domain/range filler is an ordinary class expression, so a Nominal, a
        # HasValue or an InverseRole can hide in one exactly as in an inclusion
        # -- and it reaches the tableau through _new_branch's internalisation.
        for _role, filler in tbox.role_domains + tbox.role_ranges:
            _reject_beyond_alc(filler)
    branch, tbox_concepts, rbox = _new_branch(tbox)
    if tbox is not None:
        _check_simple_role_box(tbox, rbox)
    _check_simple_roles([concept] + tbox_concepts, rbox)
    branch.add_node(_ROOT_NAME)
    branch.label[_ROOT_NAME].update(tbox_concepts)
    branch.label[_ROOT_NAME].add(nnf(concept))
    return _solve(branch, tbox_concepts, rbox, _Ctx(MAX_STEPS))


#: The anonymous root's name in :func:`concept_satisfiable`. A named node (a
#: ``str``), so :func:`_blocked` leaves it alone, which is the behaviour the
#: root has always had. No individual can share the name: the branch of
#: :func:`concept_satisfiable` holds the root and its witnesses and nothing
#: else, because a concept of this fragment names no individual (a
#: :class:`~unicode_logic_kit.dl.concepts.HasValue` is refused), and a witness is
#: a :class:`_Generated`, which equals no string.
_ROOT_NAME = "_root"


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
    """The individual names mentioned in ``abox`` (any assertion kind).

    Read off :data:`_AXIOM_KINDS`' ``individual_positions`` via
    :func:`_abox_individual_names`, so an assertion kind added later is
    included here by its table row alone.

    An ABox with no named individuals at all falls back to the single anonymous
    individual ``"a"``, matching :func:`abox_consistent`'s own convention that an
    empty ABox is trivially consistent (some individual exists, it just carries
    no assertions). That fallback is the ONE thing this differs in from
    :func:`~unicode_logic_kit.dl.translate._abox_individuals`, which must not
    invent a constant no assertion ever named.

    It is for :func:`abox_consistent` ONLY — the node the TBox has to run on.
    The two sweeps over "the individuals of the knowledge base",
    :func:`instance_retrieval` and :func:`realize_all`, read
    :func:`_abox_individual_names` instead: the anonymous node is not one of
    them, and reporting it as a member (``{"a"}`` for ``TBox().add(Top(), A)``
    and an empty ABox) answered about an individual nobody named.
    """
    return _abox_individual_names(abox) or {"a"}


def abox_consistent(abox: ABox, tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` is consistent (has a model).

    Raises:
        UnsupportedAxiomError: ``tbox`` or ``abox`` carries an axiom KIND no
            in-house rule decides — see "The axiom-kind table" in the module
            docstring. This guard runs first, before any concept is looked at.
        UnsupportedConceptError: an ABox concept assertion, a TBox inclusion or
            a domain/range filler contains a Nominal, a HasValue (a nominal in
            disguise) or an InverseRole-valued role — see "Inverse roles and
            nominals (I, O)" and "Value restrictions (ObjectHasValue)" in the
            module docstring.
        NonSimpleRoleError: a role-box axiom OWL 2 restricts to simple roles, a
            number restriction or a negative role assertion targets a non-simple
            role.
        RoleExpressionError: a stored role-box entry is not a usable role (a
            ``TBox`` assembled by hand), or an ABox assertion / a class
            expression uses an OWL 2 built-in property name
            (``owl:bottomObjectProperty`` …) or a role called ``=`` — read as an
            ordinary role it answers a different question (a pair related by the
            EMPTY property is inconsistent; by an ordinary role it is not).

    Setup order, which is what makes the identity assertions COMPLETE: add
    every node (the ABox's individuals), seed the labels
    with the internalised TBox, add the ABox concept labels, add the role
    edges, add the FORBIDDEN edges, mark the distinctness pairs — and only THEN
    apply the same-individual assertions, closed under the equivalence they
    generate, so ``a = b`` with ``b = c`` collapses all three onto one node.
    Merging before any completion rule runs is the point: there is no later
    moment at which a same-assertion could be discovered.
    """
    _reject_role_box(tbox, abox)
    assertion_concepts = [c for _, c in abox.concept_assertions]
    for concept in assertion_concepts:
        _reject_beyond_alc(concept)
    if tbox is not None:
        for sub, sup in tbox.inclusions:
            _reject_beyond_alc(sub)
            _reject_beyond_alc(sup)
        for _role, filler in tbox.role_domains + tbox.role_ranges:
            _reject_beyond_alc(filler)
    branch, tbox_concepts, rbox = _new_branch(tbox)
    if tbox is not None:
        _check_simple_role_box(tbox, rbox)
    _check_simple_roles(tbox_concepts + assertion_concepts, rbox)
    _check_simple_negative_role_assertions(abox, rbox)
    for ind in sorted(_individuals(abox)):
        branch.add_node(ind)
        branch.label[ind].update(tbox_concepts)
    for ind, concept in abox.concept_assertions:
        branch.label[ind].add(nnf(concept))
    for a, b, role in abox.role_assertions:
        branch.edges.add((a, role, b))
    for a, b, role in abox.negative_role_assertions:
        branch.negative_edges.add((a, role, b))
    for a, b in abox.distinct_assertions:
        branch.mark_distinct(a, b)
    _apply_same_assertions(branch, abox)
    return _solve(branch, tbox_concepts, rbox, _Ctx(MAX_STEPS))


def _apply_same_assertions(branch: _Branch, abox: ABox) -> None:
    """Merge the endpoints of every ``SameIndividual`` assertion onto one node,
    closed under the equivalence relation the assertions generate.

    ``_merge`` is the ≤-rule's own merge, reused rather than reimplemented: it
    redirects every edge (positive and negative), unions the labels and
    re-parents the distinctness pairs, which IS the semantics of "these two
    names denote one element" — including the case where a distinctness pair
    collapses, which it now reports as ``self_distinct`` rather than dropping
    (see :func:`_merge`).

    After a merge the dropped node is GONE from the branch, so a later pair
    naming it is resolved to the surviving node first, through ``alias``. The
    map is LOCAL to this function and not kept on the branch: nothing reads an
    individual name out of a concept any more (a value restriction, the one
    construct that did, is refused — see "Value restrictions
    (ObjectHasValue)" in the module docstring), and edges, forbidden edges and
    distinctness pairs are node-valued, so ``_merge`` rewrites them in place.
    Only this loop meets a name that may already have been merged away, and a
    chain — ``c`` merged into ``b``, then ``b`` into ``a`` — resolves ``c`` to
    ``a``; it terminates because a removed name is never added back.
    ``assert_same(a, a)`` resolves both ends to the same node and is then a
    no-op, as its docstring promises.
    """
    alias: Dict[_Node, _Node] = {}

    def resolve(name: _Node) -> _Node:
        while name in alias:
            name = alias[name]
        return name

    for a, b in abox.same_assertions:
        left, right = resolve(a), resolve(b)
        if left == right:
            continue
        keep, drop = _merge_order(branch, left, right)
        _merge(branch, keep, drop)
        alias[drop] = keep


def instance_check(abox: ABox, individual: str, concept: Concept,
                    tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` entails ``individual : concept``.

    Decided by the ABox-level mirror of :func:`subsumes`'s reduction: entailment
    holds iff asserting the *complement* ``individual : ¬concept`` alongside the
    existing assertions makes the knowledge base inconsistent (every model of the
    KB already puts ``individual`` in ``concept``, so adding ``¬concept`` cannot be
    satisfied). This is open-world: a False result means the KB does not entail
    membership, not that it entails non-membership.

    The probe ABox comes from :meth:`ABox.copy`, not from a field-by-field
    reconstruction: a copy that enumerates fields goes stale the moment a field
    is added, and the failure is SILENT — this function (and
    ``instance_retrieval``/``realize``/``realize_all``, which all reduce to it)
    would answer about a strictly WEAKER knowledge base than
    :func:`abox_consistent` sees on the same ABox. See :meth:`ABox.copy`.
    """
    probe = abox.copy()
    probe.assert_concept(individual, Not(concept))
    return not abox_consistent(probe, tbox)


def instance_retrieval(abox: ABox, concept: Concept, tbox: Optional[TBox] = None) -> Set[str]:
    """Return every individual of ``abox`` that ``(tbox, abox)`` entails is a ``concept``.

    Sweeps :func:`instance_check` over every individual named in ``abox`` — including
    one that appears only inside a role assertion, never a concept assertion.

    An ABox that names NO individual has none to report: the answer is the empty
    set, whatever the TBox says. (This returned ``{"a"}`` for ``TBox().add(Top(),
    A)`` and an empty ABox: :func:`abox_consistent` seeds an anonymous node ``a``
    so that an empty ABox still has an element to run the TBox on, and the sweep
    read that node as if somebody had named it — the FOL route, whose
    ``KnowledgeBaseFOL.individuals`` is ``()``, never did.)

    The shared guard runs FIRST, before the sweep: with no individual to sweep
    there is no :func:`instance_check` to inherit it from (see
    :func:`_reject_inputs`).
    """
    _reject_inputs(tbox, abox, [concept])
    return {ind for ind in sorted(_abox_individual_names(abox))
            if instance_check(abox, ind, concept, tbox)}


def realize(abox: ABox, individual: str, vocabulary: List[Concept],
            tbox: Optional[TBox] = None) -> List[Concept]:
    """Return ``individual``'s most-specific concepts from ``vocabulary``.

    ``vocabulary`` is the caller-supplied list of concepts to classify against —
    realization needs a fixed vocabulary since this reasoner has no persistent
    TBox-signature registry to draw one from automatically (see
    :func:`unicode_logic_kit.dl.classify` for that, over named TBox concepts).

    First keeps only the ``C`` in ``vocabulary`` with ``instance_check(abox,
    individual, C, tbox)``, then drops any ``C`` for which some other kept ``D``
    strictly subsumes it (``D ⊑ C`` holds but ``C ⊑ D`` does not) — the remaining
    antichain is what every OWL reasoner reports as "the" (most specific) types.

    The shared guard runs FIRST: an empty ``vocabulary`` makes the filter below
    call :func:`instance_check` zero times, and a knowledge base carrying a
    refused axiom kind used to get a quiet ``[]`` for it (see
    :func:`_reject_inputs`).
    """
    _reject_inputs(tbox, abox, vocabulary)
    candidates = [c for c in vocabulary if instance_check(abox, individual, c, tbox)]
    return [c for c in candidates
            if not any(subsumes(d, c, tbox) and not subsumes(c, d, tbox) for d in candidates)]


def realize_all(abox: ABox, vocabulary: List[Concept],
                 tbox: Optional[TBox] = None) -> Dict[str, List[Concept]]:
    """Return :func:`realize` for every individual named in ``abox``, keyed by name.

    An ABox that names no individual gives ``{}`` — there is nobody to realize
    (see :func:`instance_retrieval`: the anonymous node :func:`abox_consistent`
    seeds is not an individual of the knowledge base). The shared guard runs
    first, because with nobody to realize :func:`realize` is never called.
    """
    _reject_inputs(tbox, abox, vocabulary)
    return {ind: realize(abox, ind, vocabulary, tbox)
            for ind in sorted(_abox_individual_names(abox))}
