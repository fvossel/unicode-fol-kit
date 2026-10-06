"""The **standard translation** of ALC into first-order logic.

ALC concepts denote unary relations over a domain, and roles denote binary
relations; the standard translation makes this concrete by rendering a
concept ``C`` as a first-order formula ``π(C, x)`` with one free variable
``x`` — "the individual currently under discussion" — such that ``d`` is in
the extension of ``C`` iff ``π(C, x)`` holds under ``x ↦ d``. Concretely:

- ``Atomic("C")``  ↦  ``C(x)``            (the concept becomes a unary predicate)
- ``⊤`` / ``⊥``     ↦  ``x = x`` / ``x ≠ x``  (see "Top and Bottom" below)
- ``¬C``            ↦  ``¬π(C, x)``
- ``C ⊓ D``         ↦  ``π(C, x) ∧ π(D, x)``
- ``C ⊔ D``         ↦  ``π(C, x) ∨ π(D, x)``
- ``∃r.C``          ↦  ``∃y (r(x, y) ∧ π(C, y))``
- ``∀r.C``          ↦  ``∀y (r(x, y) → π(C, y))``
- ``≥n r.C``        ↦  ``∃≥n y (r(x, y) ∧ π(C, y))``   (see "Qualified number restrictions")
- ``≤n r.C``        ↦  ``∃≤n y (r(x, y) ∧ π(C, y))``

with ``y`` a FRESH variable at every restriction, so nested restrictions
(``∃r.(∀s.C)``) never capture an outer variable (see "Variable freshness").
A role ``r`` becomes its own binary predicate ``r(·, ·)`` with no axioms
forced on it, which is exactly why the reduction is faithful: ALC roles are
arbitrary Kripke relations, and an uninterpreted FOL predicate is exactly
that (see also :func:`concept_to_modal` for the single-role reading through
propositional modal K instead of FOL).

Top and Bottom
--------------
The FOL node set has no first-class truth-constant (no ``⊤``/``⊥`` term
that ``Node.to_z3`` renders as Z3's literal ``True``/``False``); the closest
thing is the reserved falsum atom idiom used by :mod:`unicode_fol_kit.atp.fitch`
(``Atom("⊥", ())`` there, but that idiom is *propositional* and only means
something because the Fitch checker special-cases it — it does not carry to
an arbitrary Z3/Prover9/TPTP export, where a bare atom is just another
uninterpreted symbol that could be assigned False in some model). Rendering
``⊤`` as an uninterpreted atom (``P(x) ∨ ¬P(x)`` for some fresh ``P``) is
truth-functionally a tautology but is an ugly, semantically unmotivated
detour through a predicate the concept never mentions.

Instead this module renders ``⊤``/``⊥`` through **equality**, which the FOL
Atom node already treats natively (``Atom("=", …)`` / ``Atom("≠", …)`` map to
Z3's built-in ``==``/``!=``, Prover9's ``=``, TPTP's ``=``/``!=`` — see
``Atom.to_z3``/``to_prover9``/``to_tptp`` in ``fol/_fol_nodes.py``):

- ``⊤``  ↦  ``x = x``   — valid in every model (reflexivity), matching how the
  tableau treats ``⊤``: it never causes a clash and never needs expansion,
  i.e. it constrains nothing and holds of every individual.
- ``⊥``  ↦  ``x ≠ x``   — unsatisfiable in every model, matching how the
  tableau treats ``⊥``: ``x : ⊥`` is *itself* a clash condition (see
  ``_clash`` in :mod:`unicode_fol_kit.dl.tableau`), i.e. no individual can
  satisfy it.

This is the standard textbook rendering, adds no extra symbols to the
signature, and is a genuine validity/unsatisfiability rather than a
model-dependent coincidence.

Variable freshness
-------------------
Each ``∃r.C`` / ``∀r.C`` introduces a bound variable minted by
:func:`~unicode_fol_kit.fol._identifiers.fresh_variables`: one letter plus
digits (``x0``, ``x1``, …), which is the shape the kit's VARIABLE terminal
actually accepts. Until 0.30.0 the name was ``f"{var}_{n}"``, and
``∃x_1 (r(x, x_1) ∧ …)`` is text this kit printed and its own
:func:`unicode_fol_kit.api.parse_any` rejects — the underscore is not part of
the terminal. The letter is the seed name's first character when that is a
legal variable letter on its own and ``x`` otherwise, so an ABox individual
named ``alice`` yields ``x0`` rather than ``alice_1``; the seed name itself is
excluded, so the free variable can never be captured.

A single top-level call (one call to :func:`concept_to_fol`, or one of the two
independent halves of :func:`subsumption_to_fol`) shares ONE minter across its
entire recursive walk, so EVERY restriction anywhere in that call's concept
tree — nested *or* sibling — gets a pairwise-distinct name; in particular no
two restrictions nested along the same path can ever reuse a name, so
``∃r.(∀s.C)`` translates to ``∃x0 (r(x, x0) ∧ ∀x1 (s(x0, x1) → π(C, x1)))``
with no risk of the inner ``∀`` accidentally binding the outer ``∃``'s
variable. Two SEPARATE top-level calls each start their own minter back at
``x0`` and so may independently mint the same name (e.g.
``subsumption_to_fol``'s antecedent and consequent, translated by two
independent calls to the internal translator, may both use ``x0``) — this is
not a capture risk because the two calls' quantifier scopes are siblings under
``→``, not nested inside one another.

Bound variables never share a name with an individual
------------------------------------------------------
``Variable("x")`` and ``Constant("x")`` print the same text and are the SAME
constant to Z3, so a quantifier binding ``x`` would capture an individual
called ``x``: the image of ``∃r.{x} ⊑ A`` printed ``∀x (r(x, x) → A(x))``, and
``api.prove`` over it called a consistent knowledge base inconsistent, while the
tableau (which has no variables to capture) said consistent. The same held for
every FIXED prefix variable — the GCI's ``x``, the role axioms' ``x``/``y``/``z``,
the data axioms' ``x``/``v``/``w`` — not only the minted ones. So EVERY bound
variable of an image avoids EVERY individual of the knowledge base: a prefix
variable that clashes is renamed (:func:`_binder_names`, to the first free
``letter + digits`` — exact, being alpha-equivalence), consistently across all
the axioms of one :func:`kb_to_fol` call, and the minted ones avoid the renamed
names too. The one variable that is FREE, :func:`concept_to_fol`'s ``var``, is
the caller's own and so is refused on a clash instead of renamed.

Qualified number restrictions
------------------------------
``AtLeast``/``AtMost`` (≥n r.C / ≤n r.C — see :mod:`unicode_fol_kit.dl.tableau`'s
"Qualified number restrictions" section for the tableau side of ALCQ) route through
the EXISTING :class:`~unicode_fol_kit.fol.nodes.Count` node rather than a new
counting encoding written here: ``≥n r.C`` becomes ``Count("ge", Number(n), y,
r(x, y) ∧ π(C, y))`` and ``≤n r.C`` becomes the same with ``"le"``. ``Count`` already
carries a tested standard "distinct witnesses" first-order expansion
(:meth:`~unicode_fol_kit.fol.nodes.Count._expand`, bounded at ``n ≤ 500`` — see that
class's docstring) that :meth:`Count.to_z3` lowers through automatically, so this is
exactly the independent (Z3-backed) differential oracle
``tests/test_dl_alcq.py`` cross-checks the tableau against, the same role
:func:`rbox_to_fol` plays for the RBox extension above. The counting variable ``y``
is minted by the SAME ``fresh()`` counter as every other restriction (see "Variable
freshness"), so a number restriction nested inside — or sibling to — an ordinary
∃/∀ still gets a pairwise-distinct name throughout one top-level call.

Multi-role concepts and modal K
--------------------------------
ALC is exactly multi-modal K: an ``∃r.C``/``∀r.C`` pair over a *single* role
``r`` is precisely ``◇C``/``□C`` in ordinary (single-relation) modal K. This
is what :func:`concept_to_modal` implements, generalising the single-role
``_to_modal`` test helper in ``tests/test_dl_alc.py`` from a hardcoded role to
any single role name. It genuinely cannot go further: propositional modal K
has exactly ONE accessibility relation, so a concept using two or more
*distinct* role names has no faithful Box/Diamond rendering — encoding role
identity into, say, an indexed modality (``Knows(Constant(role), …)``) would
silently reinterpret the DL role as an epistemic agent, which is a different
logic with different validities (KT45 vs K). :func:`concept_to_modal`
therefore raises :class:`NotImplementedError` for multi-role concepts and
points callers at :func:`concept_to_fol`, which has no such limitation — a
role is just another predicate name, so FOL scales to any number of roles
for free.

GCIs, TBoxes, ABoxes
---------------------
:func:`subsumption_to_fol` renders a general concept inclusion ``sub ⊑ sup``
as its universal closure ``∀x (π(sub, x) → π(sup, x))`` — the standard
reduction, matching :func:`unicode_fol_kit.dl.tableau.subsumes`'s own
``sub ⊓ ¬sup`` unsatisfiability reduction (they are interderivable: ``sub ⊑
sup`` iff ``∀x (π(sub,x) → π(sup,x))`` is valid iff ``π(sub,x) ∧ ¬π(sup,x)``
is unsatisfiable). :func:`tbox_to_fol` conjoins one such closure per GCI in a
:class:`unicode_fol_kit.dl.tableau.TBox`; :func:`abox_to_fol` renders a
:class:`unicode_fol_kit.dl.tableau.ABox`'s concept assertions (``a : C`` ↦
``π(C, a)`` with the individual ``a`` as a FOL *constant*, not a variable —
this matters for the ASCII-only Prover9/TPTP exporters, which uppercase
``Variable`` names into their variable syntax but leave ``Constant`` names
alone) and role assertions (``(a, b) : r`` ↦ ``r(a, b)``), conjoined
together. An empty TBox/ABox translates to the same equality tautology used
for ``⊤`` (over a nullary placeholder constant, since there is no ``x`` in
scope at that point) — vacuously true, matching "no axioms" / "no
assertions" imposing no constraint.

An upper-case individual name is a DOCUMENTED LIMIT of the printed text
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The kit decides predicate-versus-term by the first character's ``isupper()``
(see ``fol/_identifiers.py``'s "WHY THE FIRST CHARACTER DECIDES PREDICATE VS.
TERM"), so in the first-order grammar there is NO spelling of a
:class:`~unicode_fol_kit.fol.nodes.Constant` whose name starts upper-case. An
OWL individual, however, is an IRI or a label, where capitals are the norm —
in the OEO ontology every one of the 98 ``ObjectHasValue`` fillers and all 8
identity-axiom individuals start with one. So the text this module prints for
such an individual does not read back as the same formula, in two different
ways:

* in EQUALITY position (``abox_to_fol`` of an ``assert_same``/
  ``assert_distinct``, or a ``Nominal``) it does not parse at all —
  ``Alice = Bob`` is reported as ``Invalid predicate 'Alice'``;
* in ARGUMENT position (a role assertion, or a
  :class:`~unicode_fol_kit.dl.concepts.HasValue` image) it DOES parse, but as
  a DIFFERENT formula: only the third-order dialect accepts
  ``HasStateOfMatter(x, Liquid)``, and it reads ``Liquid`` as a
  ``PredicateTerm``, not a ``Constant``.

This is written down rather than worked around, and the two alternatives were
both rejected. Refusing the name would turn 103 OEO axioms into exceptions
over a spelling while the AST is perfectly sound (all of their images are
accepted by the Z3 backend). Renaming on print is wrong for the reason
``tests/test_printed_text_reads_back.py`` already gives for a lower-case role:
the name is the CALLER's vocabulary, not one the translation minted, and
rewriting ``Liquid`` to ``liquid`` would make the printed formula stop naming
the OWL individual. The ``dl`` route that never goes through text —
``dl.abox_consistent``/``dl.instance_check`` over the tableau, and
``api.prove`` over the ``kb_to_fol`` NODES rather than their printed form — is
unaffected, and is the route to use. The two forms of the limit are asserted
in ``tests/test_printed_text_reads_back.py``.

Inverse roles and nominals (I, O)
------------------------------------
Unlike :mod:`unicode_fol_kit.dl.tableau` (which refuses both by name — see
that module's "Inverse roles and nominals (I, O)" section), the standard
translation to FOL has no trouble with either, so this module TRANSLATES
them rather than refusing them:

- :class:`~unicode_fol_kit.dl.concepts.InverseRole` (``r⁻``), used as a
  restriction's ``role`` field, swaps the translated role atom's argument
  order: ``∃r⁻.C`` ↦ ``∃y (r(y, x) ∧ π(C, y))`` and ``∀r⁻.C`` ↦
  ``∀y (r(y, x) → π(C, y))`` (and likewise for ``AtLeast``/``AtMost``'s
  ``Count`` matrix) — exactly the FOL reading of "an r-predecessor", the
  standard translation of an inverse role (Baader et al., *DL Handbook*,
  Ch. 2). This is a one-line change confined to the atom's argument order;
  everything else about the restriction (the quantifier, the ``Count``
  encoding for ``AtLeast``/``AtMost``) is untouched.
- :class:`~unicode_fol_kit.dl.concepts.Nominal` (``{a}``) ↦ ``x = a``, with
  ``a`` rendered as the same kind of term ``concept_to_fol``'s own ``term``
  argument already is (a :class:`~unicode_fol_kit.fol.nodes.Variable` when
  translating a bare concept, a :class:`~unicode_fol_kit.fol.nodes.Constant`
  when translating an ABox assertion via :func:`abox_to_fol` — see "GCIs,
  TBoxes, ABoxes" above for why that distinction matters) — the textbook
  reading of a nominal as "the singleton set named by the individual ``a``"
  (Baader et al., *DL Handbook*, Ch. 2's "individual-generated" theories).
  This is genuinely a NEW predicate-free case, not a reuse of an existing
  branch (unlike ⊤/⊥, which reuse equality — see "Top and Bottom" above —
  a nominal names a SPECIFIC individual, not a tautology/contradiction).
- :class:`~unicode_fol_kit.dl.concepts.HasValue` (``∃r.{a}``) ↦ the ground
  atom ``r(x, a)``, NOT ``∃y (r(x, y) ∧ y = a)``. The two are the same
  formula: ``y`` occurs only inside that conjunction, so one-point elimination
  of the equality-bounded existential is a FOL validity. The reduced form is
  the one rendered because it mints no variable and puts the individual in the
  argument position OWL's own reading puts it in. The in-house tableau does NOT
  decide a value restriction (it refuses it by name; see "Value restrictions
  (ObjectHasValue)" in :mod:`unicode_fol_kit.dl.tableau`): this image with
  ``api.prove``, and ``dl.external_*``, are what decide it.

Both directions of this translation are differentially tested (see
``tests/test_dl_alc.py``): concept satisfiability/entailment against the
tableau where a genuinely independent second route exists (none does here —
these constructs are precisely what the tableau refuses — so the check runs
the OTHER direction instead, against a bounded FOL model finder/solver on the
emitted formula itself, per this kit's translation-faithfulness convention).

:func:`concept_to_modal` (single-role propositional K) is a DIFFERENT story:
propositional K has no converse modality and no nominal/naming construct at
all (that is HYBRID logic, a strictly different formalism this kit does not
implement), so it explicitly REFUSES both, by name, rather than attempt an
unfaithful encoding — see its own docstring.

RBoxes
------
:func:`rbox_to_fol` renders a :class:`~unicode_fol_kit.dl.tableau.TBox`'s RBox
(role inclusions and transitivity declarations — see "Role hierarchies and
transitive roles (RBox)" in :mod:`unicode_fol_kit.dl.tableau`'s module
docstring) the same way :func:`tbox_to_fol` renders its concept-level GCIs: a
role inclusion ``r ⊑ s`` becomes its universal closure ``∀x,y (r(x,y) →
s(x,y))`` and a transitivity declaration ``Trans(r)`` becomes ``∀x,y,z
(r(x,y) ∧ r(y,z) → r(x,z))``, all conjoined together. This is the reduction
the tableau's ∀-rule generalisation (RBox rule H) and ∀+-rule (RBox rule S)
implement as completion-graph propagation, so ``subsumption_to_fol(C, D)`` being
entailed by the premises ``tbox_to_fol(tbox, concept_inclusions_only=True)`` and
``rbox_to_fol(tbox)`` is the independent, structurally unrelated cross-check this
module's differential test battery runs through the kit's backends against
``tableau.subsumes(C, D, tbox)``.

The data layer: a guarded ONE-sorted image
--------------------------------------------
OWL 2 has two disjoint domains, the object domain ``Δ_I`` and the data domain
``Δ_D`` (see :mod:`unicode_fol_kit.dl.datatypes`). The image of the data layer
is plain first-order logic with two reserved unary predicates, ``OwlThing`` and
``OwlData``, NOT the kit's many-sorted logic: a sorted constant must be
lower-case and every OEO individual and literal is CamelCase, and many-sorted
logic here is only guards under another syntax (its ``SortedQuantifier`` is
relativised away on the way to plain FOL) that supplies non-emptiness and
sub-sorts but not the one thing two-sortedness needs, disjointness.

* ``DataExists``/``DataForAll``/``DataAtLeast``/``DataAtMost`` mint a bound
  variable from the SAME minter as every object restriction and guard it with
  the data range's image ``δ(DR, w)``; ``DataHasValue`` is the ground atom
  ``d(x, t)`` for the literal's term ``t`` and mints nothing.
* the data axioms are SIDE axioms, like the role box: ``SubDataPropertyOf``
  ``∀x ∀v (d(x, v) → e(x, v))``, ``DataPropertyDomain`` ``∀x ∀v (d(x, v) →
  π(C, x))``, ``DataPropertyRange`` ``∀x ∀v (d(x, v) → δ(DR, v))`` (the
  datatype read as a unary predicate over the one domain — NOT the GCI
  ``⊤ ⊑ ∀d.DR``, whose image would carry an ``x = x`` filler),
  ``DatatypeDefinition`` ``∀v (D(v) ↔ δ(DR, v))``, and so on.
* what makes the image TWO-sorted is not in any one axiom and is not part of
  the formula: :func:`data_sort_axioms` derives, from the vocabulary the
  knowledge base actually uses, the separation ``∀t ¬(OwlThing(t) ∧
  OwlData(t))``, the typing of every property and individual, the datatype
  lattice and its disjointness, and the distinctness of distinct literals.
  :func:`kb_to_fol` puts them in ``side_axioms``.
* ONE consequence is easy to miss, and is why the image of a GCI changes: with
  a non-empty data domain in the theory, ``∀x (π(sub, x) → π(sup, x))`` also
  ranges over data values, and a data value satisfies every antecedent that
  says nothing about it (``⊤``, ``¬A``, ``∀r.C``). ``⊤ ⊑ {a}`` would then
  identify a data value with the individual ``a`` — a contradiction with the
  separation, for a knowledge base OWL 2 finds consistent. So in the two-sorted
  image every GCI is relativised to the object domain, ``∀x (OwlThing(x) ∧
  π(sub, x) → π(sup, x))``, and so is ``Reflexive(r)``. :func:`kb_to_fol` does
  it, and builds the GOAL the same way: :meth:`KnowledgeBaseFOL.subsumption_goal`,
  :meth:`~KnowledgeBaseFOL.unsatisfiability_goal` and
  :meth:`~KnowledgeBaseFOL.instance_goal` relativise to whatever
  :attr:`KnowledgeBaseFOL.separation` says, so a caller never has to know. (For
  a hand-built query ``object_sort=True`` on :func:`subsumption_to_fol` is the
  same relativisation.)
* the side axioms are derived from the vocabulary the knowledge base uses, so a
  QUESTION that names a datatype, a data property, a literal or an object
  property the knowledge base does not is asked of a weaker theory: the datatype
  lattice, the typing and the literal facts for that name are simply not there.
  ``kb_to_fol(tbox, abox, query=[concept, …])`` adds the vocabulary of the
  concepts you are going to ask about to everything derived from the
  vocabulary, and the three goal methods REFUSE, by name, a concept the bundle
  does not cover — the wrong spelling cannot be followed silently.
* ONE name is ONE predicate, so a name used as both an object property and a
  data property, or as both a class and a datatype, would be conflated into a
  single predicate and change what follows (a functional ``P`` with an object
  successor and a data value came out INCONSISTENT). OWL 2 DL forbids both
  pairs; the image REFUSES them by name (``UnsupportedDatatypeError``, from
  :func:`kb_to_fol`, :func:`data_sort_axioms`, :func:`databox_to_fol` and
  :func:`abox_to_fol`) and asks for one of the two to be renamed. A class, an
  object property and an individual sharing a name (OWL 2 DL punning that IS
  allowed) are accepted, and are THREE symbols in the image: the unary
  predicate ``A(x)`` of the class, the binary predicate ``A(x, y)`` of the
  property and the constant ``A`` of the individual. A route that keys a
  symbol on its kind and arity reads them as three — the TPTP writers do, so
  ``api.prove`` with Vampire or E answers over a punned knowledge base.
* that refusal is per call, over what the call is given, so boxes rendered one
  at a time and conjoined by hand are not seen together by any of them.
  :func:`check_kb_names` runs the same check over several pieces at once — the
  ``TBox`` and ``ABox`` the images were built from.

The two-sorted image is SOUND — every OWL 2 interpretation expands to a model of
it, so it entails nothing the knowledge base does not — and deliberately not
COMPLETE:
the lattice states the OWL 2 datatype map's subtype and disjointness facts,
literals are distinct within a family whose lexical-to-value map is injective,
and an ordering facet is an UNINTERPRETED comparison atom for ``api.prove`` (use
:mod:`unicode_fol_kit.atp.z3_arith` for arithmetic over the data ranges alone).
So ``proved`` transfers to OWL 2 and ``refuted`` does NOT, for a knowledge base
with a data layer: :attr:`KnowledgeBaseFOL.refutation_is_decisive` is ``False``
exactly then, and its docstring says what each prover status lets a caller
conclude. The other two separations are NOT sound for a data layer: without the
restriction of every inclusion to the object domain, ``⊤ ⊑ {a}`` also ranges
over data values, the premises are stronger than OWL 2's, and an OWL-consistent
knowledge base can have an inconsistent image. The goal methods of the bundle
refuse them for that reason.

Knowledge bases: the TBox/RBox split is a trap
-----------------------------------------------
:class:`~unicode_fol_kit.dl.tableau.TBox` holds BOTH the concept inclusions and the
RBox, but the FOL image of each lives in its own function, and
:func:`tbox_to_fol` renders ONLY the concept inclusions. A question proved against its
output alone is asked of a WEAKER theory — the GCIs hold, but the roles are unrelated
and none is transitive — so it can come back REFUTED for a subsumption the tableau
accepts (a false counterexample). The spelling that used to run, with the instance
that was recorded as a regression test::

    t = TBox().add_role_inclusion("hasChild", "hasDescendant")
    dl.subsumes(∃hasChild.⊤, ∃hasDescendant.⊤, t)                 # True
    api.prove(subsumption_to_fol(∃hasChild.⊤, ∃hasDescendant.⊤),
              [tbox_to_fol(t)])                                   # REFUTED: the role
                                                                  # box was dropped

so :func:`tbox_to_fol` now RAISES :class:`RoleBoxOmittedError` for a TBox carrying a
role box, unless the caller writes ``concept_inclusions_only=True`` — the only way
to say "yes, I know the role box is not in this formula". The supported entry point
for a whole knowledge base is :func:`kb_to_fol`, which returns the knowledge base
and the role-box image SEPARATELY (a :class:`KnowledgeBaseFOL`), following the kit's
side-axiom convention (:class:`~unicode_fol_kit.comorphism.TranslationResult`): the
side axioms are never conjoined into the main formula, the caller passes them as
``premises`` (see ``Comorphism.side_axioms`` for why folding them in is wrong).

The other renderers have no analogous silent drop, because none of them is handed a
TBox: :func:`concept_to_fol`, :func:`subsumption_to_fol` and :func:`abox_to_fol`
render exactly what they are given, which makes each of them an answer about the
EMPTY knowledge base (no GCIs, no role box). That is the right reading for a bare
concept or an ABox-only question, and the wrong one for any question *relative to*
a knowledge base — there the TBox image and the role-box image must be premises
too, which is what :class:`KnowledgeBaseFOL` bundles.
"""

import re
from dataclasses import dataclass, field, fields, is_dataclass
from typing import FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple

from ..fol.nodes import (
    Node, Variable, Constant, Number, Atom,
    Not as _FNot, And as _FAnd, Or as _FOr, Implies, Iff, Quantifier,
    Box, Diamond, Count,
)
from ..fol._identifiers import fresh_variables, fresh_variable_like, variable_pattern
from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DataExists, DataForAll, DataHasValue,
    DataAtLeast, DataAtMost, DATA_CONCEPTS,
)
from .datatypes import (
    OWL_DATA, OWL_THING, DataRange, Literal, UnsupportedDatatypeError,
    canonical_datatype_name, datarange_literals, datarange_datatypes,
    datarange_to_fol, datatype_ancestors, datatype_family,
    EXACT_NUMBER_DATATYPES,
)
from .tableau import (
    TBox, ABox, _AXIOM_KINDS, _abox_individual_names, _reject_abox_roles,
    _reject_concept_role, _validate_data_box, _validate_role_box,
)

__all__ = [
    "concept_to_fol", "subsumption_to_fol", "tbox_to_fol", "abox_to_fol",
    "rbox_to_fol", "databox_to_fol", "data_sort_axioms", "check_kb_names",
    "kb_to_fol", "KnowledgeBaseFOL", "SideAxiom", "RoleBoxOmittedError",
    "concept_to_modal",
]


# --------------------------------------------------------------------------- #
# Standard translation to FOL.
# --------------------------------------------------------------------------- #

def _individual_names(concept) -> set:
    """Every individual name ``_translate`` will render as a ``Constant``.

    Two concept kinds carry one: a :class:`~unicode_fol_kit.dl.concepts.Nominal`
    (``{a}`` becomes ``term = a``) and a
    :class:`~unicode_fol_kit.dl.concepts.HasValue` (``∃r.{a}`` becomes
    ``r(term, a)``). Roles and atomic concepts become predicates, which live in
    their own namespace. The RECURSION is generic over the dataclass fields so
    a new concept type with a nested concept is reached without being named
    here — but the ``individual`` FIELD is not, and a kind missed here fails
    SILENTLY: the avoid set handed to :func:`_fresh_var_factory` would be
    incomplete, so a minted bound variable could share a name with the
    individual and CAPTURE it (``Variable("x0")`` and ``Constant("x0")`` print
    the same text and are the same Z3 expression). ``tests/test_dl_has_value.py``
    has the regression for exactly that, with a HasValue individual named
    ``"x0"``.
    """
    names = set()
    stack = [concept]
    while stack:
        node = stack.pop()
        if isinstance(node, (Nominal, HasValue)):
            names.add(node.individual)
        if is_dataclass(node):
            for field in fields(node):
                value = getattr(node, field.name)
                if isinstance(value, Concept):
                    stack.append(value)
    return names


def _fresh_var_factory(base: str, avoid=()):
    """Return a callable producing variable names distinct from ``base``, from
    ``avoid``, and from every name it has already produced (see "Variable
    freshness" above).

    The names come from :func:`~unicode_fol_kit.fol._identifiers.fresh_variables`
    so that they are names the kit's own parser reads back; ``base`` only picks
    the letter (and is itself excluded), because it may be an ABox individual's
    name and so no legal variable at all. ``avoid`` is the individual names the
    translation will render as constants (:func:`_individual_names`): a bound
    variable that happened to share a name with one of them would CAPTURE it —
    ``Variable("a0")`` and ``Constant("a0")`` print the same and are the same
    Z3 expression — so the nominal would stop denoting its own individual.
    """
    letter = base[:1] if re.fullmatch(variable_pattern(), base[:1] or " ") else "x"
    used = {base} | set(avoid)

    def fresh() -> str:
        name = fresh_variables(1, letter=letter, avoid=used)[0]
        used.add(name)
        return name

    return fresh


def _kb_individual_names(tbox: Optional[TBox], abox: Optional[ABox]) -> Set[str]:
    """Every individual name of the whole knowledge base ``(tbox, abox)`` — the
    set no BOUND variable of its image may share a name with.

    It is :attr:`_Vocabulary.individuals`, the one walk that already reaches
    every place a name can occur: the assertion positions of the ABox AND the
    fillers of every nominal and value restriction in a concept inclusion, a
    domain or range axiom, a data property domain or an ABox class assertion.
    (:attr:`KnowledgeBaseFOL.individuals` deliberately lists only the ABox's
    own, but a filler is a ``Constant`` of the image all the same.) Reusing it
    keeps ONE definition of "an individual of this knowledge base" instead of a
    second hand-written walk that could drift from it.
    """
    return set(_collect_vocabulary(tbox, abox).individuals)


def _binder_names(preferred: Sequence[str], avoid: Iterable[str]) -> Tuple[str, ...]:
    """The bound-variable names to use for the prefix variables ``preferred``,
    given the individual names ``avoid`` the image renders as ``Constant``\\ s.

    A name that clashes with an individual is RENAMED, never refused: a bound
    variable called ``x`` and a constant called ``x`` print the same text and are
    the SAME Z3 constant, so ``∃r.{x} ⊑ A`` printed ``∀x (r(x, x) → A(x))`` —
    the quantifier captured the individual — and the knowledge base
    ``∃r.{x} ⊑ ⊥`` with ``r(a, a)``, ``a ≠ x`` (which only forbids an r-edge
    INTO the individual ``x``) was reported inconsistent. Renaming a bound
    variable is exact (alpha-equivalence), so a name that does not clash is
    returned untouched and every image that never named an individual
    ``x``/``y``/``z`` is byte-for-byte what it was.

    The replacement is :func:`~unicode_fol_kit.fol._identifiers.fresh_variable_like`
    — the first free ``letter + digits`` — and avoids every individual, every
    OTHER preferred name and every replacement already made, so two prefix
    variables never collapse onto one. A caller that goes on to mint further
    variables must hand THESE names to :func:`_fresh_var_factory`, not the
    preferred ones: ``x`` renamed to ``x1`` leaves ``x`` itself free for the
    minter, which would otherwise be allowed to reuse it.
    """
    avoid = set(avoid)
    taken = set(preferred)
    chosen: List[str] = []
    for name in preferred:
        if name in avoid:
            name = fresh_variable_like(name, avoid | taken)
            taken.add(name)
        chosen.append(name)
    return tuple(chosen)


def _role_atom(role, x: Node, y: Node) -> Node:
    """Render the role atom for an ``x —role→ y`` edge: ``role(x, y)``, or — when
    ``role`` is an :class:`~unicode_fol_kit.dl.concepts.InverseRole` — ``role(y,
    x)`` (see the module docstring's "Inverse roles and nominals (I, O)"
    section: the standard translation of ``r⁻`` swaps the atom's argument order,
    nothing else).
    """
    if isinstance(role, InverseRole):
        return Atom(role.role, (y, x))
    return Atom(role, (x, y))


def _t_top(concept, term, fresh) -> Node:
    return Atom("=", (term, term))


def _t_bottom(concept, term, fresh) -> Node:
    return Atom("≠", (term, term))


def _t_atomic(concept, term, fresh) -> Node:
    return Atom(concept.name, (term,))


def _t_nominal(concept, term, fresh) -> Node:
    return Atom("=", (term, Constant(concept.individual)))


def _t_has_value(concept, term, fresh) -> Node:
    """``π(∃r.{a}, t)`` as the ground atom ``r(t, a)`` — see
    :class:`~unicode_fol_kit.dl.concepts.HasValue` for the one-point
    elimination that makes this the same formula as ``∃y (r(t, y) ∧ y = a)``.

    ``_role_atom``, not ``Atom`` by hand, so an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole`-valued role gets the
    swapped argument order ``r(a, t)`` for free; ``Constant``, not
    ``Variable``, exactly as :func:`abox_to_fol` renders an ABox individual,
    which is what the ASCII Prover9/TPTP exporters need to tell a name from a
    bound variable. No variable is minted, so ``fresh`` is unused.
    """
    return _role_atom(concept.role, term, Constant(concept.individual))


def _t_not(concept, term, fresh) -> Node:
    return _FNot(_translate(concept.concept, term, fresh))


def _t_and(concept, term, fresh) -> Node:
    return _FAnd(_translate(concept.left, term, fresh),
                 _translate(concept.right, term, fresh))


def _t_or(concept, term, fresh) -> Node:
    return _FOr(_translate(concept.left, term, fresh),
                _translate(concept.right, term, fresh))


def _t_exists(concept, term, fresh) -> Node:
    w = Variable(fresh())
    return Quantifier("∃", w, _FAnd(
        _role_atom(concept.role, term, w), _translate(concept.concept, w, fresh)))


def _t_forall(concept, term, fresh) -> Node:
    w = Variable(fresh())
    return Quantifier("∀", w, Implies(
        _role_atom(concept.role, term, w), _translate(concept.concept, w, fresh)))


def _t_count(concept, term, fresh) -> Node:
    w = Variable(fresh())
    matrix = _FAnd(_role_atom(concept.role, term, w),
                   _translate(concept.concept, w, fresh))
    op = "ge" if isinstance(concept, AtLeast) else "le"
    return Count(op, Number(concept.n), w, matrix)


def _t_data_exists(concept, term, fresh) -> Node:
    """``π(∃d.DR, t)`` = ``∃w (d(t, w) ∧ δ(DR, w))``: the exact mirror of
    :func:`_t_exists` with a data atom, the bound variable minted from the SAME
    factory so it is pairwise distinct from every object restriction's."""
    w = Variable(fresh())
    return Quantifier("∃", w, _FAnd(
        Atom(concept.prop, (term, w)), datarange_to_fol(concept.datarange, w)))


def _t_data_forall(concept, term, fresh) -> Node:
    """``π(∀d.DR, t)`` = ``∀w (d(t, w) → δ(DR, w))``."""
    w = Variable(fresh())
    return Quantifier("∀", w, Implies(
        Atom(concept.prop, (term, w)), datarange_to_fol(concept.datarange, w)))


def _t_data_has_value(concept, term, fresh) -> Node:
    """``π(DataHasValue(d lt), t)`` = the ground atom ``d(t, t_lt)``. A literal
    denotes ONE fixed data value (OWL 2 §2.3.4: ``{ x | (x, lt^LT) ∈ d^DP }``),
    so there is no quantifier, no bound variable and no datatype guard — the
    literal already pins its datatype. ``fresh`` is unused."""
    return Atom(concept.prop, (term, concept.value.to_term()))


def _t_data_count(concept, term, fresh) -> Node:
    """``≥n d.DR`` / ``≤n d.DR`` through the SAME ``Count`` node the object
    cardinalities use, so ``Count._expand`` and ``Count.to_z3`` carry it."""
    w = Variable(fresh())
    matrix = _FAnd(Atom(concept.prop, (term, w)), datarange_to_fol(concept.datarange, w))
    op = "ge" if isinstance(concept, DataAtLeast) else "le"
    return Count(op, Number(concept.n), w, matrix)


# One entry per concrete concept class. A chain of `isinstance` branches was the
# single worst merge point in this file -- every new class expression kind added
# one branch in the middle of one function -- so the dispatch is a table a new
# kind appends ONE line to, keyed by exact type (dl.concepts' concept classes
# are all concrete frozen dataclasses with no subclassing, so exact-type lookup
# is total: an unlisted type is a genuine programming error, reported as such).
_TRANSLATORS = {
    Top: _t_top,
    Bottom: _t_bottom,
    Atomic: _t_atomic,
    Nominal: _t_nominal,
    HasValue: _t_has_value,
    Not: _t_not,
    And: _t_and,
    Or: _t_or,
    Exists: _t_exists,
    ForAll: _t_forall,
    AtLeast: _t_count,
    AtMost: _t_count,
    DataExists: _t_data_exists,
    DataForAll: _t_data_forall,
    DataHasValue: _t_data_has_value,
    DataAtLeast: _t_data_count,
    DataAtMost: _t_data_count,
}


def _translate(concept: Concept, term: Node, fresh) -> Node:
    """Render ``concept`` as a FOL formula with ``term`` (a Variable or
    Constant) standing for the individual under discussion; ``fresh`` mints
    the bound variable for each nested restriction (see :func:`_fresh_var_factory`).
    """
    handler = _TRANSLATORS.get(type(concept))
    if handler is None:
        raise TypeError(f"concept_to_fol: unsupported concept {type(concept).__name__}")
    # An OWL 2 built-in property name (or ``=``/``≠``) as THIS node's role is
    # refused by name, not rendered as the ordinary predicate of that name: the
    # universal/empty property is not one, and the image of ``∃owl:bottom…C``
    # as an uninterpreted atom is satisfiable where the restriction is not.
    # Here, in the one dispatch every concept passes through, so no handler has
    # to remember it.
    _reject_concept_role(concept, where="dl.translate")
    return handler(concept, term, fresh)


def concept_to_fol(concept: Concept, var: str = "x") -> Node:
    """Render ``concept`` as a FOL formula ``π(concept, var)`` with one free
    variable ``var`` (see the module docstring for the translation rules).

    ``concept`` is satisfiable (:func:`unicode_fol_kit.dl.tableau.concept_satisfiable`)
    iff ``∃var π(concept, var)`` is FOL-satisfiable — wrap the result in a
    ``Quantifier("∃", Variable(var), …)`` to test that directly (e.g. via
    :func:`unicode_fol_kit.is_satisfiable`).

    This is satisfiability w.r.t. the EMPTY knowledge base: nothing about any
    TBox or RBox is in the formula. For ``concept_satisfiable(concept, tbox)``
    pass ``kb_to_fol(tbox).tbox_premises`` as the premises of the query (see
    :func:`kb_to_fol`); the role box in particular is NOT implied by anything
    here.

    A concept with a DATA restriction (``DataExists`` and its four siblings) is
    NOT answered by this formula closed under ``∃``: the formula says nothing
    about the data domain, so a data value satisfies the existential and
    ``∃HasV.xsd:integer ⊓ ∀HasV.xsd:string`` would come out satisfiable, where
    OWL 2 makes it unsatisfiable (the two datatypes are disjoint). Build the
    knowledge base with ``kb_to_fol(tbox, abox, query=[concept])`` and ask
    ``kb.unsatisfiability_goal(concept)``, which carries the sort and datatype
    axioms the question needs. The registry edge ``alc → fol`` refuses such a
    concept for exactly that reason; this function renders it, because the
    knowledge-base images are built from it.

    Raises:
        ValueError: ``var`` is the name of an individual the concept itself
            names (a nominal or value restriction). ``var`` is the one FREE
            variable of the result — the caller quantifies over it — so it
            cannot be renamed behind the caller's back (every other bound
            variable of an image is renamed to avoid a clash, see
            :func:`_binder_names`); and ``Variable("x")`` and ``Constant("x")``
            are the same constant to Z3, so ``∃x`` over ``π(∃r.{x}, x)`` would
            bind the individual. Pass another ``var``.
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            a restriction's role is an OWL 2 built-in property
            name or ``=``/``≠`` (see :func:`~unicode_fol_kit.dl.tableau.reserved_role`):
            an uninterpreted predicate of that name would be a different
            restriction.
    """
    _check_concepts_punning((concept,), "dl.concept_to_fol")
    names = _individual_names(concept)
    if var in names:
        raise ValueError(
            f"dl.concept_to_fol: the free variable {var!r} has the same name as "
            f"an individual this concept names (a nominal or a value "
            f"restriction), and a variable and a constant of one name are the "
            f"same constant to every backend — the individual would be bound "
            f"by whatever quantifies {var!r}. Pass var= another name, e.g. "
            f"var={fresh_variable_like(var, names | {var})!r}.")
    return _translate(concept, Variable(var), _fresh_var_factory(var, names))


def subsumption_to_fol(sub: Concept, sup: Concept, var: str = "x", *,
                       object_sort: bool = False) -> Node:
    """Render the GCI ``sub ⊑ sup`` as its universal closure
    ``∀var (π(sub, var) → π(sup, var))``.

    ``object_sort=True`` relativises the closure to the OBJECT domain,
    ``∀var (OwlThing(var) ∧ π(sub, var) → π(sup, var))`` — the form a GCI takes
    in the two-sorted image of a knowledge base that has a data layer (see
    "The data layer" in the module docstring: unrelativised, the quantifier
    also ranges over data values, which satisfy every antecedent that says
    nothing about them). It is what a GOAL must look like to be the question
    :func:`kb_to_fol` ``(…, separation="two-sorted")`` poses. The default is
    the plain closure, byte-identical to every release before the data layer.

    A goal asked of a knowledge base is better built by the knowledge base:
    :meth:`KnowledgeBaseFOL.subsumption_goal` picks the relativisation that
    fits ``kb.separation`` and refuses a concept whose vocabulary the bundle's
    side axioms do not cover. On a TWO-sorted bundle the plain default spelling
    answers ``refuted`` for a pure object-level subsumption that holds
    (``A ⊑ B``, ``B ⊑ C`` entail ``A ⊑ C``, and the unrelativised goal asks
    about data values too) — silently, which is why the methods exist.

    ``sub ⊑ sup`` holds (:func:`unicode_fol_kit.dl.tableau.subsumes`) iff this
    formula is FOL-valid — check via :func:`unicode_fol_kit.is_valid`.

    "Valid" is subsumption w.r.t. the EMPTY knowledge base. Subsumption relative
    to a TBox (``subsumes(sub, sup, tbox)``) is NOT ``is_valid`` of this formula
    and NOT ``Implies(tbox_to_fol(tbox), …)`` either — the latter drops the role
    box. Use ``api.prove(subsumption_to_fol(sub, sup), kb_to_fol(tbox).tbox_premises)``
    (see :func:`kb_to_fol`).

    ``var`` names the variable the closure binds, and it is a PREFERENCE: when
    ``sub`` or ``sup`` names an individual (a nominal, a value restriction) of
    that very name, the bound variable is renamed to the first free ``letter +
    digits`` (``∃r.{x} ⊑ A`` prints ``∀x0 (r(x0, x) → A(x0))``, not the
    capturing ``∀x (r(x, x) → A(x))``). The quantifier binds the variable, so
    the rename is exact — the contrast with :func:`concept_to_fol`, whose
    ``var`` is FREE and is refused instead.

    Raises:
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            a restriction's role is an OWL 2 built-in property
            name or ``=``/``≠``.
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            ``sub`` and ``sup`` together use one name as
            two kinds OWL 2 DL keeps apart — an object property and a data
            property, or a class and a datatype (``∃P.B ⊓ ∃P.xsd:integer``): the
            image has one predicate per name. The refusal is per call, over
            what the call is given; whether a name clashes with the knowledge
            base the goal is asked of is checked by the bundle's own goal
            methods (:meth:`KnowledgeBaseFOL.subsumption_goal`).
    """
    _check_concepts_punning((sub, sup), "dl.subsumption_to_fol")
    return _subsumption_image(sub, sup, var, object_sort, ())


def _subsumption_image(sub: Concept, sup: Concept, var: str, object_sort: bool,
                       avoid: Iterable[str]) -> Node:
    """:func:`subsumption_to_fol`, with ``avoid`` — the individual names of the
    WHOLE knowledge base the GCI is part of — added to the two concepts' own.

    The prefix variable is bound by the closure, so a ``var`` that clashes with
    an individual is renamed (:func:`_binder_names`) rather than left to capture
    it, and the variables the two translations mint avoid the RENAMED name."""
    avoid = set(avoid) | _individual_names(sub) | _individual_names(sup)
    (var,) = _binder_names((var,), avoid)
    v = Variable(var)
    antecedent = _translate(sub, v, _fresh_var_factory(var, avoid))
    consequent = _translate(sup, v, _fresh_var_factory(var, avoid))
    if object_sort:
        antecedent = _FAnd(Atom(OWL_THING, (v,)), antecedent)
    return Quantifier("∀", v, Implies(antecedent, consequent))


# The constant the empty-knowledge-base tautology is built from. ``c_`` plus a
# word is the kit's CONSTANT terminal (fol._identifiers.constant_pattern), so
# the text this prints reads back through api.parse_any as the SAME formula.
# Until 0.30.0 this was Constant("_"), which printed `_ = _` — text the kit's
# own parser rejects ("Unexpected character '_'"), so an RBox-only or empty
# knowledge base violated the "everything printed reads back" property that
# tests/test_printed_text_reads_back.py exists to hold (measured on the OEO
# fragment: 150 of 3636 accepted axioms printed an unreadable image for exactly
# this reason, every one of them an RBox-only knowledge base whose `formula` is
# this tautology). `c = c` is valid whatever `c` denotes, so a knowledge base
# that happens to name an individual `c_tautology` is still rendered correctly
# — the same argument concept_to_modal's reserved `_MODAL_TRUE_ATOM` makes.
_TAUTOLOGY_CONSTANT = Constant("c_tautology")


def _tautology() -> Node:
    """A closed, genuinely valid formula — the FOL image of "no constraint"
    (an empty TBox or ABox). See "GCIs, TBoxes, ABoxes" in the module docstring.
    """
    return Atom("=", (_TAUTOLOGY_CONSTANT, _TAUTOLOGY_CONSTANT))


def _conjoin(parts: List[Node]) -> Node:
    """Fold a (possibly empty) list of formulas into a single conjunction,
    BALANCED: depth ``ceil(log2 n)`` rather than ``n``.

    A left fold — what this did until 0.30.0 — makes the conjunction's depth
    equal the number of axioms, and the kit's node operations are recursive, so
    a real ontology's image could be built but not used. Measured on this tree
    with the default ``sys.getrecursionlimit() == 1000``: a TBox of 495 concept
    inclusions printed, 496 raised ``RecursionError`` from the shared printer,
    and at 1000 conjuncts EVERY operation failed — ``to_unicode_str``,
    ``to_dict``, ``to_tptp``, ``to_prover9``, ``to_z3``, and ``__eq__`` /
    ``__hash__``, the last two generated by ``@dataclass`` and so beyond any
    printer fix. The OEO fragment (3091 concept inclusions) was already over
    that line. Only reducing the TREE's depth fixes all seven at once; raising
    the recursion limit would trade a clean exception for a segfault.

    A conjunction is associative, so this is the SAME formula up to
    associativity: identical models, and ``_formula_alpha_equal`` unaffected.
    What DOES change is printed parenthesisation for three or more conjuncts
    (``And(And(P, Q), R)`` prints ``P ∧ Q ∧ R``; the balanced
    ``And(And(P, Q), And(R, S))`` prints ``P ∧ Q ∧ (R ∧ S)``) — identical for
    0, 1 and 2 conjuncts, which is every pinned string in the suite.
    """
    if not parts:
        return _tautology()
    level = list(parts)
    while len(level) > 1:
        level = [_FAnd(level[i], level[i + 1]) if i + 1 < len(level) else level[i]
                 for i in range(0, len(level), 2)]
    return level[0]


def _side_axiom_census(tbox: TBox) -> str:
    """``"2 SubObjectPropertyOf axiom(s), 1 TransitiveObjectProperty axiom(s)"``
    — the side axioms ``tbox`` carries, named by their OWL keyword.

    Derived from :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`' ``part ==
    "side"`` rows, so a side-axiom kind added later names itself in
    :class:`RoleBoxOmittedError`'s message without anyone editing the message.
    """
    parts = []
    for row in _AXIOM_KINDS:
        if row.holder != "tbox" or row.part != "side":
            continue
        count = len(getattr(tbox, row.field))
        if count:
            parts.append(f"{count} {row.kind} axiom(s)")
    return ", ".join(parts)


def _carries_data_box(tbox: TBox) -> bool:
    """True iff ``tbox`` stores an axiom of a ``layer == "data"`` side kind (a
    data-box axiom) -- the ones :func:`databox_to_fol`, not :func:`rbox_to_fol`,
    renders. Derived from :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`, like
    :func:`_side_axiom_census`, so a data-box kind added later is named too."""
    return any(row.holder == "tbox" and row.part == "side" and row.layer == "data"
               and getattr(tbox, row.field) for row in _AXIOM_KINDS)


class RoleBoxOmittedError(ValueError):
    """Raised by :func:`tbox_to_fol` when the TBox carries a role box and the
    caller did not say that rendering only the concept inclusions is intended.

    See "Knowledge bases: the TBox/RBox split is a trap" in the module
    docstring: the concept-inclusion image alone is not the TBox's meaning, and
    using it as the knowledge base can produce false counterexamples.
    """


def tbox_to_fol(tbox: TBox, var: str = "x", *, concept_inclusions_only: bool = False,
                object_sort: bool = False) -> Node:
    """Render every GCI/equivalence in ``tbox`` as its universal closure
    (:func:`subsumption_to_fol`) and conjoin them.

    An empty TBox renders as a tautology (no axioms ⇒ no constraint). The
    TBox is entailment-consistent with :func:`unicode_fol_kit.dl.tableau.TBox`:
    equivalences are stored as the pair of inclusions they abbreviate
    (``TBox.add_equivalence``), so they fall out of ``tbox.inclusions`` with
    no special case needed here.

    **Only the concept inclusions are rendered.** A :class:`TBox` also holds a
    role box (role inclusions, transitivity and every other role-box axiom — the
    ``part == "side"`` rows of ``dl.tableau._AXIOM_KINDS``) and a data box, and
    their image is NOT in the result; a formula built from this function alone
    therefore describes a weaker theory than ``tbox`` and can be refuted where
    the tableau's ``subsumes(…, tbox)`` succeeds (a false counterexample). To
    make that impossible to do by accident, a TBox that carries any such side
    axiom raises :class:`RoleBoxOmittedError` — use :func:`kb_to_fol`
    (the knowledge base plus the role box as separate premises) or
    :func:`rbox_to_fol` for the role-box image (:func:`databox_to_fol` for the
    data-box image, which the message names when the TBox carries one). Pass
    ``concept_inclusions_only=True`` to say, at the call site, that the
    concept-inclusion image alone is what you want (e.g. to render or inspect the
    GCIs, or when the role box is supplied some other way).

    The condition is DERIVED from :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`
    via :meth:`~unicode_fol_kit.dl.tableau.TBox.has_side_axioms`, not written out
    over the fields that happened to exist when it was added: a TBox field that
    escaped a hand-written ``or`` here would render as a tautology and raise
    nothing, which is a silent loss rather than an error.

    ``object_sort=True`` relativises every GCI to the object domain — see
    :func:`subsumption_to_fol`.

    A class and an object property of one name are two symbols in the result
    (``A(x)`` and ``A(x, y)``), as in every image of this module — see
    :func:`kb_to_fol`.

    Raises:
        RoleBoxOmittedError: ``tbox`` carries a side axiom — a role-box axiom or
            a data-box axiom — and ``concept_inclusions_only`` is false.
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            the TBox uses one name as two kinds OWL 2 DL
            keeps apart (an object property and a data property, a class and a
            datatype) — see :func:`kb_to_fol`.
    """
    if not concept_inclusions_only and tbox.has_side_axioms():
        # rbox_to_fol renders the ROLE box only (a tautology for a TBox whose
        # side axioms are all data-box ones); the data box has its own renderer,
        # which the message names whenever the TBox carries a data-box axiom.
        images = ("rbox_to_fol(tbox) for the role-box image"
                  + (" and databox_to_fol(tbox) for the data-box image"
                     if _carries_data_box(tbox) else ""))
        raise RoleBoxOmittedError(
            f"tbox_to_fol: this TBox carries side axioms ({_side_axiom_census(tbox)}) "
            "that tbox_to_fol does not render, so its output alone is a WEAKER theory "
            "than the TBox and can be refuted where dl.subsumes(…, tbox) succeeds. Use "
            "kb_to_fol(tbox, abox) (the knowledge base and the side axioms, to be "
            f"passed as premises) or, for one box alone, {images}; "
            "pass concept_inclusions_only=True if the concept-inclusion image alone "
            "is really what you want.")
    vocabulary = _collect_vocabulary(tbox, None)
    _check_name_punning(vocabulary, "dl.tbox_to_fol")
    return _tbox_image(tbox, var, object_sort, set(vocabulary.individuals))


def _tbox_image(tbox: TBox, var: str, object_sort: bool,
                avoid: Iterable[str]) -> Node:
    """The conjunction of every GCI of ``tbox``, each bound variable avoiding
    ``avoid`` — the individual names of the whole knowledge base — so that one
    :func:`kb_to_fol` call binds the same prefix variable in every conjunct."""
    return _conjoin([_subsumption_image(sub, sup, var, object_sort, avoid)
                     for sub, sup in tbox.inclusions])


@dataclass(frozen=True)
class SideAxiom:
    """One side axiom of a knowledge base's FOL image: a premise that is NEVER
    a conjunct of :attr:`KnowledgeBaseFOL.formula` (see :func:`kb_to_fol`).

    Fields:

    * ``kind`` — the OWL 2 keyword this axiom came from, e.g.
      ``"SubObjectPropertyOf"`` or ``"TransitiveObjectProperty"``. The OWL name
      rather than an internal one, so a caller can census an ontology's image
      per axiom kind (:meth:`KnowledgeBaseFOL.axioms_of_kind`) without a second
      translation table. It is the ``kind`` column of
      :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`.
    * ``group`` — which route owns the premise: ``"rbox"`` for a role-box
      axiom, ``"data"`` for the image of a data-box axiom, ``"sort"`` for the
      object/data separation and the typing it needs, ``"datatype"`` for the
      datatype lattice and the literals. (:attr:`KnowledgeBaseFOL.rbox_axioms`
      and :attr:`~KnowledgeBaseFOL.data_axioms` are the two cases the kit itself
      asks about.) A ``group`` rather than a type hierarchy because the
      caller's question is a fork, not a taxonomy. The ``kind`` of a ``"sort"``
      or ``"datatype"`` axiom is a descriptive name, not an OWL keyword — there
      is no OWL axiom it came from.
    * ``formula`` — the axiom itself.
    """

    kind: str
    group: str
    formula: Node


def _forall(variables: List[Variable], body: Node) -> Node:
    """``∀v1 … ∀vn body`` — the universal closure, outermost variable first."""
    for variable in reversed(variables):
        body = Quantifier("∀", variable, body)
    return body


def _chain_variables(length: int, x: str, y: str, z: str,
                     avoid: Iterable[str] = ()) -> List[Variable]:
    """``length`` variable names for a property chain's quantifier prefix.

    The first three are ``x``, ``y``, ``z`` — the same three
    :func:`_rbox_axioms` already uses for transitivity, which IS the chain
    ``r ∘ r ⊑ r``, so the two images stay visually comparable. Beyond three the
    kit has no fourth canonical name, so the rest come from
    :func:`_fresh_var_factory` (``x0``, ``x1``, …), which yields the
    one-letter-plus-digits shape the kit's VARIABLE terminal accepts — never a
    hand-rolled ``f"{base}_{n}"``. ``avoid`` is the individual names of the
    knowledge base: a chain axiom names none, so it cannot capture one, but the
    invariant "no bound variable of an image shares a name with an individual"
    is kept without exception rather than only where it is needed.
    """
    names = [x, y, z][:length]
    if length > 3:
        fresh = _fresh_var_factory(x, avoid={y, z} | set(avoid))
        while len(names) < length:
            names.append(fresh())
    return [Variable(name) for name in names]


def _chain_axiom(chain, super_role, x: str, y: str, z: str,
                 avoid: Iterable[str] = ()) -> Node:
    """The FOL image of ``P1 ∘ … ∘ Pn ⊑ Q``: for ``n = 2``,
    ``∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z))``.

    OWL 2 direct semantics: the axiom holds iff for every ``y0 … yn`` with
    ``<y_{i-1}, y_i> ∈ Pi^I`` we have ``<y0, yn> ∈ Q^I`` — so the body is the
    conjunction of the ``n`` step atoms (folded by :func:`_conjoin`, like every
    other conjunction this module builds) and the head links the first variable
    to the last.
    """
    variables = _chain_variables(len(chain) + 1, x, y, z, avoid)
    body = _conjoin([_role_atom(role, variables[i], variables[i + 1])
                     for i, role in enumerate(chain)])
    return _forall(variables, Implies(body, _role_atom(super_role, variables[0],
                                                       variables[-1])))


def _rbox_axioms(tbox: TBox, x: str = "x", y: str = "y",
                 z: str = "z", *, object_sort: bool = False,
                 avoid: Optional[Iterable[str]] = None) -> List[SideAxiom]:
    """The role box of ``tbox`` as a list of :class:`SideAxiom` — one per role
    inclusion, then one per transitive role, then one per further role-box axiom
    in the order :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS` lists them.
    Every set-valued field is sorted, so the order is deterministic despite the
    fields being unordered sets.

    The ONE place the role box becomes FOL: :func:`rbox_to_fol` conjoins what
    this returns and :func:`kb_to_fol` carries it as
    :attr:`KnowledgeBaseFOL.side_axioms`, so a new role-box axiom kind is
    rendered for both by appending one entry here (and, as every kind must,
    one row of :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`).

    Every stored entry is re-validated first — the SECOND line of defence
    behind :meth:`~unicode_fol_kit.dl.tableau.TBox.add_role_inclusion` and
    friends, and the SAME validation
    (:func:`~unicode_fol_kit.dl.tableau._validate_role_box`) the tableau's
    shared guard runs, so the two routes cannot disagree about whether a ``TBox``
    assembled by hand, or mutated in place, is a question at all: it must fail
    LOUDLY rather than print an atom like ``('r', 's')(x, y)`` that looks like
    an axiom and is not.

    The three prefix variables are the PREFERENCES ``x``, ``y``, ``z``: each one
    that is also the name of an individual of the knowledge base (``avoid`` —
    by default the individuals the TBox's own class expressions name;
    :func:`kb_to_fol` passes the whole knowledge base's) is renamed, so a domain
    axiom over ``∃r.{x}`` does not bind the individual ``x``
    (:func:`_binder_names`).
    """
    where = "dl.rbox_to_fol"
    _validate_role_box(tbox, where=where)
    avoid = (_kb_individual_names(tbox, None) if avoid is None else set(avoid))
    x, y, z = _binder_names((x, y, z), avoid)
    parts: List[SideAxiom] = []
    for sub_role, super_role in tbox.role_inclusions:
        vx, vy = Variable(x), Variable(y)
        # _role_atom, not Atom(...) by hand: it is the function that already
        # knows an InverseRole swaps the atom's argument order, and is what
        # every concept restriction in this module uses.
        parts.append(SideAxiom("SubObjectPropertyOf", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy,
                Implies(_role_atom(sub_role, vx, vy),
                        _role_atom(super_role, vx, vy))))))
    for role in sorted(tbox.transitive_roles):
        vx, vy, vz = Variable(x), Variable(y), Variable(z)
        parts.append(SideAxiom("TransitiveObjectProperty", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy, Quantifier("∀", vz,
                Implies(_FAnd(Atom(role, (vx, vy)), Atom(role, (vy, vz))),
                        Atom(role, (vx, vz))))))))
    for left, right in tbox.disjoint_role_pairs:
        vx, vy = Variable(x), Variable(y)
        parts.append(SideAxiom("DisjointObjectProperties", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy,
                _FNot(_FAnd(Atom(left, (vx, vy)), Atom(right, (vx, vy))))))))
    for role in sorted(tbox.asymmetric_roles):
        vx, vy = Variable(x), Variable(y)
        parts.append(SideAxiom("AsymmetricObjectProperty", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy,
                Implies(Atom(role, (vx, vy)), _FNot(Atom(role, (vy, vx))))))))
    for role in sorted(tbox.irreflexive_roles):
        vx = Variable(x)
        parts.append(SideAxiom("IrreflexiveObjectProperty", "rbox",
            Quantifier("∀", vx, _FNot(Atom(role, (vx, vx))))))
    for role in sorted(tbox.functional_roles):
        vx, vy, vz = Variable(x), Variable(y), Variable(z)
        parts.append(SideAxiom("FunctionalObjectProperty", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy, Quantifier("∀", vz,
                Implies(_FAnd(Atom(role, (vx, vy)), Atom(role, (vx, vz))),
                        Atom("=", (vy, vz))))))))
    for p, q in tbox.inverse_role_pairs:
        vx, vy = Variable(x), Variable(y)
        parts.append(SideAxiom("InverseObjectProperties", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy,
                Iff(Atom(p, (vx, vy)), Atom(q, (vy, vx)))))))
    for role in sorted(tbox.symmetric_roles):
        vx, vy = Variable(x), Variable(y)
        parts.append(SideAxiom("SymmetricObjectProperty", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy,
                Implies(Atom(role, (vx, vy)), Atom(role, (vy, vx)))))))
    for role in sorted(tbox.reflexive_roles):
        vx = Variable(x)
        # Reflexive(r) is "every INDIVIDUAL is r-related to itself". The one
        # role-box axiom with an unguarded universal over a single variable, so
        # in the two-sorted image it needs the object-domain guard (a data
        # value is not r-related to itself, and the typing of r forbids it).
        reflexive: Node = Atom(role, (vx, vx))
        if object_sort:
            reflexive = Implies(Atom(OWL_THING, (vx,)), reflexive)
        parts.append(SideAxiom("ReflexiveObjectProperty", "rbox",
            Quantifier("∀", vx, reflexive)))
    for role in sorted(tbox.inverse_functional_roles):
        vx, vy, vz = Variable(x), Variable(y), Variable(z)
        parts.append(SideAxiom("InverseFunctionalObjectProperty", "rbox",
            Quantifier("∀", vx, Quantifier("∀", vy, Quantifier("∀", vz,
                Implies(_FAnd(Atom(role, (vy, vx)), Atom(role, (vz, vx))),
                        Atom("=", (vy, vz))))))))
    for chain, super_role in tbox.role_chains:
        parts.append(SideAxiom("ObjectPropertyChain", "rbox",
                               _chain_axiom(chain, super_role, x, y, z, avoid)))
    # The two role-box kinds whose axiom carries a CLASS EXPRESSION, so the
    # filler goes through the full _translate (12 of the 110 OEO domain axioms
    # and 10 of the 108 range axioms have a non-atomic one) at the FIRST
    # variable for a domain axiom and the SECOND for a range axiom -- that
    # choice of variable is the whole difference between them.
    for kind, field_name, position in (("ObjectPropertyDomain", "role_domains", 0),
                                       ("ObjectPropertyRange", "role_ranges", 1)):
        for role, concept in getattr(tbox, field_name):
            vx, vy = Variable(x), Variable(y)
            # The avoid set must carry the prefix variables AND every
            # individual of the knowledge base: a minted x0 that collided with
            # one of them would capture it (see _fresh_var_factory). The prefix
            # variables themselves were already renamed away from the
            # individuals above, which is what stops the FIXED letters x and y
            # -- not only the minted ones -- from binding a filler's individual.
            fresh = _fresh_var_factory(
                x, avoid={x, y, z} | avoid | _individual_names(concept))
            parts.append(SideAxiom(kind, "rbox",
                Quantifier("∀", vx, Quantifier("∀", vy,
                    Implies(Atom(role, (vx, vy)),
                            _translate(concept, (vx, vy)[position], fresh))))))
    return parts


def rbox_to_fol(tbox: TBox, x: str = "x", y: str = "y", z: str = "z") -> Node:
    """Render every role-box axiom in ``tbox`` as its FOL image (see "RBoxes" in
    the module docstring) and conjoin them. Each image is the OWL 2
    direct-semantics sentence for that axiom:

    - ``r ⊑ s``                     ↦ ``∀x ∀y (r(x, y) → s(x, y))``
    - ``r ⊑ s⁻``                    ↦ ``∀x ∀y (r(x, y) → s(y, x))``
    - ``Trans(r)``                  ↦ ``∀x ∀y ∀z (r(x, y) ∧ r(y, z) → r(x, z))``
    - ``Disj(p, q)``                ↦ ``∀x ∀y ¬(p(x, y) ∧ q(x, y))``
    - ``Asym(r)``                   ↦ ``∀x ∀y (r(x, y) → ¬r(y, x))``
    - ``Irr(r)``                    ↦ ``∀x ¬r(x, x)``        (ONE variable)
    - ``Func(r)``                   ↦ ``∀x ∀y ∀z (r(x, y) ∧ r(x, z) → y = z)``
    - ``Inv(p, q)``                 ↦ ``∀x ∀y (p(x, y) ↔ q(y, x))``  (ONE ↔: the
      axiom is an EQUALITY of relations, not two inclusions)
    - ``Sym(r)``                    ↦ ``∀x ∀y (r(x, y) → r(y, x))``
    - ``Refl(r)``                   ↦ ``∀x r(x, x)``
    - ``InvFunc(r)``                ↦ ``∀x ∀y ∀z (r(y, x) ∧ r(z, x) → y = z)``
      (the argument order is the whole content of the axiom)
    - ``p1 ∘ p2 ⊑ q``               ↦ ``∀x ∀y ∀z (p1(x, y) ∧ p2(y, z) → q(x, z))``
    - ``Dom(r, C)``                 ↦ ``∀x ∀y (r(x, y) → π(C, x))``
    - ``Rng(r, C)``                 ↦ ``∀x ∀y (r(x, y) → π(C, y))``   (the filler
      at the SECOND variable — the only difference from the domain axiom)

    An ``EquivalentObjectProperties`` axiom has no entry of its own because
    :meth:`~unicode_fol_kit.dl.tableau.TBox.add_equivalent_roles` stores it as
    the role inclusions it abbreviates, so it renders as those.

    This is the ROLE box only: the data box's images are
    :func:`databox_to_fol`'s, so a TBox carrying data axioms alone renders as
    the tautology here (the role box IS empty). :func:`kb_to_fol` renders both.

    Set-valued fields are sorted before rendering so the output (and hence any
    string comparison of it) is deterministic despite them being unordered
    ``set``s. A role box with no axioms at all — including every plain ALC
    ``TBox`` predating this function — renders as a tautology, matching
    :func:`tbox_to_fol`'s own empty-TBox convention.

    This is a SIDE axiom of every question asked relative to ``tbox``: pass it
    (or, better, the per-axiom tuple :attr:`KnowledgeBaseFOL.axioms`) as a
    premise of ``api.prove`` — :func:`kb_to_fol` does that bookkeeping.

    ``x``, ``y`` and ``z`` are the PREFERRED names of the bound variables: one
    that is also the name of an individual a domain or range filler names
    (``∃r.{x}``) is renamed to the first free ``letter + digits`` instead of
    binding that individual (see :func:`_binder_names`).

    The images of the boxes are built one call at a time, so a name used as two
    kinds of thing ACROSS boxes (an object property here, a data property in the
    data box) cannot be seen by any one of them: the refusal of such a clash is
    per call, over what the call is given. :func:`kb_to_fol` is the call that
    sees everything, and refuses it; :func:`check_kb_names` runs the same check
    over the boxes of images rendered separately. A class, an object property and
    an individual of one name are three symbols here (see :func:`kb_to_fol`).

    Raises:
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            a role-box entry does not hold a usable role —
            see :class:`~unicode_fol_kit.dl.tableau.RoleExpressionError`. The
            builders refuse the same values, so this fires only for a ``TBox``
            assembled or mutated by hand — and it is the SAME validation the
            tableau's shared guard runs, so both routes refuse it.
    """
    return _conjoin([a.formula for a in _rbox_axioms(tbox, x, y, z)])


def _databox_axioms(tbox: TBox, x: str = "x", v: str = "v",
                    w: str = "w", *,
                    avoid: Optional[Iterable[str]] = None) -> List[SideAxiom]:
    """The data box of ``tbox`` as :class:`SideAxiom` s of group ``"data"`` — in
    the order :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS` lists the kinds.
    Every OWL 2 direct-semantics sentence below is derived in
    :func:`databox_to_fol`'s docstring. Property names are re-validated here, the
    second line of defence behind the builders, by the SAME validation
    (:func:`~unicode_fol_kit.dl.tableau._validate_data_box`) the tableau's
    shared guard runs, and the prefix variables are renamed away from the
    knowledge base's individuals exactly as :func:`_rbox_axioms` does — a data
    property domain over ``∃r.{v}`` must not bind the individual ``v``.
    """
    where = "dl.databox_to_fol"
    _validate_data_box(tbox, where=where)
    avoid = (_kb_individual_names(tbox, None) if avoid is None else set(avoid))
    x, v, w = _binder_names((x, v, w), avoid)
    parts: List[SideAxiom] = []

    def closed(variables, body) -> Node:
        return _forall([Variable(name) for name in variables], body)

    for sub_prop, super_prop in tbox.data_property_inclusions:
        vx, vv = Variable(x), Variable(v)
        parts.append(SideAxiom("SubDataPropertyOf", "data", closed((x, v), Implies(
            Atom(sub_prop, (vx, vv)), Atom(super_prop, (vx, vv))))))
    for left, right in tbox.disjoint_data_property_pairs:
        vx, vv = Variable(x), Variable(v)
        parts.append(SideAxiom("DisjointDataProperties", "data", closed((x, v), _FNot(
            _FAnd(Atom(left, (vx, vv)), Atom(right, (vx, vv)))))))
    for prop in sorted(tbox.functional_data_properties):
        vx, vv, vw = Variable(x), Variable(v), Variable(w)
        parts.append(SideAxiom("FunctionalDataProperty", "data", closed((x, v, w), Implies(
            _FAnd(Atom(prop, (vx, vv)), Atom(prop, (vx, vw))), Atom("=", (vv, vw))))))
    for prop, concept in tbox.data_property_domains:
        vx, vv = Variable(x), Variable(v)
        # The filler is a full class expression (a union in two OEO axioms), so
        # it goes through _translate at the FIRST variable; the avoid set
        # carries the prefix variables (already renamed away from every
        # individual) and every individual of the knowledge base.
        fresh = _fresh_var_factory(
            x, avoid={x, v, w} | avoid | _individual_names(concept))
        parts.append(SideAxiom("DataPropertyDomain", "data", closed((x, v), Implies(
            Atom(prop, (vx, vv)), _translate(concept, vx, fresh)))))
    for prop, datarange in tbox.data_property_ranges:
        vx, vv = Variable(x), Variable(v)
        parts.append(SideAxiom("DataPropertyRange", "data", closed((x, v), Implies(
            Atom(prop, (vx, vv)), datarange_to_fol(datarange, vv)))))
    for name, datarange in tbox.datatype_definitions:
        vv = Variable(v)
        parts.append(SideAxiom("DatatypeDefinition", "data", closed((v,), Iff(
            Atom(name, (vv,)), datarange_to_fol(datarange, vv)))))
    return parts


def databox_to_fol(tbox: TBox, x: str = "x", v: str = "v", w: str = "w") -> Node:
    """Render every data-box axiom in ``tbox`` as its FOL image and conjoin them
    (see "The data layer" in the module docstring). Each image is the OWL 2
    direct-semantics sentence for that axiom, the datatype read as a unary
    predicate over the one domain:

    - ``SubDataPropertyOf(d e)``       ↦ ``∀x ∀v (d(x, v) → e(x, v))``
    - ``DisjointDataProperties(d e)``  ↦ ``∀x ∀v ¬(d(x, v) ∧ e(x, v))``
    - ``FunctionalDataProperty(d)``    ↦ ``∀x ∀v ∀w (d(x, v) ∧ d(x, w) → v = w)``
    - ``DataPropertyDomain(d C)``      ↦ ``∀x ∀v (d(x, v) → π(C, x))``
    - ``DataPropertyRange(d DR)``      ↦ ``∀x ∀v (d(x, v) → δ(DR, v))``
    - ``DatatypeDefinition(D DR)``     ↦ ``∀v (D(v) ↔ δ(DR, v))`` — a DEFINITION,
      so a biconditional and not a pair of inclusions read one way.

    ``EquivalentDataProperties`` has no entry of its own: it is stored as the
    inclusions it abbreviates. A data box with nothing in it is a tautology,
    like :func:`rbox_to_fol`'s empty role box. This is a SIDE axiom of every
    question asked relative to ``tbox`` — :func:`kb_to_fol` does the
    bookkeeping, and adds the two-sorted axioms of :func:`data_sort_axioms`.

    The refusal of a name used as two kinds of thing is PER CALL: this function
    sees the vocabulary of ``tbox``, not of the ABox or of a role box rendered
    separately, so a clash across boxes built one call at a time is invisible to
    it. :func:`kb_to_fol` is the call that sees everything, and
    :func:`check_kb_names` runs the same check over boxes rendered separately.

    Raises:
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            a data-box entry does not hold a usable property
            name (only reachable for a ``TBox`` assembled by hand).
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            a literal in a data range has no term, or a
            name of ``tbox`` is used both as an object property and a data
            property or both as a class and a datatype (see :func:`kb_to_fol`).
    """
    where = "dl.databox_to_fol"
    _validate_data_box(tbox, where=where)
    # The whole TBox's vocabulary decides whether a predicate of this image is
    # also another kind's (``P`` an object role in a GCI, a data property here).
    vocabulary = _collect_vocabulary(tbox, None)
    _check_name_punning(vocabulary, where)
    return _conjoin([a.formula for a in _databox_axioms(
        tbox, x, v, w, avoid=vocabulary.individuals)])


def abox_to_fol(abox: ABox) -> Node:
    """Render every assertion in ``abox`` as a FOL formula and conjoin them.

    A concept assertion ``a : C`` becomes ``π(C, a)`` with the individual
    ``a`` translated as a :class:`~unicode_fol_kit.fol.nodes.Constant` (not a
    Variable — see "GCIs, TBoxes, ABoxes" above for why this matters). A role
    assertion ``(a, b) : r`` becomes ``r(a, b)``. A distinctness assertion
    ``a ≠ b`` (see :meth:`~unicode_fol_kit.dl.tableau.ABox.assert_distinct` and
    "Qualified number restrictions" in :mod:`unicode_fol_kit.dl.tableau`'s module
    docstring — this reasoner has no unique name assumption, so this is the ONLY
    thing that ever forces two individuals apart) becomes the FOL atom ``a ≠ b``
    directly — no translation needed, ``Atom`` already renders it natively for
    every backend. A same-individual assertion ``a = b``
    (:meth:`~unicode_fol_kit.dl.tableau.ABox.assert_same`) is its exact mirror,
    and a negative role assertion
    (:meth:`~unicode_fol_kit.dl.tableau.ABox.assert_negative_role`) becomes the
    ground literal ``¬r(a, b)``. A data property assertion
    (:meth:`~unicode_fol_kit.dl.tableau.ABox.assert_data`) is the ground atom
    ``d(a, t)`` for the literal's term ``t`` (``HasNumber(alice, 400)``), and a
    negative one its negation. An ABox with no assertions at all renders as a
    tautology.

    The conjuncts come in assertion-kind order — concept assertions, role
    assertions, distinctness, sameness, negative role assertions, data
    assertions, negative data assertions — each kind in the order it was
    asserted, folded by :func:`_conjoin`.

    The refusal of a name used as two kinds of thing is PER CALL, over the ABox
    alone: a name that is a role here and a data property in a TBox rendered
    separately is invisible to this function. :func:`kb_to_fol` is the call that
    sees everything, and :func:`check_kb_names` runs the same check over boxes
    rendered separately.

    The result is the ABox ALONE. Whether the assertions are consistent, or
    entail ``a : C``, *relative to a TBox* (the usual question — GCIs apply to
    every named individual, and a role box changes which edges count) is not
    answered by this formula: pass ``kb_to_fol(tbox, abox).premises`` as the
    premises of the query instead (see :func:`kb_to_fol`). An ABox-only question
    — "do these bare assertions clash?" — is exactly what this renders.

    ``abox_to_fol(ABox().assert_concept(a, C))`` is also the way to spell the
    GOAL ``π(C, a)`` of an instance-checking query with the individual as a
    constant.

    Raises:
        ~unicode_fol_kit.dl.tableau.RoleExpressionError:
            an assertion's property is an OWL 2 built-in name
            (``owl:topObjectProperty`` …), ``=``/``≠``, an inverse role or no
            name at all — see
            :func:`~unicode_fol_kit.dl.tableau._reject_abox_roles`. Printed as
            the uninterpreted predicate of that name it would be a different
            assertion (the EMPTY property relates no pair, so ``(a, b) :
            owl:bottomObjectProperty`` is inconsistent, ``(a, b) : p`` is not).
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            one name is both the property of a role
            assertion and the property of a data assertion, or both a class
            of a concept assertion and a datatype of a literal (see
            :func:`kb_to_fol`).
    """
    vocabulary = _collect_vocabulary(None, abox)
    _check_name_punning(vocabulary, "dl.abox_to_fol")
    return _abox_image(abox, vocabulary.individuals)


def _abox_image(abox: ABox, avoid: Iterable[str]) -> Node:
    """:func:`abox_to_fol` with ``avoid`` — the individual names of the whole
    knowledge base — added to the names the minted variables must avoid."""
    _reject_abox_roles(abox, where="dl.abox_to_fol")
    avoid = set(avoid)
    parts: List[Node] = []
    for individual, concept in abox.concept_assertions:
        term = Constant(individual)
        parts.append(_translate(
            concept, term,
            _fresh_var_factory(individual, avoid | _individual_names(concept))))
    for a, b, role in abox.role_assertions:
        parts.append(Atom(role, (Constant(a), Constant(b))))
    for a, b in abox.distinct_assertions:
        parts.append(Atom("≠", (Constant(a), Constant(b))))
    # SameIndividual(a b) holds iff a^I = b^I: the exact mirror of the
    # distinctness atom above, and ``=`` is native in every backend (Z3 ==,
    # Prover9 =, TPTP =) exactly as ``≠`` is.
    for a, b in abox.same_assertions:
        parts.append(Atom("=", (Constant(a), Constant(b))))
    # NegativeObjectPropertyAssertion(r a b) holds iff <a^I, b^I> ∉ r^I: the
    # negated GROUND literal, not a concept assertion about a nominal.
    for a, b, role in abox.negative_role_assertions:
        parts.append(_FNot(Atom(role, (Constant(a), Constant(b)))))
    # DataPropertyAssertion(d a lt) holds iff <a^I, lt^LT> ∈ d^DP: the ground
    # atom, with the individual as a Constant (as for a role assertion) and the
    # literal as the TERM of its data value. Nothing is quantified, so no
    # variable is minted. The negative form is the negated ground literal.
    for individual, prop, value in abox.data_assertions:
        parts.append(Atom(prop, (Constant(individual), value.to_term())))
    for individual, prop, value in abox.negative_data_assertions:
        parts.append(_FNot(Atom(prop, (Constant(individual), value.to_term()))))
    return _conjoin(parts)


# --------------------------------------------------------------------------- #
# A whole knowledge base: the TBox, the ABox and the role box, kept apart.
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class KnowledgeBaseFOL:
    """The FOL image of a knowledge base ``(tbox, abox)`` — see :func:`kb_to_fol`.

    Fields:

    * ``formula`` — the knowledge base itself: the conjunction of the concept-
      inclusion image and the ABox image (a half with nothing in it is left out,
      so a TBox-only knowledge base has ``formula == tbox``; with nothing at all
      it is the usual equality tautology).
    * ``side_axioms`` — the SIDE axioms as :class:`SideAxiom` values, each
      carrying the OWL ``kind`` it came from and its ``group``: the role-box
      image (one per role inclusion, then one per further role-box axiom in the
      order of ``dl.tableau._AXIOM_KINDS``, set-valued fields sorted), the
      data-box image and, for a knowledge base with a data layer, the sort
      axioms; empty when the TBox has none of them. They are premises,
      NEVER conjoined into ``formula``. ``axioms`` is the bare-formula view of
      this ONE field, not a second list that could drift out of step with it.
    * ``formulas`` — the per-axiom list behind ``formula``: the concept-
      inclusion image and the ABox image, each present only when it has
      content, so ``formula == _conjoin(formulas)``. A caller with an
      ontology-sized knowledge base can pass ``(*kb.formulas, *kb.axioms)``
      as premises instead of the single conjunction; the two are
      entailment-equivalent (a conjunction of premises and a list of premises
      have the same models).
    * ``tbox`` / ``abox`` — the two halves of ``formula`` on their own
      (:func:`tbox_to_fol` with ``concept_inclusions_only=True``, and
      :func:`abox_to_fol`), each a tautology when empty. A question that is about
      the terminology alone (subsumption, concept satisfiability) needs ``tbox``
      but not ``abox``.
    * ``individuals`` — the sorted names of the individuals the ABox mentions
      (concept assertions, role-assertion endpoints, identity, distinctness and
      negative role assertions — the ``individual_positions`` column of
      :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`, so an assertion kind
      added later is counted without touching this scan); each is a FOL
      :class:`~unicode_fol_kit.fol.nodes.Constant` of that name in
      ``abox``/``formula``, which is what a goal about an individual has to use.
      An individual named in an ABox assertion is an individual of the ABox
      wherever in the assertion it stands: ``a : ∃r.{b}`` (a value restriction
      or a nominal, at any depth of the asserted class expression) lists ``b``
      as well as ``a``. The in-house tableau refuses those concepts, so what
      this changes is this field and the sweeps of the external routes.

      The ABox is the SCOPE, not merely where the scan happens to look: a
      caller's individual can also reach the TBox half, as the filler of a
      nominal (``C ⊑ {a}`` → ``∀x (C(x) → x = a)``) or of a value restriction
      (``C ⊑ ∃r.{a}`` → ``∀x (C(x) → r(x, a))``), and such a name is a
      ``Constant`` in ``formula`` that this field does NOT report. That is
      deliberate: ``individuals`` is the list of things the knowledge base
      makes ASSERTIONS about, which is what ``instance_retrieval`` and
      ``realize_all`` enumerate, and the two routes agree only because all
      three read the same scan. A caller that needs every name in term
      position should walk the image — ``node.walk()`` yields terms too.

    * ``separation`` — which theory of the data layer ``side_axioms`` carries:
      ``"two-sorted"`` (the object/data separation, the typing of every
      property and individual, the datatype lattice, literal distinctness — and
      every GCI of ``formula``/``tbox`` relativised to the object domain),
      ``"data-lattice"`` (the datatype facts only, no object/data separation,
      GCIs as written) or ``"none"`` (the data-box images alone). ``"none"`` for
      every knowledge base without a data layer, whatever was asked for, since
      nothing is then added. A GOAL asked of a ``"two-sorted"`` knowledge base
      must be relativised too — :meth:`subsumption_goal`,
      :meth:`unsatisfiability_goal` and :meth:`instance_goal` build it so.
    * ``data_layer`` — whether the knowledge base, together with the ``query=``
      concepts it was built for, has a data layer at all: a data property, a
      datatype or a literal occurs in it. :attr:`refutation_is_decisive` is its
      negation.

    ``premises`` and ``tbox_premises`` are the two premise lists the common
    questions need, and the three ``*_goal`` methods build the matching goal.
    How to use them with :func:`unicode_fol_kit.api.prove` is in
    :func:`kb_to_fol`.
    """

    formula: Node
    side_axioms: Tuple[SideAxiom, ...]
    tbox: Node
    abox: Node
    individuals: Tuple[str, ...] = ()
    formulas: Tuple[Node, ...] = ()
    separation: str = "none"
    data_layer: bool = False
    # What the side axioms were derived from, read by the three goal methods to
    # tell a concept they cover from one they do not. Internal: not part of the
    # logical content, so it neither prints nor takes part in ==.
    _coverage: Optional["_Coverage"] = field(default=None, repr=False, compare=False)

    @property
    def axioms(self) -> Tuple[Node, ...]:
        """``side_axioms``' formulas alone, in the same order — the premise list
        to hand a prover.

        DERIVED, not stored: one source of truth means no package can append to
        one list and forget the other.
        """
        return tuple(a.formula for a in self.side_axioms)

    @property
    def rbox_axioms(self) -> Tuple[Node, ...]:
        """The ``group == "rbox"`` side axioms' formulas — the role-box image."""
        return tuple(a.formula for a in self.side_axioms if a.group == "rbox")

    @property
    def data_axioms(self) -> Tuple[Node, ...]:
        """The side axioms' formulas belonging to the data layer (``group`` in
        ``"data"`` — the images of the data-box axioms —, ``"sort"`` — the
        object/data separation and the typing — and ``"datatype"`` — the
        datatype lattice, literal typing and literal distinctness).

        Empty for a knowledge base without a data layer. A caller can ask "which
        of these premises belong to the data layer?" of any bundle, without
        knowing which entry point built it.
        """
        return tuple(a.formula for a in self.side_axioms
                     if a.group in ("data", "sort", "datatype"))

    def axioms_of_kind(self, kind: str) -> Tuple[Node, ...]:
        """The side axioms' formulas whose OWL ``kind`` is ``kind``, in order.

        ``kind`` is an OWL 2 keyword as :data:`SideAxiom.kind` spells it, e.g.
        ``"TransitiveObjectProperty"``. An unknown kind gives ``()`` rather
        than raising: the question "did this knowledge base's image carry any
        axiom of kind K?" has a correct answer for every K, and "none" is it.
        """
        return tuple(a.formula for a in self.side_axioms if a.kind == kind)

    @property
    def premises(self) -> Tuple[Node, ...]:
        """``(formula, *axioms)`` — "the whole knowledge base holds": the premises
        of a question relative to the TBox AND the ABox (instance checking).

        For an ontology-sized knowledge base ``(*formulas, *axioms)`` says the
        same thing one axiom at a time; see ``formulas``."""
        return (self.formula, *self.axioms)

    @property
    def tbox_premises(self) -> Tuple[Node, ...]:
        """``(tbox, *axioms)`` — "the terminology holds", ABox left out: the
        premises of a question about concepts relative to the TBox
        (subsumption, concept satisfiability)."""
        return (self.tbox, *self.axioms)

    @property
    def refutation_is_decisive(self) -> bool:
        """Whether a ``"refuted"`` verdict of :func:`unicode_fol_kit.api.prove`
        over this bundle is an answer about OWL 2, and not only about the image:
        ``True`` exactly when the knowledge base (with the ``query=`` concepts it
        was built for) has NO data layer.

        What a caller may conclude from each status, for a goal built by
        :meth:`subsumption_goal`, :meth:`unsatisfiability_goal` or
        :meth:`instance_goal` and the premises the method's docstring names:

        * ``"proved"`` — YES, for every goal these methods hand out. Under the
          two-sorted separation the image is SOUND for the data layer: every
          OWL 2 interpretation of the knowledge base expands to a model of the
          image, so what the image entails the knowledge base entails. That
          is NOT so for a data-layer bundle built with
          ``separation="data-lattice"`` or ``"none"``: its inclusions also range
          over data values, which makes its premises stronger than OWL 2's, and
          the methods refuse such a bundle by name instead of building a goal.
        * ``"refuted"`` — NO when this property is ``True`` (the image of an
          object-only knowledge base is faithful: a countermodel of the image
          is one of the knowledge base). When it is ``False`` it means only
          that the IMAGE has a countermodel, and the image is deliberately not
          COMPLETE, so the countermodel may be one OWL 2 excludes. Three things
          it does not state: an ordering facet is an uninterpreted comparison
          (a range ``xsd:integer[>= 10]`` with ``HasN(a, 5)`` is OWL-inconsistent
          and ``refuted`` here; ``HasN(a, 15)`` entails ``a : ∃HasN.xsd:integer[>= 3]``
          in OWL and does not here); a literal is typed only by the datatype it
          was written with (``d(a, "1.0"^^xsd:decimal)`` entails
          ``a : ∃d.xsd:integer`` in OWL and does not here, and
          ``d(a, "5"^^xsd:int)`` entails ``a : ∃d.xsd:nonNegativeInteger``); and
          the size of a value space is not stated. Decide facet arithmetic over
          the data ranges alone with ``atp.z3_arith.is_valid_arith``.
        * ``"unknown"`` — no answer within the budget, in either direction.
        """
        return not self.data_layer

    def _covers(self, method: str, *concepts: Concept) -> "_Coverage":
        """The coverage of this bundle, after checking that it covers
        ``concepts``; raises by name otherwise (see :func:`_check_goal_concepts`)."""
        coverage = self._coverage
        if coverage is None:
            raise ValueError(
                f"KnowledgeBaseFOL.{method}: this bundle was not built by "
                f"dl.kb_to_fol, so it does not know which vocabulary its side "
                f"axioms cover and cannot say whether a goal is the question "
                f"it asks. Build it with dl.kb_to_fol(tbox, abox, query=[...]).")
        if self.data_layer and self.separation != "two-sorted":
            raise UnsupportedDatatypeError(
                f"KnowledgeBaseFOL.{method}: this bundle has a data layer and was "
                f"built with separation={self.separation!r}. Its inclusions are then "
                f"not restricted to the object domain, so its premises are STRONGER "
                f"than OWL 2's — '⊤ ⊑ {{a}}' also ranges over data values there — "
                f"and an OWL-consistent knowledge base can have an inconsistent "
                f"image, from which every goal is proved. A proof over this bundle "
                f"does not transfer to OWL 2. Build it with "
                f"separation='two-sorted' (the default).")
        _check_goal_concepts(coverage, self.separation, self.data_layer,
                             concepts, where=f"KnowledgeBaseFOL.{method}")
        return coverage

    def subsumption_goal(self, sub: Concept, sup: Concept) -> Node:
        """The goal ``sub ⊑ sup``, relativised the way this bundle needs it
        (to the object domain when ``separation == "two-sorted"``, as written
        otherwise): ``api.prove(kb.subsumption_goal(sub, sup),
        kb.tbox_premises)`` is ``"proved"`` ⇒ ``sub ⊑ sup`` follows from the
        terminology (what ``dl.subsumes(sub, sup, tbox)`` asks, over the
        constructs the tableau does not refuse). With ``kb.premises`` instead
        the ABox is a premise as well. ``"refuted"`` is the answer NO only
        when :attr:`refutation_is_decisive`.

        Raises:
            ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
                a concept names a data property, a
                datatype, a literal (or, on a two-sorted bundle, an object
                property) the bundle's side axioms do not cover, so the
                question would be asked of a weaker theory than the one OWL 2
                describes — pass ``query=[sub, sup]`` to :func:`kb_to_fol`; or
                a name is used as two kinds of thing at once.
            ~unicode_fol_kit.dl.tableau.RoleExpressionError:
                a restriction's role is an OWL 2 built-in
                property name.
        """
        coverage = self._covers("subsumption_goal", sub, sup)
        return _subsumption_image(sub, sup, coverage.var,
                                  self.separation == "two-sorted", coverage.avoid)

    def unsatisfiability_goal(self, concept: Concept) -> Node:
        """The goal "no object is in ``concept``" — on a two-sorted bundle
        ``¬∃x (OwlThing(x) ∧ π(concept, x))``, otherwise ``¬∃x π(concept, x)``:
        ``api.prove(kb.unsatisfiability_goal(concept), kb.tbox_premises)`` is
        ``"proved"`` ⇒ the concept is UNSATISFIABLE with respect to the
        terminology (``dl.concept_satisfiable(concept, tbox)`` is ``False``). A
        ``"refuted"`` answers "satisfiable" only when
        :attr:`refutation_is_decisive`.

        The ``OwlThing`` conjunct is what makes this the OWL 2 question: a data
        value satisfies every concept that says nothing about it, so without it
        ``∃HasV.xsd:integer ⊓ ∀HasV.xsd:string`` would be "satisfiable" by a
        data value, where OWL 2 makes it unsatisfiable (the datatypes are
        disjoint).

        Raises:
            ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
                as :meth:`subsumption_goal`, with ``query=[concept]``.
            ~unicode_fol_kit.dl.tableau.RoleExpressionError:
                as :meth:`subsumption_goal`, with ``query=[concept]``.
        """
        coverage = self._covers("unsatisfiability_goal", concept)
        avoid = set(coverage.avoid) | _individual_names(concept)
        (var,) = _binder_names((coverage.var,), avoid)
        x = Variable(var)
        body = _translate(concept, x, _fresh_var_factory(var, avoid))
        if self.separation == "two-sorted":
            body = _FAnd(Atom(OWL_THING, (x,)), body)
        return _FNot(Quantifier("∃", x, body))

    def instance_goal(self, individual: str, concept: Concept) -> Node:
        """The goal ``individual : concept`` — ``π(concept, individual)`` with
        the individual as a constant: ``api.prove(kb.instance_goal(a, C),
        kb.premises)`` is ``"proved"`` ⇒ the knowledge base entails ``a : C``
        (``dl.instance_check(abox, a, C, tbox)``). An individual the bundle
        does not type (it occurs in no axiom) is asked about as an OBJECT on a
        two-sorted bundle, ``OwlThing(a) → π(C, a)``: every OWL 2 individual is
        in the object domain.

        Raises:
            ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
                as :meth:`subsumption_goal`, with ``query=[concept]``.
            ~unicode_fol_kit.dl.tableau.RoleExpressionError:
                as :meth:`subsumption_goal`, with ``query=[concept]``.
            TypeError: ``individual`` is not a non-empty name.
        """
        if not isinstance(individual, str) or not individual:
            raise TypeError(
                f"KnowledgeBaseFOL.instance_goal: the individual is a non-empty "
                f"name (str), got {type(individual).__name__} {individual!r}.")
        coverage = self._covers("instance_goal", concept)
        term = Constant(individual)
        avoid = set(coverage.avoid) | _individual_names(concept) | {individual}
        goal = _translate(concept, term, _fresh_var_factory(individual, avoid))
        if self.separation == "two-sorted" and individual not in coverage.individuals:
            return Implies(Atom(OWL_THING, (term,)), goal)
        return goal

    def to_dict(self) -> dict:
        """JSON-compatible form: every formula through its own ``to_dict``.

        The five keys are the FORMULAS — ``side_axioms``' ``kind``/``group``
        labels are bookkeeping for the caller, not part of the logical content,
        and ``formulas`` is a regrouping of ``formula``; a reader of this dict
        loses nothing it could use to ask a prover a question.
        """
        return {
            "formula": self.formula.to_dict(),
            "axioms": [a.to_dict() for a in self.axioms],
            "tbox": self.tbox.to_dict(),
            "abox": self.abox.to_dict(),
            "individuals": list(self.individuals),
        }


def _abox_individuals(abox: ABox) -> Tuple[str, ...]:
    """The individual names ``abox`` mentions, sorted — and NO anonymous
    fallback individual, unlike the tableau's own (private) ``_individuals``:
    there the placeholder exists so an empty ABox still has a node to run on,
    here it would be a constant no assertion ever named.

    The scan itself is :func:`~unicode_fol_kit.dl.tableau._abox_individual_names`,
    driven by :data:`~unicode_fol_kit.dl.tableau._AXIOM_KINDS`'
    ``individual_positions`` column: an assertion kind added later would
    otherwise have to be remembered in two independent field-by-field scans,
    and the one that forgot it would report ``individuals == ()`` for a
    knowledge base that names individuals.
    """
    return tuple(sorted(_abox_individual_names(abox)))


# --------------------------------------------------------------------------- #
# The two-sorted discipline: the vocabulary a knowledge base uses, and the
# side axioms derived from it.
# --------------------------------------------------------------------------- #

_SEPARATIONS = ("two-sorted", "data-lattice", "none")


def _check_separation(separation: str, where: str = "dl.kb_to_fol") -> None:
    if separation not in _SEPARATIONS:
        raise UnsupportedDatatypeError(
            f"{where}: separation={separation!r} is not one of "
            f"{', '.join(map(repr, _SEPARATIONS))}. 'two-sorted' is the full "
            f"discipline (the default), 'data-lattice' only the datatype facts, "
            f"'none' the data-box images alone.")


@dataclass
class _Vocabulary:
    """The names a knowledge base uses, by kind — what the sort axioms are
    derived FROM, so that they are scoped to the knowledge base's own vocabulary
    and not to every name in the OWL 2 datatype map."""

    classes: Set[str] = field(default_factory=set)
    object_roles: Set[str] = field(default_factory=set)
    data_properties: Set[str] = field(default_factory=set)
    individuals: Set[str] = field(default_factory=set)
    datatypes: Set[str] = field(default_factory=set)
    literals: List[Literal] = field(default_factory=list)

    def has_data(self) -> bool:
        """True iff the knowledge base has a data layer at all: a data property,
        a datatype or a literal occurs in it. Every data axiom and every data
        restriction names at least a data property, so this is the whole test."""
        return bool(self.data_properties or self.datatypes or self.literals)

    def add_role(self, role) -> None:
        self.object_roles.add(role.role if isinstance(role, InverseRole) else role)

    def add_literal(self, literal: Literal) -> None:
        self.literals.append(literal)
        self.datatypes.add(literal.datatype)

    def add_datarange(self, datarange: DataRange) -> None:
        self.datatypes.update(datarange_datatypes(datarange))
        for literal in datarange_literals(datarange):
            self.add_literal(literal)

    def add_concept(self, concept: Concept) -> None:
        if isinstance(concept, Atomic):
            self.classes.add(concept.name)
        elif isinstance(concept, Nominal):
            self.individuals.add(concept.individual)
        elif isinstance(concept, HasValue):
            self.add_role(concept.role)
            self.individuals.add(concept.individual)
        elif isinstance(concept, Not):
            self.add_concept(concept.concept)
        elif isinstance(concept, (And, Or)):
            self.add_concept(concept.left)
            self.add_concept(concept.right)
        elif isinstance(concept, (Exists, ForAll, AtLeast, AtMost)):
            self.add_role(concept.role)
            self.add_concept(concept.concept)
        elif isinstance(concept, (DataExists, DataForAll, DataAtLeast, DataAtMost)):
            self.data_properties.add(concept.prop)
            self.add_datarange(concept.datarange)
        elif isinstance(concept, DataHasValue):
            self.data_properties.add(concept.prop)
            self.add_literal(concept.value)
        # Top / Bottom mention nothing.


def _collect_vocabulary(tbox: Optional[TBox], abox: Optional[ABox], *,
                        where: str = "dl.translate",
                        query: Iterable[Concept] = ()) -> _Vocabulary:
    """Walk every axiom of ``(tbox, abox)`` once and collect its vocabulary,
    then the vocabulary of the ``query`` concepts: the concepts a caller is going
    to ASK about join the knowledge base's vocabulary, because everything derived
    from the vocabulary (the separation regime, the sort and datatype axioms, the
    punning check, the avoid set of the bound variables) must cover the question
    as well as the knowledge base. See :func:`kb_to_fol`.

    Hand-listed over the fields, like every consumer of the TBox/ABox shape, and
    for that reason pinned by ``tests/test_dl_data.py``: a field the walk does
    not read would silently shrink the sort axioms.

    Every stored value is VALIDATED first (``dl.tableau._validate_role_box`` and
    friends — the same checks the tableau's shared guard runs), because this walk
    is the first thing every image does with a ``TBox`` and a hand-built one with
    a malformed entry (a 3-tuple where a pair is stored) would otherwise die here,
    with the bare ``ValueError`` of an unpacking, before any second line of
    defence could name it.
    """
    if tbox is not None:
        _validate_role_box(tbox, where=where)
        _validate_data_box(tbox, where=where)
    _reject_abox_roles(abox, where=where)
    v = _Vocabulary()
    if tbox is not None:
        for sub, sup in tbox.inclusions:
            v.add_concept(sub)
            v.add_concept(sup)
        for sub_role, super_role in tbox.role_inclusions:
            v.add_role(sub_role)
            v.add_role(super_role)
        for names in (tbox.transitive_roles, tbox.symmetric_roles,
                      tbox.asymmetric_roles, tbox.reflexive_roles,
                      tbox.irreflexive_roles, tbox.functional_roles,
                      tbox.inverse_functional_roles):
            v.object_roles.update(names)
        for pair in tbox.inverse_role_pairs + tbox.disjoint_role_pairs:
            v.object_roles.update(pair)
        for chain, super_role in tbox.role_chains:
            v.object_roles.update(chain)
            v.object_roles.add(super_role)
        for role, concept in tbox.role_domains + tbox.role_ranges:
            v.object_roles.add(role)
            v.add_concept(concept)
        for pair in tbox.data_property_inclusions + tbox.disjoint_data_property_pairs:
            v.data_properties.update(pair)
        v.data_properties.update(tbox.functional_data_properties)
        for prop, concept in tbox.data_property_domains:
            v.data_properties.add(prop)
            v.add_concept(concept)
        for prop, datarange in tbox.data_property_ranges:
            v.data_properties.add(prop)
            v.add_datarange(datarange)
        for name, datarange in tbox.datatype_definitions:
            v.datatypes.add(canonical_datatype_name(name))
            v.add_datarange(datarange)
    if abox is not None:
        for individual, concept in abox.concept_assertions:
            v.individuals.add(individual)
            v.add_concept(concept)
        for a, b, role in abox.role_assertions + abox.negative_role_assertions:
            v.individuals.update((a, b))
            v.object_roles.add(role)
        for a, b in abox.distinct_assertions + abox.same_assertions:
            v.individuals.update((a, b))
        for individual, prop, literal in abox.data_assertions + abox.negative_data_assertions:
            v.individuals.add(individual)
            v.data_properties.add(prop)
            v.add_literal(literal)
    for concept in query:
        v.add_concept(concept)
    return v


def _check_reserved_names(vocabulary: _Vocabulary, separation: str,
                          where: str = "dl.kb_to_fol") -> None:
    """Refuse a knowledge base that uses a name the data image reserves.

    ``OwlData`` is reserved whenever there is a data layer (``rdfs:Literal`` and
    every complement are rendered with it); ``OwlThing`` only when the
    two-sorted axioms are asked for. A class that happened to be called
    ``OwlData`` would otherwise be constrained by the sort axioms as if it were
    the data domain — a silent change to the ontology's own class.
    """
    reserved = (OWL_DATA, OWL_THING) if separation == "two-sorted" else (OWL_DATA,)
    for name in reserved:
        for kind, names in (("class", vocabulary.classes),
                            ("object role", vocabulary.object_roles),
                            ("data property", vocabulary.data_properties),
                            ("individual", vocabulary.individuals),
                            ("datatype", vocabulary.datatypes)):
            if name in names:
                guard = ("the data domain" if name == OWL_DATA else "the object domain")
                raise UnsupportedDatatypeError(
                    f"{where}: {name!r} is this module's reserved guard "
                    f"predicate for {guard} of the OWL 2 two-sorted image (see "
                    f"data_sort_axioms), but this knowledge base uses {name!r} as "
                    f"a {kind} name, so the sort axioms would constrain the "
                    f"ontology's own {kind}. Rename it"
                    + (", or pass separation='data-lattice' (which reserves only "
                       "'OwlData') or 'none'." if name == OWL_THING else "."))


def _check_concepts_punning(concepts: Sequence[Concept], where: str) -> None:
    """:func:`_check_name_punning` over the vocabulary of ``concepts`` alone: the
    refusal of a pun INSIDE what a renderer is given (``∃P.B ⊓ ∃P.xsd:integer``),
    for the entry points that never see a knowledge base."""
    vocabulary = _Vocabulary()
    for concept in concepts:
        vocabulary.add_concept(concept)
    _check_name_punning(vocabulary, where, "the concepts it is given")


def _check_name_punning(vocabulary: _Vocabulary, where: str,
                        scope: str = "this knowledge base") -> None:
    """Refuse a knowledge base that uses ONE name for two kinds OWL 2 DL keeps
    apart: an object property and a data property, or a class and a datatype.

    OWL 2 DL (Structural Specification, section 5.8.1) forbids both pairs. The
    stored axioms keep the kinds apart (the TBox has separate fields for roles
    and data properties), but the first-order image has ONE predicate per name:
    ``P(x, y)`` of an object property and ``P(x, v)`` of a data property are the
    same predicate, so the conflation changes what follows from the knowledge
    base (a functional ``P`` with an object successor and a data value became
    INCONSISTENT, which the two-sorted reading says it is not). Printing it as
    one predicate would be an approximation; so it is refused, by name, before
    any image is built. A class, an object property and an individual that share
    a name (punning OWL 2 DL does allow) are not touched.

    A class is compared with the datatypes by its CANONICAL name, so a class
    spelled with the full ``http://www.w3.org/2001/XMLSchema#integer`` IRI is
    the datatype ``xsd:integer`` too.
    """
    pairs = (
        ("an object property", vocabulary.object_roles,
         "a data property", vocabulary.data_properties,
         lambda name: name),
        ("a class", vocabulary.classes,
         "a datatype", vocabulary.datatypes,
         canonical_datatype_name),
    )
    for first_kind, first, second_kind, second, canonical in pairs:
        if not first or not second:
            continue
        clash = sorted(name for name in first if canonical(name) in second)
        if clash:
            name = clash[0]
            raise UnsupportedDatatypeError(
                f"{where}: the name {name!r} is used as both {first_kind} and "
                f"{second_kind} in {scope}. OWL 2 DL forbids that "
                f"(the two are disjoint kinds), and the first-order image has "
                f"ONE predicate per name, so it would read {name!r} as both at "
                f"once and change what follows. Rename one of them"
                + (f" (all clashing names: {', '.join(map(repr, clash))})."
                   if len(clash) > 1 else "."))


def _literal_family(literal: Literal) -> Optional[str]:
    """The group within which two distinct literal TERMS are known to be
    distinct VALUES, or ``None`` when this kit cannot say.

    Exact numbers are compared by value (``Number``), the strings by their
    (whitespace-processed) text — ``xsd:string``, language-tagged strings, and
    ``xsd:normalizedString``/``xsd:token``, whose term IS the ``xsd:string`` term
    of the processed text (:meth:`~unicode_fol_kit.dl.datatypes.Literal.to_term`)
    —, ``xsd:anyURI`` by its collapsed text, ``xsd:boolean`` by its canonical
    ``true``/``false``. Other datatypes (``xsd:dateTime``, ``xsd:hexBinary``, …)
    have lexical forms that are NOT in one-to-one correspondence with values
    (``"0A"`` and ``"0a"`` are one hexBinary value), so claiming two different
    spellings denote different values would be unsound.
    """
    if literal.datatype in EXACT_NUMBER_DATATYPES:
        return "number"
    if literal.datatype in ("xsd:string", "rdf:PlainLiteral", "xsd:normalizedString",
                            "xsd:token"):
        return "string"
    if literal.datatype == "xsd:anyURI":
        return "anyURI"
    if literal.datatype == "xsd:boolean":
        return "boolean"
    return None


@dataclass(frozen=True)
class _Coverage:
    """What the side axioms of one :func:`kb_to_fol` bundle were derived from:
    the vocabulary of the knowledge base AND of the ``query=`` concepts, and the
    ``var`` the bundle's GCIs bind. The three goal methods of
    :class:`KnowledgeBaseFOL` read it to tell a concept the bundle covers from one
    it does not. ``individuals`` is every individual the image types and so
    every one a bound variable must avoid.
    """

    var: str
    vocabulary: _Vocabulary
    individuals: FrozenSet[str]
    literals: FrozenSet[Tuple[Node, str]]       # (term, written datatype) per literal

    @property
    def avoid(self) -> FrozenSet[str]:
        return self.individuals


def _reject_data_concept(concept: Concept, where: str) -> None:
    """Refuse, by name, a concept with a data restriction for the registry edge
    ``alc → fol``, which declares ``faithful`` and carries no side axioms.

    That is true of a concept without a data layer. With one the image is a
    guarded ONE-sorted theory whose sorts, typing and datatype lattice are side
    axioms of a KNOWLEDGE BASE (:func:`data_sort_axioms`), so the bare image is a
    weaker theory: ``∃HasV.xsd:integer ⊓ ∀HasV.xsd:string`` closed existentially is
    satisfiable by a data value, where OWL 2 makes it unsatisfiable. A concept
    without one is untouched.
    """
    vocabulary = _Vocabulary()
    vocabulary.add_concept(concept)
    if not vocabulary.has_data():
        return
    names = ([f"the data property {name!r}" for name in sorted(vocabulary.data_properties)]
             + [f"the datatype {name!r}" for name in sorted(vocabulary.datatypes)])
    raise UnsupportedDatatypeError(
        f"{where}: the concept {concept.to_unicode()} has a data restriction "
        f"({', '.join(names)}). Its first-order image is ONE-sorted over "
        f"OwlThing and OwlData, and what makes it two-sorted — the separation "
        f"of the two domains, the typing of the property, the datatype lattice "
        f"and its disjointness, the literal facts — are side axioms of a "
        f"KNOWLEDGE BASE, not of one concept. This edge declares 'faithful' "
        f"and carries none, so it would answer for a weaker theory: "
        f"∃HasV.xsd:integer ⊓ ∀HasV.xsd:string would be satisfiable (a data "
        f"value satisfies it) where OWL 2 makes it unsatisfiable. Ask the "
        f"knowledge base instead: kb = dl.kb_to_fol(tbox, abox, "
        f"query=[concept]), then api.prove(kb.unsatisfiability_goal(concept), "
        f"kb.tbox_premises) (kb.subsumption_goal and kb.instance_goal are "
        f"the other two questions).")


def _literal_key(literal: Literal) -> Tuple[Node, str]:
    """``(term, datatype)`` of a literal — one ``LiteralTyping`` fact of the
    image. Raises :class:`UnsupportedDatatypeError` for a literal with no term."""
    return (literal.to_term(), literal.datatype)


def _query_concepts(query, where: str) -> Tuple[Concept, ...]:
    """``query=`` as a tuple of concepts, or a :class:`TypeError` naming the
    mistake: a bare concept (``query=C``) or a string would otherwise iterate
    into nonsense, and a non-concept is no question."""
    if isinstance(query, (Concept, str)):
        raise TypeError(
            f"{where}: query= is an iterable of the concepts you are going to "
            f"ask about — write query=[concept], not query={query!r}.")
    concepts = () if query is None else tuple(query)      # None: no query
    for concept in concepts:
        if not isinstance(concept, Concept):
            raise TypeError(
                f"{where}: query= takes concepts (dl.Atomic, dl.DataExists, …), "
                f"got {type(concept).__name__} {concept!r}.")
    # Rendered once, only to refuse by name what no goal could be built from:
    # an OWL 2 built-in property name as a role, a literal with no term. Better
    # here than as a typing axiom for a name that is no property at all.
    for concept in concepts:
        names = _individual_names(concept)
        _translate(concept, Variable("x"), _fresh_var_factory("x", names | {"x"}))
    return concepts


def _check_goal_concepts(coverage: _Coverage, separation: str, data_layer: bool,
                         concepts: Sequence[Concept], where: str) -> None:
    """Refuse, by name, a goal over ``concepts`` that the bundle behind
    ``coverage`` is not the right theory for.

    Two things make the answer wrong, and both are silent in the prover: a name
    used as two kinds of thing at once (the punning check, run over the bundle's
    vocabulary together with the goal's), and a name whose side axioms are not
    there. What a two-sorted bundle derives its axioms from is the object
    properties (typing), data properties (typing), datatypes (guard, lattice,
    disjointness) and literals (typing, distinctness); a data-lattice bundle
    only the last two; a bundle with no data layer none of them, so ANY data
    vocabulary in the goal is uncovered. ``separation="none"`` over a data layer
    says the caller supplies the discipline, so nothing is checked.
    """
    goal = _Vocabulary()
    for concept in concepts:
        goal.add_concept(concept)
    have = coverage.vocabulary
    _check_name_punning(_Vocabulary(
        classes=have.classes | goal.classes,
        object_roles=have.object_roles | goal.object_roles,
        data_properties=have.data_properties | goal.data_properties,
        datatypes=have.datatypes | goal.datatypes), where,
        "this knowledge base together with the goal")
    if data_layer:
        _check_reserved_names(goal, separation, where)

    roles = data_layer and separation == "two-sorted"
    properties = (not data_layer) or separation == "two-sorted"
    datatypes = (not data_layer) or separation in ("two-sorted", "data-lattice")
    missing: List[str] = []
    if roles:
        missing += [f"the object property {name!r}"
                    for name in sorted(goal.object_roles - have.object_roles)]
    if properties:
        missing += [f"the data property {name!r}"
                    for name in sorted(goal.data_properties - have.data_properties)]
    if datatypes:
        wanted = {canonical_datatype_name(name) for name in goal.datatypes}
        known = {canonical_datatype_name(name) for name in have.datatypes}
        missing += [f"the datatype {name!r}"
                    for name in sorted(wanted - known - {"rdfs:Literal"})]
        seen = {}
        for literal in goal.literals:
            key = _literal_key(literal)
            if key not in coverage.literals:
                seen[literal.to_unicode()] = literal
        missing += [f"the literal {text}" for text in sorted(seen)]
    if not missing:
        return
    why = ("this knowledge base has no data layer, so its image carries no sort, "
           "typing or datatype axioms at all" if not data_layer else
           "the sort, typing, datatype-lattice and literal axioms of this "
           "knowledge base's image are derived from the names IT uses")
    raise UnsupportedDatatypeError(
        f"{where}: the goal names {', '.join(missing)}, which the knowledge "
        f"base this bundle was built from does not cover ({why}). A goal over "
        f"them is asked of a weaker theory than the one OWL 2 describes and "
        f"comes back 'refuted' for entailments OWL 2 makes — silently. Hand the "
        f"concepts you are going to ask about to the knowledge base when you "
        f"build it, dl.kb_to_fol(tbox, abox, query=[...]), and ask the new "
        f"bundle.")


def _sort_axioms(vocabulary: _Vocabulary, separation: str) -> List[SideAxiom]:
    """The derived side axioms of a knowledge base that has a data layer. See
    :func:`data_sort_axioms` for what each one says and why it is there.

    The four prefix variables avoid the knowledge base's individuals like every
    other binder of the image (:func:`_binder_names`). None of these axioms
    mentions an individual UNDER a quantifier, so none can capture one — it is
    kept as an invariant of the whole image, not a case analysis."""
    parts: List[SideAxiom] = []
    x, y, t, v = (Variable(name) for name in _binder_names(
        ("x", "y", "t", "v"), vocabulary.individuals))
    thing, data = (lambda term: Atom(OWL_THING, (term,))), (lambda term: Atom(OWL_DATA, (term,)))

    def forall(variables, body) -> Node:
        return _forall(list(variables), body)

    if separation == "two-sorted":
        parts.append(SideAxiom("DomainSeparation", "sort",
            forall([t], _FNot(_FAnd(thing(t), data(t))))))
        parts.append(SideAxiom("DomainNonEmptiness", "sort",
            Quantifier("∃", t, thing(t))))
        parts.append(SideAxiom("DomainNonEmptiness", "sort",
            Quantifier("∃", t, data(t))))
        for role in sorted(vocabulary.object_roles):
            parts.append(SideAxiom("ObjectPropertyTyping", "sort", forall([x, y], Implies(
                Atom(role, (x, y)), _FAnd(thing(x), thing(y))))))
        for prop in sorted(vocabulary.data_properties):
            parts.append(SideAxiom("DataPropertyTyping", "sort", forall([x, v], Implies(
                Atom(prop, (x, v)), _FAnd(thing(x), data(v))))))
        for individual in sorted(vocabulary.individuals):
            parts.append(SideAxiom("IndividualTyping", "sort", thing(Constant(individual))))

    datatypes = sorted(canonical_datatype_name(name) for name in vocabulary.datatypes
                       if canonical_datatype_name(name) != "rdfs:Literal")
    used = set(datatypes)
    for name in datatypes:
        parts.append(SideAxiom("DatatypeGuard", "datatype", forall([v], Implies(
            Atom(name, (v,)), data(v)))))
    for name in datatypes:
        for ancestor in sorted(datatype_ancestors(name) & used):
            parts.append(SideAxiom("DatatypeSubsumption", "datatype", forall([v], Implies(
                Atom(name, (v,)), Atom(ancestor, (v,))))))
    for i, left in enumerate(datatypes):
        for right in datatypes[i + 1:]:
            family_left, family_right = datatype_family(left), datatype_family(right)
            if family_left is not None and family_right is not None \
                    and family_left != family_right:
                parts.append(SideAxiom("DatatypeDisjointness", "datatype", forall([v], _FNot(
                    _FAnd(Atom(left, (v,)), Atom(right, (v,)))))))

    # Literals: one TERM per data value, however many spellings denote it.
    terms: dict = {}
    for literal in vocabulary.literals:
        term = literal.to_term()
        entry = terms.setdefault(term, {"datatypes": set(), "family": _literal_family(literal)})
        entry["datatypes"].add(literal.datatype)
    ordered = sorted(terms, key=lambda term: term.to_unicode_str())
    for term in ordered:
        parts.append(SideAxiom("LiteralTyping", "datatype", data(term)))
        for name in sorted(terms[term]["datatypes"]):
            if name != "rdfs:Literal":
                parts.append(SideAxiom("LiteralTyping", "datatype", Atom(name, (term,))))
    for family in ("number", "string", "anyURI", "boolean"):
        members = [term for term in ordered if terms[term]["family"] == family]
        for i, left in enumerate(members):
            for right in members[i + 1:]:
                parts.append(SideAxiom("LiteralDistinctness", "datatype",
                                       Atom("≠", (left, right))))
    return parts


def data_sort_axioms(tbox: Optional[TBox] = None, abox: Optional[ABox] = None, *,
                     separation: str = "two-sorted",
                     query: Iterable[Concept] = ()) -> Tuple[SideAxiom, ...]:
    """The side axioms that turn the data layer's one-sorted image into the
    two-sorted theory OWL 2 describes, derived from the vocabulary ``(tbox,
    abox)`` actually uses — the same axioms :func:`kb_to_fol` puts in
    ``side_axioms``, for a caller who builds a question by hand (a bare
    :func:`concept_to_fol` query, say) and needs them as premises.

    Empty for a knowledge base without a data layer, and for
    ``separation="none"``. ``query`` is :func:`kb_to_fol`'s: the concepts you are
    going to ask about, whose vocabulary joins the knowledge base's — a
    knowledge base without a data layer asked about a data restriction HAS one,
    for this purpose.

    ``separation="two-sorted"`` (``group "sort"``, then ``"datatype"``):

    * ``DomainSeparation`` ``∀t ¬(OwlThing(t) ∧ OwlData(t))`` — OWL 2's object
      and data domains are disjoint;
    * ``DomainNonEmptiness`` ``∃t OwlThing(t)``, ``∃t OwlData(t)``;
    * ``ObjectPropertyTyping`` ``∀x ∀y (r(x, y) → OwlThing(x) ∧ OwlThing(y))``
      per object role, ``DataPropertyTyping`` ``∀x ∀v (d(x, v) → OwlThing(x) ∧
      OwlData(v))`` per data property, ``IndividualTyping`` ``OwlThing(a)`` per
      individual — one per NAME the knowledge base uses, not per class name:
      with every GCI relativised to the object domain a class atom needs no
      typing of its own.

    Both ``"two-sorted"`` and ``"data-lattice"`` (``group "datatype"``), over the
    datatypes the knowledge base MENTIONS:

    * ``DatatypeGuard`` ``∀v (D(v) → OwlData(v))`` — a datatype is a subset of
      the data domain (``rdfs:Literal`` IS the data domain and is rendered as
      ``OwlData`` itself, so it has none);
    * ``DatatypeSubsumption`` ``∀v (D(v) → E(v))`` for ``D`` below ``E`` in the
      OWL 2 datatype map, both mentioned (``xsd:integer`` ⊑ ``xsd:decimal``);
    * ``DatatypeDisjointness`` ``∀v ¬(D(v) ∧ E(v))`` for two mentioned built-in
      datatypes of different families (``xsd:integer``/``xsd:string``): this is
      what makes ``DataPropertyRange(d xsd:integer)`` together with
      ``DataPropertyRange(d xsd:string)`` force ``d`` empty;
    * ``LiteralTyping`` ``OwlData(t)`` and ``D(t)`` for each literal's term ``t``
      and datatype ``D``;
    * ``LiteralDistinctness`` ``t ≠ u`` for two distinct terms within the exact
      numbers, within the strings (``xsd:string``, language-tagged strings and
      the whitespace-processed ``xsd:normalizedString``/``xsd:token``), within
      the ``xsd:anyURI`` values, within the booleans — pairwise, so QUADRATIC in
      the number of distinct literals of one family (1000 distinct integers are
      499,500 axioms). Across families the typing and the disjointness already
      separate them; for the datatypes whose lexical forms are not in
      one-to-one correspondence with values (``xsd:dateTime``,
      ``xsd:hexBinary``) nothing is claimed.

    What it is not: complete. Facet comparisons are uninterpreted atoms for
    ``api.prove`` (use :mod:`unicode_fol_kit.atp.z3_arith` for arithmetic over
    data ranges alone), and the cardinality of a value space (``xsd:boolean``
    has exactly two values) is not stated.

    Raises:
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            ``separation`` is not a known name, the
            knowledge base uses ``OwlThing``/``OwlData`` as its own name, a
            literal has no term, or one name is used both as an object property
            and a data property or both as a class and a datatype (OWL 2 DL
            forbids both; the image has one predicate per name — rename one).
    """
    _check_separation(separation)
    queried = _query_concepts(query, "dl.data_sort_axioms")
    vocabulary = _collect_vocabulary(tbox, abox, query=queried)
    _check_name_punning(vocabulary, "dl.data_sort_axioms")
    if separation == "none" or not vocabulary.has_data():
        return ()
    _check_reserved_names(vocabulary, separation)
    return tuple(_sort_axioms(vocabulary, separation))


def _union_vocabularies(vocabularies: Iterable[_Vocabulary]) -> _Vocabulary:
    """One :class:`_Vocabulary` holding every name of each of ``vocabularies``."""
    union = _Vocabulary()
    for vocabulary in vocabularies:
        union.classes |= vocabulary.classes
        union.object_roles |= vocabulary.object_roles
        union.data_properties |= vocabulary.data_properties
        union.individuals |= vocabulary.individuals
        union.datatypes |= vocabulary.datatypes
        union.literals.extend(vocabulary.literals)
    return union


def check_kb_names(*parts, separation: str = "two-sorted",
                   query: Iterable[Concept] = ()) -> None:
    """Run, over several pieces of one knowledge base at once, the check on names
    that :func:`kb_to_fol` runs over the whole of it.

    Every function that renders one box of a knowledge base —
    :func:`tbox_to_fol`, :func:`rbox_to_fol`, :func:`databox_to_fol`,
    :func:`abox_to_fol` — refuses a name used as two kinds OWL 2 DL keeps apart
    (an object property and a data property, a class and a datatype, or a name
    the data image reserves) only over what it is given. A caller who renders the
    boxes one call at a time, from the same ontology or from several, and
    conjoins the images by hand, therefore has no call that sees the clash:
    ``P`` as the object property of an ABox role assertion and as the data
    property of a TBox's ``DataPropertyRange`` is ONE predicate ``P`` in the
    combined image, and what follows from it changes. This function takes the
    pieces and answers what :func:`kb_to_fol` would answer about their union.

    ``parts`` are the :class:`~unicode_fol_kit.dl.tableau.TBox`,
    :class:`~unicode_fol_kit.dl.tableau.ABox` or
    :class:`KnowledgeBaseFOL` objects the images were built from, in any number
    and any mixture (a bundle contributes the vocabulary it was built over,
    ``query=`` concepts included). A formula is not accepted: the image of a box
    is an ordinary first-order formula, in which ``P(x, y)`` of an object
    property and ``P(x, v)`` of a data property are the same atom, so which kind
    a predicate was is not recorded in it, and any guess from its shape would be
    an approximation. ``separation`` and ``query`` are :func:`kb_to_fol`'s.

    A class, an object property and an individual that share a name (punning
    that OWL 2 DL does allow) are accepted: in the image they are three symbols,
    the unary predicate ``A(x)``, the binary predicate ``A(x, y)`` and the
    constant ``A``.

    Returns ``None``; the function exists for what it refuses.

    Raises:
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            ``separation`` is not a known name, a name of the union is used as
            both an object property and a data property or as both a class and a
            datatype, or ``OwlThing``/``OwlData`` is used as one of its own
            names — the refusals :func:`kb_to_fol` makes, here over the union of
            the pieces.
        TypeError: a piece is not a ``TBox``, ``ABox`` or ``KnowledgeBaseFOL``
            (a formula is named in the message), or ``query`` is not an
            iterable of concepts.
        ValueError: a ``KnowledgeBaseFOL`` piece was not built by
            :func:`kb_to_fol`, so it does not record its vocabulary.
    """
    where = "dl.check_kb_names"
    _check_separation(separation, where)
    queried = _query_concepts(query, where)
    vocabularies = []
    for part in parts:
        if isinstance(part, TBox):
            vocabularies.append(_collect_vocabulary(part, None, where=where))
        elif isinstance(part, ABox):
            vocabularies.append(_collect_vocabulary(None, part, where=where))
        elif isinstance(part, KnowledgeBaseFOL):
            if part._coverage is None:
                raise ValueError(
                    f"{where}: this KnowledgeBaseFOL was not built by "
                    f"dl.kb_to_fol, so it does not record the vocabulary it was "
                    f"built over. Pass the TBox and ABox it was built from.")
            vocabularies.append(part._coverage.vocabulary)
        elif isinstance(part, Node):
            raise TypeError(
                f"{where}: got a formula ({type(part).__name__}), but the image "
                f"of a box does not record which kind each of its predicates is "
                f"(P(x, y) of an object property and P(x, v) of a data property "
                f"are the same atom), so the names cannot be checked from it. "
                f"Pass the TBox / ABox the image was built from.")
        else:
            raise TypeError(
                f"{where}: takes TBox, ABox or KnowledgeBaseFOL objects, got "
                f"{type(part).__name__} {part!r}.")
    vocabulary = _union_vocabularies(
        vocabularies + [_collect_vocabulary(None, None, where=where, query=queried)])
    _check_name_punning(vocabulary, where, "the pieces it is given, taken together")
    if vocabulary.has_data():
        _check_reserved_names(vocabulary, separation, where)


def kb_to_fol(tbox: Optional[TBox] = None, abox: Optional[ABox] = None,
              var: str = "x", *, separation: str = "two-sorted",
              query: Iterable[Concept] = ()) -> KnowledgeBaseFOL:
    """Render the knowledge base ``(tbox, abox)`` as FOL — the supported way to ask
    a question *relative to* a TBox that has a role box.

    The concept inclusions (:func:`tbox_to_fol`) and the ABox
    (:func:`abox_to_fol`) become :attr:`~KnowledgeBaseFOL.formula`; the role box
    (:func:`rbox_to_fol`'s content, one formula per axiom) becomes the SEPARATE
    :attr:`~KnowledgeBaseFOL.side_axioms`, each a :class:`SideAxiom` carrying
    the OWL keyword it came from, so a census of the image per axiom kind
    (:meth:`~KnowledgeBaseFOL.axioms_of_kind`) is a question with an answer;
    :attr:`~KnowledgeBaseFOL.axioms` is the bare-formula view of that one
    field. Following the kit's side-axiom convention
    (:class:`~unicode_fol_kit.comorphism.TranslationResult`), the axioms are never
    conjoined into the formula: the caller passes them as premises, which is what
    ``premises`` / ``tbox_premises`` spell. ``tbox`` may be ``None`` (an ABox-only
    knowledge base) and ``abox`` may be ``None`` (a TBox-only one), the same
    defaults as the tableau API; ``var`` is :func:`tbox_to_fol`'s.

    ``query`` is an iterable of the concepts you are going to ASK about. Their
    vocabulary — classes, object properties, data properties, datatypes,
    literals, individuals — joins the knowledge base's for everything derived
    from the vocabulary: the separation regime (a data restriction in the query
    makes the image two-sorted even when the TBox and ABox have no data layer),
    the sort, typing, datatype-lattice, disjointness and literal axioms, the
    punning check and the variables a binder must avoid. Without ``query`` the
    bundle is what it always was. It matters because those axioms are scoped to
    the names the knowledge base mentions, so a goal naming ``xsd:decimal`` over
    a knowledge base that only mentions ``xsd:integer`` would be asked of a
    theory without ``integer ⊑ decimal`` — and a concept whose satisfiability
    turns on the datatype lattice would come out satisfiable. The goal methods
    below REFUSE a concept the bundle does not cover, by name, and say to pass
    ``query=``.

    Each of the standard questions, with the tableau function it must agree with
    (``kb = kb_to_fol(tbox, abox, query=[…the concepts below…])``; ``prove`` is
    :func:`unicode_fol_kit.api.prove`, whose verdict ``.status`` is ``"proved"``,
    ``"refuted"`` or ``"unknown"``)::

        # (a) subsumption relative to the TBox (the ABox plays no part)
        prove(kb.subsumption_goal(sub, sup), kb.tbox_premises)
        #   proved  <=>  dl.subsumes(sub, sup, tbox)        refuted <=> it does not

        # (b) concept satisfiability relative to the TBox
        prove(kb.unsatisfiability_goal(C), kb.tbox_premises)
        #   proved  <=>  dl.concept_satisfiable(C, tbox) is False

        # (c) instance checking: does the knowledge base entail  a : C ?
        prove(kb.instance_goal("a", C), kb.premises)
        #   proved  <=>  dl.instance_check(abox, "a", C, tbox)

        # (d) consistency of the knowledge base   (Not = unicode_fol_kit.fol.nodes.Not)
        prove(Not(kb.formula), kb.axioms)
        #   proved  <=>  INCONSISTENT  (dl.abox_consistent(abox, tbox) is False)
        #   refuted <=>  consistent    (same as is_satisfiable(kb.formula ∧ kb.axioms))

    For a knowledge base without a data layer each goal method builds exactly the
    spelling the earlier releases documented (``subsumption_to_fol(sub, sup)``;
    ``¬∃x π(C, x)``, the ``Quantifier("∃", Variable("x"), …)`` around the free
    ``x``; ``abox_to_fol(ABox().assert_concept("a", C))``, ``π(C, a)`` with the
    individual as a constant), up to a renamed bound variable where an individual
    is called ``x``. The point of the methods is the knowledge base WITH a data
    layer, where the right goal depends on :attr:`KnowledgeBaseFOL.separation`
    and the wrong one answers silently wrong: they pick it, and
    :attr:`KnowledgeBaseFOL.refutation_is_decisive` says what a ``"refuted"`` is
    worth. An inconsistent knowledge base entails everything, in (c) as in the
    tableau; ``"unknown"`` means the backends gave no answer within budget
    (first-order entailment with transitivity is only semi-decidable), not that
    either answer holds.

    Do NOT build these queries from the pieces by hand with
    ``Implies(tbox_to_fol(tbox), …)``: that drops the role box and can report a
    false counterexample (see the module docstring); :func:`tbox_to_fol` refuses
    such a TBox unless told ``concept_inclusions_only=True``.

    **A knowledge base with a data layer** (a data property, a datatype or a
    literal anywhere in it, the ``query`` concepts included) additionally gets
    the data box's images and — per ``separation`` — the axioms that make it a
    two-sorted theory, all in ``side_axioms`` (see "The data layer" in the module
    docstring and :func:`data_sort_axioms`). What makes the question the
    prover answers the TWO-SORTED one:

    * the premises: ``kb.premises`` / ``kb.tbox_premises`` / ``kb.axioms`` as
      above — they already contain the separation, the typing, the lattice and
      the literal facts; ``kb.formula`` already has every GCI relativised to
      the object domain;
    * the goal from the three methods, which relativise it the same way when
      ``kb.separation == "two-sorted"``; the consistency query
      ``Not(kb.formula)`` needs nothing extra.

    The two-sorted image of a data layer is SOUND and not complete (see
    :attr:`KnowledgeBaseFOL.refutation_is_decisive`): ``"proved"`` transfers to
    OWL 2, ``"refuted"`` does not.

    ``separation`` is ``"two-sorted"`` (the default: the full discipline),
    ``"data-lattice"`` (only the datatype facts — faithful WITHIN the data
    domain, no object/data separation, GCIs as written, so the premise count is
    that of the knowledge base plus its datatypes and literals) or ``"none"``
    (the data-box images alone, and the caller supplies any sort discipline).
    Neither of those two is sound for a knowledge base with a data layer:
    their inclusions are not restricted to the object domain, so they also
    range over data values and the premises are STRONGER than OWL 2's — the
    three goal methods refuse such a bundle, and a proof obtained from its
    premises by hand does not transfer.
    The effective choice is recorded in :attr:`KnowledgeBaseFOL.separation`.
    A knowledge base WITHOUT a data layer gets none of this, whatever
    ``separation`` says: its output is byte-identical to a release before the
    data layer existed.

    Raises:
        ~unicode_fol_kit.dl.datatypes.UnsupportedDatatypeError:
            ``separation`` is not one of the three names;
            the knowledge base uses ``OwlThing``/``OwlData`` (the reserved
            guard predicates) as one of its own names; a literal has no term;
            or one name is used both as an object property and a data property
            or both as a class and a datatype — OWL 2 DL forbids both, and the
            image has ONE predicate per name, so it would conflate them and
            change what follows. Rename one of the two.
        TypeError: ``query`` is not an iterable of concepts (``query=C`` for one
            concept is a mistake: write ``query=[C]``).

    A class, an object property and an individual that share a name (OWL 2 DL
    punning, which is allowed) are not refused and are not conflated: the image
    writes the class as the unary predicate ``A(x)``, the object property as the
    binary predicate ``A(x, y)`` and the individual as the constant ``A`` — three
    symbols. :func:`tbox_to_fol`, :func:`rbox_to_fol`, :func:`abox_to_fol` and
    :func:`databox_to_fol` write them the same way, so images of one ontology
    rendered box by box and conjoined are one theory. A route that keys a symbol
    on its kind and arity (the TPTP writers: Vampire, E) reads three symbols.
    Names that punning does NOT allow are refused — see :func:`check_kb_names`,
    which runs that check over boxes rendered separately.

    The agreement with the tableau holds on the fragment it decides — ALCH with
    transitive roles, and qualified number restrictions on simple roles (the
    ``Count`` image). The translation itself is wider (inverse roles, nominals)
    and is then decided by the FOL backends alone.
    """
    _check_separation(separation)
    queried = _query_concepts(query, "dl.kb_to_fol")
    vocabulary = _collect_vocabulary(tbox, abox, where="dl.kb_to_fol", query=queried)
    _check_name_punning(vocabulary, "dl.kb_to_fol")
    effective = separation if vocabulary.has_data() else "none"
    if vocabulary.has_data():
        _check_reserved_names(vocabulary, separation)
    object_sort = effective == "two-sorted"
    # ONE avoid set for the whole call: every bound variable of every axiom
    # below — the GCI prefix variable, the role-box and data-box prefix
    # variables, the sort axioms', the minted ones — avoids every individual of
    # the knowledge base, so no binder anywhere in the image shares a name with
    # a constant and the image of one axiom never depends on which others
    # happen to be in the call (see _binder_names).
    avoid = vocabulary.individuals
    tbox_image = (_tbox_image(tbox, var, object_sort, avoid)
                  if tbox is not None else _tautology())
    abox_image = _abox_image(abox, avoid) if abox is not None else _tautology()
    has_gcis = tbox is not None and bool(tbox.inclusions)
    # Derived from the axiom-kind table (ABox.is_empty), not from a hand-written
    # `or` over the assertion fields: an assertion kind this condition did not
    # know about would drop the ABox half of `formula` SILENTLY.
    has_assertions = abox is not None and not abox.is_empty()
    formulas = tuple(([tbox_image] if has_gcis else []) +
                     ([abox_image] if has_assertions else []))
    side_axioms: List[SideAxiom] = []
    if tbox is not None:
        side_axioms.extend(_rbox_axioms(tbox, object_sort=object_sort, avoid=avoid))
        side_axioms.extend(_databox_axioms(tbox, avoid=avoid))
    if effective != "none":
        side_axioms.extend(_sort_axioms(vocabulary, effective))
    return KnowledgeBaseFOL(
        formula=_conjoin(list(formulas)),
        side_axioms=tuple(side_axioms),
        tbox=tbox_image,
        abox=abox_image,
        individuals=_abox_individuals(abox) if abox is not None else (),
        formulas=formulas,
        separation=effective,
        data_layer=vocabulary.has_data(),
        _coverage=_Coverage(
            var=var, vocabulary=vocabulary,
            individuals=frozenset(vocabulary.individuals),
            literals=frozenset(_literal_key(literal)
                               for literal in vocabulary.literals)),
    )


# --------------------------------------------------------------------------- #
# Single-role concepts as propositional modal K formulas.
# --------------------------------------------------------------------------- #

_IO_MODAL_MSG = (
    "concept_to_modal: {what} has no faithful propositional-K rendering — "
    "plain modal K has no converse modality (inverse roles need TENSE/hybrid "
    "logic) and no naming/nominal construct at all (that is HYBRID logic, a "
    "strictly different formalism this kit does not implement); refusing "
    "rather than silently dropping or misencoding it. Use concept_to_fol "
    "instead: the standard translation to FOL handles both faithfully (see "
    "its module docstring's 'Inverse roles and nominals (I, O)' section)."
)


def _roles_used(concept: Concept) -> set:
    """Return the set of distinct role names occurring anywhere in ``concept``."""
    if isinstance(concept, (Top, Bottom, Atomic)):
        return set()
    if isinstance(concept, Nominal):
        raise NotImplementedError(_IO_MODAL_MSG.format(what=f"the nominal {{{concept.individual}}}"))
    if isinstance(concept, DATA_CONCEPTS):
        raise NotImplementedError(
            f"concept_to_modal: the data restriction {type(concept).__name__} "
            f"({concept.to_unicode()}) has no propositional-K rendering — modal K "
            f"has no data domain, only possible worlds. Use concept_to_fol, whose "
            f"image handles it (see its 'The data layer' section).")
    if isinstance(concept, Not):
        return _roles_used(concept.concept)
    if isinstance(concept, (And, Or)):
        return _roles_used(concept.left) | _roles_used(concept.right)
    if isinstance(concept, (Exists, ForAll)):
        if isinstance(concept.role, InverseRole):
            raise NotImplementedError(
                _IO_MODAL_MSG.format(what=f"the inverse role {concept.role.role}⁻"))
        # A built-in property name is not "the one accessibility relation" of K
        # (the universal relation is a different modality, the empty one has no
        # worlds to move to): refused by name, as every other route does.
        _reject_concept_role(concept, where="dl.concept_to_modal")
        return {concept.role} | _roles_used(concept.concept)
    raise TypeError(f"concept_to_modal: unsupported concept {type(concept).__name__}")


# A reserved nullary atom used only to spell out a structural tautology/
# contradiction (mirrors the reserved-atom idiom in unicode_fol_kit.atp.fitch's
# falsum handling). Since `p ∨ ¬p` is valid — and `p ∧ ¬p` unsatisfiable — for
# ANY p, this is correct regardless of what this particular name denotes, even
# in the (harmless) case that a concept happens to be literally named "⊤".
_MODAL_TRUE_ATOM = Atom("⊤", ())


def _to_modal(concept: Concept) -> Node:
    """Translate a single-role concept to a propositional modal-K formula."""
    if isinstance(concept, Atomic):
        return Atom(concept.name, ())
    if isinstance(concept, Top):
        return _FOr(_MODAL_TRUE_ATOM, _FNot(_MODAL_TRUE_ATOM))
    if isinstance(concept, Bottom):
        return _FAnd(_MODAL_TRUE_ATOM, _FNot(_MODAL_TRUE_ATOM))
    if isinstance(concept, Not):
        return _FNot(_to_modal(concept.concept))
    if isinstance(concept, And):
        return _FAnd(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, Or):
        return _FOr(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, Exists):
        return Diamond(_to_modal(concept.concept))
    if isinstance(concept, ForAll):
        return Box(_to_modal(concept.concept))
    raise TypeError(f"concept_to_modal: unsupported concept {type(concept).__name__}")


_MULTI_ROLE_MSG = (
    "concept_to_modal: concept uses {n} distinct roles {roles}; propositional "
    "modal K has exactly ONE accessibility relation, so per-role restrictions "
    "(∃r.C / ∀r.C for different r) cannot be faithfully rendered as Box/Diamond "
    "— there is no honest way to recover which role a given □/◇ came from. Use "
    "concept_to_fol instead: it has no such limitation, since a role is just "
    "another binary FOL predicate r(x, y) and FOL scales to any number of them."
)


def concept_to_modal(concept: Concept) -> Node:
    """Translate a SINGLE-role concept to a propositional modal-K formula.

    ``∃r.C`` ↦ ``◇C``, ``∀r.C`` ↦ ``□C`` (ALC restricted to one role is
    exactly modal K — see "Multi-role concepts and modal K" in the module
    docstring). ``concept`` is satisfiable (:func:`unicode_fol_kit.dl.tableau.concept_satisfiable`)
    iff its image here is satisfiable in K, decidable via
    :func:`unicode_fol_kit.atp.modal_tableau.is_modal_valid` on the negation
    (``not is_modal_valid(Not(concept_to_modal(concept)), frame="K")``).

    Raises:
        NotImplementedError: ``concept`` mentions two or more distinct role
            names — see :func:`concept_to_fol` for the general (FOL) translation.
    """
    roles = _roles_used(concept)
    if len(roles) > 1:
        raise NotImplementedError(
            _MULTI_ROLE_MSG.format(n=len(roles), roles=sorted(roles)))
    return _to_modal(concept)
