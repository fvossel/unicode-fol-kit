"""The ``dl`` subpackage — the description logic **ALC**.

Concept constructors (``import unicode_logic_kit.dl as dl``)::

    dl.Top(), dl.Bottom(), dl.Atomic("Person"), dl.Not(C),
    dl.And(C, D), dl.Or(C, D), dl.Exists("hasChild", C), dl.ForAll("hasChild", C),
    dl.AtLeast(2, "hasChild", C), dl.AtMost(1, "hasChild", C)   # qualified number
                                                                 # restrictions (ALCQ)

Reasoning over a (general) TBox / ABox::

    dl.concept_satisfiable(C, tbox)   # is C satisfiable w.r.t. the TBox?
    dl.subsumes(C, D, tbox)           # does the TBox entail C ⊑ D?
    dl.equivalent(C, D, tbox)         # C ≡ D?
    dl.abox_consistent(abox, tbox)    # is the knowledge base consistent?

Instance/realization queries over an ABox, all pure reductions to ``abox_consistent``
(see :mod:`unicode_logic_kit.dl.tableau`)::

    dl.instance_check(abox, "alice", C, tbox)       # does the KB entail alice : C?
    dl.instance_retrieval(abox, C, tbox)             # every individual entailed to be C
    dl.realize(abox, "alice", vocabulary, tbox)      # alice's most-specific concepts
    dl.realize_all(abox, vocabulary, tbox)           # realize() for every individual

TBox classification — the whole named-concept subsumption hierarchy as a pure
reduction to ``subsumes`` (see :mod:`unicode_logic_kit.dl.classification`)::

    dl.classify(tbox)                 # -> Classification(equivalents, parents,
                                       #    children, ancestors)

ALC is exactly multi-modal K; the reasoner is a tableau with TBox internalisation
and subset blocking (see :mod:`unicode_logic_kit.dl.tableau`).

Parsing the glyph concept syntax back into a :class:`Concept`
(:mod:`unicode_logic_kit.dl.parser`)::

    dl.parse_concept("∃hasChild.(Doctor ⊓ ¬Rich)")   # -> Concept
    dl.parse_gci("Doctor ⊑ ∃hasChild.⊤")              # -> (Concept, Concept)

Parsing/rendering the W3C OWL 2 Manchester Syntax (ALC fragment only,
:mod:`unicode_logic_kit.dl.owl_manchester`)::

    dl.parse_manchester("hasChild some (Doctor and not Rich)")   # -> Concept
    dl.to_manchester(C)                                          # -> str
    dl.parse_manchester_axiom("Doctor SubClassOf hasChild some owl:Thing")
    #  -> ("subclass", Concept, Concept)
    dl.parse_manchester_role_axiom("hasChild SubPropertyOf hasDescendant")
    #  -> ("subproperty", "hasChild", "hasDescendant")
    dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive")
    #  -> ("transitive", "hasDescendant")
    dl.parse_manchester_role_axiom("partOf InverseOf hasPart")
    #  -> ("inverse", "partOf", "hasPart")
    dl.parse_manchester_role_axiom("hasSink DisjointWith hasSource")
    #  -> ("disjoint", "hasSink", "hasSource")

Parsing/rendering the W3C OWL 2 Functional-Style Syntax (ALCHQ fragment, a whole
ontology document rather than a single axiom, :mod:`unicode_logic_kit.dl.owl_functional`)::

    dl.parse_owl_functional("Ontology(SubClassOf(Doctor Person))")   # -> (TBox, ABox)
    dl.to_owl_functional(tbox, abox)                                 # -> str
    dl.parse_owl_functional_class_expression("ObjectSomeValuesFrom(hasChild Doctor)")
    #  -> Exists("hasChild", Atomic("Doctor"))
    dl.to_owl_functional_class_expression(C)                        # -> str

The standard translation to FOL, so ALC reuses the kit's FOL provers/exports
(:mod:`unicode_logic_kit.dl.translate`)::

    dl.concept_to_fol(C)                # -> FOL formula π(C, x), one free var x
    dl.subsumption_to_fol(C, D)         # -> ∀x (π(C, x) → π(D, x))
    dl.tbox_to_fol(tbox)                # -> conjunction of subsumption_to_fol per GCI
    dl.rbox_to_fol(tbox)                # -> conjunction of role-inclusion/transitivity closures
    dl.abox_to_fol(abox)                # -> conjunction of the ABox's assertions
    dl.kb_to_fol(tbox, abox)            # -> KnowledgeBaseFOL: the KB + the role box as SEPARATE axioms
    dl.check_kb_names(tbox, abox)       # -> None: kb_to_fol's check on names, over boxes rendered apart
    dl.concept_to_modal(C)              # -> propositional modal-K formula (single role only)

A :class:`TBox` holds the concept inclusions AND the role box, but ``tbox_to_fol``
renders the concept inclusions only — so it RAISES ``dl.RoleBoxOmittedError`` for a TBox
that has role inclusions or transitive roles (``concept_inclusions_only=True`` is the
explicit opt-out). Ask any question *relative to* a knowledge base through
``kb_to_fol``, passing the role box as premises, never folded into the formula::

    kb = dl.kb_to_fol(tbox, abox)
    api.prove(kb.subsumption_goal(C, D), kb.tbox_premises)         # = dl.subsumes(C, D, tbox)
    api.prove(kb.unsatisfiability_goal(C), kb.tbox_premises)       # proved <=> C is unsatisfiable
    api.prove(kb.instance_goal("a", C), kb.premises)               # = dl.instance_check(...)
    api.prove(fol.Not(kb.formula), kb.axioms)       # proved <=> the knowledge base is inconsistent

Role hierarchies and transitive roles (RBox), on top of the concept-level TBox
(:mod:`unicode_logic_kit.dl.tableau`)::

    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    dl.subsumes(dl.Exists("hasChild", dl.Exists("hasChild", C)), dl.Exists("hasDescendant", C), t)
    #  -> True: ∃hasChild.∃hasChild.C ⊑ ∃hasDescendant.C, entailed by the RBox alone

Qualified number restrictions (ALCQ), on SIMPLE roles only (a role that is
transitive, or has a transitive sub-role, raises ``NonSimpleRoleError`` by name —
see :mod:`unicode_logic_kit.dl.tableau`'s "Qualified number restrictions" section)::

    dl.concept_satisfiable(dl.And(dl.AtLeast(2, "r", C), dl.AtMost(1, "r", dl.Top())))
    #  -> False: at least 2 pairwise-distinct r-successors but at most 1 r-successor at all

``ABox.assert_distinct(a, b)`` records ``a ≠ b`` — this reasoner has no unique name
assumption (see the same tableau section), so two ABox individuals otherwise remain
mergeable, which matters as soon as a number restriction is in play.

``instance_check``/``classify``/the rest of the reasoning API above respect a TBox's
RBox automatically, since they all reduce to ``concept_satisfiable``/``abox_consistent``
— no separate RBox-aware entry point is needed anywhere else.

The rest of the OWL 2 object property box
------------------------------------------
A :class:`TBox` carries every OWL 2 object-property axiom kind, and
``dl.rbox_to_fol`` renders every one of them (so ``kb_to_fol`` + ``api.prove``
and ``dl.external_*`` answer them all). What the IN-HOUSE tableau does with
each is the second column of ``dl.tableau._AXIOM_KINDS``::

    t = (dl.TBox()
         .add_disjoint_roles("hasSink", "hasSource")   # decided: a clash rule
         .add_asymmetric_role("hasPhysicalInput")      # decided: a clash rule
         .add_irreflexive_role("hasPhysicalInput")     # decided: a clash rule
         .add_functional_role("hasState"))             # decided: ⊤ ⊑ ≤1 P.⊤
    dl.abox_consistent(dl.ABox().assert_role("a", "a", "hasPhysicalInput"), t)
    #  -> False: Irr(hasPhysicalInput) is ∀x ¬hasPhysicalInput(x, x)

    dl.concept_satisfiable(dl.Top(), dl.TBox().add_symmetric_role("r"))
    #  -> raises dl.UnsupportedAxiomError, naming SymmetricObjectProperty and
    #     saying why (a symmetric role IS the inverse-role inclusion r ⊑ r⁻,
    #     and a back-edge breaks subset blocking) and what to use instead

Refused by name, each with its own remedy in the message:
``InverseObjectProperties`` (:meth:`~unicode_logic_kit.dl.TBox.add_inverse_roles`),
``SymmetricObjectProperty``, ``ReflexiveObjectProperty``,
``InverseFunctionalObjectProperty`` and a property chain
(:meth:`~unicode_logic_kit.dl.TBox.add_role_chain`) — plus an
:class:`~unicode_logic_kit.dl.concepts.InverseRole` on either side of a role
inclusion, which is accepted and rendered correctly but not decided in house.
``EquivalentObjectProperties``
(:meth:`~unicode_logic_kit.dl.TBox.add_equivalent_roles`) needs no rule at all:
it is stored as the role inclusions it abbreviates.

OWL 2 (Structural Specification §11) restricts asymmetry, irreflexivity, role
disjointness, functionality and inverse-functionality — and every qualified
number restriction — to SIMPLE roles, and the kit enforces exactly that
condition, by name (:class:`NonSimpleRoleError`), on the in-house AND the
external route. A role-box builder handed something that is not a usable role
in that position raises :class:`RoleExpressionError` on the call that is wrong::

    dl.TBox().add_role_inclusion(("r", "s"), "t")
    #  -> raises dl.RoleExpressionError: a sequence of roles is a PROPERTY
    #     CHAIN -- use dl.TBox.add_role_chain(chain, super_role)
    dl.TBox().add_role_inclusion("P", "owl:topObjectProperty")
    #  -> raises dl.RoleExpressionError: an OWL 2 BUILT-IN property name, not
    #     an ordinary role. ``dl.parse_owl_functional`` consumes the
    #     TAUTOLOGICAL inclusion into it as a documented no-op; every other use
    #     of a built-in name is refused by name there too.

Class expressions and the ABox: value restrictions, domain/range, identity
---------------------------------------------------------------------------
``dl.HasValue(role, individual)`` is OWL's ``ObjectHasValue(r a)``, written
``exists r.{a}``: a NOMINAL in disguise, so the in-house tableau REFUSES it, as
it refuses a bare ``Nominal`` (see :class:`~unicode_logic_kit.dl.concepts.HasValue`
for why it is a constructor of its own and not ``dl.Exists(role,
dl.Nominal(a))``, and "Value restrictions (ObjectHasValue)" in
:mod:`unicode_logic_kit.dl.tableau` for why no in-house rule for it is sound: a
value restriction gives a generated node an edge back to a named one, which the
subset blocking the tableau terminates by does not cover). Its FOL image is the
GROUND ATOM, the one-point reduction of ``exists y (r(x, y) and y = a)``, and
that image, with ``api.prove`` — or ``dl.external_*`` (HermiT) — is what decides
it::

    dl.concept_to_fol(dl.HasValue("HasStateOfMatter", "Liquid"))
    #  -> HasStateOfMatter(x, Liquid)
    dl.concept_satisfiable(dl.And(dl.HasValue("r", "a"), dl.ForAll("r", dl.Bottom())))
    #  -> raises dl.UnsupportedConceptError, naming the value restriction and
    #     the routes that do decide it. The FOL image proves the hand-derived
    #     verdict (unsatisfiable: a would have to be in bottom).

``TBox.add_role_domain`` / ``add_role_range`` store
``ObjectPropertyDomain``/``ObjectPropertyRange`` NATIVELY rather than as the
GCIs they are equivalent to, so the image is the direct two-variable sentence
and ``to_owl_functional`` round-trips the axiom to itself; the tableau decides
them by internalising those GCIs, with no new rule::

    dl.rbox_to_fol(dl.TBox().add_role_domain("Covers", dl.Atomic("Study")))
    #  -> forall x forall y (Covers(x, y) -> Study(x))

``ABox.assert_same`` (``SameIndividual``) is decided by node MERGING, closed
under the equivalence the assertions generate, before any completion rule runs;
``ABox.assert_negative_role`` (``NegativeObjectPropertyAssertion``, arguments in
``assert_role``'s order) by a clash condition over FORBIDDEN edges. The second
refuses a NON-SIMPLE role by name, since seeing a forbidden edge is what its
verdict depends on and the tableau never materialises a transitive role's
derived edges::

    dl.abox_consistent(dl.ABox().assert_same("a", "b").assert_distinct("a", "b"))
    #  -> False: a = b and a != b have no common model

``dl.parse_owl_functional_axioms(text)`` is the per-axiom reader for a whole
ontology: it returns an :class:`OwlFunctionalResult` with the TBox/ABox it could
build plus one :class:`RefusedAxiom` per axiom outside the fragment, each naming
the construct, its offset and its own source text. ``dl.parse_owl_functional``
stays strict, raising on the first such construct. The lenient reader recovers
from :class:`OwlFunctionalUnsupportedError` and nothing else: MALFORMED input
still raises::

    doc = dl.parse_owl_functional_axioms(text)
    doc.ok, doc.accepted, doc.refused_keywords
    kb = doc.to_kb()        # == dl.kb_to_fol(doc.tbox, doc.abox)

One limit to know before printing an image that mentions an individual: the kit
decides predicate-versus-term by the first character's case, so an UPPER-case
individual name -- the norm for an OWL IRI -- prints as itself and does not read
back as the same formula (``Alice = Bob`` does not parse;
``HasStateOfMatter(x, Liquid)`` parses only as third-order, with ``Liquid`` a
``PredicateTerm``). The AST is sound either way, and the routes that never go
through text are unaffected. See ``tests/test_printed_text_reads_back.py``.

Inverse roles and nominals (I, O) — outside ALCHQ, refused by the in-house tableau
(a value restriction, ``dl.HasValue``, is a nominal and is refused with them)::

    dl.concept_satisfiable(dl.Exists(dl.InverseRole("hasChild"), dl.Top()))
    #  -> raises dl.UnsupportedConceptError: no in-house tableau rule decides I/O

``dl.translate`` translates both constructs faithfully to FOL regardless (a role
expression has a standard FOL image, argument order swapped; a nominal ``{a}``
becomes the equality ``x = a`` — see :mod:`unicode_logic_kit.dl.translate`'s module
docstring). To actually DECIDE a concept that needs either, use
:mod:`unicode_logic_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner (an
optional dependency — install with ``pip install unicode-logic-kit[owl]``)::

    dl.owl_reasoner_available()                       # owlready2 importable?
    dl.external_concept_satisfiable(dl.And(dl.Nominal("a"), dl.Nominal("b")))
    #  -> True: {a} ⊓ {b} is satisfiable absent an explicit DifferentIndividuals
    #     assertion (OWL 2 has no unique name assumption)
    dl.external_instance_check(
        dl.ABox().assert_role("alice", "bob", "hasChild"), "bob",
        dl.Exists(dl.InverseRole("hasChild"), dl.Top()))
    #  -> True: bob has an incoming hasChild edge, i.e. an hasChild-inverse successor

Which route decides what — the axiom-kind table
------------------------------------------------
Every axiom kind a :class:`TBox`/:class:`ABox` can hold has ONE row in
``dl.tableau._AXIOM_KINDS``, and the row says what the in-house tableau does
with it and what the FOL image does with it (see "The axiom-kind table" in
:mod:`unicode_logic_kit.dl.tableau`'s module docstring). Two rules follow, and
they are the kit's answer to "could these two routes disagree?":

* **Builders never refuse.** ``TBox.add_*``/``ABox.assert_*`` accept every
  kind, because a TBox is what a parser fills from a file.
* **A kind the tableau has no rule for is refused BY NAME at query time**, by
  :class:`UnsupportedAxiomError`, from ``concept_satisfiable``/
  ``abox_consistent`` — and so from everything that reduces to them. Never
  approximated, never silently ignored. ``dl.kb_to_fol`` + ``api.prove``, or
  ``dl.external_*``, is where such a kind is answered instead.

The FOL image keeps the two apart as well: ``kb_to_fol(tbox, abox).formula``
is the knowledge base and ``.side_axioms`` the premises that are NOT part of
it (each a :class:`SideAxiom` carrying the OWL ``kind`` it came from, so
``kb.axioms_of_kind("TransitiveObjectProperty")`` is a question with an
answer), while ``tbox_to_fol`` refuses outright to hand back a concept-
inclusion image that silently drops them.

The data layer: two sorts
--------------------------
OWL 2's second sort -- data values, datatypes, data properties -- is STORED
(:class:`DataExists`, :class:`DataForAll`, :class:`DataHasValue`,
:class:`DataAtLeast`, :class:`DataAtMost`; ``TBox.add_data_property_*`` and
``add_datatype_definition``; ``ABox.assert_data``/``assert_negative_data``;
:class:`Literal` and the data ranges :class:`Datatype`,
:class:`DatatypeRestriction`, :class:`DataOneOf`, :class:`DataComplementOf`,
:class:`DataIntersectionOf`, :class:`DataUnionOf`), READ and WRITTEN by the
Manchester and Functional-Style syntaxes, and TRANSLATED by the FOL image --
and REFUSED by the in-house tableau, by name, kind by kind (it has no data
domain), and by ``dl.owl_reasoner``. What answers is ``dl.kb_to_fol`` +
``api.prove``; facets are decided by ``atp.z3_arith``.

The image is a guarded ONE-sorted theory over two reserved predicates,
:data:`OWL_THING` and :data:`OWL_DATA`. The separation of the two domains, the
typing of every data property and individual, the datatype lattice and literal
distinctness are SIDE axioms (``group`` ``"sort"``/``"datatype"``), so the
two-sorted question is the one the prover answers only if they are PREMISES:
pass ``kb.premises`` / ``kb.tbox_premises``, not ``kb.formula`` alone, and let the
bundle build the GOAL, ``kb.subsumption_goal(C, D)``, ``kb.unsatisfiability_goal(C)``
or ``kb.instance_goal(a, C)``, which relativise it the way ``kb.separation``
says (a hand-built goal needs ``subsumption_to_fol(..., object_sort=True)``).
Every GCI of such an image is restricted to ``OwlThing`` (an unrestricted
``⊤ ⊑ {a}`` would range over data values and make an OWL-consistent knowledge
base inconsistent). The sort, typing and datatype axioms are derived from the
vocabulary the knowledge base uses, so name the concepts you are going to ask
about when you build it, ``dl.kb_to_fol(tbox, abox, query=[C, D])`` -- a goal over
a name the bundle does not cover is refused by name, not answered wrongly. The
image is sound -- every OWL model expands to a model of it, so ``proved``
transfers to OWL 2 -- and deliberately not complete: facets are uninterpreted
for ``api.prove``, a literal is typed only by the datatype it was written with,
and the size of a value space is not stated, so ``refuted`` does not transfer
(``kb.refutation_is_decisive`` is ``False`` exactly when there is a data layer).
See "The data layer: two sorts" in the description-logic guide.

Every ``dl.external_*`` function mirrors its ``dl.<name>`` in-house-tableau
namesake's signature and reduction exactly (``external_subsumes`` reduces to
``external_concept_satisfiable`` the way ``subsumes`` reduces to
``concept_satisfiable``, and so on), just decided over the bigger ALCHQ + I + O
fragment instead — see :mod:`unicode_logic_kit.dl.owl_reasoner`'s module docstring.
"""

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DataExists, DataForAll, DataHasValue,
    DataAtLeast, DataAtMost, nnf,
)
from .datatypes import (
    Literal, DataRange, Datatype, DatatypeRestriction, DataOneOf,
    DataComplementOf, DataIntersectionOf, DataUnionOf, UnsupportedDatatypeError,
    OWL_THING, OWL_DATA, datarange_to_fol,
)
from .tableau import (
    TBox, ABox,
    concept_satisfiable, concept_unsatisfiable, subsumes, equivalent, abox_consistent,
    instance_check, instance_retrieval, realize, realize_all,
    NonSimpleRoleError, UnsupportedConceptError, UnsupportedAxiomError,
    RoleExpressionError,
)
from .classification import classify, Classification
from .parser import parse_concept, parse_gci, ConceptSyntaxError
from .translate import (
    concept_to_fol, subsumption_to_fol, tbox_to_fol, rbox_to_fol, abox_to_fol,
    databox_to_fol, data_sort_axioms, check_kb_names,
    kb_to_fol, KnowledgeBaseFOL, SideAxiom, RoleBoxOmittedError,
    concept_to_modal,
)
from .owl_manchester import (
    parse_manchester, to_manchester, parse_manchester_axiom,
    parse_manchester_role_axiom, role_axiom_to_manchester, ManchesterSyntaxError,
    parse_manchester_data_range, to_manchester_data_range, parse_manchester_literal,
)
from .owl_functional import (
    parse_owl_functional, parse_owl_functional_axioms, to_owl_functional,
    parse_owl_functional_class_expression, to_owl_functional_class_expression,
    OwlFunctionalResult, RefusedAxiom, ConsumedAxiom,
    OwlFunctionalSyntaxError, OwlFunctionalUnsupportedError,
)
from .owl_reasoner import (
    available as owl_reasoner_available,
    external_concept_satisfiable, external_concept_unsatisfiable,
    external_subsumes, external_equivalent,
    external_abox_consistent, external_instance_check, external_instance_retrieval,
    external_realize, external_realize_all,
    OwlReasonerError,
)

__all__ = [
    "Concept", "Top", "Bottom", "Atomic", "Not", "And", "Or", "Exists", "ForAll",
    "AtLeast", "AtMost", "InverseRole", "Nominal", "HasValue", "nnf",
    "DataExists", "DataForAll", "DataHasValue", "DataAtLeast", "DataAtMost",
    "Literal", "DataRange", "Datatype", "DatatypeRestriction", "DataOneOf",
    "DataComplementOf", "DataIntersectionOf", "DataUnionOf",
    "UnsupportedDatatypeError", "OWL_THING", "OWL_DATA", "datarange_to_fol",
    "TBox", "ABox",
    "concept_satisfiable", "concept_unsatisfiable", "subsumes", "equivalent",
    "abox_consistent",
    "instance_check", "instance_retrieval", "realize", "realize_all",
    "NonSimpleRoleError", "UnsupportedConceptError", "UnsupportedAxiomError",
    "RoleExpressionError",
    "classify", "Classification",
    "parse_concept", "parse_gci", "ConceptSyntaxError",
    "concept_to_fol", "subsumption_to_fol", "tbox_to_fol", "rbox_to_fol", "abox_to_fol",
    "databox_to_fol", "data_sort_axioms", "check_kb_names",
    "kb_to_fol", "KnowledgeBaseFOL", "SideAxiom", "RoleBoxOmittedError",
    "concept_to_modal",
    "parse_manchester", "to_manchester", "parse_manchester_axiom",
    "parse_manchester_role_axiom", "role_axiom_to_manchester", "ManchesterSyntaxError",
    "parse_manchester_data_range", "to_manchester_data_range", "parse_manchester_literal",
    "parse_owl_functional", "parse_owl_functional_axioms", "to_owl_functional",
    "parse_owl_functional_class_expression", "to_owl_functional_class_expression",
    "OwlFunctionalResult", "RefusedAxiom", "ConsumedAxiom",
    "OwlFunctionalSyntaxError", "OwlFunctionalUnsupportedError",
    "owl_reasoner_available",
    "external_concept_satisfiable", "external_concept_unsatisfiable",
    "external_subsumes", "external_equivalent",
    "external_abox_consistent", "external_instance_check", "external_instance_retrieval",
    "external_realize", "external_realize_all",
    "OwlReasonerError",
]
