"""The ``dl`` subpackage — the description logic **ALC**.

Concept constructors (``import unicode_fol_kit.dl as dl``)::

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
(see :mod:`unicode_fol_kit.dl.tableau`)::

    dl.instance_check(abox, "alice", C, tbox)       # does the KB entail alice : C?
    dl.instance_retrieval(abox, C, tbox)             # every individual entailed to be C
    dl.realize(abox, "alice", vocabulary, tbox)      # alice's most-specific concepts
    dl.realize_all(abox, vocabulary, tbox)           # realize() for every individual

TBox classification — the whole named-concept subsumption hierarchy as a pure
reduction to ``subsumes`` (see :mod:`unicode_fol_kit.dl.classification`)::

    dl.classify(tbox)                 # -> Classification(equivalents, parents,
                                       #    children, ancestors)

ALC is exactly multi-modal K; the reasoner is a tableau with TBox internalisation
and subset blocking (see :mod:`unicode_fol_kit.dl.tableau`).

Parsing the glyph concept syntax back into a :class:`Concept`
(:mod:`unicode_fol_kit.dl.parser`)::

    dl.parse_concept("∃hasChild.(Doctor ⊓ ¬Rich)")   # -> Concept
    dl.parse_gci("Doctor ⊑ ∃hasChild.⊤")              # -> (Concept, Concept)

Parsing/rendering the W3C OWL 2 Manchester Syntax (ALC fragment only,
:mod:`unicode_fol_kit.dl.owl_manchester`)::

    dl.parse_manchester("hasChild some (Doctor and not Rich)")   # -> Concept
    dl.to_manchester(C)                                          # -> str
    dl.parse_manchester_axiom("Doctor SubClassOf hasChild some owl:Thing")
    #  -> ("subclass", Concept, Concept)
    dl.parse_manchester_role_axiom("hasChild SubPropertyOf hasDescendant")
    #  -> ("subproperty", "hasChild", "hasDescendant")
    dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive")
    #  -> ("transitive", "hasDescendant")

Parsing/rendering the W3C OWL 2 Functional-Style Syntax (ALCHQ fragment, a whole
ontology document rather than a single axiom, :mod:`unicode_fol_kit.dl.owl_functional`)::

    dl.parse_owl_functional("Ontology(SubClassOf(Doctor Person))")   # -> (TBox, ABox)
    dl.to_owl_functional(tbox, abox)                                 # -> str
    dl.parse_owl_functional_class_expression("ObjectSomeValuesFrom(hasChild Doctor)")
    #  -> Exists("hasChild", Atomic("Doctor"))
    dl.to_owl_functional_class_expression(C)                        # -> str

The standard translation to FOL, so ALC reuses the kit's FOL provers/exports
(:mod:`unicode_fol_kit.dl.translate`)::

    dl.concept_to_fol(C)                # -> FOL formula π(C, x), one free var x
    dl.subsumption_to_fol(C, D)         # -> ∀x (π(C, x) → π(D, x))
    dl.tbox_to_fol(tbox)                # -> conjunction of subsumption_to_fol per GCI
    dl.rbox_to_fol(tbox)                # -> conjunction of role-inclusion/transitivity closures
    dl.abox_to_fol(abox)                # -> conjunction of the ABox's assertions
    dl.concept_to_modal(C)              # -> propositional modal-K formula (single role only)

Role hierarchies and transitive roles (RBox), on top of the concept-level TBox
(:mod:`unicode_fol_kit.dl.tableau`)::

    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    dl.subsumes(dl.Exists("hasChild", dl.Exists("hasChild", C)), dl.Exists("hasDescendant", C), t)
    #  -> True: ∃hasChild.∃hasChild.C ⊑ ∃hasDescendant.C, entailed by the RBox alone

Qualified number restrictions (ALCQ), on SIMPLE roles only (a role that is
transitive, or has a transitive sub-role, raises ``NonSimpleRoleError`` by name —
see :mod:`unicode_fol_kit.dl.tableau`'s "Qualified number restrictions" section)::

    dl.concept_satisfiable(dl.And(dl.AtLeast(2, "r", C), dl.AtMost(1, "r", dl.Top())))
    #  -> False: at least 2 pairwise-distinct r-successors but at most 1 r-successor at all

``ABox.assert_distinct(a, b)`` records ``a ≠ b`` — this reasoner has no unique name
assumption (see the same tableau section), so two ABox individuals otherwise remain
mergeable, which matters as soon as a number restriction is in play.

``instance_check``/``classify``/the rest of the reasoning API above respect a TBox's
RBox automatically, since they all reduce to ``concept_satisfiable``/``abox_consistent``
— no separate RBox-aware entry point is needed anywhere else.

Inverse roles and nominals (I, O) — outside ALCHQ, refused by the in-house tableau::

    dl.concept_satisfiable(dl.Exists(dl.InverseRole("hasChild"), dl.Top()))
    #  -> raises dl.UnsupportedConceptError: no in-house tableau rule decides I/O

``dl.translate`` translates both constructs faithfully to FOL regardless (a role
expression has a standard FOL image, argument order swapped; a nominal ``{a}``
becomes the equality ``x = a`` — see :mod:`unicode_fol_kit.dl.translate`'s module
docstring). To actually DECIDE a concept that needs either, use
:mod:`unicode_fol_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner (an
optional dependency — install with ``pip install unicode-fol-kit[owl]``)::

    dl.owl_reasoner_available()                       # owlready2 importable?
    dl.external_concept_satisfiable(dl.And(dl.Nominal("a"), dl.Nominal("b")))
    #  -> True: {a} ⊓ {b} is satisfiable absent an explicit DifferentIndividuals
    #     assertion (OWL 2 has no unique name assumption)
    dl.external_instance_check(
        dl.ABox().assert_role("alice", "bob", "hasChild"), "bob",
        dl.Exists(dl.InverseRole("hasChild"), dl.Top()))
    #  -> True: bob has an incoming hasChild edge, i.e. an hasChild-inverse successor

Every ``dl.external_*`` function mirrors its ``dl.<name>`` in-house-tableau
namesake's signature and reduction exactly (``external_subsumes`` reduces to
``external_concept_satisfiable`` the way ``subsumes`` reduces to
``concept_satisfiable``, and so on), just decided over the bigger ALCHQ + I + O
fragment instead — see :mod:`unicode_fol_kit.dl.owl_reasoner`'s module docstring.
"""

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, nnf,
)
from .tableau import (
    TBox, ABox,
    concept_satisfiable, concept_unsatisfiable, subsumes, equivalent, abox_consistent,
    instance_check, instance_retrieval, realize, realize_all,
    NonSimpleRoleError, UnsupportedConceptError,
)
from .classification import classify, Classification
from .parser import parse_concept, parse_gci, ConceptSyntaxError
from .translate import (
    concept_to_fol, subsumption_to_fol, tbox_to_fol, rbox_to_fol, abox_to_fol,
    concept_to_modal,
)
from .owl_manchester import (
    parse_manchester, to_manchester, parse_manchester_axiom,
    parse_manchester_role_axiom, role_axiom_to_manchester, ManchesterSyntaxError,
)
from .owl_functional import (
    parse_owl_functional, to_owl_functional,
    parse_owl_functional_class_expression, to_owl_functional_class_expression,
    OwlFunctionalSyntaxError,
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
    "AtLeast", "AtMost", "InverseRole", "Nominal", "nnf",
    "TBox", "ABox",
    "concept_satisfiable", "concept_unsatisfiable", "subsumes", "equivalent",
    "abox_consistent",
    "instance_check", "instance_retrieval", "realize", "realize_all",
    "NonSimpleRoleError", "UnsupportedConceptError",
    "classify", "Classification",
    "parse_concept", "parse_gci", "ConceptSyntaxError",
    "concept_to_fol", "subsumption_to_fol", "tbox_to_fol", "rbox_to_fol", "abox_to_fol",
    "concept_to_modal",
    "parse_manchester", "to_manchester", "parse_manchester_axiom",
    "parse_manchester_role_axiom", "role_axiom_to_manchester", "ManchesterSyntaxError",
    "parse_owl_functional", "to_owl_functional",
    "parse_owl_functional_class_expression", "to_owl_functional_class_expression",
    "OwlFunctionalSyntaxError",
    "owl_reasoner_available",
    "external_concept_satisfiable", "external_concept_unsatisfiable",
    "external_subsumes", "external_equivalent",
    "external_abox_consistent", "external_instance_check", "external_instance_retrieval",
    "external_realize", "external_realize_all",
    "OwlReasonerError",
]
