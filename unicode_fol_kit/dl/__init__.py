"""The ``dl`` subpackage — the description logic **ALC**.

Concept constructors (``import unicode_fol_kit.dl as dl``)::

    dl.Top(), dl.Bottom(), dl.Atomic("Person"), dl.Not(C),
    dl.And(C, D), dl.Or(C, D), dl.Exists("hasChild", C), dl.ForAll("hasChild", C)

Reasoning over a (general) TBox / ABox::

    dl.concept_satisfiable(C, tbox)   # is C satisfiable w.r.t. the TBox?
    dl.subsumes(C, D, tbox)           # does the TBox entail C ⊑ D?
    dl.equivalent(C, D, tbox)         # C ≡ D?
    dl.abox_consistent(abox, tbox)    # is the knowledge base consistent?

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

The standard translation to FOL, so ALC reuses the kit's FOL provers/exports
(:mod:`unicode_fol_kit.dl.translate`)::

    dl.concept_to_fol(C)                # -> FOL formula π(C, x), one free var x
    dl.subsumption_to_fol(C, D)         # -> ∀x (π(C, x) → π(D, x))
    dl.tbox_to_fol(tbox)                # -> conjunction of subsumption_to_fol per GCI
    dl.abox_to_fol(abox)                # -> conjunction of the ABox's assertions
    dl.concept_to_modal(C)              # -> propositional modal-K formula (single role only)
"""

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, nnf,
)
from .tableau import (
    TBox, ABox,
    concept_satisfiable, concept_unsatisfiable, subsumes, equivalent, abox_consistent,
)
from .parser import parse_concept, parse_gci, ConceptSyntaxError
from .translate import (
    concept_to_fol, subsumption_to_fol, tbox_to_fol, abox_to_fol, concept_to_modal,
)
from .owl_manchester import parse_manchester, to_manchester, parse_manchester_axiom, ManchesterSyntaxError

__all__ = [
    "Concept", "Top", "Bottom", "Atomic", "Not", "And", "Or", "Exists", "ForAll", "nnf",
    "TBox", "ABox",
    "concept_satisfiable", "concept_unsatisfiable", "subsumes", "equivalent",
    "abox_consistent",
    "parse_concept", "parse_gci", "ConceptSyntaxError",
    "concept_to_fol", "subsumption_to_fol", "tbox_to_fol", "abox_to_fol",
    "concept_to_modal",
    "parse_manchester", "to_manchester", "parse_manchester_axiom", "ManchesterSyntaxError",
]
