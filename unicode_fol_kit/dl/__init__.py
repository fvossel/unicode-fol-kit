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
"""

from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, nnf,
)
from .tableau import (
    TBox, ABox,
    concept_satisfiable, concept_unsatisfiable, subsumes, equivalent, abox_consistent,
)

__all__ = [
    "Concept", "Top", "Bottom", "Atomic", "Not", "And", "Or", "Exists", "ForAll", "nnf",
    "TBox", "ABox",
    "concept_satisfiable", "concept_unsatisfiable", "subsumes", "equivalent",
    "abox_consistent",
]
