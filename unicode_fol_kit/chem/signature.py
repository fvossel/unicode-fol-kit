"""The declared ChemLog vocabulary as a first-class kit signature.

Plus the alias mapping between the two spellings
:mod:`unicode_fol_kit.chem.mol` can emit. (The summary line above carries no
role and no dotted name on purpose: autosummary truncates it at the first
period, so ``:mod:`unicode_fol_kit.chem.mol``` would be cut after
``unicode_fol_kit.`` and leave an unterminated backtick in the generated
table.)

:data:`CHEMLOG_SIGNATURE` is what makes
``unicode_fol_kit.api.check(formula, signature=CHEMLOG_SIGNATURE)`` reject a
class definition that uses an unknown predicate or the wrong arity — the
paper's own failure analysis attributes 89 of 136 failed classifications to
"pure syntax", and a chunk of that is exactly the kind of vocabulary slip
(wrong arity, a typo'd predicate name, a hallucinated one) a signature check
catches for free, before the definition ever reaches model checking. It is
built from :func:`unicode_fol_kit.chem._naming.chemlog_predicate_arities`
(the SAME source :mod:`.mol` itself consults) rather than a second,
hand-copied literal list — so a predicate ``mol_to_structure(naming=
"chemlog")`` can actually produce is *by construction* always something
``CHEMLOG_SIGNATURE`` declares, and vice versa. This module has no RDKit
dependency (:mod:`._naming` does not either) — a caller wanting only
signature validation, not molecule translation, never pays RDKit's import
cost.

What ``CHEMLOG_SIGNATURE`` does NOT cover — documented, not silent
------------------------------------------------------------------------
Only the CANONICAL hydrogen-count (0..3) and formal-charge (-1, 0, +1)
range is declared, matching the ChemLog spec text's own literal examples
(see :mod:`._naming`'s ``CANONICAL_HS_RANGE`` / ``CANONICAL_CHARGES``). A
real molecule needing ``has_4_hs`` (methane) or ``charge_m2`` (a doubly-
anionic atom, e.g. one oxygen of a deprotonated phosphate) still gets that
predicate POPULATED by ``mol_to_structure`` (its atom loop adds such keys on
demand — see that module's docstring), but ``CHEMLOG_SIGNATURE.validate()``
/ ``api.check`` will then honestly report it as an UNDECLARED predicate
rather than silently accepting anything shaped like ``charge_m<N>``. This is
the kit's loud-refusal convention applied to the signature itself: widening
the declared range is a caller's explicit choice
(``CHEMLOG_SIGNATURE.merge(Signature.from_dict({"predicates": {"charge_m2": 1}}))``),
never an implicit one made silently on a caller's behalf here.

Argument sorts are deliberately left unset (every :class:`PredicateDecl` has
``arg_sorts=None``) — ChemLog's own vocabulary is single-sorted (there is
only one kind of individual, "atom"), so there is nothing for a sort
declaration to distinguish.
"""

from typing import Dict

from ..fol.signature import Signature, PredicateDecl
from . import _naming

__all__ = ["CHEMLOG_SIGNATURE", "CHEMLOG_TO_PAPER", "PAPER_TO_CHEMLOG",
           "to_paper_naming", "to_chemlog_naming"]

#: The ChemLog (TPTP-style) vocabulary as a first-class kit :class:`Signature`
#: — see the module docstring for exactly what is (and is not) covered.
CHEMLOG_SIGNATURE = Signature(predicates={
    name: PredicateDecl(name, arity)
    for name, arity in _naming.chemlog_predicate_arities().items()
})

#: ChemLog-spelling predicate name -> the ChEBI2FOL-paper-prose spelling of
#: the SAME predicate (e.g. ``"has_3_hs" -> "has3Hs"``, ``"bSINGLE" ->
#: "singleBond"``). Covers exactly the predicates :data:`CHEMLOG_SIGNATURE`
#: declares MINUS ``has_bond_to`` (the paper's prose never names a second
#: bond-existence relation — see :mod:`._naming`) and minus the five
#: computed predicates (``in_ring`` etc. — scheme-invariant, so an alias
#: entry would be a no-op; see :mod:`._naming`'s closing paragraph).
CHEMLOG_TO_PAPER: Dict[str, str] = dict(_naming.CHEMLOG_TO_PAPER)

#: The inverse of :data:`CHEMLOG_TO_PAPER`.
PAPER_TO_CHEMLOG: Dict[str, str] = dict(_naming.PAPER_TO_CHEMLOG)


def to_paper_naming(chemlog_name: str) -> str:
    """Translate a ChemLog-spelled predicate name to its paper-prose spelling.

    Raises :class:`KeyError` (naming the symbol) for a predicate outside
    :data:`CHEMLOG_TO_PAPER`'s domain — either not part of the ChemLog
    vocabulary at all, or one of the two documented exclusions above
    (``has_bond_to``, or a computed predicate, which needs no translation
    since it is spelled identically already).
    """
    try:
        return CHEMLOG_TO_PAPER[chemlog_name]
    except KeyError:
        raise KeyError(
            f"to_paper_naming: {chemlog_name!r} has no paper-prose alias "
            "(either not a ChemLog predicate at all, or one of the "
            "documented exclusions — see the chem.signature module "
            "docstring)"
        ) from None


def to_chemlog_naming(paper_name: str) -> str:
    """Translate a paper-prose-spelled predicate name to its ChemLog spelling.

    Inverse of :func:`to_paper_naming`; raises :class:`KeyError` on the same
    terms.
    """
    try:
        return PAPER_TO_CHEMLOG[paper_name]
    except KeyError:
        raise KeyError(
            f"to_chemlog_naming: {paper_name!r} has no ChemLog alias "
            "(either not a recognised paper-prose predicate, or one of the "
            "documented exclusions — see the chem.signature module "
            "docstring)"
        ) from None
