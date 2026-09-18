"""Modal/deontic formula → DRS shell (``fol_to_modal_drs``) — the two ACE-7
surface shapes, measured against live APE, on top of the untouched classical
route.

:func:`unicode_fol_kit.drt.reverse.fol_to_drs` recognizes exactly the
classical standard-translation image and refuses ``Box``/``Diamond``/
``Obligatory``/``Permitted`` by name wherever they occur — read-only here,
reused verbatim for every classical subformula (see its module docstring).
This module adds exactly the two shapes ACE's modal surface can carry
(Attempto's own reading: the modal auxiliary sits INSIDE the verb phrase,
"John must wait.", not a sentence-level paraphrase — see
:mod:`unicode_fol_kit.ace.verbalize`'s module docstring), each probed live
before being written (``tests/test_ace_modal_verbalize.py``):

- **FLAT**: a modality wrapping a whole formula, ``Modality(∃-chain
  classical)`` — "John must wait." — becomes :class:`ModalBox`.
- **NESTED IN A DUPLEX CONSEQUENT**: ``∀-chain(antecedent → Modality(∃-chain
  classical))`` — the probed "modal-universal" fixture, rendered as "If
  there is a man X1 then X1 must wait." — becomes :class:`ModalImpl`.

Neither wrapper joins :class:`unicode_fol_kit.drt.nodes.Condition`: the
classical DRS core stays modality-free by design (``drt/reverse.py``'s own
module docstring), so these are small standalone dataclasses that sit ABOVE
``drt.nodes.DRS``/``Impl``, used only inside this package.

Any other placement — modality mixed with classical conjuncts in one box,
modality inside a negation/disjunction/antecedent, modality nested inside
another modality, a duplex two ∀-levels deep whose INNER consequent is
modal — is refused by the SAME message ``fol_to_drs`` already gives a bare
modal node reached in a position it does not expect ("... has no classical
DRS condition ..."): every shape outside the two above falls straight
through to :func:`~unicode_fol_kit.drt.reverse.fol_to_drs` on the ORIGINAL
formula, unchanged, so the refusal is exactly as loud and as precisely
located as the classical route's own.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Union

from ..drt.nodes import DRS
from ..drt.reverse import fol_to_drs
from ..fol.nodes import (
    Box, Diamond, Implies, Node, Obligatory, Permitted, Quantifier,
)

__all__ = ["ModalBox", "ModalImpl", "fol_to_modal_drs"]

#: Inverts ace.translate._MODAL_NODES: the kit modal node type -> ACE's
#: auxiliary word. Kept local (not imported from .translate) because that
#: module imports drs_reader/mapping machinery this one has no other need
#: of; the table itself is tiny and the inverse relationship is asserted by
#: the tests, not merely assumed.
_MODAL_TYPES = (Box, Diamond, Obligatory, Permitted)
_MODALITY_OF = {Box: "must", Diamond: "can", Obligatory: "should",
                Permitted: "may"}


@dataclass(frozen=True)
class ModalBox:
    """A modality wrapping a whole classical box: ``Modality[drs]`` —
    "John must wait." ``modality`` is one of "must"/"can"/"should"/"may";
    ``drs`` is exactly what :func:`~unicode_fol_kit.drt.reverse.fol_to_drs`
    would build for the modal node's own inner formula."""

    modality: str
    drs: DRS


@dataclass(frozen=True)
class ModalImpl:
    """A duplex condition whose CONSEQUENT carries a modality:
    ``[antecedent] => Modality[consequent]`` — "Every man must wait.",
    verbalized as "If there is a man X1 then X1 must wait." Mirrors
    :class:`unicode_fol_kit.drt.nodes.Impl` (donkey-sentence accessibility:
    ``antecedent``'s referents are visible in ``consequent``), except the
    consequent sits under a modality instead of being a plain box."""

    antecedent: DRS
    modality: str
    consequent: DRS


def fol_to_modal_drs(formula: Node) -> Union[DRS, ModalBox, ModalImpl]:
    """Rebuild the DRS (or modal DRS shell) ``formula`` is the standard
    translation of, recognizing the two probed modal shapes on top of the
    classical image (see the module docstring for the exact boundary).

    Raises:
        unicode_fol_kit.drt.reverse.FolToDrsError: ``formula`` is outside
            the classical image AND outside the two probed modal shapes —
            the same exception :func:`~unicode_fol_kit.drt.reverse.fol_to_drs`
            raises, since every unsupported placement is delegated to it
            unchanged.
    """
    if isinstance(formula, _MODAL_TYPES):
        return ModalBox(_MODALITY_OF[type(formula)],
                        fol_to_drs(formula.formula))
    if isinstance(formula, Quantifier) and formula.type == "∀":
        grafted = _duplex_with_modal_consequent(formula)
        if grafted is not None:
            return grafted
    return fol_to_drs(formula)


def _duplex_with_modal_consequent(formula: Node) -> Optional[ModalImpl]:
    """``None`` when ``formula``'s ∀-chain does not end in ``Implies`` with a
    modal right-hand side (the caller then falls back to plain
    ``fol_to_drs``, which gives the exact classical refusal). Otherwise the
    graft: substitute the modal node's OWN inner formula for the modal node
    in the ∀-chain, hand the now-fully-classical formula to ``fol_to_drs``
    (which rebuilds antecedent AND consequent correctly, donkey accessibility
    included), then re-attach the modality to the resulting consequent —
    reusing ``fol_to_drs`` for every classical piece rather than
    re-deriving ``_duplex_condition``'s logic here."""
    inner = formula
    while isinstance(inner, Quantifier) and inner.type == "∀":
        inner = inner.formula
    if not (isinstance(inner, Implies) and isinstance(inner.right, _MODAL_TYPES)):
        return None
    modality = _MODALITY_OF[type(inner.right)]
    classical = fol_to_drs(_replace_consequent(formula, inner.right.formula))
    # fol_to_drs(∀-chain(... -> ...)) always rebuilds to a DRS with no
    # referents of its own and exactly one Impl condition (mirrors
    # drt.reverse._duplex_condition's return shape).
    impl = classical.conditions[0]
    return ModalImpl(impl.antecedent, modality, impl.consequent)


def _replace_consequent(formula: Node, new_right: Node) -> Node:
    """Rebuild ``formula``'s ∀-chain with its Implies' right-hand side
    swapped for ``new_right`` — the modal node's own inner formula."""
    if isinstance(formula, Quantifier) and formula.type == "∀":
        return Quantifier("∀", formula.variable,
                          _replace_consequent(formula.formula, new_right))
    assert isinstance(formula, Implies)  # guaranteed by the caller's check
    return Implies(formula.left, new_right)
