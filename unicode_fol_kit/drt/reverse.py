"""FOL → DRS (``fol_to_drs``): the standard translation, run backwards.

:func:`unicode_fol_kit.drt.export.drs_to_fol` maps every DRS onto a
first-order formula of a very particular SHAPE — outer ∃-chains for boxes,
``∀-chain(antecedent → ∃-chain consequent)`` for duplex conditions,
``¬∃-chain`` for negations, counting quantifiers over ``Part_of`` for
``Card``. This module recognizes exactly that image and rebuilds the box
structure; everything outside it is refused by name
(:class:`FolToDrsError`), never approximated:

- modal/temporal/second-order operators — no classical DRS holds them
  (the ACE formula route exists precisely because of that);
- a bare universal without an implication body — no box exports to it;
- a counting quantifier whose matrix is not ``Part_of(v, g)`` — that is
  the FORMULA-level counting reading (``∃=2 x (Dog(x) ∧ …)``), which is
  strictly more expressive than a ``Card`` condition;
- function or number terms in argument positions, and free variables
  (caught by ``DRS.validate`` — an undeclared referent is exactly what a
  free variable becomes).

Two deliberate canonicalizations, both semantically invisible:
``Part_of(a, b)`` atoms come back as the typed ``Part`` condition (the
two export identically), and a strict ``Card`` bound that was shifted on
export returns in shifted form (``Card(g, >, 2)`` exports as ``∃≥3`` and
reads back as ``Card(g, >=, 3)`` — the same claim over natural counts).
The inverse property the tests pin is therefore at the FORMULA level:
``drs_to_fol(fol_to_drs(f)) == f`` node-identically for every ``f`` in
the export's image, and Z3-equivalent to the originating DRS.

The practical use is the ACE chain: ``formula_to_ace`` =
:func:`~unicode_fol_kit.ace.verbalize.drs_to_ace` ∘ ``fol_to_drs`` — "is
this formula expressible as ACE?" becomes two refusal-checked steps with
the round trip as the safety net.
"""

from __future__ import annotations

from typing import List, Tuple

from ..fol.nodes import (
    And, Atom, Constant, Count, Implies, Node, Not, Number, Or as FolOr,
    Quantifier, Variable,
)
from .nodes import DRS, Card, Condition, Eq, Impl, Neg, Or, Part, Pred

__all__ = ["fol_to_drs", "FolToDrsError"]


class FolToDrsError(ValueError):
    """The formula lies outside the image of the standard translation."""


_COUNT_TO_CARD = {"ge": ">=", "le": "<=", "eq": "="}


def fol_to_drs(formula: Node) -> DRS:
    """Rebuild the DRS a formula is the standard translation of.

    Refuses (:class:`FolToDrsError`) anything outside
    :func:`~unicode_fol_kit.drt.export.drs_to_fol`'s image — see the
    module docstring for the exact boundary and the two canonicalizations.
    The result always passes ``DRS.validate``.
    """
    drs = _box(formula)
    try:
        drs.validate()
    except ValueError as exc:
        raise FolToDrsError(
            f"fol_to_drs: the rebuilt DRS fails validation — usually a "
            f"free variable in the input formula ({exc})") from exc
    return drs


def _box(formula: Node) -> DRS:
    refs: List[str] = []
    while isinstance(formula, Quantifier) and formula.type == "∃":
        refs.append(formula.variable.name)
        formula = formula.formula
    conditions = tuple(_condition(c) for c in _conjuncts(formula))
    try:
        return DRS(tuple(refs), conditions)
    except ValueError as exc:
        raise FolToDrsError(f"fol_to_drs: {exc}") from exc


def _conjuncts(formula: Node) -> List[Node]:
    if isinstance(formula, And):
        return _conjuncts(formula.left) + _conjuncts(formula.right)
    return [formula]


def _condition(formula: Node) -> Condition:
    if isinstance(formula, Atom):
        return _atom_condition(formula)
    if isinstance(formula, Count):
        return _card_condition(formula)
    if isinstance(formula, Not):
        return Neg(_box(formula.formula))
    if isinstance(formula, FolOr):
        return Or(_box(formula.left), _box(formula.right))
    if isinstance(formula, Quantifier) and formula.type == "∀":
        return _duplex_condition(formula)
    if isinstance(formula, Quantifier):
        # A ∃ HERE (not in an outer chain) means the input associated its
        # conjunction around it — ∃x P ∧ Q is not a box shape the export
        # produces (it puts every ∃ in front of its whole box).
        raise FolToDrsError(
            "fol_to_drs: an existential inside a conjunct — the export "
            "always lifts ∃ in front of its whole box, so this formula is "
            "not in its image")
    raise FolToDrsError(
        f"fol_to_drs: {type(formula).__name__} has no classical DRS "
        "condition — outside the standard translation's image")


def _atom_condition(atom: Atom) -> Condition:
    args = tuple(_term_name(t) for t in atom.args)
    try:
        if atom.predicate == "=" and len(args) == 2:
            return Eq(args[0], args[1])
        if atom.predicate == "Part_of" and len(args) == 2:
            # Canonicalization: the typed Part condition and a plain
            # Part_of atom export identically; the typed form wins.
            return Part(args[0], args[1])
        return Pred(atom.predicate, args)
    except ValueError as exc:
        raise FolToDrsError(f"fol_to_drs: {exc}") from exc


def _card_condition(count: Count) -> Condition:
    body = count.formula
    if not (isinstance(body, Atom) and body.predicate == "Part_of"
            and len(body.args) == 2
            and isinstance(body.args[0], Variable)
            and body.args[0].name == count.variable.name):
        raise FolToDrsError(
            "fol_to_drs: a counting quantifier whose matrix is not "
            "Part_of(v, g) is the FORMULA-level counting reading — "
            "strictly more expressive than a Card condition, no DRS image")
    group = _term_name(body.args[1])
    try:
        return Card(group, _COUNT_TO_CARD[count.op], count.n.value)
    except ValueError as exc:
        raise FolToDrsError(f"fol_to_drs: {exc}") from exc


def _duplex_condition(formula: Node) -> Condition:
    refs: List[str] = []
    while isinstance(formula, Quantifier) and formula.type == "∀":
        refs.append(formula.variable.name)
        formula = formula.formula
    if not isinstance(formula, Implies):
        raise FolToDrsError(
            f"fol_to_drs: a universal without an implication body (got "
            f"{type(formula).__name__}) — no box exports to ∀ without →, "
            "so this formula is not in the standard translation's image")
    antecedent_conds = tuple(_condition(c) for c in _conjuncts(formula.left))
    try:
        antecedent = DRS(tuple(refs), antecedent_conds)
    except ValueError as exc:
        raise FolToDrsError(f"fol_to_drs: {exc}") from exc
    return Impl(antecedent, _box(formula.right))


def _term_name(term: Node) -> str:
    if isinstance(term, (Variable, Constant)):
        return term.name
    if isinstance(term, Number):
        raise FolToDrsError(
            "fol_to_drs: a number in argument position — DRS conditions "
            "take referents and constants only (values travel as c_ "
            "constants, e.g. c_30)")
    raise FolToDrsError(
        f"fol_to_drs: a {type(term).__name__} term in argument position — "
        "DRS conditions take referents and constants only")
