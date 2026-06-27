"""Truth tables for propositional formulas — classical, Kleene K3, and Priest LP.

A truth table enumerates every assignment of truth values to the formula's atoms and
records the formula's value (and whether that value is *designated*) under each. The
three logics share the strong-Kleene connective tables and differ only in the value
set and the designated values:

- **classical** — values ``{0, 1}``; designated ``{1}``.
- **K3** (strong Kleene) — values ``{0, ½, 1}``; designated ``{1}``.
- **LP** (Priest) — values ``{0, ½, 1}``; designated ``{½, 1}`` (paraconsistent).

Restricted to ``{0, 1}`` the strong-Kleene tables coincide with the classical ones,
so all three reuse :func:`unicode_fol_kit.semantics.manyvalued.kleene_value`.

Each distinct atom (by surface form — ``P`` and ``P(a)`` are different columns) is a
propositional variable. Quantified formulas have no finite truth table and are
rejected.

Public API: :func:`truth_table`, :class:`TruthTable`, and the convenience predicates
:func:`is_tautology`, :func:`is_contradiction`, :func:`is_satisfiable_tt`.
"""

from dataclasses import dataclass
from itertools import product
from typing import Dict, List, Tuple

from ..fol.nodes import Node, Atom, Quantifier, SortedQuantifier
from ..fol._so_nodes import SecondOrderQuantifier
from .manyvalued import kleene_value, DESIGNATED


# Value sets and designated sets per logic (classical added to the K3/LP table).
_VALUES = {
    "classical": (1.0, 0.0),
    "K3": (1.0, 0.5, 0.0),
    "LP": (1.0, 0.5, 0.0),
}
_DESIGNATED = {"classical": frozenset({1.0}), **DESIGNATED}

# Display glyphs.
_GLYPH_BOOL = {1.0: "T", 0.0: "F"}
_GLYPH_MANY = {1.0: "1", 0.5: "½", 0.0: "0"}


def _collect_atoms(formula: Node) -> List[str]:
    """Return the distinct atom surface-forms in ``formula``, in first-occurrence order.

    Raises ValueError on a quantified formula (no finite truth table exists).
    """
    if isinstance(formula, (Quantifier, SortedQuantifier, SecondOrderQuantifier)):
        raise ValueError(
            "truth_table: quantified formulas have no finite truth table; "
            "use the finite model finder or an evaluator instead."
        )
    order: List[str] = []
    seen = set()

    def walk(node: Node) -> None:
        if isinstance(node, (Quantifier, SortedQuantifier, SecondOrderQuantifier)):
            raise ValueError(
                "truth_table: quantified formulas have no finite truth table."
            )
        if isinstance(node, Atom):
            key = node.to_unicode_str()
            if key not in seen:
                seen.add(key)
                order.append(key)
            return
        for child in node._child_nodes():
            walk(child)

    walk(formula)
    return order


@dataclass(frozen=True)
class TruthTable:
    """A computed truth table: atom columns, value rows, and the designated flags.

    ``atoms`` are the column headers (atom surface-forms). ``rows`` is a tuple of
    ``(assignment, value, designated)`` where ``assignment`` is the tuple of atom
    values aligned with ``atoms``, ``value`` is the formula's value, and
    ``designated`` says whether ``value`` is designated under ``logic``.
    """

    formula: Node
    atoms: Tuple[str, ...]
    rows: Tuple[Tuple[Tuple[float, ...], float, bool], ...]
    logic: str

    @property
    def is_tautology(self) -> bool:
        """True iff the formula is designated under every assignment."""
        return all(d for _, _, d in self.rows)

    @property
    def is_contradiction(self) -> bool:
        """True iff the formula is designated under no assignment."""
        return not any(d for _, _, d in self.rows)

    @property
    def is_satisfiable(self) -> bool:
        """True iff the formula is designated under some assignment."""
        return any(d for _, _, d in self.rows)

    def render(self) -> str:
        """Render the truth table as a GitHub-flavoured Markdown table."""
        glyph = _GLYPH_BOOL if self.logic == "classical" else _GLYPH_MANY
        head = list(self.atoms) + [self.formula.to_unicode_str()]
        lines = ["| " + " | ".join(head) + " |",
                 "|" + "|".join(["---"] * len(head)) + "|"]
        for assignment, value, _ in self.rows:
            cells = [glyph[v] for v in assignment] + [glyph[value]]
            lines.append("| " + " | ".join(cells) + " |")
        return "\n".join(lines)

    def __str__(self) -> str:
        return self.render()


def truth_table(formula: Node, logic: str = "classical") -> TruthTable:
    """Compute the :class:`TruthTable` of a propositional ``formula`` under ``logic``.

    Args:
        formula: a quantifier-free formula; each distinct atom is a propositional
            variable.
        logic: ``"classical"`` (values {0,1}), ``"K3"`` or ``"LP"`` (values {0,½,1}).

    Raises:
        ValueError: on an unknown logic or a quantified formula.
    """
    if logic not in _VALUES:
        raise ValueError(f"truth_table: unknown logic {logic!r} "
                         f"(use 'classical', 'K3', or 'LP').")
    atoms = _collect_atoms(formula)
    values = _VALUES[logic]
    designated = _DESIGNATED[logic]
    rows = []
    for assignment in product(values, repeat=len(atoms)):
        valuation: Dict[str, float] = dict(zip(atoms, assignment))
        value = kleene_value(formula, valuation)
        rows.append((assignment, value, value in designated))
    return TruthTable(formula, tuple(atoms), tuple(rows), logic)


def is_tautology(formula: Node, logic: str = "classical") -> bool:
    """True iff ``formula`` is designated under every assignment (a logical truth)."""
    return truth_table(formula, logic).is_tautology


def is_contradiction(formula: Node, logic: str = "classical") -> bool:
    """True iff ``formula`` is designated under no assignment."""
    return truth_table(formula, logic).is_contradiction


def is_satisfiable_tt(formula: Node, logic: str = "classical") -> bool:
    """True iff ``formula`` is designated under some assignment."""
    return truth_table(formula, logic).is_satisfiable
