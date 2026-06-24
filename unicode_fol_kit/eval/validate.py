"""Well-formedness / validity report for (LLM-generated) FOL formulas.

This module provides lightweight, purely structural checks that flag the
defects most commonly seen in machine-produced first-order formulas:

  * the formula is not a closed sentence (it has free logical variables);
  * a predicate or function symbol is applied with inconsistent arities;
  * leftover lambda machinery (Lambda / Application / LambdaVar) that should
    have been eliminated before the formula was considered final;
  * (via ``validate_text``) the raw model output does not even parse.

The entry points are:

  * ``validate(node)``      — inspect an already-parsed AST.
  * ``is_wellformed(node)`` — the headline boolean.
  * ``validate_text(text)`` — parse raw text first, capturing parse failures.

Nothing here mutates its input; every traversal is read-only.
"""

from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

from unicode_fol_kit.fol.nodes import (
    Node,
    Variable,
    Constant,
    Function,
    Atom,
    Lambda,
    Application,
    LambdaVar,
    SortedQuantifier,
    SortedConstant,
    free_variables,
)


# ---------------------------------------------------------------------------
# Report dataclass
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ValidationReport:
    """An immutable summary of the well-formedness checks run on a formula.

    Namespacing of ``arity_conflicts``: predicate and function symbols live in
    SEPARATE namespaces, so a key is a 2-tuple ``("pred", name)`` or
    ``("func", name)``. This keeps a predicate ``P`` used as ``P/1`` from
    falsely conflicting with an unrelated function ``p`` used as ``p/2``.

    Fields:
        is_closed: True iff the formula has no free logical variables (it is a
            sentence). Free occurrences of both ``Variable`` and ``LambdaVar``
            count against closedness.
        free_variable_names: sorted, de-duplicated names of the free
            Variable/LambdaVar occurrences.
        arity_consistent: True iff every predicate symbol is used with a single
            arity and likewise every function symbol.
        arity_conflicts: maps a namespaced symbol key ``("pred"|"func", name)``
            to the sorted tuple of the distinct arities observed; only symbols
            with more than one distinct arity appear.
        has_lambdas: True iff any Lambda / Application / LambdaVar remains.
        predicates / functions / constants: sorted ``name/arity`` (predicates,
            functions) or ``name`` (constants) inventories for quick inspection.
        sorts_used: sorted sort names from SortedQuantifier / SortedConstant.
        parseable: True for ``validate(node)``; ``validate_text`` sets it False
            on a parse failure.
        error: the parse-error message when ``parseable`` is False, else None.
    """

    is_closed: bool
    free_variable_names: Tuple[str, ...]
    arity_consistent: bool
    arity_conflicts: Dict[Tuple[str, str], Tuple[int, ...]]
    has_lambdas: bool
    predicates: Tuple[str, ...]
    functions: Tuple[str, ...]
    constants: Tuple[str, ...]
    sorts_used: Tuple[str, ...]
    parseable: bool = True
    error: Optional[str] = None

    def __str__(self) -> str:
        """Render a compact, human-readable multi-line summary."""
        if not self.parseable:
            return f"ValidationReport(parseable=False, error={self.error!r})"
        lines = [
            "ValidationReport(",
            f"  parseable        = {self.parseable}",
            f"  is_closed        = {self.is_closed}",
            f"  free_variables   = {', '.join(self.free_variable_names) or '-'}",
            f"  arity_consistent = {self.arity_consistent}",
            f"  arity_conflicts  = {dict(self.arity_conflicts) or '-'}",
            f"  has_lambdas      = {self.has_lambdas}",
            f"  predicates       = {', '.join(self.predicates) or '-'}",
            f"  functions        = {', '.join(self.functions) or '-'}",
            f"  constants        = {', '.join(self.constants) or '-'}",
            f"  sorts_used       = {', '.join(self.sorts_used) or '-'}",
            ")",
        ]
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Internal inventory collection
# ---------------------------------------------------------------------------

@dataclass
class _Inventory:
    """Mutable scratch collector populated by a single pre-order walk.

    Kept private and never returned; ``validate`` freezes the results into the
    immutable ``ValidationReport``. Arities are accumulated per namespaced
    symbol so that conflicts can be detected afterwards.
    """

    pred_arities: Dict[str, set] = field(default_factory=dict)
    func_arities: Dict[str, set] = field(default_factory=dict)
    constants: set = field(default_factory=set)
    sorts: set = field(default_factory=set)
    has_lambdas: bool = False


# Comparison atoms (=, ≠, <, >, ≤, ≥) and arithmetic functions (+, -, *, /) are
# built-in operators, not user predicate/function symbols, so they are excluded
# from the inventories and from arity-consistency checking.
_BUILTIN_PREDS = frozenset({"=", "≠", "<", ">", "≤", "≥"})
_BUILTIN_FUNCS = frozenset({"+", "-", "*", "/"})


def _collect(node: Node, inv: _Inventory) -> None:
    """Walk ``node`` in pre-order, recording every symbol into ``inv``.

    Uses ``node.walk()`` (the shared pre-order traversal) so that any future
    structural node type is covered without changes here. Each occurrence is
    classified purely by node type; nothing is mutated on the input.
    """
    for n in node.walk():
        if isinstance(n, (Lambda, Application, LambdaVar)):
            inv.has_lambdas = True

        if isinstance(n, Atom):
            if n.predicate not in _BUILTIN_PREDS:
                inv.pred_arities.setdefault(n.predicate, set()).add(len(n.args))
        elif isinstance(n, Function):
            if n.name not in _BUILTIN_FUNCS:
                inv.func_arities.setdefault(n.name, set()).add(len(n.args))
        elif isinstance(n, Constant):
            inv.constants.add(n.name)
        elif isinstance(n, SortedConstant):
            inv.constants.add(n.name)
            inv.sorts.add(n.sort)
        elif isinstance(n, SortedQuantifier):
            inv.sorts.add(n.sort)


def _arity_conflicts(inv: _Inventory) -> Dict[Tuple[str, str], Tuple[int, ...]]:
    """Return namespaced symbols seen with more than one arity.

    Keys are ``("pred", name)`` / ``("func", name)``; values are the sorted
    tuple of distinct arities. Symbols with a single consistent arity are
    omitted, so an empty dict means full arity consistency.
    """
    conflicts: Dict[Tuple[str, str], Tuple[int, ...]] = {}
    for name, arities in inv.pred_arities.items():
        if len(arities) > 1:
            conflicts[("pred", name)] = tuple(sorted(arities))
    for name, arities in inv.func_arities.items():
        if len(arities) > 1:
            conflicts[("func", name)] = tuple(sorted(arities))
    return conflicts


def _inventory_strings(arities: Dict[str, set]) -> Tuple[str, ...]:
    """Render a name->arities map as a sorted tuple of ``name/arity`` strings.

    A symbol with conflicting arities yields one entry per distinct arity (e.g.
    ``P/1`` and ``P/2``), so the inventory faithfully shows every form seen.
    """
    entries = []
    for name, arity_set in arities.items():
        for arity in sorted(arity_set):
            entries.append(f"{name}/{arity}")
    return tuple(sorted(entries))


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def validate(node: Node) -> ValidationReport:
    """Run all well-formedness checks on an already-parsed AST.

    The returned report always has ``parseable=True`` (the node was, by
    definition, parsed to exist). ``validate_text`` is the entry point that can
    report a parse failure.

    Args:
        node: any FOL/MSFL ``Node``.

    Returns:
        A frozen ``ValidationReport`` describing closedness, arity consistency,
        residual lambda machinery, and symbol inventories.
    """
    free = free_variables(node)
    free_names = tuple(sorted({v.name for v in free}))

    inv = _Inventory()
    _collect(node, inv)

    conflicts = _arity_conflicts(inv)

    return ValidationReport(
        is_closed=not free,
        free_variable_names=free_names,
        arity_consistent=not conflicts,
        arity_conflicts=conflicts,
        has_lambdas=inv.has_lambdas,
        predicates=_inventory_strings(inv.pred_arities),
        functions=_inventory_strings(inv.func_arities),
        constants=tuple(sorted(inv.constants)),
        sorts_used=tuple(sorted(inv.sorts)),
        parseable=True,
        error=None,
    )


def is_wellformed(node: Node) -> bool:
    """Convenience headline check on an already-parsed AST.

    A node is well-formed iff it is a closed sentence, every symbol is used
    with a single arity, and no lambda machinery remains.
    """
    report = validate(node)
    return report.is_closed and report.arity_consistent and not report.has_lambdas


def validate_text(text: str, parser=None) -> ValidationReport:
    """Parse ``text`` then validate it, capturing syntactic failures.

    This is the entry point for raw model output: a parse failure
    (``NamingError`` / ``ParsingError``) yields a report with
    ``parseable=False`` and the error message in ``error`` rather than raising.

    Args:
        text: the raw formula string.
        parser: an ``MSFLParser`` instance (or anything with a compatible
            ``.parse``). Defaults to a fresh ``MSFLParser()`` (classical FOL
            mode). Pass ``MSFLParser(many_sorted=True)`` etc. for other modes.

    Returns:
        On success, a report with ``parseable=True`` plus the ``validate(node)``
        fields. On a parse failure, a report with ``parseable=False``, the
        error message in ``error``, and conservative empty/false field values.
    """
    # Imported lazily so the AST-only checks (validate / is_wellformed) do not
    # pull in the parser stack, and to mirror the package's import boundaries.
    from unicode_fol_kit import MSFLParser, NamingError, ParsingError

    if parser is None:
        parser = MSFLParser()

    try:
        node = parser.parse(text)
    except (NamingError, ParsingError) as exc:
        return ValidationReport(
            is_closed=False,
            free_variable_names=(),
            arity_consistent=False,
            arity_conflicts={},
            has_lambdas=False,
            predicates=(),
            functions=(),
            constants=(),
            sorts_used=(),
            parseable=False,
            error=str(exc),
        )

    return validate(node)
