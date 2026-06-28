"""Free logic — first-order logic without the existence assumption.

Classical FOL assumes every term denotes an *existing* individual, so universal
instantiation ``∀x φ → φ(c)`` and existential generalisation ``φ(c) → ∃x φ`` are
valid. **Free logic** drops that assumption: quantifiers range only over an *inner
domain* of existing objects ``E``, while constants and function terms may denote an
object of the wider outer domain, or fail to denote at all. An existence predicate
``E!(t)`` says "``t`` denotes an existing object", and the classical inference rules
hold only in their *guarded* forms ``(∀x φ ∧ E!(c)) → φ(c)`` and ``(φ(c) ∧ E!(c)) → ∃x φ``.

A :class:`FreeModel` carries an ``outer`` domain, the ``existing`` inner subset, a
(possibly partial) constant/function interpretation, and predicate tables over the
outer domain. Two policies for an atom that contains a **non-denoting** term:

- ``"negative"`` (default) — the atom is simply **false** (negative free logic;
  ``t = t`` then also fails when ``t`` does not denote);
- ``"positive"`` — self-identity ``t = t`` is **true** for any term, while every other
  atom with a non-denoting term is false (the common positive-free-logic convention
  for identity).

Public API: :class:`FreeModel`, :data:`NONDENOTING`, :func:`free_satisfies`,
:func:`free_holds`.
"""

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, Mapping, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
)

# Sentinel returned by term evaluation when a term has no referent.
NONDENOTING = object()

_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")
_EXISTS_PRED = "E!"     # the existence predicate


@dataclass(frozen=True)
class FreeModel:
    """A free-logic model: an inner ``existing`` domain inside an ``outer`` domain.

    ``outer`` lists every object (existing or merely possible); ``existing`` is the
    inner domain the quantifiers range over (⊆ ``outer``). ``constants`` maps a name to
    an ``outer`` element — a name absent from the map is **non-denoting**. ``functions``
    maps ``(name, arity)`` to a partial table ``{argtuple: value}`` (a missing entry, or
    any non-denoting argument, makes the application non-denoting). ``predicates`` maps
    ``(name, arity)`` to a set of ``outer`` tuples.
    """

    outer: Tuple[Any, ...]
    existing: FrozenSet[Any]
    constants: Mapping[str, Any] = field(default_factory=dict)
    functions: Mapping[Tuple[str, int], Mapping[Tuple[Any, ...], Any]] = field(default_factory=dict)
    predicates: Mapping[Tuple[str, int], FrozenSet[Tuple[Any, ...]]] = field(default_factory=dict)


def _term_value(term: Node, model: FreeModel, assignment: Mapping[str, Any]):
    """Evaluate a term to an outer-domain element, or :data:`NONDENOTING`."""
    if isinstance(term, Variable):
        return assignment.get(term.name, NONDENOTING)
    if isinstance(term, Constant):
        return model.constants.get(term.name, NONDENOTING)
    if isinstance(term, Number):
        return model.constants.get(str(term.value), NONDENOTING)
    if isinstance(term, Function):
        args = tuple(_term_value(a, model, assignment) for a in term.args)
        if any(v is NONDENOTING for v in args):
            return NONDENOTING
        table = model.functions.get((term.name, len(term.args)), {})
        return table.get(args, NONDENOTING)
    raise TypeError(f"free_logic: not a term: {type(term).__name__}")


def free_satisfies(formula: Node, model: FreeModel,
                   assignment: Optional[Mapping[str, Any]] = None,
                   policy: str = "negative") -> bool:
    """Return whether ``model`` satisfies ``formula`` under free-logic semantics.

    Quantifiers range over ``model.existing``; ``E!(t)`` is true iff ``t`` denotes an
    existing object; an atom with a non-denoting term is handled per ``policy``
    (``"negative"`` / ``"positive"`` — see the module docstring).
    """
    if assignment is None:
        assignment = {}
    if policy not in ("negative", "positive"):
        raise ValueError(f"free_satisfies: unknown policy {policy!r} (negative / positive).")

    if isinstance(formula, Atom):
        return _atom(formula, model, assignment, policy)
    if isinstance(formula, Not):
        return not free_satisfies(formula.formula, model, assignment, policy)
    if isinstance(formula, And):
        return (free_satisfies(formula.left, model, assignment, policy)
                and free_satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Or):
        return (free_satisfies(formula.left, model, assignment, policy)
                or free_satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Xor):
        return (free_satisfies(formula.left, model, assignment, policy)
                != free_satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Implies):
        return ((not free_satisfies(formula.left, model, assignment, policy))
                or free_satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Iff):
        return (free_satisfies(formula.left, model, assignment, policy)
                == free_satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Quantifier):
        var = formula.variable.name
        results = (
            free_satisfies(formula.formula, model, {**assignment, var: d}, policy)
            for d in model.existing
        )
        if formula.type in _FORALL:
            return all(results)
        if formula.type in _EXISTS:
            return any(results)
        raise ValueError(f"free_satisfies: unknown quantifier {formula.type!r}")
    raise TypeError(f"free_satisfies: unsupported node {type(formula).__name__}")


def _atom(atom: Atom, model: FreeModel, assignment: Mapping[str, Any], policy: str) -> bool:
    """Truth value of an atom, applying the non-denoting policy."""
    values = tuple(_term_value(a, model, assignment) for a in atom.args)
    nondenoting = any(v is NONDENOTING for v in values)

    if atom.predicate == _EXISTS_PRED and len(atom.args) == 1:
        return (not nondenoting) and values[0] in model.existing
    if atom.predicate in ("=", "≠"):
        if nondenoting:
            # negative: t=t false when t non-denoting; positive: self-identity true.
            eq = (policy == "positive" and atom.args[0] == atom.args[1])
            return eq if atom.predicate == "=" else (not eq)
        eq = values[0] == values[1]
        return eq if atom.predicate == "=" else (not eq)
    if nondenoting:
        return False                              # negative & positive agree for predicates
    relation = model.predicates.get((atom.predicate, len(atom.args)), frozenset())
    return values in relation


def free_holds(formula: Node, model: FreeModel, policy: str = "negative") -> bool:
    """Convenience: ``free_satisfies`` of a closed ``formula`` (empty assignment)."""
    return free_satisfies(formula, model, {}, policy)
