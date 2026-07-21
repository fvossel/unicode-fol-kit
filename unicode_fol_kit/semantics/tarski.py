"""Classical (two-valued) Tarskian model theory for FOL and MSFOL.

A :class:`Structure` is a first-order "world": a non-empty domain of
individuals together with interpretations of the constant, function, and
predicate symbols (and, for MSFOL, the named sorts). :func:`satisfies`
computes the truth value of a formula in such a structure under a variable
assignment, following Tarski's recursive definition of satisfaction.

Only the classical fragment is interpreted here. Łukasiewicz (fuzzy) operators
and lambda nodes are rejected with a clear error: the former need the
many-valued evaluator, the latter must be beta-reduced / lambda-eliminated
first.

Functional style: the variable assignment dict is never mutated. When a
quantifier ranges over the domain, the binding is added to a *copy* of the
assignment for each candidate individual.
"""

import operator
from typing import Any, Callable, Dict, Iterable, Mapping, Optional, Tuple, Union

from ..fol.nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    Count, Cardinality, SortedCount, SortedCardinality, Measure,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

# Quantifier.type spellings accepted for each quantifier kind.
_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

#: The function symbol a :class:`Measure` term denotes. Matches ``Measure.to_z3`` and
#: ``Measure.to_prover9``, so a structure found here interprets the same symbol the
#: provers see.
_MEASURE_FUNC = ("measure", 2)

# Infix comparison predicates that are NOT equality/disequality. Their
# extensions live in Structure.predicates like any ordinary relation.
_ORDER_COMPARISONS = frozenset({"<", ">", "≤", "≥"})

#: Numeric readings of the order comparisons (see :func:`_order_value`).
_ORDER_OPS = {
    "<": operator.lt, ">": operator.gt, "≤": operator.le, "≥": operator.ge,
}

# Łukasiewicz node types: two-valued Tarski cannot interpret them.
_FUZZY_TYPES = (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
)

# Lambda-calculus node types: must be eliminated before evaluation.
_LAMBDA_TYPES = (LambdaVar, Lambda, Application)


class Structure:
    """A first-order structure (model / "world") over a non-empty domain.

    Args:
        domain: a non-empty iterable of individuals (any hashable Python
            values, e.g. ``{"alice", "bob"}`` or ``{0, 1}``). Stored as a
            tuple preserving order; duplicates are dropped.
        constants: maps a constant NAME (str) to an individual in the domain.
            Interprets both :class:`Constant` and :class:`SortedConstant`.
            :class:`Number` ``n`` defaults to the individual ``n`` unless the
            name ``str(n)`` is overridden here.
        functions: maps ``(name, arity)`` to either a Python callable
            ``(*args) -> individual`` or a plain dict ``{arg_tuple: individual}``.
            A dict is looked up by the tuple of evaluated argument individuals.
        predicates: maps ``(name, arity)`` to the relation's extension — a set
            (or any container) of argument tuples of individuals. A nullary
            predicate maps ``(name, 0)`` to a bool. A missing predicate denotes
            the empty relation (always false), except for the order comparisons
            ``< > ≤ ≥``, which fall back to arithmetic when both operands
            evaluate to numbers — see :func:`_order_value`.
        sorts: maps a sort name (str) to its universe — a subset of the domain.
            Used by :class:`SortedQuantifier` to restrict the quantifier range.

    All mapping arguments default to empty, so a bare ``Structure(domain)`` is
    a valid (if symbol-free) world.
    """

    def __init__(
        self,
        domain: Iterable[Any],
        constants: Optional[Mapping[str, Any]] = None,
        functions: Optional[Mapping[Tuple[str, int], Union[Callable, Mapping]]] = None,
        predicates: Optional[Mapping[Tuple[str, int], Any]] = None,
        sorts: Optional[Mapping[str, Iterable[Any]]] = None,
    ):
        """Build a structure, copying each mapping so later edits never leak in."""
        # Deduplicate while preserving order; reject an empty domain.
        seen = []
        for d in domain:
            if d not in seen:
                seen.append(d)
        if not seen:
            raise ValueError("Structure domain must be non-empty.")
        self.domain: Tuple[Any, ...] = tuple(seen)

        self.constants: Dict[str, Any] = dict(constants or {})
        self.functions: Dict[Tuple[str, int], Union[Callable, Mapping]] = dict(functions or {})
        self.predicates: Dict[Tuple[str, int], Any] = dict(predicates or {})
        self.sorts: Dict[str, Tuple[Any, ...]] = {
            name: tuple(universe) for name, universe in (sorts or {}).items()
        }

    def __repr__(self) -> str:
        """Show the domain size and the symbol tables for quick inspection."""
        return (
            f"Structure(domain={self.domain!r}, "
            f"constants={self.constants!r}, "
            f"functions={list(self.functions)!r}, "
            f"predicates={list(self.predicates)!r}, "
            f"sorts={self.sorts!r})"
        )

    def sort_universe(self, sort: str) -> Tuple[Any, ...]:
        """Return the universe of a named sort.

        Raises:
            KeyError: if the sort is undeclared. An undeclared sort is an error
                rather than the empty set, since ``∀x:Undeclared φ`` vacuously
                true and ``∃x:Undeclared φ`` false would silently mask a typo.
        """
        if sort not in self.sorts:
            raise KeyError(
                f"Sort {sort!r} is not declared in this structure "
                f"(known sorts: {sorted(self.sorts)})."
            )
        return self.sorts[sort]


def term_value(term: Node, structure: Structure, assignment: Mapping[str, Any]) -> Any:
    """Evaluate a term to its individual in the structure under an assignment.

    - :class:`Variable` ``v`` → ``assignment[v.name]``.
    - :class:`Constant` / :class:`SortedConstant` ``c`` → ``structure.constants[c.name]``.
    - :class:`Number` ``n`` → ``structure.constants.get(str(n), n)`` (the literal
      value itself by default).
    - :class:`Function` → the interpreted function applied to the evaluated args;
      the interpretation may be a callable or a ``{arg_tuple: value}`` dict.

    Raises:
        KeyError: for an unassigned variable or an uninterpreted constant.
        ValueError: for an uninterpreted function symbol, a dict interpretation
            missing an argument tuple, or a lambda / non-term node.
    """
    if isinstance(term, Variable):
        if term.name not in assignment:
            raise KeyError(f"Variable {term.name!r} is not bound in the assignment.")
        return assignment[term.name]

    if isinstance(term, (Constant, SortedConstant)):
        if term.name not in structure.constants:
            raise KeyError(
                f"Constant {term.name!r} has no interpretation in the structure."
            )
        return structure.constants[term.name]

    if isinstance(term, Number):
        return structure.constants.get(str(term.value), term.value)

    if isinstance(term, Function):
        args = tuple(term_value(a, structure, assignment) for a in term.args)
        key = (term.name, len(term.args))
        if key not in structure.functions:
            raise ValueError(
                f"Function {term.name!r}/{len(term.args)} has no interpretation "
                f"in the structure."
            )
        interp = structure.functions[key]
        if callable(interp):
            return interp(*args)
        # Dict-style interpretation: look up the evaluated argument tuple.
        if args not in interp:
            raise ValueError(
                f"Function {term.name!r}/{len(term.args)} is undefined for "
                f"arguments {args!r}."
            )
        return interp[args]

    if isinstance(term, (Cardinality, SortedCardinality)):
        # |{v : φ}| counts the individuals satisfying φ. The count is a NATURAL
        # NUMBER, not a domain individual — comparing it with a Number literal works
        # because both evaluate to Python ints, but comparing it to a domain element
        # is a category error the untyped evaluator cannot catch.
        return sum(1 for _ in _witnesses(term, structure, assignment))

    if isinstance(term, Measure):
        # μ(entity, dimension) is the binary function ``measure``, matching the Z3 and
        # Prover9 lowerings — a structure that interprets it agrees with the provers.
        args = (term_value(term.entity, structure, assignment),
                term_value(term.dimension, structure, assignment))
        if _MEASURE_FUNC not in structure.functions:
            raise ValueError(
                "Measure term μ(…) needs an interpretation for the function "
                f"{_MEASURE_FUNC[0]!r}/{_MEASURE_FUNC[1]} in the structure."
            )
        interp = structure.functions[_MEASURE_FUNC]
        if callable(interp):
            return interp(*args)
        if args not in interp:
            raise ValueError(
                f"Function {_MEASURE_FUNC[0]!r}/{_MEASURE_FUNC[1]} is undefined for "
                f"arguments {args!r}."
            )
        return interp[args]

    if isinstance(term, _LAMBDA_TYPES):
        raise ValueError(
            f"Cannot evaluate lambda node {type(term).__name__} as a term; "
            "beta-reduce and lambda-eliminate the formula first."
        )

    raise ValueError(
        f"term_value: {type(term).__name__} is not a term node."
    )


def _witnesses(
    binder: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
) -> Iterable[Any]:
    """Yield the individuals in ``binder``'s range that satisfy its matrix.

    Shared by the counting quantifiers and the cardinality terms: both bind one
    variable over a matrix and differ only in what they do with the witnesses. A
    sorted binder ranges over its sort's universe, an unsorted one over the domain.
    """
    universe = (structure.sort_universe(binder.sort)
                if isinstance(binder, (SortedCount, SortedCardinality))
                else structure.domain)
    name = binder.variable.name
    for d in universe:
        if satisfies(binder.formula, structure, _extend(assignment, name, d)):
            yield d


def _is_number(value: Any) -> bool:
    """Whether a term value counts as a number for an order comparison.

    ``bool`` is excluded even though Python makes it an ``int`` subclass: a truth
    value is not a position on a scale, and letting ``True ≥ False`` quietly
    succeed would hide a modelling error rather than surface it.
    """
    return not isinstance(value, bool) and isinstance(value, (int, float))


def _order_value(atom: Atom, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """Truth value of a binary order comparison ``< > ≤ ≥``.

    Three readings apply, in this order of precedence:

    1. A :class:`Cardinality` operand forces the **numeric** reading. A cardinality
       is a natural number this evaluator computes itself, so there is no freedom
       left to a structure; routing it through a relation extension would be a
       category error. A cardinality compared against a non-number raises.
    2. Otherwise a **declared** extension wins. The order symbols are ordinary
       relation symbols of the language, and a structure may interpret ``<`` over
       its domain however it likes — that is also the reading ``to_z3`` /
       ``to_prover9`` export, where the comparison is an uninterpreted relation.
    3. Otherwise, if both operands evaluate to numbers, the **numeric** reading
       applies. This is what makes an undeclared order over :class:`Measure` values
       behave: ``μ`` is an uninterpreted function, so a structure that maps it to
       numbers without also declaring ``≥`` would otherwise fall through to the
       empty relation and be silently false — the same failure mode (1) exists to
       prevent for cardinalities.

    Anything else is the empty relation, hence false, like any uninterpreted
    predicate. Note the asymmetry between (1) and (2) is deliberate and not an
    inconsistency: a cardinality *is* a number, whereas a measure's values are
    whatever the structure says they are.
    """
    left, right = (term_value(a, structure, assignment) for a in atom.args)

    if any(isinstance(a, (Cardinality, SortedCardinality)) for a in atom.args):
        for value in (left, right):
            if not _is_number(value):
                raise ValueError(
                    f"Cannot compare a cardinality with {value!r}: an order "
                    f"comparison involving |{{v : φ}}| is numeric, so both operands "
                    f"must evaluate to numbers."
                )
        return _ORDER_OPS[atom.predicate](left, right)

    key = (atom.predicate, 2)
    if key in structure.predicates:
        return (left, right) in structure.predicates[key]

    if _is_number(left) and _is_number(right):
        return _ORDER_OPS[atom.predicate](left, right)

    return False


def _atom_value(atom: Atom, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """Compute the truth value of an atomic formula.

    Equality ``=`` is identity of the two term values; ``≠`` is non-identity.
    A nullary predicate reads its bool from ``predicates[(name, 0)]``. A binary
    order comparison ``< > ≤ ≥`` is delegated to :func:`_order_value`. Every other
    predicate is true iff the tuple of argument values lies in its extension; a
    missing extension is the empty relation, hence false.
    """
    if atom.predicate == "=" and len(atom.args) == 2:
        return term_value(atom.args[0], structure, assignment) == \
            term_value(atom.args[1], structure, assignment)
    if atom.predicate == "≠" and len(atom.args) == 2:
        return term_value(atom.args[0], structure, assignment) != \
            term_value(atom.args[1], structure, assignment)

    if not atom.args:
        return bool(structure.predicates.get((atom.predicate, 0), False))

    if atom.predicate in _ORDER_COMPARISONS and len(atom.args) == 2:
        return _order_value(atom, structure, assignment)

    values = tuple(term_value(a, structure, assignment) for a in atom.args)
    extension = structure.predicates.get((atom.predicate, len(atom.args)), ())
    return values in extension


def _extend(assignment: Mapping[str, Any], name: str, value: Any) -> Dict[str, Any]:
    """Return a copy of the assignment with ``name`` bound to ``value``.

    The input mapping is never mutated (functional style).
    """
    extended = dict(assignment)
    extended[name] = value
    return extended


def satisfies(
    formula: Node,
    structure: Structure,
    assignment: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Return whether ``structure`` satisfies ``formula`` under ``assignment``.

    ``assignment`` maps logical variable names to individuals; it defaults to
    the empty assignment (appropriate for a sentence with no free variables).

    Connectives follow the classical truth tables. ``∀x φ`` holds iff every
    individual of the domain satisfies ``φ`` with ``x`` bound to it; ``∃x φ``
    iff some individual does. A :class:`SortedQuantifier` ranges over the named
    sort's universe instead of the whole domain.

    Raises:
        ValueError: on a Łukasiewicz node (use the fuzzy evaluator — Tarski is
            two-valued) or a lambda node (eliminate it first), or on an unknown
            quantifier type or node type.
    """
    if assignment is None:
        assignment = {}

    if isinstance(formula, Atom):
        return _atom_value(formula, structure, assignment)

    if isinstance(formula, Not):
        return not satisfies(formula.formula, structure, assignment)

    if isinstance(formula, And):
        return (satisfies(formula.left, structure, assignment)
                and satisfies(formula.right, structure, assignment))

    if isinstance(formula, Or):
        return (satisfies(formula.left, structure, assignment)
                or satisfies(formula.right, structure, assignment))

    if isinstance(formula, Xor):
        return (satisfies(formula.left, structure, assignment)
                != satisfies(formula.right, structure, assignment))

    if isinstance(formula, Implies):
        return ((not satisfies(formula.left, structure, assignment))
                or satisfies(formula.right, structure, assignment))

    if isinstance(formula, Iff):
        return (satisfies(formula.left, structure, assignment)
                == satisfies(formula.right, structure, assignment))

    if isinstance(formula, Quantifier):
        return _eval_quantifier(
            formula.type, formula.variable.name, structure.domain,
            formula.formula, structure, assignment,
        )

    if isinstance(formula, SortedQuantifier):
        universe = structure.sort_universe(formula.sort)
        return _eval_quantifier(
            formula.type, formula.variable.name, universe,
            formula.formula, structure, assignment,
        )

    if isinstance(formula, (Count, SortedCount)):
        # ∃≥n / ∃≤n / ∃=n: count the witnesses, compare against the bound. The whole
        # (finite) universe is walked — ``le`` and ``eq`` need the exact count anyway,
        # and the universes here are the small ones the model search enumerates.
        witnesses = sum(1 for _ in _witnesses(formula, structure, assignment))
        n = formula.n.value
        if formula.op == "ge":
            return witnesses >= n
        if formula.op == "le":
            return witnesses <= n
        if formula.op == "eq":
            return witnesses == n
        raise ValueError(f"Unknown counting-quantifier op: {formula.op!r}")

    if isinstance(formula, _FUZZY_TYPES):
        raise ValueError(
            f"Cannot evaluate Łukasiewicz node {type(formula).__name__} with the "
            "two-valued Tarskian evaluator; use the fuzzy evaluator instead."
        )

    if isinstance(formula, _LAMBDA_TYPES):
        raise ValueError(
            f"Cannot evaluate lambda node {type(formula).__name__}; beta-reduce "
            "and lambda-eliminate the formula before calling satisfies."
        )

    raise ValueError(
        f"satisfies: unsupported node type {type(formula).__name__}."
    )


def _eval_quantifier(
    qtype: str,
    var_name: str,
    universe: Iterable[Any],
    body: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
) -> bool:
    """Evaluate a quantifier over a given universe of individuals.

    ``∀`` holds iff the body holds for every individual; ``∃`` iff for some.
    Each candidate is bound in a fresh copy of the assignment (no mutation).
    """
    if qtype in _FORALL:
        return all(
            satisfies(body, structure, _extend(assignment, var_name, d))
            for d in universe
        )
    if qtype in _EXISTS:
        return any(
            satisfies(body, structure, _extend(assignment, var_name, d))
            for d in universe
        )
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def models(formula: Node, structure: Structure) -> bool:
    """Convenience alias: ``satisfies(formula, structure, {})``.

    Reads as "structure models formula" — the sentence is evaluated under the
    empty assignment, so it is meaningful for closed formulas (no free
    variables).
    """
    return satisfies(formula, structure, {})
