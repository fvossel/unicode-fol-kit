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

from typing import Any, Callable, Dict, Iterable, Mapping, Optional, Tuple, Union

from ..fol.nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

# Quantifier.type spellings accepted for each quantifier kind.
_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

# Infix comparison predicates that are NOT equality/disequality. Their
# extensions live in Structure.predicates like any ordinary relation.
_ORDER_COMPARISONS = frozenset({"<", ">", "≤", "≥"})

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
            the empty relation (always false).
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

    if isinstance(term, _LAMBDA_TYPES):
        raise ValueError(
            f"Cannot evaluate lambda node {type(term).__name__} as a term; "
            "beta-reduce and lambda-eliminate the formula first."
        )

    raise ValueError(
        f"term_value: {type(term).__name__} is not a term node."
    )


def _atom_value(atom: Atom, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """Compute the truth value of an atomic formula.

    Equality ``=`` is identity of the two term values; ``≠`` is non-identity.
    A nullary predicate reads its bool from ``predicates[(name, 0)]``. Every
    other predicate (including the order comparisons ``< > ≤ ≥``) is true iff
    the tuple of argument values lies in its extension; a missing extension is
    the empty relation, hence false.
    """
    if atom.predicate == "=" and len(atom.args) == 2:
        return term_value(atom.args[0], structure, assignment) == \
            term_value(atom.args[1], structure, assignment)
    if atom.predicate == "≠" and len(atom.args) == 2:
        return term_value(atom.args[0], structure, assignment) != \
            term_value(atom.args[1], structure, assignment)

    if not atom.args:
        return bool(structure.predicates.get((atom.predicate, 0), False))

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
