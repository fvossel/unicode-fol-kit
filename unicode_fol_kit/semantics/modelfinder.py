"""Finite model finder — search for a finite model (or countermodel) of a theory.

The complement of the provers: where ``prove`` / ``is_valid`` answer *"does it
follow?"*, this answers *"is there a structure where it holds?"* by brute-force
enumeration of finite :class:`~unicode_fol_kit.semantics.tarski.Structure`\\ s over a
domain ``{0, 1, …, k-1}`` for increasing ``k``, checking each with the Tarskian
evaluator. It is the Mace4-style partner of the resolution prover: a valid entailment
has *no* countermodel, an invalid one usually has a small finite one.

- :func:`find_model` — a finite model satisfying every formula of a theory, or None.
- :func:`find_countermodel` — a finite structure satisfying ``premises`` but not
  ``conclusion`` (a witness that the entailment fails), or None.
- :func:`is_satisfiable_finite` / :func:`is_valid_finite` — the boolean wrappers.

Free variables are read as universally quantified (each formula is universally
closed). The search is **bounded**: a domain size whose interpretation space exceeds
``max_candidates`` is skipped, so ``None`` means "no model found within the bounds",
not "unsatisfiable" (first-order satisfiability is undecidable, and some satisfiable
sentences have only infinite models).

**Many-sorted (MSFOL)** input is handled directly: each named sort gets a non-empty
universe (a non-empty subset of the domain) enumerated alongside the rest of the
interpretation, sorted constants are placed inside their sort, and a
``SortedQuantifier`` ranges over its sort — so a found :class:`Structure` carries the
``sorts`` mapping. Sorts may overlap (the relativisation reading).

Public API: :func:`find_model`, :func:`find_countermodel`,
:func:`is_satisfiable_finite`, :func:`is_valid_finite`.
"""

from itertools import product
from typing import List, Optional

from ..fol.nodes import Node, Atom, Not, Quantifier, Variable, Constant, Number, Function
from ..fol.nodes import SortedConstant, SortedQuantifier
from ..fol.nodes import Count, Cardinality, SortedCount, SortedCardinality
from ..fol.nodes import SlashedExists, Measure
from .tarski import Structure, models, _MEASURE_FUNC


#: Node types that bind a logical variable over a ``formula`` scope — the quantifiers,
#: the counting quantifiers and cardinality terms (and their sorted variants), and the
#: IF-logic slashed existential.
_VAR_BINDERS = (Quantifier, SortedQuantifier, Count, Cardinality,
                SortedCount, SortedCardinality, SlashedExists)

#: The subset of the above that additionally names a sort the structures must interpret.
_SORTED_BINDERS = (SortedQuantifier, SortedCount, SortedCardinality)


MAX_CANDIDATES = 1 << 20  # ~1M structures per domain size before a size is skipped


# ---------------------------------------------------------------------------
# Free-variable closure and signature collection
# ---------------------------------------------------------------------------

def _free_var_names(node: Node, bound: frozenset = frozenset()) -> set:
    """Return the names of variables occurring free in ``node``."""
    if isinstance(node, Variable):
        return set() if node.name in bound else {node.name}
    if isinstance(node, SlashedExists):
        # The slash set names ENCLOSING binders, so those names are free here (and
        # are not shadowed by this binder's own variable).
        inner = _free_var_names(node.formula, bound | {node.variable.name})
        return inner | {n for n in node.slashed if n not in bound}
    if isinstance(node, _VAR_BINDERS):
        return _free_var_names(node.formula, bound | {node.variable.name})
    names: set = set()
    for child in node._child_nodes():
        names |= _free_var_names(child, bound)
    return names


def _universal_closure(node: Node) -> Node:
    """Wrap ``node`` in ∀ for each free variable (deterministic order)."""
    result = node
    for name in sorted(_free_var_names(node), reverse=True):
        result = Quantifier("∀", Variable(name), result)
    return result


class _Signature:
    """The constants, functions, predicates, and sorts a theory's structures interpret."""

    def __init__(self):
        self.constants: set = set()                 # names
        self.functions: set = set()                 # (name, arity)
        self.predicates: set = set()                # (name, arity)
        self.sorts: set = set()                      # sort names (MSFOL)
        self.sorted_constants: dict = {}             # constant name -> sort name

    def scan(self, node: Node) -> None:
        if isinstance(node, SortedConstant):
            self.constants.add(node.name)
            self.sorts.add(node.sort)
            self.sorted_constants[node.name] = node.sort
        elif isinstance(node, Constant):
            self.constants.add(node.name)
        elif isinstance(node, Number):
            self.constants.add(str(node.value))
        elif isinstance(node, Function):
            self.functions.add((node.name, len(node.args)))
            for a in node.args:
                self.scan(a)
        elif isinstance(node, Measure):
            # μ(entity, dimension) denotes the binary function ``measure`` — the same
            # symbol Measure.to_z3 / to_prover9 emit, so a structure found here
            # interprets what the provers see. The dimension is an ordinary term.
            self.functions.add(_MEASURE_FUNC)
            self.scan(node.entity)
            self.scan(node.dimension)
        elif isinstance(node, Atom):
            if node.predicate not in ("=", "≠"):     # identity is built in
                self.predicates.add((node.predicate, len(node.args)))
            for a in node.args:
                self.scan(a)
        elif isinstance(node, _VAR_BINDERS):
            # Scan only the scope: a binder's ``variable`` is not a signature symbol,
            # and a Count's ``n`` is a cardinality bound, not an individual — walking
            # the children generically would register it as a domain constant.
            if isinstance(node, _SORTED_BINDERS):
                self.sorts.add(node.sort)
            self.scan(node.formula)
        else:
            for child in node._child_nodes():
                self.scan(child)


# ---------------------------------------------------------------------------
# Enumeration of finite interpretations
# ---------------------------------------------------------------------------

def _candidate_count(sig: "_Signature", k: int) -> int:
    """The number of distinct interpretations of ``sig`` over a ``k``-element domain."""
    total = k ** len(sig.constants)
    for _, arity in sig.functions:
        total *= k ** (k ** arity)
    for _, arity in sig.predicates:
        total *= 1 << (k ** arity)
    # Each sort ranges over the non-empty subsets of the domain (its universe).
    for _ in sig.sorts:
        total *= (1 << k) - 1
    return total


def _nonempty_subsets(domain: tuple):
    """Yield every non-empty subset of ``domain`` as a tuple (a sort universe)."""
    items = list(domain)
    for mask in range(1, 1 << len(items)):
        yield tuple(items[i] for i in range(len(items)) if (mask >> i) & 1)


def _func_pred_interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(functions, predicates)`` for every interpretation of the func/pred part."""
    func_sig = sorted(sig.functions)
    pred_sig = sorted(sig.predicates)
    func_options = []
    for _, arity in func_sig:
        arg_tuples = list(product(domain, repeat=arity))
        func_options.append(list(product(domain, repeat=len(arg_tuples))))
    pred_options = []
    for _, arity in pred_sig:
        arg_tuples = list(product(domain, repeat=arity))
        pred_options.append(list(product((False, True), repeat=len(arg_tuples))))
    for func_choice in (product(*func_options) if func_options else [()]):
        functions = {}
        for (name, arity), values in zip(func_sig, func_choice):
            arg_tuples = list(product(domain, repeat=arity))
            functions[(name, arity)] = dict(zip(arg_tuples, values))
        for pred_choice in (product(*pred_options) if pred_options else [()]):
            predicates = {}
            for (name, arity), mask in zip(pred_sig, pred_choice):
                arg_tuples = list(product(domain, repeat=arity))
                predicates[(name, arity)] = {t for t, inc in zip(arg_tuples, mask) if inc}
            yield functions, predicates


def _sorted_interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(constants, functions, predicates, sorts)`` for an MSFOL signature.

    Each sort gets a non-empty universe (a non-empty subset of the domain); a sorted
    constant is restricted to its sort's universe; the rest is the classical
    enumeration. Sorts may overlap (the relativisation reading).
    """
    sort_names = sorted(sig.sorts)
    const_names = sorted(sig.constants)
    sort_options = [list(_nonempty_subsets(domain)) for _ in sort_names]
    for sort_choice in (product(*sort_options) if sort_options else [()]):
        sorts = {name: universe for name, universe in zip(sort_names, sort_choice)}
        const_option_lists = [
            list(sorts[sig.sorted_constants[name]]) if name in sig.sorted_constants
            else list(domain)
            for name in const_names
        ]
        for const_choice in (product(*const_option_lists) if const_option_lists else [()]):
            constants = dict(zip(const_names, const_choice))
            for functions, predicates in _func_pred_interpretations(sig, domain):
                yield constants, functions, predicates, sorts


def _interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(constants, functions, predicates)`` dicts for every interpretation."""
    k = len(domain)
    const_names = sorted(sig.constants)
    func_sig = sorted(sig.functions)
    pred_sig = sorted(sig.predicates)

    # Per-symbol option lists.
    const_options = list(product(domain, repeat=len(const_names)))
    func_options = []
    for _, arity in func_sig:
        arg_tuples = list(product(domain, repeat=arity))
        func_options.append(list(product(domain, repeat=len(arg_tuples))))
    pred_options = []
    for _, arity in pred_sig:
        arg_tuples = list(product(domain, repeat=arity))
        pred_options.append(list(product((False, True), repeat=len(arg_tuples))))

    for const_choice in const_options:
        constants = dict(zip(const_names, const_choice))
        for func_choice in (product(*func_options) if func_options else [()]):
            functions = {}
            for (name, arity), values in zip(func_sig, func_choice):
                arg_tuples = list(product(domain, repeat=arity))
                functions[(name, arity)] = dict(zip(arg_tuples, values))
            for pred_choice in (product(*pred_options) if pred_options else [()]):
                predicates = {}
                for (name, arity), mask in zip(pred_sig, pred_choice):
                    arg_tuples = list(product(domain, repeat=arity))
                    predicates[(name, arity)] = {
                        t for t, inc in zip(arg_tuples, mask) if inc
                    }
                yield constants, functions, predicates


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def find_model(formulas, max_size: int = 4,
               max_candidates: int = MAX_CANDIDATES) -> Optional[Structure]:
    """Return a finite :class:`Structure` satisfying every formula, or None.

    Searches domains of size ``1 .. max_size`` in turn, enumerating every
    interpretation of the theory's signature and returning the first structure in
    which all formulas hold. A domain size whose interpretation space exceeds
    ``max_candidates`` is skipped (so a return of None is bounded, not a proof of
    unsatisfiability).
    """
    sentences = [_universal_closure(f) for f in formulas]
    sig = _Signature()
    for s in sentences:
        sig.scan(s)
    for k in range(1, max_size + 1):
        if _candidate_count(sig, k) > max_candidates:
            continue
        domain = tuple(range(k))
        if sig.sorts:
            for constants, functions, predicates, sorts in _sorted_interpretations(sig, domain):
                structure = Structure(domain, constants=constants, functions=functions,
                                      predicates=predicates, sorts=sorts)
                if all(models(s, structure) for s in sentences):
                    return structure
        else:
            for constants, functions, predicates in _interpretations(sig, domain):
                structure = Structure(domain, constants=constants,
                                      functions=functions, predicates=predicates)
                if all(models(s, structure) for s in sentences):
                    return structure
    return None


def find_countermodel(premises, conclusion: Node, max_size: int = 4,
                      max_candidates: int = MAX_CANDIDATES) -> Optional[Structure]:
    """Return a finite structure satisfying ``premises`` but not ``conclusion``, or None.

    A countermodel witnesses that ``premises`` do **not** entail ``conclusion``. The
    conclusion is universally closed and negated, so the structure refutes the
    entailment for some assignment of its free variables.
    """
    refuted = Not(_universal_closure(conclusion))
    return find_model(list(premises) + [refuted], max_size, max_candidates)


def is_satisfiable_finite(formula: Node, max_size: int = 4,
                          max_candidates: int = MAX_CANDIDATES) -> bool:
    """True iff ``formula`` has a finite model of size ≤ ``max_size`` (bounded)."""
    return find_model([formula], max_size, max_candidates) is not None


def is_valid_finite(formula: Node, max_size: int = 4,
                    max_candidates: int = MAX_CANDIDATES) -> bool:
    """True iff no finite countermodel of ``formula`` exists up to ``max_size`` (bounded).

    Bounded and one-sided: True means "no countermodel found within the bounds"
    (strong evidence of validity, not a proof); a False is a genuine refutation —
    :func:`find_countermodel` returns the witnessing structure.
    """
    return find_countermodel([], formula, max_size, max_candidates) is None
