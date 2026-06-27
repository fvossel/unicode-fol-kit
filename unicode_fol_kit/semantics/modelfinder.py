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

Public API: :func:`find_model`, :func:`find_countermodel`,
:func:`is_satisfiable_finite`, :func:`is_valid_finite`.
"""

from itertools import product
from typing import List, Optional

from ..fol.nodes import Node, Atom, Not, Quantifier, Variable, Constant, Number, Function
from ..fol.nodes import SortedConstant
from .tarski import Structure, models


MAX_CANDIDATES = 1 << 20  # ~1M structures per domain size before a size is skipped


# ---------------------------------------------------------------------------
# Free-variable closure and signature collection
# ---------------------------------------------------------------------------

def _free_var_names(node: Node, bound: frozenset = frozenset()) -> set:
    """Return the names of variables occurring free in ``node``."""
    if isinstance(node, Variable):
        return set() if node.name in bound else {node.name}
    if isinstance(node, Quantifier):
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
    """The constants, functions, and predicates a theory's structures must interpret."""

    def __init__(self):
        self.constants: set = set()                 # names
        self.functions: set = set()                 # (name, arity)
        self.predicates: set = set()                # (name, arity)

    def scan(self, node: Node) -> None:
        if isinstance(node, (Constant, SortedConstant)):
            self.constants.add(node.name)
        elif isinstance(node, Number):
            self.constants.add(str(node.value))
        elif isinstance(node, Function):
            self.functions.add((node.name, len(node.args)))
            for a in node.args:
                self.scan(a)
        elif isinstance(node, Atom):
            if node.predicate not in ("=", "≠"):     # identity is built in
                self.predicates.add((node.predicate, len(node.args)))
            for a in node.args:
                self.scan(a)
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
    return total


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
