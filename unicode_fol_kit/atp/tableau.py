"""Analytic (semantic) tableaux — a refutation method that also yields countermodels.

A tableau decomposes a set of formulas with the standard signed-free rules: the
*α* (non-branching) rules break a conjunctive formula into its parts, the *β*
(branching) rules split a disjunctive one, the *δ* rule witnesses an existential with
a fresh constant, and the *γ* rule instantiates a universal at the available terms. A
branch **closes** when it contains both ``φ`` and ``¬φ`` (or ``⊥``); the set is jointly
**unsatisfiable** iff *every* branch closes. An *open* saturated branch is, by
contrast, a model — so a failed refutation hands back a countermodel for free.

This gives a fourth proof method alongside resolution, Fitch, and the sequent
calculus: ``is_valid_tableau(φ)`` builds a tableau for ``¬φ`` (valid iff it closes),
and ``tableau_model`` returns the open branch's literals as a satisfying assignment.

Propositional tableaux are decidable and complete; the first-order rules are run under
a step bound (``γ``-instantiation is only semi-decidable), so — like the resolution
prover — a non-closing first-order tableau within the bound is reported as "open"
without claiming satisfiability.

Public API: :func:`tableau_closed`, :func:`is_valid_tableau`, :func:`prove_tableau`,
:func:`tableau_model`.
"""

from typing import List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant, Number, Function,
)
from .fitch import FALSUM, is_falsum, _subst_var, _q_kind, _free_vars


def _neg(f: Node) -> Node:
    """Return the complementary formula of ``f`` (``¬φ`` ↔ ``φ``)."""
    return f.formula if isinstance(f, Not) else Not(f)


def _ground_terms(node: Node, acc: set) -> None:
    """Collect the closed (variable-free) constant/number/function terms in ``node``."""
    if isinstance(node, (Constant, Number)):
        acc.add(node)
    elif isinstance(node, Function):
        if not _free_vars(node):
            acc.add(node)
        for a in node.args:
            _ground_terms(a, acc)
    elif isinstance(node, Atom):
        for a in node.args:
            _ground_terms(a, acc)
    else:
        for child in node._child_nodes():
            _ground_terms(child, acc)


def _terms_of(formula: Node, existing: Tuple[Node, ...], cap: int) -> Tuple[Node, ...]:
    """Return ``existing`` extended with ``formula``'s ground terms, capped at ``cap``."""
    if len(existing) >= cap:
        return existing
    acc: set = set()
    _ground_terms(formula, acc)
    result = list(existing)
    for t in sorted(acc, key=lambda n: n.to_unicode_str()):
        if t not in result:
            result.append(t)
            if len(result) >= cap:
                break
    return tuple(result)


def _is_literal(f: Node) -> bool:
    """True iff ``f`` is an atom, a negated atom, or ⊥ (no rule applies)."""
    if is_falsum(f):
        return True
    if isinstance(f, Atom):
        return True
    if isinstance(f, Not) and isinstance(f.formula, Atom):
        return True
    return False


class _Ctx:
    """Search context: a step budget, a fresh-constant source, and a term-pool cap."""

    def __init__(self, max_steps: int, max_terms: int):
        self.budget = [max_steps]
        self.max_terms = max_terms
        self._fresh = [0]
        self.open_branch: Optional[frozenset] = None

    def fresh_const(self) -> Constant:
        name = f"_t{self._fresh[0]}"
        self._fresh[0] += 1
        return Constant(name)


def _rule(f: Node):
    """Classify ``f`` and return its expansion.

    Returns one of:
      ``("alpha", [comp, …])`` — add all components to the branch;
      ``("beta", [[…], […]])`` — split the branch (each list a new branch's adds);
      ``("delta", var, body, neg)`` — witness with a fresh constant;
      ``("gamma", var, body, neg)`` — universal, instantiate at terms.
    """
    if isinstance(f, And):
        return ("alpha", [f.left, f.right])
    if isinstance(f, Or):
        return ("beta", [[f.left], [f.right]])
    if isinstance(f, Implies):
        return ("beta", [[Not(f.left)], [f.right]])
    if isinstance(f, Iff):
        return ("beta", [[f.left, f.right], [Not(f.left), Not(f.right)]])
    if isinstance(f, Xor):
        return ("beta", [[f.left, Not(f.right)], [Not(f.left), f.right]])
    if _q_kind(f) == "∃":
        return ("delta", f.variable, f.formula, False)
    if _q_kind(f) == "∀":
        return ("gamma", f.variable, f.formula, False)
    if isinstance(f, Not):
        g = f.formula
        if isinstance(g, Not):
            return ("alpha", [g.formula])
        if isinstance(g, And):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Or):
            return ("alpha", [Not(g.left), Not(g.right)])
        if isinstance(g, Implies):
            return ("alpha", [g.left, Not(g.right)])
        if isinstance(g, Iff):
            return ("beta", [[g.left, Not(g.right)], [Not(g.left), g.right]])
        if isinstance(g, Xor):
            return ("beta", [[g.left, g.right], [Not(g.left), Not(g.right)]])
        if _q_kind(g) == "∀":
            return ("delta", g.variable, g.formula, True)
        if _q_kind(g) == "∃":
            return ("gamma", g.variable, g.formula, True)
    raise ValueError(f"tableau: no rule for {type(f).__name__} {f.to_unicode_str()}")


def _instance(var: Variable, body: Node, neg: bool, term: Node) -> Node:
    """Return ``body[var:=term]``, negated when the source was ¬∃ / ∀ on the right."""
    inst = _subst_var(body, var, term)
    return Not(inst) if neg else inst


def _close(work: Tuple[Node, ...], lits: frozenset,
           gammas: Tuple[Tuple, ...], terms: Tuple[Node, ...],
           used: frozenset, ctx: "_Ctx") -> bool:
    """Return True iff this branch (and all its splits) close."""
    if ctx.budget[0] <= 0:
        return False
    ctx.budget[0] -= 1

    if work:
        f, rest = work[0], work[1:]

        if _is_literal(f):
            if is_falsum(f) or _neg(f) in lits:
                return True
            if f in lits:
                return _close(rest, lits, gammas, terms, used, ctx)
            # A new literal may introduce ground terms a universal can instantiate at.
            return _close(rest, lits | {f}, gammas, _terms_of(f, terms, ctx.max_terms), used, ctx)

        kind = _rule(f)[0]
        rule = _rule(f)
        if kind == "alpha":
            return _close(tuple(rule[1]) + rest, lits, gammas, terms, used, ctx)
        if kind == "beta":
            left, right = rule[1]
            return (_close(tuple(left) + rest, lits, gammas, terms, used, ctx)
                    and _close(tuple(right) + rest, lits, gammas, terms, used, ctx))
        if kind == "delta":
            _, var, body, neg = rule
            if len(terms) >= ctx.max_terms:
                # Term-pool cap reached: give up on this branch (sound but incomplete).
                if ctx.open_branch is None:
                    ctx.open_branch = lits
                return False
            c = ctx.fresh_const()
            inst = _instance(var, body, neg, c)
            return _close((inst,) + rest, lits, gammas, terms + (c,), used, ctx)
        if kind == "gamma":
            _, var, body, neg = rule
            key = f
            new_gammas = gammas + ((key, var, body, neg),)
            pool = terms if terms else (ctx.fresh_const(),)
            insts = tuple(_instance(var, body, neg, t) for t in pool)
            new_used = used | {(key, t) for t in pool}
            new_terms = terms if terms else pool
            return _close(insts + rest, lits, new_gammas, new_terms, new_used, ctx)
        raise AssertionError(kind)

    # No compound work left: re-instantiate a universal at a term it has not used.
    for key, var, body, neg in gammas:
        for t in terms:
            if (key, t) not in used:
                inst = _instance(var, body, neg, t)
                return _close((inst,), lits, gammas, terms,
                              used | {(key, t)}, ctx)
    # Saturated and not closed: an OPEN branch — record it as a (counter)model.
    if ctx.open_branch is None:
        ctx.open_branch = lits
    return False


def _initial_terms(formulas, cap: int) -> Tuple[Node, ...]:
    """The ground terms occurring in the initial formula set (the γ-instantiation seed)."""
    terms: Tuple[Node, ...] = ()
    for f in formulas:
        terms = _terms_of(f, terms, cap)
    return terms


def tableau_closed(formulas, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``formulas`` are jointly unsatisfiable (every branch closes).

    Sound; complete and decidable for the propositional fragment. First-order
    ``γ``-instantiation is bounded by ``max_terms`` (the size of the per-branch term
    pool) and ``max_steps``, so a False on a first-order input is "no closed tableau
    within the bounds", never a claim of satisfiability.
    """
    ctx = _Ctx(max_steps, max_terms)
    return _close(tuple(formulas), frozenset(), (),
                  _initial_terms(formulas, max_terms), frozenset(), ctx)


def is_valid_tableau(formula: Node, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``formula`` is valid — its negation's tableau closes."""
    return tableau_closed([Not(formula)], max_steps, max_terms)


def prove_tableau(premises, conclusion: Node, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``premises`` entail ``conclusion`` (premises + ¬conclusion close)."""
    return tableau_closed(list(premises) + [Not(conclusion)], max_steps, max_terms)


def tableau_model(formulas, max_steps: int = 20000, max_terms: int = 8) -> Optional[dict]:
    """Return a satisfying literal assignment if ``formulas`` are satisfiable, else None.

    On an open (saturated) branch the literals are returned as a dict mapping each
    atom's surface form to its truth value; ``None`` means the tableau closed
    (unsatisfiable) within the bound.
    """
    ctx = _Ctx(max_steps, max_terms)
    closed = _close(tuple(formulas), frozenset(), (),
                    _initial_terms(formulas, max_terms), frozenset(), ctx)
    if closed or ctx.open_branch is None:
        return None
    assignment = {}
    for lit in ctx.open_branch:
        if isinstance(lit, Not) and isinstance(lit.formula, Atom):
            assignment[lit.formula.to_unicode_str()] = False
        elif isinstance(lit, Atom):
            assignment[lit.to_unicode_str()] = True
    return assignment
