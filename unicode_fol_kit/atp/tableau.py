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
:func:`tableau_model`, and — for a recorded, independently-checkable proof object —
:func:`prove_tableau_detailed` / :class:`TableauProof` (checked by
:mod:`unicode_fol_kit.atp.tableau_check`).
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant, Number, Function,
    Contrast, Count, Cardinality,
)
from .fitch import FALSUM, is_falsum, _subst_var, _q_kind, _free_vars


def _neg(f: Node) -> Node:
    """Return the complementary formula of ``f`` (``¬φ`` ↔ ``φ``)."""
    return f.formula if isinstance(f, Not) else Not(f)


def _any_modal(formulas) -> bool:
    """True iff any formula carries a modal/temporal/epistemic/deontic operator.

    Such formulas have no classical tableau rule; they are routed to the labelled
    modal tableau (:mod:`unicode_fol_kit.atp.modal_tableau`) instead of raising.
    """
    from .modal_tableau import has_modal
    return any(has_modal(f) for f in formulas)


def _reject_exotic(formulas, entry: str) -> None:
    """Reject non-classical node families with a pointer at the right tool.

    Without this pre-dispatch check these nodes surfaced as a bare
    ``ValueError: tableau: no rule for X`` from deep inside the rule dispatcher —
    the same class of gap the modal routing above already closes. Each family has
    its own decision procedure; none has a sound classical tableau rule.
    """
    from ..fol._linear_nodes import Tensor, With, OPlus, LinearImplies, OfCourse, One
    from ..fol._lambek_nodes import Product, Under, Over
    from ..fol._team_nodes import Dependence, SlashedExists
    from ..fol._so_nodes import SecondOrderQuantifier
    from ..semantics._modal_reject import FUZZY_TYPES
    hints = (
        ((Tensor, With, OPlus, LinearImplies, OfCourse, One),
         "a linear-logic (ILL) connective; decide derivability with "
         "atp.linear.ill_prove / ill_derivable"),
        ((Product, Under, Over),
         "a Lambek-calculus connective; decide derivability with "
         "atp.lambek.lambek_prove / lambek_derivable"),
        ((Dependence, SlashedExists),
         "team-semantic (dependence/IF logic); evaluate with team_satisfies / "
         "team_models"),
        ((SecondOrderQuantifier,),
         "second-order; use the sequent calculus's SO rules, satisfies_so, or "
         "hol.secondorder"),
        (FUZZY_TYPES,
         "a Łukasiewicz connective; evaluate with semantics.fuzzy.evaluate or "
         "decide with atp.z3_fuzzy.fuzzy_is_valid"),
    )
    for f in formulas:
        for sub in f.walk():
            for types, hint in hints:
                if isinstance(sub, types):
                    raise NotImplementedError(
                        f"{entry}: {type(sub).__name__} is {hint}. No sound "
                        "classical proof rule exists for it here.")


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
    if isinstance(f, Contrast):
        # Concession is truth-functionally conjunction (Contrast's own contract).
        return ("alpha", [f.left, f.right])
    if isinstance(f, Or):
        return ("beta", [[f.left], [f.right]])
    if isinstance(f, Implies):
        return ("beta", [[Not(f.left)], [f.right]])
    if isinstance(f, Iff):
        return ("beta", [[f.left, f.right], [Not(f.left), Not(f.right)]])
    if isinstance(f, Xor):
        return ("beta", [[f.left, Not(f.right)], [Not(f.left), f.right]])
    if isinstance(f, Count):
        # The distinct-witnesses expansion is plain FOL, which this tableau's
        # quantifier rules handle — the same lowering to_z3/to_prover9 use.
        return ("alpha", [f._expand()])
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
        if isinstance(g, Contrast):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Or):
            return ("alpha", [Not(g.left), Not(g.right)])
        if isinstance(g, Implies):
            return ("alpha", [g.left, Not(g.right)])
        if isinstance(g, Iff):
            return ("beta", [[g.left, Not(g.right)], [Not(g.left), g.right]])
        if isinstance(g, Xor):
            return ("beta", [[g.left, g.right], [Not(g.left), Not(g.right)]])
        if isinstance(g, Count):
            return ("alpha", [Not(g._expand())])
        if _q_kind(g) == "∀":
            return ("delta", g.variable, g.formula, True)
        if _q_kind(g) == "∃":
            return ("gamma", g.variable, g.formula, True)
    if isinstance(f, (Cardinality,)) or (
            isinstance(f, Not) and isinstance(f.formula, Cardinality)):
        raise NotImplementedError(
            "tableau: a bare Cardinality term is not a formula, and cardinality "
            "comparisons are not first-order — evaluate them with "
            "semantics.tarski.satisfies / the finite model finder, or export to "
            "HOL via hol.secondorder.")
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
    """The γ-instantiation seed: initial ground terms plus the input's free variables.

    A FREE variable of the input is treated as a constant — the standard reading
    under which validity of a formula with free variables is validity of its
    universal closure (``valid ∀a.φ  ⟺  unsat ¬φ[a := fresh constant]``), which is
    also how the Z3 and resolution back-ends read free variables. Without this a
    γ-formula was never instantiated at a free variable and e.g.
    ``¬∃x P(x) → ¬P(a)`` (free ``a``) was silently left unproved.
    Bound occurrences never reach this seed: it runs on the top-level input only,
    and the free-variable set excludes them by definition.
    """
    terms: Tuple[Node, ...] = ()
    for f in formulas:
        terms = _terms_of(f, terms, cap)
    free: set = set()
    for f in formulas:
        free |= _free_vars(f)                    # a set of Variable NODES
    for v in sorted(free, key=lambda n: n.name):
        if len(terms) >= cap:
            break
        if v not in terms:
            terms = terms + (v,)
    return terms


def tableau_closed(formulas, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``formulas`` are jointly unsatisfiable (every branch closes).

    Sound; complete and decidable for the propositional fragment. First-order
    ``γ``-instantiation is bounded by ``max_terms`` (the size of the per-branch term
    pool) and ``max_steps``, so a False on a first-order input is "no closed tableau
    within the bounds", never a claim of satisfiability.

    Modal/temporal/epistemic/deontic formulas have no classical rule; they are routed
    to the labelled modal tableau (over the system **K** by default — for other frames
    call :mod:`unicode_fol_kit.atp.modal_tableau` directly).
    """
    formulas = list(formulas)
    _reject_exotic(formulas, "tableau_closed")
    if _any_modal(formulas):
        from .modal_tableau import modal_tableau_closed
        return modal_tableau_closed(formulas)
    ctx = _Ctx(max_steps, max_terms)
    return _close(tuple(formulas), frozenset(), (),
                  _initial_terms(formulas, max_terms), frozenset(), ctx)


def is_valid_tableau(formula: Node, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``formula`` is valid — its negation's tableau closes.

    A modal formula is decided over the system **K** by the labelled modal tableau;
    use :func:`unicode_fol_kit.atp.modal_tableau.is_modal_valid` for other frames.
    """
    _reject_exotic([formula], "is_valid_tableau")
    if _any_modal([formula]):
        from .modal_tableau import is_modal_valid
        return is_modal_valid(formula)
    return tableau_closed([Not(formula)], max_steps, max_terms)


def prove_tableau(premises, conclusion: Node, max_steps: int = 20000, max_terms: int = 8) -> bool:
    """Return True iff ``premises`` entail ``conclusion`` (premises + ¬conclusion close).

    For modal inputs this is **local** consequence over the system **K** (see
    :func:`unicode_fol_kit.atp.modal_tableau.modal_prove` for other frames).
    """
    return tableau_closed(list(premises) + [Not(conclusion)], max_steps, max_terms)


def tableau_model(formulas, max_steps: int = 20000, max_terms: int = 8) -> Optional[dict]:
    """Return a satisfying literal assignment if ``formulas`` are satisfiable, else None.

    On an open (saturated) branch the literals are returned as a dict mapping each
    atom's surface form to its truth value; ``None`` means the tableau closed
    (unsatisfiable) within the bound.

    A modal model is a Kripke structure, not a flat literal assignment, so a modal
    input is rejected here with a pointer to
    :func:`unicode_fol_kit.atp.modal_tableau.modal_countermodel`, which returns a
    verified :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`.
    """
    formulas = list(formulas)
    _reject_exotic(formulas, "tableau_model")
    if _any_modal(formulas):
        raise NotImplementedError(
            "tableau_model: a modal formula's model is a Kripke structure, not a flat "
            "assignment — use unicode_fol_kit.atp.modal_tableau.modal_countermodel "
            "(or modal_decide) instead.")
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


# ---------------------------------------------------------------------------
# Tier 3: a tableau PROOF OBJECT, recorded alongside the search above with
# zero effect on it (see _close_recording's docstring — it is a separate,
# additive function; every entry point above still calls the untouched
# original _close, so their behaviour is unchanged by everything below).
# Independently checked by :mod:`unicode_fol_kit.atp.tableau_check`, which
# never imports this module's rule-application machinery (``_rule``,
# ``_close``, ``_close_recording``, ``_instance``) — only the plain data
# classes below.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TableauStep:
    """One rule application in a recorded tableau proof — one node of its tree.

    Every step has exactly one ``parent_id`` (``0`` denotes the tableau's root —
    :attr:`TableauProof.root_formulas`, i.e. premises + ¬conclusion) and adds the
    formula(s) in ``produced`` to the branch it extends:

    - ``"alpha"`` (non-branching): ``produced`` is all of the principal formula's
      own components (e.g. both conjuncts of an ``And``) — one child step.
    - ``"beta"`` (branching): recorded as TWO SIBLING steps sharing the same
      ``parent_id`` *and* the same ``principal_formula`` — one per branch, each
      with ``branch_split=True`` and its own alternative in ``produced``.
    - ``"gamma"`` (∀-instantiation): ``produced`` and ``terms`` are parallel
      tuples of the same length — ``produced[i]`` is the principal formula's
      matrix with its bound variable substituted by ``terms[i]``. A single step
      may instantiate at several terms at once (the initial encounter of a
      universal instantiates at every ground term already on the branch); a
      later re-instantiation on saturation is always a single-term step.
    - ``"delta"`` (∃-witness): ``produced`` is a single formula — the principal
      formula's matrix substituted by the fresh witnessing constant recorded in
      ``fresh_constant``.

    ``step_id`` is 1-based and equal to the step's position in
    :attr:`TableauProof.steps` (mirrors :class:`atp.resolution_check
    .ResolutionStep`'s ``index`` convention).
    """

    step_id: int
    parent_id: int
    rule: str
    principal_formula: Node
    produced: Tuple[Node, ...]
    branch_split: bool = False
    terms: Tuple[Node, ...] = ()
    fresh_constant: Optional[Node] = None

    def __post_init__(self):
        """Coerce ``produced``/``terms`` to tuples for hashability."""
        object.__setattr__(self, "produced", tuple(self.produced))
        object.__setattr__(self, "terms", tuple(self.terms))

    def to_dict(self) -> dict:
        return {
            "step_id": self.step_id,
            "parent_id": self.parent_id,
            "rule": self.rule,
            "principal_formula": self.principal_formula.to_dict(),
            "produced": [f.to_dict() for f in self.produced],
            "branch_split": self.branch_split,
            "terms": [t.to_dict() for t in self.terms],
            "fresh_constant": self.fresh_constant.to_dict() if self.fresh_constant is not None else None,
        }


@dataclass(frozen=True)
class TableauClosure:
    """One closed branch's closure pair, with the node IDs where both lie.

    ``leaf_id`` is the tree node (``0``, or a :class:`TableauStep`'s ``step_id``)
    at which the branch closes — it must be a genuine leaf (no step cites it as a
    parent). ``literal`` is the formula whose processing triggered the closure;
    ``literal_step_id`` names the branch node where it actually occurs (``0`` for
    a root formula, else a step whose ``produced`` contains it). When ``literal``
    is ⊥ itself the branch is self-closing and ``complement``/``complement_step_id``
    are both ``None``; otherwise ``complement`` is ``literal``'s complementary
    formula and ``complement_step_id`` names where IT occurs on the same branch.
    """

    leaf_id: int
    literal: Node
    literal_step_id: int
    complement: Optional[Node] = None
    complement_step_id: Optional[int] = None

    def to_dict(self) -> dict:
        return {
            "leaf_id": self.leaf_id,
            "literal": self.literal.to_dict(),
            "literal_step_id": self.literal_step_id,
            "complement": self.complement.to_dict() if self.complement is not None else None,
            "complement_step_id": self.complement_step_id,
        }


@dataclass(frozen=True)
class TableauProof:
    """A full recorded tableau proof: the root formulas, the rule-application
    tree, and every closed branch's closure pair.

    This records what the search DID — it is not itself a certificate that the
    search was sound. Call :func:`unicode_fol_kit.atp.tableau_check
    .check_tableau_proof` to verify one independently before trusting it.
    """

    root_formulas: Tuple[Node, ...]
    steps: Tuple[TableauStep, ...] = ()
    closures: Tuple[TableauClosure, ...] = ()

    def __post_init__(self):
        """Coerce ``root_formulas``/``steps``/``closures`` to tuples for hashability."""
        object.__setattr__(self, "root_formulas", tuple(self.root_formulas))
        object.__setattr__(self, "steps", tuple(self.steps))
        object.__setattr__(self, "closures", tuple(self.closures))

    def to_dict(self) -> dict:
        return {
            "root_formulas": [f.to_dict() for f in self.root_formulas],
            "steps": [s.to_dict() for s in self.steps],
            "closures": [c.to_dict() for c in self.closures],
        }


class _Recorder:
    """Builds a :class:`TableauProof` tree alongside :func:`_close_recording`.

    Pure bookkeeping: every method here only records what the search already
    decided (see :func:`_close_recording`'s docstring) — nothing here feeds back
    into a decision, so recording cannot change the search's order or result.
    """

    def __init__(self):
        self._next_id = 1
        self.steps: List[TableauStep] = []
        self.steps_by_id: Dict[int, TableauStep] = {}
        self.closures: List[TableauClosure] = []

    def add(self, parent_id: int, rule: str, principal: Node, produced,
            branch_split: bool = False, terms=(), fresh_constant: Optional[Node] = None) -> int:
        """Append a new :class:`TableauStep`, returning its fresh ``step_id``."""
        step_id = self._next_id
        self._next_id += 1
        step = TableauStep(step_id, parent_id, rule, principal, tuple(produced),
                           branch_split, tuple(terms), fresh_constant)
        self.steps.append(step)
        self.steps_by_id[step_id] = step
        return step_id

    def _origin(self, formula: Node, node_id: int, root_formulas) -> int:
        """The nearest branch node (searching leaf-to-root) whose ``produced``
        (or, at ``0``, ``root_formulas``) contains ``formula``."""
        cur = node_id
        while cur != 0:
            step = self.steps_by_id[cur]
            if any(formula == p for p in step.produced):
                return cur
            cur = step.parent_id
        return 0

    def close(self, node_id: int, root_formulas, literal: Node,
              complement: Optional[Node] = None) -> None:
        """Record a branch closure at ``node_id`` (see :class:`TableauClosure`)."""
        literal_id = self._origin(literal, node_id, root_formulas)
        complement_id = self._origin(complement, node_id, root_formulas) if complement is not None else None
        self.closures.append(TableauClosure(node_id, literal, literal_id, complement, complement_id))


def _close_recording(work: Tuple[Node, ...], lits: frozenset,
                     gammas: Tuple[Tuple, ...], terms: Tuple[Node, ...],
                     used: frozenset, ctx: "_Ctx", rec: "_Recorder",
                     node_id: int, root_formulas: Tuple[Node, ...]) -> bool:
    """A recording twin of :func:`_close` — the engine behind :func:`prove_tableau_detailed`.

    Line-for-line the same search as :func:`_close` — same term pools, the same
    ``ctx.fresh_const()`` call sequence, the same budget accounting, the same
    (deterministic, backtracking-free) control flow — with a :class:`_Recorder`
    call added at every point :func:`_close` makes a decision, so the two never
    diverge in VERDICT for the same inputs. Kept as a wholly separate function
    (rather than adding recorder hooks to ``_close`` itself) specifically so
    :func:`prove_tableau` and every other existing entry point above keep
    calling the untouched original: this function has zero effect on their
    behaviour, by construction, not merely by argument.

    Because the search is deterministic and never backtracks (every choice —
    which fresh constant, which pool terms, which unused ``(key, t)`` pair to
    reinstantiate — is made once, immediately, never retried), a top-level
    ``True`` return means every :class:`TableauStep`/:class:`TableauClosure`
    recorded during the whole call genuinely lies on the closed proof: nothing
    here is spliced out afterwards, and nothing is recorded that a failed
    sub-call later discards (a ``False`` anywhere propagates straight up
    through this call's own ``and``/return, which is why :func:`prove_tableau_detailed`
    simply discards the whole recorder when the top call returns ``False``).
    """
    if ctx.budget[0] <= 0:
        return False
    ctx.budget[0] -= 1

    if work:
        f, rest = work[0], work[1:]

        if _is_literal(f):
            if is_falsum(f):
                rec.close(node_id, root_formulas, f)
                return True
            if _neg(f) in lits:
                rec.close(node_id, root_formulas, f, _neg(f))
                return True
            if f in lits:
                return _close_recording(rest, lits, gammas, terms, used, ctx, rec, node_id, root_formulas)
            return _close_recording(rest, lits | {f}, gammas, _terms_of(f, terms, ctx.max_terms),
                                    used, ctx, rec, node_id, root_formulas)

        kind = _rule(f)[0]
        rule = _rule(f)
        if kind == "alpha":
            child = rec.add(node_id, "alpha", f, rule[1])
            return _close_recording(tuple(rule[1]) + rest, lits, gammas, terms, used,
                                    ctx, rec, child, root_formulas)
        if kind == "beta":
            left, right = rule[1]
            left_id = rec.add(node_id, "beta", f, left, branch_split=True)
            right_id = rec.add(node_id, "beta", f, right, branch_split=True)
            return (_close_recording(tuple(left) + rest, lits, gammas, terms, used,
                                     ctx, rec, left_id, root_formulas)
                    and _close_recording(tuple(right) + rest, lits, gammas, terms, used,
                                         ctx, rec, right_id, root_formulas))
        if kind == "delta":
            _, var, body, neg = rule
            if len(terms) >= ctx.max_terms:
                # Term-pool cap reached: give up on this branch (sound but incomplete) —
                # mirrors _close exactly; this path is never on a path that ends up True.
                if ctx.open_branch is None:
                    ctx.open_branch = lits
                return False
            c = ctx.fresh_const()
            inst = _instance(var, body, neg, c)
            child = rec.add(node_id, "delta", f, (inst,), fresh_constant=c)
            return _close_recording((inst,) + rest, lits, gammas, terms + (c,), used,
                                    ctx, rec, child, root_formulas)
        if kind == "gamma":
            _, var, body, neg = rule
            key = f
            new_gammas = gammas + ((key, var, body, neg),)
            pool = terms if terms else (ctx.fresh_const(),)
            insts = tuple(_instance(var, body, neg, t) for t in pool)
            new_used = used | {(key, t) for t in pool}
            new_terms = terms if terms else pool
            child = rec.add(node_id, "gamma", f, insts, terms=pool)
            return _close_recording(insts + rest, lits, new_gammas, new_terms, new_used,
                                    ctx, rec, child, root_formulas)
        raise AssertionError(kind)

    # No compound work left: re-instantiate a universal at a term it has not used.
    for key, var, body, neg in gammas:
        for t in terms:
            if (key, t) not in used:
                inst = _instance(var, body, neg, t)
                child = rec.add(node_id, "gamma", key, (inst,), terms=(t,))
                return _close_recording((inst,), lits, gammas, terms, used | {(key, t)},
                                        ctx, rec, child, root_formulas)
    # Saturated and not closed: an OPEN branch — never reached on a path that ends up True.
    if ctx.open_branch is None:
        ctx.open_branch = lits
    return False


def prove_tableau_detailed(premises, conclusion: Node, max_steps: int = 20000,
                           max_terms: int = 8) -> Optional["TableauProof"]:
    """Return a :class:`TableauProof` if a closed tableau is found within budget, else ``None``.

    Builds the SAME tableau :func:`prove_tableau` would — :func:`_close_recording`
    mirrors :func:`_close` exactly (see its docstring) — plus a proof object
    recording every rule application and every branch's closure pair.

    ``None`` is NEVER a verdict of invalidity, exactly as for :func:`prove_tableau`:
    it only means no closed tableau was found within ``max_steps``/``max_terms``
    (first-order γ-instantiation is merely semi-decidable). Call
    :func:`unicode_fol_kit.atp.tableau_check.check_tableau_proof` to independently
    verify a returned proof before trusting it — this function's own bookkeeping is
    not a soundness guarantee.

    Raises the same ``NotImplementedError`` as :func:`prove_tableau` for a
    non-classical node family. A modal input is also rejected here (with a
    pointer to :mod:`unicode_fol_kit.atp.modal_tableau`) since the labelled modal
    tableau does not build a detailed proof object of this shape.
    """
    formulas = list(premises) + [Not(conclusion)]
    _reject_exotic(formulas, "prove_tableau_detailed")
    if _any_modal(formulas):
        raise NotImplementedError(
            "prove_tableau_detailed: modal tableaux do not build a detailed proof "
            "object here — use modal_tableau.modal_prove for the plain verdict.")
    root_formulas = tuple(formulas)
    ctx = _Ctx(max_steps, max_terms)
    rec = _Recorder()
    closed = _close_recording(root_formulas, frozenset(), (), _initial_terms(formulas, max_terms),
                              frozenset(), ctx, rec, 0, root_formulas)
    if not closed:
        return None
    return TableauProof(root_formulas, tuple(rec.steps), tuple(rec.closures))
