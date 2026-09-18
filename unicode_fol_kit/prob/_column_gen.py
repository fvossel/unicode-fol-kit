"""Exact column generation for ``nilsson.entailment_bounds(strategy="column_generation")``.

:func:`~unicode_fol_kit.prob.nilsson.entailment_bounds`'s default (``"direct"``)
strategy materialises one Z3 ``Real`` per possible world — ``2^n`` of them for
``n`` distinct atoms — which is exact but explicitly bounded by ``max_atoms``
(12 by default) precisely because that blow-up is real. This module answers
the SAME linear program without ever building that array: it grows a small
``columns`` list of worlds ON DEMAND, deciding which world to add next by
SOLVING a small optimization problem (the "pricing subproblem") rather than
by enumerating all ``2^n`` candidates and checking each — so its cost per
iteration is polynomial in ``n`` (a Z3 Boolean-SAT search over the ``n``
atoms) regardless of how large ``2^n`` is, and it never runs into
``max_atoms`` at all. It is bounded instead by ``max_columns`` (500 by
default): if optimality is not certified within that many columns,
:func:`solve` raises ``ValueError`` rather than ever returning an unproven
bound, exactly the kit's "refuse loudly" contract for every other bounded
search.

**The LP, in row form.** Every :class:`~unicode_fol_kit.prob.nilsson.ProbConstraint`
becomes two ``≥`` rows over the SAME variables ``nilsson.entailment_bounds``'s
direct path uses (one nonnegative ``p_w`` per world ``w``, ``Σ p_w = 1``):
an unconditional ``lower ≤ P(φ) ≤ upper`` becomes
``Σ_w 1{w⊨φ}·p_w ≥ lower`` and ``Σ_w (−1{w⊨φ})·p_w ≥ −upper``; a conditional
``lower ≤ P(φ|ψ) ≤ upper`` (Nilsson's linear form, see ``nilsson``'s module
docstring) becomes ``Σ_w (1{w⊨φ∧ψ} − lower·1{w⊨ψ})·p_w ≥ 0`` and
``Σ_w (upper·1{w⊨ψ} − 1{w⊨φ∧ψ})·p_w ≥ 0``. Every row is thus a *linear
functional of the world* ``w`` — represented here as an :class:`_Row`, which
carries that functional TWICE: once as a Python closure over an exact
:class:`~fractions.Fraction` valuation (``coeff_of``, used to add a *known*
world as a new LP column) and once as a Z3 expression over per-atom
:func:`z3.Bool` variables (``z3_coeff``, used by the pricing subproblem to
search for an *unknown* world maximizing a linear combination of these
functionals — see :func:`_price`).

**Two-phase column generation, and its termination/optimality proof.**
:func:`solve` runs PHASE 1 once (find any world-set whose convex hull meets
every row, or PROVE none exists — the ``ValueError`` today's direct method
also raises) and then PHASE 2 twice (minimize, then maximize, ``P(conclusion)``
over that now-feasible restricted master, each free to add further columns).
Both phases share one mechanism:

1. *Restricted primal*: the SAME LP :func:`~unicode_fol_kit.prob.nilsson.entailment_bounds`
   solves, but only over the CURRENT ``columns`` (a genuine feasible point of
   the FULL LP too — the other worlds implicitly have ``p_w = 0``). Solved
   exactly with :class:`z3.Optimize`, exactly like ``nilsson._solve``.
2. *Explicit dual*: Z3's ``Optimize`` exposes no shadow-price/dual accessor
   (verified: ``dir(z3.Optimize())`` has none), so the dual LP of that SAME
   restricted primal is derived BY HAND (standard LP duality: one dual
   variable ``y_i ≥ 0`` per ``≥`` row, one free dual ``λ`` for the ``Σp=1``
   row) and solved as its OWN small :class:`z3.Optimize` call — see
   :func:`_solve_dual`. Strong duality (both LPs are finite, feasible, and
   bounded by construction) gives an ``(y, λ)`` that is EXACTLY optimal for
   the restricted primal, not merely a heuristic estimate.
3. *Pricing subproblem*: does some world ``w*`` — not necessarily already in
   ``columns`` — violate ``(y, λ)``'s dual feasibility, i.e. is
   ``Σ_i y_i·coeff_i(w*) + λ − cost(w*) > 0``? This is searched EXACTLY over
   all ``2^n`` worlds at once via one small :class:`z3.Optimize` call with a
   :func:`z3.Bool` decision variable per atom (see :func:`_price`) — a SAT
   search, never an enumeration. If such a ``w*`` exists, its column strictly
   improves the restricted primal (the classical "negative reduced cost"
   test) and is added; ``columns`` has grown by exactly one WORLD NOT
   ALREADY PRESENT (an already-included column's reduced cost at the
   restricted master's own optimal dual can never be positive — if it were,
   that restricted LP, which already has that column as a decision variable,
   would not have been at its own optimum, a contradiction — so pricing
   never rediscovers an existing column; a defensive check against exactly
   that is kept anyway, see :func:`_phase2`).
4. *Termination*: because ``columns`` only grows and there are only finitely
   many worlds (``2^n``), the loop cannot run forever — it must reach either
   ``max_columns`` (raise, per the brake above) or a state where NO world
   improves ``(y, λ)``.
5. *Optimality, when pricing finds nothing*: ``(y, λ)`` is then dual-feasible
   for the FULL problem too (every world, not just ``columns``, satisfies its
   constraint) — so by WEAK duality, its dual objective ``Σ_i b_i·y_i + λ`` is
   a valid bound on the TRUE (all-``2^n``-columns) primal optimum. The
   restricted primal's own optimal value is, by STRONG duality (point 2),
   exactly that same dual objective — and is ALSO a valid feasible value of
   the true primal (point 1: restricted-feasible implies full-feasible). A
   value that is simultaneously a bound in one direction and an achieved
   value in the other can only be the true optimum itself: restricted primal
   optimum = true (``2^n``-column) primal optimum, EXACTLY, with no gap.
   This is the proof obligation :func:`solve`'s own docstring, and
   ``tests/test_nilsson_colgen.py``, hold this module to.

**Feasibility (phase 1) via artificial variables.** The restricted primal can
itself be infeasible for a small seed ``columns`` (a single arbitrary world
essentially never satisfies every constraint's exact bounds on its own). One
nonnegative artificial/slack ``s_i`` is added to each row (``Σ_w coeff_i(w)·p_w
+ s_i ≥ b_i``, so ANY nonempty ``columns`` makes phase 1 trivially feasible —
even a single world, by taking ``s_i`` large enough), and phase 1 minimizes
``Σ_i s_i`` via the SAME primal/dual/pricing/termination machinery above (cost
0 for every ``p_w``; an extra dual bound ``y_i ≤ 1`` from each ``s_i``'s own
unit cost — see :func:`_phase1`). Reaching ``Σ s_i = 0`` means every ``s_i``
is individually 0 (a sum of nonnegatives), so that same optimal point is
ALSO feasible for the real (artificial-free) rows — phase 2 continues from
those exact columns. Pricing certifying optimality while ``Σ s_i > 0`` still
holds is the SAME optimality proof above applied to phase 1's own objective:
the true (``2^n``-column) minimum total-artificial-mass is ALSO that positive
value, i.e. genuinely no distribution over ANY set of worlds satisfies every
row — the constraint set is probabilistically inconsistent, and
:func:`solve` raises the identical ``ValueError``
:func:`~unicode_fol_kit.prob.nilsson._infeasible_error` builds for the direct
strategy.

Internal module (leading underscore): nothing here is re-exported from
:mod:`unicode_fol_kit.prob`. Reached only through
``entailment_bounds(..., strategy="column_generation")`` — see that
function's docstring for the public contract — or directly, by
``tests/test_nilsson_colgen.py``, for white-box checks (the explicit witness
distribution, the dual construction) the public API does not expose.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, List, Optional, Sequence, Tuple

import z3

from ..fol.nodes import And, Node
from .nilsson import (
    ProbConstraint,
    _eval,
    _infeasible_error,
    _to_z3_bool,
    _z3_to_fraction,
)

__all__: List[str] = []  # internal module; see this file's own module docstring


# ---------------------------------------------------------------------------
# Rows: one linear functional of a world, represented two ways at once.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _Row:
    """One ``≥`` row of the LP: ``Σ_w coeff_of(w)·p_w ≥ rhs``.

    ``coeff_of`` evaluates the row's coefficient at a CONCRETE world (a
    ``Dict[str, bool]`` valuation) — used when a world already chosen (by
    :func:`_price`, or the phase-1 seed) is added to the restricted master or
    its dual. ``z3_coeff`` builds the SAME coefficient as a Z3 rational
    expression over per-atom :func:`z3.Bool` variables — used only inside
    :func:`_price`, which searches for an UNKNOWN world maximizing a linear
    combination of these, without enumerating any.
    """

    coeff_of: Callable[[Dict[str, bool]], Fraction]
    z3_coeff: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
    rhs: Fraction
    label: str


def _indicator(formula: Node, valuation: Dict[str, bool]) -> Fraction:
    """``1`` if ``valuation ⊨ formula`` else ``0``, as an exact Fraction."""
    return Fraction(1) if _eval(formula, valuation) else Fraction(0)


def _z3_indicator(formula: Node, atom_vars: Dict[str, "z3.BoolRef"]) -> "z3.ArithRef":
    """The Z3-expression counterpart of :func:`_indicator`: ``If(formula, 1, 0)``."""
    return z3.If(_to_z3_bool(formula, atom_vars), z3.RealVal(1), z3.RealVal(0))


def _build_rows(constraints: Sequence[ProbConstraint]) -> List[_Row]:
    """Turn every :class:`ProbConstraint` into its two ``≥`` rows (see the module docstring)."""
    rows: List[_Row] = []
    for c in constraints:
        if c.given is None:
            formula, lower, upper = c.formula, c.lower, c.upper
            rows.append(_Row(
                coeff_of=lambda val, f=formula: _indicator(f, val),
                z3_coeff=lambda av, f=formula: _z3_indicator(f, av),
                rhs=lower,
                label=f"P({formula.to_unicode_str()}) >= {lower}",
            ))
            rows.append(_Row(
                coeff_of=lambda val, f=formula: -_indicator(f, val),
                z3_coeff=lambda av, f=formula: -_z3_indicator(f, av),
                rhs=-upper,
                label=f"P({formula.to_unicode_str()}) <= {upper}",
            ))
        else:
            conj = And(c.formula, c.given)
            given, lower, upper = c.given, c.lower, c.upper
            rows.append(_Row(
                coeff_of=lambda val, conj=conj, given=given, lower=lower: (
                    _indicator(conj, val) - lower * _indicator(given, val)),
                z3_coeff=lambda av, conj=conj, given=given, lower=lower: (
                    _z3_indicator(conj, av) - z3.RealVal(lower) * _z3_indicator(given, av)),
                rhs=Fraction(0),
                label=f"P({c.formula.to_unicode_str()}|{given.to_unicode_str()}) >= {lower} (conditional)",
            ))
            rows.append(_Row(
                coeff_of=lambda val, conj=conj, given=given, upper=upper: (
                    upper * _indicator(given, val) - _indicator(conj, val)),
                z3_coeff=lambda av, conj=conj, given=given, upper=upper: (
                    z3.RealVal(upper) * _z3_indicator(given, av) - _z3_indicator(conj, av)),
                rhs=Fraction(0),
                label=f"P({c.formula.to_unicode_str()}|{given.to_unicode_str()}) <= {upper} (conditional)",
            ))
    return rows


# ---------------------------------------------------------------------------
# The restricted master's dual, and the pricing subproblem.
# ---------------------------------------------------------------------------

def _solve_dual(rows: Sequence[_Row], columns: Sequence[Dict[str, bool]],
                cost_of: Callable[[Dict[str, bool]], Fraction],
                y_upper_bound: Optional[Fraction] = None) -> Tuple[List[Fraction], Fraction]:
    """Solve the EXPLICIT dual of the restricted primal over ``columns``.

    Restricted primal: ``min Σ_w cost_of(w)·p_w`` s.t. ``Σ_w coeff_i(w)·p_w
    ≥ rhs_i`` for each row (dual ``y_i ≥ 0``), ``Σ_w p_w = 1`` (dual ``λ``
    free), ``p_w ≥ 0``, over ``w`` in ``columns`` only. Its dual: ``max
    Σ_i rhs_i·y_i + λ`` s.t. ``Σ_i coeff_i(w)·y_i + λ ≤ cost_of(w)`` for
    every ``w`` in ``columns`` (never the full ``2^n`` — that is exactly what
    makes this the RESTRICTED dual), ``y_i ≥ 0`` [``≤ y_upper_bound`` when
    given — phase 1's artificial variables each contribute exactly this
    extra per-row dual bound, see :func:`_phase1`], ``λ`` free.

    A fresh :class:`z3.Optimize` every call, per this module's own docstring
    (point 2): the restricted primal is always feasible (``columns`` is
    always nonempty, and phase 1's slack rows make it feasible even for a
    single, arbitrary column) and bounded (every cost/coefficient here is a
    bounded rational combination of ``{0, 1}``-valued indicators over a
    ``Σp=1`` polytope), so by strong duality the dual is always feasible and
    bounded too — ``y=0, λ=0`` is always a trivial dual-feasible point
    (``0 ≤ cost_of(w)`` — true since every objective in this module is a
    nonnegative combination of indicators) confirming that directly. A
    ``check() != sat`` here is therefore an internal invariant violation, not
    a possible user-facing outcome.
    """
    m = len(rows)
    y = [z3.Real(f"nilsson_cg!y_{i}") for i in range(m)]
    lam = z3.Real("nilsson_cg!lambda")
    opt = z3.Optimize()
    for yi in y:
        opt.add(yi >= 0)
        if y_upper_bound is not None:
            opt.add(yi <= z3.RealVal(y_upper_bound))
    for w in columns:
        lhs = lam
        for yi, row in zip(y, rows):
            coeff = row.coeff_of(w)
            if coeff != 0:
                lhs = lhs + yi * z3.RealVal(coeff)
        opt.add(lhs <= z3.RealVal(cost_of(w)))
    objective = lam
    for yi, row in zip(y, rows):
        if row.rhs != 0:
            objective = objective + z3.RealVal(row.rhs) * yi
    opt.maximize(objective)
    if opt.check() != z3.sat:
        raise AssertionError(
            "nilsson column generation: the restricted dual LP was unexpectedly "
            "infeasible — this is an internal invariant violation (see _solve_dual's "
            "own docstring for why it should never happen), not a malformed input."
        )
    model = opt.model()
    y_vals = [_z3_to_fraction(model.eval(yi, model_completion=True)) for yi in y]
    lam_val = _z3_to_fraction(model.eval(lam, model_completion=True))
    return y_vals, lam_val


def _price(atom_list: Sequence[str], rows: Sequence[_Row], y: Sequence[Fraction], lam: Fraction,
          cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
          ) -> Tuple[bool, Optional[Dict[str, bool]], Fraction]:
    """The pricing subproblem: search ALL ``2^n`` worlds at once for the one maximizing
    ``Σ_i y_i·coeff_i(w) + λ − cost(w)`` (a world's "reduced cost", negated).

    One fresh :func:`z3.Bool` decision variable per atom, an exact rational
    objective built from the SAME ``_Row.z3_coeff`` expressions the
    restricted master's rows use (so pricing and the master agree on the LP
    by construction, never merely by separate testing), one
    :class:`z3.Optimize` call — a genuine SAT/OMT search over the ``2^n``
    worlds, never an enumeration of them. Always satisfiable (any Boolean
    assignment is a candidate; the objective is a bounded rational
    combination of ``{0,1}``-indicators, hence bounded too), so ``found`` is
    always ``True`` in practice; the check is kept defensively rather than
    assumed.

    Returns ``(found, valuation, value)``: ``valuation`` is total over
    ``atom_list`` (``model_completion=True``, since an atom absent from every
    row the current ``y`` weights nonzero would otherwise be left as a Z3
    don't-care).
    """
    atom_vars = {a: z3.Bool(f"nilsson_cg!atom_{i}") for i, a in enumerate(atom_list)}
    opt = z3.Optimize()
    objective = z3.RealVal(lam)
    for yi, row in zip(y, rows):
        if yi == 0:
            continue
        objective = objective + z3.RealVal(yi) * row.z3_coeff(atom_vars)
    objective = objective - cost_z3_of(atom_vars)
    handle = opt.maximize(objective)
    if opt.check() != z3.sat:
        return False, None, Fraction(0)
    value = _z3_to_fraction(opt.upper(handle))
    model = opt.model()
    valuation = {a: bool(z3.is_true(model.eval(atom_vars[a], model_completion=True))) for a in atom_list}
    return True, valuation, value


# ---------------------------------------------------------------------------
# The restricted PRIMAL, solved directly (for the final value + witness).
# ---------------------------------------------------------------------------

def _solve_restricted_primal(rows: Sequence[_Row], columns: Sequence[Dict[str, bool]],
                             cost_of: Callable[[Dict[str, bool]], Fraction]
                             ) -> Tuple[Fraction, List[Tuple[Dict[str, bool], Fraction]]]:
    """Solve ``min Σ_w cost_of(w)·p_w`` over the current ``columns`` exactly.

    Returns ``(optimal value, witness)`` where ``witness`` is the explicit
    distribution the optimum is attained by: every ``(world, p_w)`` pair from
    the optimal model with ``p_w`` strictly positive. This is a genuine
    feasible point of the FULL (all-``2^n``-columns) problem too (the other
    worlds are implicitly at ``p_w = 0``), which is exactly what licenses
    calling this value "attained" rather than merely "achievable in the
    limit" — the property ``tests/test_nilsson_colgen.py`` re-checks
    independently by recomputing every constraint's probability and the
    objective directly from ``witness`` via :func:`~unicode_fol_kit.prob.nilsson._eval`.
    """
    opt = z3.Optimize()
    p = [z3.Real(f"nilsson_cg!p_{i}") for i in range(len(columns))]
    for pi in p:
        opt.add(pi >= 0)
    opt.add(z3.Sum(p) == z3.RealVal(1))
    for row in rows:
        terms = [z3.RealVal(row.coeff_of(w)) * pi for w, pi in zip(columns, p) if row.coeff_of(w) != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        opt.add(lhs >= z3.RealVal(row.rhs))
    obj_terms = [z3.RealVal(cost_of(w)) * pi for w, pi in zip(columns, p) if cost_of(w) != 0]
    objective = z3.Sum(obj_terms) if obj_terms else z3.RealVal(0)
    handle = opt.minimize(objective)
    if opt.check() != z3.sat:
        raise AssertionError(
            "nilsson column generation: the final restricted primal was unexpectedly "
            "infeasible — phase 1 already certified this exact column set feasible; "
            "this is an internal invariant violation, not a malformed input."
        )
    value = _z3_to_fraction(opt.lower(handle))
    model = opt.model()
    witness: List[Tuple[Dict[str, bool], Fraction]] = []
    for w, pi in zip(columns, p):
        pv = _z3_to_fraction(model.eval(pi, model_completion=True))
        if pv != 0:
            witness.append((w, pv))
    return value, witness


# ---------------------------------------------------------------------------
# Phase 1 (feasibility via artificial variables) and phase 2 (optimize).
# ---------------------------------------------------------------------------

_ZERO_COST: Callable[[Dict[str, bool]], Fraction] = lambda w: Fraction(0)
_ZERO_COST_Z3: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"] = lambda av: z3.RealVal(0)


def _solve_restricted_primal_phase1(rows: Sequence[_Row], columns: Sequence[Dict[str, bool]]) -> Fraction:
    """The phase-1 restricted primal's optimal value: ``min Σ_i s_i`` with one
    nonnegative artificial ``s_i`` relaxing each row (see the module docstring's
    "Feasibility (phase 1)" section) — ALWAYS feasible for a nonempty ``columns``.
    """
    m = len(rows)
    opt = z3.Optimize()
    p = [z3.Real(f"nilsson_cg!p_{i}") for i in range(len(columns))]
    s = [z3.Real(f"nilsson_cg!s_{i}") for i in range(m)]
    for pi in p:
        opt.add(pi >= 0)
    for si in s:
        opt.add(si >= 0)
    opt.add(z3.Sum(p) == z3.RealVal(1))
    for i, row in enumerate(rows):
        terms = [z3.RealVal(row.coeff_of(w)) * pi for w, pi in zip(columns, p) if row.coeff_of(w) != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        opt.add(lhs + s[i] >= z3.RealVal(row.rhs))
    handle = opt.minimize(z3.Sum(s) if s else z3.RealVal(0))
    if opt.check() != z3.sat:
        raise AssertionError(
            "nilsson column generation: the phase-1 restricted primal was unexpectedly "
            "infeasible — it is feasible by construction for any nonempty columns "
            "(the artificials alone can always satisfy every row); internal invariant "
            "violation, not a malformed input."
        )
    return _z3_to_fraction(opt.lower(handle))


def _max_columns_error(max_columns: int, columns: Sequence[Dict[str, bool]]) -> ValueError:
    """The ``ValueError`` raised when column generation exhausts its ``max_columns`` brake."""
    return ValueError(
        f"entailment_bounds: column generation did not certify optimality within "
        f"max_columns={max_columns} (currently {len(columns)} columns generated). "
        "Never returns an unproven bound — pass a larger max_columns explicitly if "
        "a harder problem is intended."
    )


def _phase1(atom_list: Sequence[str], rows: Sequence[_Row], columns: List[Dict[str, bool]],
           max_columns: int, constraints: Sequence[ProbConstraint]) -> List[Dict[str, bool]]:
    """Grow ``columns`` (in place, and returned) until the restricted master is
    genuinely feasible (no artificials needed), or PROVE the full constraint
    set is probabilistically inconsistent (raising the same ``ValueError`` the
    direct strategy raises for the same reason — see the module docstring's
    "Feasibility" section for the termination/correctness argument).
    """
    while True:
        artificial_total = _solve_restricted_primal_phase1(rows, columns)
        if artificial_total == 0:
            return columns
        y, lam = _solve_dual(rows, columns, _ZERO_COST, y_upper_bound=Fraction(1))
        found, w_new, value = _price(atom_list, rows, y, lam, _ZERO_COST_Z3)
        if not found or value <= 0 or w_new in columns:
            raise _infeasible_error(constraints)
        if len(columns) >= max_columns:
            raise _max_columns_error(max_columns, columns)
        columns.append(w_new)


def _phase2(atom_list: Sequence[str], rows: Sequence[_Row], columns: List[Dict[str, bool]],
           cost_of: Callable[[Dict[str, bool]], Fraction],
           cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"],
           minimize: bool, max_columns: int
           ) -> Tuple[Fraction, List[Dict[str, bool]], List[Tuple[Dict[str, bool], Fraction]]]:
    """Grow ``columns`` until pricing certifies optimality, then return the exact
    optimum of ``minimize``/``maximize`` ``Σ_w cost_of(w)·p_w`` and its witness.

    Maximizing is handled by minimizing the NEGATED cost throughout (so the
    dual/pricing machinery above, written once for "minimize", covers both
    directions) and negating the final value back.
    """
    sign = 1 if minimize else -1
    signed_cost_of = lambda w: sign * cost_of(w)
    signed_cost_z3 = lambda av: z3.RealVal(sign) * cost_z3_of(av)
    while True:
        y, lam = _solve_dual(rows, columns, signed_cost_of)
        found, w_new, value = _price(atom_list, rows, y, lam, signed_cost_z3)
        if not found or value <= 0 or w_new in columns:
            break
        if len(columns) >= max_columns:
            raise _max_columns_error(max_columns, columns)
        columns.append(w_new)
    value, witness = _solve_restricted_primal(rows, columns, signed_cost_of)
    return sign * value, columns, witness


# ---------------------------------------------------------------------------
# Public (within this internal module) entry point.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ColumnGenerationResult:
    """The full result of :func:`solve`, including what the public
    ``ProbBounds`` does not carry: the number of columns actually generated,
    and each bound's explicit witnessing distribution — both worlds white-box
    tests (``tests/test_nilsson_colgen.py``) check independently.
    """

    lower: Fraction
    upper: Fraction
    n_columns: int
    lower_witness: List[Tuple[Dict[str, bool], Fraction]]
    upper_witness: List[Tuple[Dict[str, bool], Fraction]]


def solve(atom_list: Sequence[str], constraints: Sequence[ProbConstraint], conclusion: Node,
         max_columns: int) -> ColumnGenerationResult:
    """Column-generation counterpart of ``nilsson.entailment_bounds``'s direct-strategy body.

    Runs phase 1 once (feasibility; see the module docstring), then phase 2
    twice (minimize, then maximize, ``P(conclusion)``, each continuing from
    wherever the previous phase left ``columns`` — the feasible region does
    not depend on the objective, so reusing columns across phases is free and
    correct, never wrong to reuse a world already known to be in the
    polytope). See this module's own docstring for the full termination and
    optimality proof.

    Raises:
        ValueError: if the constraint set is probabilistically inconsistent
            (identical message to the direct strategy's), or if optimality is
            not certified within ``max_columns`` generated columns.
    """
    rows = _build_rows(constraints)
    cost_of = lambda w: _indicator(conclusion, w)
    cost_z3_of = lambda av: _z3_indicator(conclusion, av)

    seed = {a: False for a in atom_list}
    columns: List[Dict[str, bool]] = [seed]
    columns = _phase1(atom_list, rows, columns, max_columns, constraints)

    lower, columns, lower_witness = _phase2(
        atom_list, rows, columns, cost_of, cost_z3_of, True, max_columns)
    upper, columns, upper_witness = _phase2(
        atom_list, rows, columns, cost_of, cost_z3_of, False, max_columns)

    return ColumnGenerationResult(lower, upper, len(columns), lower_witness, upper_witness)
