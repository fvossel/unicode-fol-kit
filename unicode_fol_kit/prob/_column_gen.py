"""Exact column generation for ``nilsson.entailment_bounds(strategy="column_generation")``.

:func:`~unicode_fol_kit.prob.nilsson.entailment_bounds`'s default (``"direct"``)
strategy materialises one Z3 ``Real`` per possible world — ``2^n`` of them for
``n`` distinct atoms — which is exact but explicitly bounded by ``max_atoms``
(12 by default) precisely because that blow-up is real. This module answers
the SAME linear program without ever building that array: it grows a small
``columns`` list of worlds ON DEMAND, deciding which world to add next by
SOLVING a small optimization problem (the "pricing subproblem") rather than
by enumerating all ``2^n`` candidates and checking each — so its cost per
iteration does not grow with ``2^n`` for a wide problem (a Z3 Boolean-SAT
search over the ``n`` atoms), and it never runs into ``max_atoms`` at all. It
is bounded instead by ``max_columns`` (500 by default): if optimality is not
certified within that many columns, :func:`solve` raises ``ValueError``
rather than ever returning an unproven bound, exactly the kit's "refuse
loudly" contract for every other bounded search.

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
world as a new LP column and to evaluate any world EXACTLY) and once as a Z3
expression over per-atom :func:`z3.Bool` variables (``z3_coeff``, used by the
pricing subproblem to search for an *unknown* world maximizing a linear
combination of these functionals — see :func:`_price`).

**What is trusted: nothing the optimiser says.** Z3's ``Optimize`` is not a
certificate: on a pricing objective built from ``If`` terms it has been
measured to return a world that is not a maximiser, with a value that is not
the value of the world it returned, and different answers for identical
inputs in one process. Every stop of the loops below therefore rests on
something that is checked exactly, never on an optimiser's report:

* a world handed back by pricing is a column only if its reduced cost,
  recomputed with :class:`~fractions.Fraction` arithmetic from ``coeff_of``,
  is positive (the optimiser's own value is not read at all);
* "no world improves" is established by exhaustive exact evaluation of every
  world when ``n`` is at most :data:`_EXHAUSTIVE_PRICING_MAX_ATOMS`, and
  otherwise by an UNSATISFIABLE :class:`z3.Solver` query "some world has a
  positive reduced cost" — a decision procedure, which can answer ``unsat``
  only when no such world exists. The optimiser only proposes a world to try
  first; when the proposal does not improve, the solver query is asked and
  either supplies an improving world or proves there is none;
* the dual ``(y, λ)`` the optimiser returns is re-checked exactly against
  every column (``y ≥ 0`` and every dual row satisfied), and the primal
  witness is re-checked exactly (nonnegative, sums to 1, every row holds);
* a bound is returned only when the exact value of the primal witness EQUALS
  the exact objective of a dual that no world violates (below); an
  optimiser's answer that fails any of these checks ends in ``ValueError``,
  never in a bound.

**Two-phase column generation, and its termination/optimality proof.**
:func:`solve` runs PHASE 1 once (find any world-set whose convex hull meets
every row, or PROVE none exists — the ``ValueError`` today's direct method
also raises) and then PHASE 2 twice (minimize, then maximize, ``P(conclusion)``
over that now-feasible restricted master, each free to add further columns).
Both phases share one mechanism:

1. *Restricted primal*: the SAME LP :func:`~unicode_fol_kit.prob.nilsson.entailment_bounds`
   solves, but only over the CURRENT ``columns`` (a genuine feasible point of
   the FULL LP too — the other worlds implicitly have ``p_w = 0``). Solved
   with :class:`z3.Optimize`, exactly like ``nilsson._solve``; the distribution
   it returns is re-verified, and its value is recomputed, exactly.
2. *Explicit dual*: Z3's ``Optimize`` exposes no shadow-price/dual accessor
   (verified: ``dir(z3.Optimize())`` has none), so the dual LP of that SAME
   restricted primal is derived BY HAND (standard LP duality: one dual
   variable ``y_i ≥ 0`` per ``≥`` row, one free dual ``λ`` for the ``Σp=1``
   row) and solved as its OWN small :class:`z3.Optimize` call — see
   :func:`_solve_dual`. Whatever it returns is a dual-FEASIBLE point for the
   columns once the exact re-check passes.
3. *Pricing subproblem*: does some world ``w*`` — not necessarily already in
   ``columns`` — violate ``(y, λ)``'s dual feasibility, i.e. is
   ``Σ_i y_i·coeff_i(w*) + λ − cost(w*) > 0``? If such a ``w*`` exists, its
   column improves the restricted primal (the classical "positive reduced
   cost" test) and is added. ``columns`` has grown by exactly one WORLD NOT
   ALREADY PRESENT: the dual was just verified feasible for every column, so
   no column in ``columns`` has a positive reduced cost.
4. *Termination*: because ``columns`` only grows and there are only finitely
   many worlds (``2^n``), the loop cannot run forever — it must reach either
   ``max_columns`` (raise, per the brake above) or a state where NO world
   violates ``(y, λ)``.
5. *Optimality, when pricing finds nothing*: ``(y, λ)`` is then dual-feasible
   for the FULL problem too (every world, not just ``columns``, satisfies its
   constraint) — so by WEAK duality, its dual objective ``Σ_i b_i·y_i + λ`` is
   a valid bound on the TRUE (all-``2^n``-columns) primal optimum: for any
   feasible distribution ``p``, ``cost(p) ≥ Σ_w (Σ_i y_i·coeff_i(w) + λ)·p_w
   ≥ Σ_i y_i·b_i + λ``. The restricted primal's witness is ALSO a feasible
   point of the true primal, so its value bounds the optimum from the other
   side. The two numbers are compared EXACTLY: when they are equal, the common
   value is the true (``2^n``-column) primal optimum, with no gap, and the
   witness attains it. (By STRONG duality of the restricted LP they ARE equal
   whenever the optimiser solved both restricted programs correctly; when
   they differ, the optimiser erred on one of them and the programs are
   solved again, a bounded number of times, before :func:`solve` raises
   ``ValueError`` — it never returns a value it could not certify.) This is
   the proof obligation :func:`solve`'s own docstring, and
   ``tests/test_nilsson_colgen.py``, hold this module to.

**Feasibility (phase 1) via a Farkas certificate.** The restricted primal can
itself be infeasible for a small seed ``columns`` (a single arbitrary world
essentially never satisfies every constraint's exact bounds on its own).
Phase 1 asks a :class:`z3.Solver` whether the rows can be met by some
distribution over ``columns``, and accepts a model only after checking it
exactly. If not, it solves the dual of the phase-1 LP (one nonnegative
artificial ``s_i`` relaxing each row, hence ``0 ≤ y_i ≤ 1``, cost 0 for every
``p_w``): a vector ``(y, λ)`` with ``Σ_i y_i·coeff_i(w) + λ ≤ 0`` for every
column and ``Σ_i b_i·y_i + λ > 0`` (checked exactly). Such a vector shows the
RESTRICTED rows infeasible; pricing then looks for a world that violates the
vector, and if there is none (the exhaustive or the unsatisfiable-query check
above) the very same vector shows that NO distribution over ANY set of worlds
meets every row (Farkas): for a feasible ``p``, ``Σ_i b_i·y_i + λ ≤ Σ_w
(Σ_i y_i·coeff_i(w) + λ)·p_w ≤ 0``, contradicting ``> 0``. The constraint set is
then probabilistically inconsistent, and :func:`solve` raises the identical
``ValueError`` :func:`~unicode_fol_kit.prob.nilsson._infeasible_error` builds
for the direct strategy. An optimiser's word that "nothing is feasible" is
never what that verdict rests on.

Internal module (leading underscore): nothing here is re-exported from
:mod:`unicode_fol_kit.prob`. Reached only through
``entailment_bounds(..., strategy="column_generation")`` — see that
function's docstring for the public contract — or directly, by
``tests/test_nilsson_colgen.py``, for white-box checks (the explicit witness
distribution, the dual construction) the public API does not expose.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
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

#: Up to this many atoms the pricing step evaluates every world exactly (at most
#: ``2**6 = 64`` of them); beyond it a world is searched for with Z3 and the absence of an
#: improving world is proved by an unsatisfiable solver query. Read at call time.
_EXHAUSTIVE_PRICING_MAX_ATOMS = 6

#: How often the restricted LPs are solved again when the exact primal value and the exact
#: dual objective disagree (they cannot, if the optimiser solved both correctly).
_CERTIFICATION_ATTEMPTS = 3

_World = Dict[str, bool]


# ---------------------------------------------------------------------------
# Rows: one linear functional of a world, represented two ways at once.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _Row:
    """One ``≥`` row of the LP: ``Σ_w coeff_of(w)·p_w ≥ rhs``.

    ``coeff_of`` evaluates the row's coefficient at a CONCRETE world (a
    ``Dict[str, bool]`` valuation) — used when a world already chosen (by
    :func:`_price`, or the phase-1 seed) is added to the restricted master or
    its dual, and to evaluate any world exactly. ``z3_coeff`` builds the SAME
    coefficient as a Z3 rational expression over per-atom :func:`z3.Bool`
    variables — used only inside :func:`_price`, which searches for an UNKNOWN
    world maximizing a linear combination of these, without enumerating any.
    """

    coeff_of: Callable[[_World], Fraction]
    z3_coeff: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
    rhs: Fraction
    label: str


def _indicator(formula: Node, valuation: _World) -> Fraction:
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
# Exact arithmetic on what the optimiser returns.
# ---------------------------------------------------------------------------

def _unverified_error(what: str) -> ValueError:
    """The ``ValueError`` raised when an answer of Z3 fails the exact re-check made on it.

    No bound is returned in that case: a value that could not be certified is refused, in
    the same way every other bounded search of the kit refuses.
    """
    return ValueError(
        "entailment_bounds: column generation could not certify its answer — "
        f"{what}. No bound is returned rather than an unverified one; retry, or use "
        "strategy='direct' when the number of atoms allows it."
    )


def _reduced_cost(rows: Sequence[_Row], y: Sequence[Fraction], lam: Fraction,
                  cost_of: Callable[[_World], Fraction], world: _World) -> Fraction:
    """``Σ_i y_i·coeff_i(w) + λ − cost(w)``, computed exactly (positive: the dual is violated at ``w``)."""
    total = lam - cost_of(world)
    for yi, row in zip(y, rows):
        if yi != 0:
            total += yi * row.coeff_of(world)
    return total


def _dual_value(rows: Sequence[_Row], y: Sequence[Fraction], lam: Fraction) -> Fraction:
    """The dual objective ``Σ_i rhs_i·y_i + λ``, exactly."""
    return lam + sum((row.rhs * yi for yi, row in zip(y, rows)), Fraction(0))


def _distribution_is_exact(rows: Sequence[_Row], columns: Sequence[_World],
                           weights: Sequence[Fraction]) -> bool:
    """``True`` iff ``weights`` (one per column) are, exactly, a distribution meeting every row."""
    if any(p < 0 for p in weights) or sum(weights, Fraction(0)) != 1:
        return False
    for row in rows:
        total = sum((row.coeff_of(w) * p for w, p in zip(columns, weights) if p != 0), Fraction(0))
        if total < row.rhs:
            return False
    return True


# ---------------------------------------------------------------------------
# The restricted master's dual, and the pricing subproblem.
# ---------------------------------------------------------------------------

def _solve_dual(rows: Sequence[_Row], columns: Sequence[_World],
                cost_of: Callable[[_World], Fraction],
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
    (point 2). ``y = 0, λ = 0`` is always a dual-feasible point (``0 ≤
    cost_of(w)`` — true since every objective in this module is a nonnegative
    combination of indicators), and the restricted primal is feasible and
    bounded, so the dual is feasible and bounded too.

    What comes back is checked exactly before it is returned: every ``y_i``
    within its bounds and every dual row satisfied at every column, in
    :class:`~fractions.Fraction` arithmetic. An answer that fails the check
    (or no answer at all) ends in ``ValueError``; the dual is never trusted on
    the optimiser's word.
    """
    m = len(rows)
    y = [z3.Real(f"nilsson_cg!y_{i}") for i in range(m)]
    lam = z3.Real("nilsson_cg!lambda")
    coefficients = [[row.coeff_of(w) for row in rows] for w in columns]
    costs = [cost_of(w) for w in columns]
    opt = z3.Optimize()
    for yi in y:
        opt.add(yi >= 0)
        if y_upper_bound is not None:
            opt.add(yi <= z3.RealVal(y_upper_bound))
    for cs, cost in zip(coefficients, costs):
        lhs = lam
        for yi, coeff in zip(y, cs):
            if coeff != 0:
                lhs = lhs + yi * z3.RealVal(coeff)
        opt.add(lhs <= z3.RealVal(cost))
    objective = lam
    for yi, row in zip(y, rows):
        if row.rhs != 0:
            objective = objective + z3.RealVal(row.rhs) * yi
    opt.maximize(objective)
    if opt.check() != z3.sat:
        raise _unverified_error("the restricted dual LP was reported unsatisfiable, "
                                "although y = 0, lambda = 0 satisfies it")
    model = opt.model()
    y_vals = [_z3_to_fraction(model.eval(yi, model_completion=True)) for yi in y]
    lam_val = _z3_to_fraction(model.eval(lam, model_completion=True))
    if any(v < 0 or (y_upper_bound is not None and v > y_upper_bound) for v in y_vals):
        raise _unverified_error("the dual returned by the optimiser leaves its bounds")
    for cs, cost in zip(coefficients, costs):
        if lam_val + sum((yi * coeff for yi, coeff in zip(y_vals, cs)), Fraction(0)) > cost:
            raise _unverified_error("the dual returned by the optimiser violates one of its own rows")
    return y_vals, lam_val


def _z3_reduced_cost(atom_vars: Dict[str, "z3.BoolRef"], rows: Sequence[_Row], y: Sequence[Fraction],
                     lam: Fraction, cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
                     ) -> "z3.ArithRef":
    """The Z3 expression of :func:`_reduced_cost` over per-atom Boolean variables."""
    objective = z3.RealVal(lam)
    for yi, row in zip(y, rows):
        if yi == 0:
            continue
        objective = objective + z3.RealVal(yi) * row.z3_coeff(atom_vars)
    return objective - cost_z3_of(atom_vars)


def _world_of(model: "z3.ModelRef", atom_list: Sequence[str],
              atom_vars: Dict[str, "z3.BoolRef"]) -> _World:
    """The world a Z3 model assigns, total over ``atom_list`` (``model_completion=True``,
    since an atom the objective does not mention would otherwise be a don't-care)."""
    return {a: bool(z3.is_true(model.eval(atom_vars[a], model_completion=True))) for a in atom_list}


def _propose_world(atom_list: Sequence[str], rows: Sequence[_Row], y: Sequence[Fraction], lam: Fraction,
                   cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]) -> Optional[_World]:
    """A world Z3's optimiser PROPOSES as the maximiser of the reduced cost — a guess only.

    One fresh :func:`z3.Bool` per atom and one :class:`z3.Optimize` call over the SAME
    ``_Row.z3_coeff`` expressions the master uses. Neither the world nor any value the
    optimiser reports is believed: :func:`_price` evaluates the world itself, exactly, and
    asks a solver for another one when this one does not improve.
    """
    atom_vars = {a: z3.Bool(f"nilsson_cg!atom_{i}") for i, a in enumerate(atom_list)}
    opt = z3.Optimize()
    opt.maximize(_z3_reduced_cost(atom_vars, rows, y, lam, cost_z3_of))
    if opt.check() != z3.sat:
        return None
    return _world_of(opt.model(), atom_list, atom_vars)


def _find_violating_world(atom_list: Sequence[str], rows: Sequence[_Row], y: Sequence[Fraction],
                          lam: Fraction, cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
                          ) -> Optional[_World]:
    """A world whose reduced cost is positive, or ``None`` if the solver PROVES there is none.

    A :class:`z3.Solver` query ``reduced cost > 0`` over the per-atom Booleans: ``unsat`` is
    the certificate that the dual is feasible for every one of the ``2^n`` worlds. ``unknown``
    is not an answer and ends in ``ValueError``.
    """
    atom_vars = {a: z3.Bool(f"nilsson_cg!atom_{i}") for i, a in enumerate(atom_list)}
    solver = z3.Solver()
    solver.add(_z3_reduced_cost(atom_vars, rows, y, lam, cost_z3_of) > 0)
    result = solver.check()
    if result == z3.unsat:
        return None
    if result != z3.sat:
        raise _unverified_error("the solver could not decide whether some world violates the dual")
    return _world_of(solver.model(), atom_list, atom_vars)


def _price(atom_list: Sequence[str], rows: Sequence[_Row], y: Sequence[Fraction], lam: Fraction,
           cost_of: Callable[[_World], Fraction],
           cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"]
           ) -> Tuple[bool, Optional[_World], Fraction]:
    """The pricing subproblem: is there a world whose reduced cost ``Σ_i y_i·coeff_i(w) + λ − cost(w)`` is positive?

    Returns ``(found, world, value)``. ``found`` is ``True`` only for a world whose reduced
    cost, recomputed here with :class:`~fractions.Fraction` arithmetic, is positive;
    ``value`` is that exact number. ``found`` is ``False`` (``world`` ``None``, ``value`` 0)
    only when it is PROVED that no world has a positive reduced cost:

    * with at most :data:`_EXHAUSTIVE_PRICING_MAX_ATOMS` atoms, by evaluating every world
      exactly (the world with the largest reduced cost is returned; among equals the first
      in the order of ``itertools.product((False, True), ...)`` over ``atom_list`` — no
      randomness);
    * with more atoms, by Z3: the optimiser proposes a world (:func:`_propose_world`) and
      the proposal is used if it improves; otherwise a :class:`z3.Solver` query asks for any
      world with a positive reduced cost, and its ``unsat`` is the proof that none exists.

    Whatever Z3 returns is re-evaluated exactly: a world it claims improves but that does
    not is a fault of the translation and ends in ``ValueError`` rather than a wrong column.
    """
    if len(atom_list) <= _EXHAUSTIVE_PRICING_MAX_ATOMS:
        best_world: Optional[_World] = None
        best = Fraction(0)
        for values in product((False, True), repeat=len(atom_list)):
            world = dict(zip(atom_list, values))
            value = _reduced_cost(rows, y, lam, cost_of, world)
            if value > best:
                best, best_world = value, world
        return best_world is not None, best_world, best

    proposal = _propose_world(atom_list, rows, y, lam, cost_z3_of)
    if proposal is not None:
        value = _reduced_cost(rows, y, lam, cost_of, proposal)
        if value > 0:
            return True, proposal, value
    found_world = _find_violating_world(atom_list, rows, y, lam, cost_z3_of)
    if found_world is None:
        return False, None, Fraction(0)
    value = _reduced_cost(rows, y, lam, cost_of, found_world)
    if value <= 0:
        raise _unverified_error("the solver reported a world that violates the dual, "
                                "but evaluating that world exactly shows it does not")
    return True, found_world, value


# ---------------------------------------------------------------------------
# The restricted PRIMAL, solved directly (for the final value + witness).
# ---------------------------------------------------------------------------

def _solve_restricted_primal(rows: Sequence[_Row], columns: Sequence[_World],
                             cost_of: Callable[[_World], Fraction]
                             ) -> Tuple[Fraction, List[Tuple[_World, Fraction]]]:
    """Solve ``min Σ_w cost_of(w)·p_w`` over the current ``columns``.

    Returns ``(value, witness)`` where ``witness`` is the explicit distribution the optimum
    is attained by: every ``(world, p_w)`` pair from the optimal model with ``p_w`` nonzero.
    The distribution is re-verified exactly (nonnegative, sums to 1, every row holds) and
    ``value`` is the exact value OF THAT DISTRIBUTION, ``Σ_w cost_of(w)·p_w`` — not a number
    the optimiser reported. It is a genuine feasible point of the FULL (all-``2^n``-columns)
    problem too (the other worlds are implicitly at ``p_w = 0``), which is exactly what
    licenses calling the value "attained" rather than merely "achievable in the limit" — the
    property ``tests/test_nilsson_colgen.py`` re-checks independently by recomputing every
    constraint's probability and the objective directly from ``witness`` via
    :func:`~unicode_fol_kit.prob.nilsson._eval`. Whether the value is also the LEAST one is
    settled by the caller against a dual (module docstring, point 5).
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
    opt.minimize(objective)
    if opt.check() != z3.sat:
        raise _unverified_error("the restricted primal LP was reported infeasible although "
                                "phase 1 had exhibited a feasible distribution over these columns")
    model = opt.model()
    weights = [_z3_to_fraction(model.eval(pi, model_completion=True)) for pi in p]
    if not _distribution_is_exact(rows, columns, weights):
        raise _unverified_error("the distribution returned by the optimiser is not a feasible "
                                "point of the restricted primal")
    witness = [(w, pv) for w, pv in zip(columns, weights) if pv != 0]
    value = sum((cost_of(w) * pv for w, pv in witness), Fraction(0))
    return value, witness


# ---------------------------------------------------------------------------
# Phase 1 (feasibility) and phase 2 (optimize).
# ---------------------------------------------------------------------------

_ZERO_COST: Callable[[_World], Fraction] = lambda w: Fraction(0)
_ZERO_COST_Z3: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"] = lambda av: z3.RealVal(0)


def _has_feasible_distribution(rows: Sequence[_Row], columns: Sequence[_World]) -> bool:
    """``True`` iff a distribution over ``columns`` meets every row — and then one is exhibited.

    A :class:`z3.Solver` query (no optimisation) whose model is accepted only after
    :func:`_distribution_is_exact` confirms it in :class:`~fractions.Fraction` arithmetic.
    ``False`` means the solver found none; the caller then asks for a certificate of it.
    """
    solver = z3.Solver()
    p = [z3.Real(f"nilsson_cg!p_{i}") for i in range(len(columns))]
    for pi in p:
        solver.add(pi >= 0)
    solver.add(z3.Sum(p) == z3.RealVal(1))
    for row in rows:
        terms = [z3.RealVal(row.coeff_of(w)) * pi for w, pi in zip(columns, p) if row.coeff_of(w) != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        solver.add(lhs >= z3.RealVal(row.rhs))
    if solver.check() != z3.sat:
        return False
    model = solver.model()
    weights = [_z3_to_fraction(model.eval(pi, model_completion=True)) for pi in p]
    if not _distribution_is_exact(rows, columns, weights):
        raise _unverified_error("the model the solver returned for the restricted rows is not a "
                                "distribution that meets them")
    return True


def _max_columns_error(max_columns: int, columns: Sequence[_World]) -> ValueError:
    """The ``ValueError`` raised when column generation exhausts its ``max_columns`` brake."""
    return ValueError(
        f"entailment_bounds: column generation did not certify optimality within "
        f"max_columns={max_columns} (currently {len(columns)} columns generated). "
        "Never returns an unproven bound — pass a larger max_columns explicitly if "
        "a harder problem is intended."
    )


def _phase1(atom_list: Sequence[str], rows: Sequence[_Row], columns: List[_World],
            max_columns: int, constraints: Sequence[ProbConstraint]) -> List[_World]:
    """Grow ``columns`` (in place, and returned) until a distribution over them meets
    every row, or PROVE the full constraint set is probabilistically inconsistent
    (raising the same ``ValueError`` the direct strategy raises for the same reason — see
    the module docstring's "Feasibility" section for the certificate).

    The ``ValueError`` for an inconsistent set is raised only with a Farkas vector in hand:
    ``y ≥ 0`` and ``λ`` with a positive exact dual value, satisfied by every column (checked
    in :func:`_solve_dual`) and by every world (checked in :func:`_price`).
    """
    while True:
        if _has_feasible_distribution(rows, columns):
            return columns
        y, lam = _solve_dual(rows, columns, _ZERO_COST, y_upper_bound=Fraction(1))
        if _dual_value(rows, y, lam) <= 0:
            raise _unverified_error("the solver found no distribution over the current columns, "
                                    "but no certificate of that exists")
        found, w_new, _value = _price(atom_list, rows, y, lam, _ZERO_COST, _ZERO_COST_Z3)
        if not found or w_new is None:       # no world violates the Farkas vector: it holds for all
            raise _infeasible_error(constraints)
        if len(columns) >= max_columns:
            raise _max_columns_error(max_columns, columns)
        if w_new in columns:
            raise _unverified_error("a world with a positive reduced cost is already a column, "
                                    "although the dual was verified feasible for every column")
        columns.append(w_new)


def _phase2(atom_list: Sequence[str], rows: Sequence[_Row], columns: List[_World],
            cost_of: Callable[[_World], Fraction],
            cost_z3_of: Callable[[Dict[str, "z3.BoolRef"]], "z3.ArithRef"],
            minimize: bool, max_columns: int
            ) -> Tuple[Fraction, List[_World], List[Tuple[_World, Fraction]]]:
    """Grow ``columns`` until pricing certifies optimality, then return the exact
    optimum of ``minimize``/``maximize`` ``Σ_w cost_of(w)·p_w`` and its witness.

    Maximizing is handled by minimizing the NEGATED cost throughout (so the
    dual/pricing machinery above, written once for "minimize", covers both
    directions) and negating the final value back.

    The value is returned only when the exact value of the primal witness equals the exact
    objective of a dual that no world violates (module docstring, point 5); otherwise the
    restricted programs are solved again, and after :data:`_CERTIFICATION_ATTEMPTS` failures
    ``ValueError`` is raised.
    """
    sign = 1 if minimize else -1
    signed_cost_of = lambda w: sign * cost_of(w)
    signed_cost_z3 = lambda av: z3.RealVal(sign) * cost_z3_of(av)
    disagreements = 0
    while True:
        y, lam = _solve_dual(rows, columns, signed_cost_of)
        found, w_new, _value = _price(atom_list, rows, y, lam, signed_cost_of, signed_cost_z3)
        if found and w_new is not None:
            if len(columns) >= max_columns:
                raise _max_columns_error(max_columns, columns)
            if w_new in columns:
                raise _unverified_error("a world with a positive reduced cost is already a column, "
                                        "although the dual was verified feasible for every column")
            columns.append(w_new)
            continue
        value, witness = _solve_restricted_primal(rows, columns, signed_cost_of)
        bound = _dual_value(rows, y, lam)
        if value == bound:
            return sign * value, columns, witness
        if value < bound:
            # Weak duality: a feasible distribution cannot cost less than the objective of a dual
            # that no world violates. Both were checked exactly, so a solver that said "no world
            # violates the dual" without it being true is the only way here.
            raise _unverified_error(
                f"the exact value of the primal witness ({value}) is below the objective of a dual "
                f"that is feasible for every world ({bound}), which weak duality rules out")
        disagreements += 1
        if disagreements >= _CERTIFICATION_ATTEMPTS:
            raise _unverified_error(
                f"the exact value of the primal witness ({value}) differs from the exact "
                f"objective of the dual that no world violates ({bound})")


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
    lower_witness: List[Tuple[_World, Fraction]]
    upper_witness: List[Tuple[_World, Fraction]]


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
            (identical message to the direct strategy's), if optimality is
            not certified within ``max_columns`` generated columns, or if an
            answer of Z3 fails the exact re-check made on it (so that no bound
            it could not certify is ever returned).
    """
    rows = _build_rows(constraints)
    cost_of = lambda w: _indicator(conclusion, w)
    cost_z3_of = lambda av: _z3_indicator(conclusion, av)

    seed = {a: False for a in atom_list}
    columns: List[_World] = [seed]
    columns = _phase1(atom_list, rows, columns, max_columns, constraints)

    lower, columns, lower_witness = _phase2(
        atom_list, rows, columns, cost_of, cost_z3_of, True, max_columns)
    upper, columns, upper_witness = _phase2(
        atom_list, rows, columns, cost_of, cost_z3_of, False, max_columns)

    return ColumnGenerationResult(lower, upper, len(columns), lower_witness, upper_witness)
