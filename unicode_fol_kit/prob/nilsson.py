"""Nilsson probabilistic-entailment bounds — exact, propositional, no sampling.

Nilsson (*Probabilistic Logic*, Artificial Intelligence 28, 1986) attaches
probability INTERVALS, not point values, to formulas: a set of constraints
``lower ≤ P(φ) ≤ upper`` need not pin down a unique probability distribution
over the possible worlds, only a convex polytope of them. The tightest bounds
on a conclusion's probability are then the minimum and maximum of ``P(ψ)``
over every distribution in that polytope — a linear program, decided here
EXACTLY (rational arithmetic throughout, never a float) via :mod:`z3`'s
``Optimize`` over ``Real`` variables fed rational literals.

**Semantics, precisely.** Collect every distinct atom (by surface form —
:meth:`~unicode_fol_kit.fol.nodes.Node.to_unicode_str`, the kit-wide
convention for "what counts as one propositional variable"; see
:mod:`unicode_fol_kit.semantics.truthtable`) occurring in the constraints and
the conclusion; a quantified formula is refused (see below). With ``n``
distinct atoms there are ``2^n`` possible worlds (truth-value assignments);
one nonnegative real variable ``p_w`` per world, constrained to sum to 1, is a
full parametrisation of every probability distribution over those worlds. An
UNconditional constraint ``lower ≤ P(φ) ≤ upper`` becomes
``lower ≤ Σ_{w ⊨ φ} p_w ≤ upper`` — linear in the ``p_w``. A CONDITIONAL
constraint (``given=φ``, ``formula=ψ``, read ``P(ψ | φ)``) is put in Nilsson's
standard LINEAR form ``lower·P(φ) ≤ P(ψ∧φ) ≤ upper·P(φ)`` rather than the
division ``P(ψ∧φ)/P(φ)`` that would leave the LP domain (products of a
constant rational with a linear expression stay linear). **When ``P(φ) = 0``
this constraint is VACUOUS** — both sides collapse to ``0 ≤ P(ψ∧φ) ≤ 0``,
which is already implied by ``P(ψ∧φ) ≤ P(φ) = 0``, so it adds no information.
This is the usual Nilsson/probability-theory treatment of a conditional whose
condition has probability zero (the conditional is undefined pointwise, but
the linear encoding degrades gracefully to "no constraint" rather than raising
or dividing by zero).

Given that polytope, :func:`entailment_bounds` returns the minimum and maximum
of ``Σ_{w ⊨ conclusion} p_w`` — the tightest probability bounds the
constraints entail for the conclusion, via two SEPARATE ``Optimize`` calls
(minimize, then maximize; both must be satisfiable together with the
constraints, or the constraint set is probabilistically inconsistent and
:func:`entailment_bounds` raises ``ValueError``). A classical special case
falls out for free: if every premise is pinned to probability 1 (via
:meth:`ProbConstraint.exact`) and the conclusion is classically entailed, both
bounds collapse to exactly ``(1, 1)`` — Nilsson's bounds subsume classical
entailment as the ``{0, 1}``-only corner of the polytope (cross-checked
against :func:`unicode_fol_kit.api.prove` in the test suite).

**Scope.** Propositional only, and DELIBERATELY so: a quantified formula
anywhere in a constraint or the conclusion raises ``ValueError`` rather than
being silently skolemised or ground over some implicit domain — the kit's
standing rule (see :mod:`unicode_fol_kit.semantics.truthtable`) is that a
formula outside a module's decidable fragment is refused loudly, never
approximated quietly. The world count is ``2^n`` in the number of distinct
atoms, so ``max_atoms`` (default 12, i.e. up to 4096 worlds) is a deliberate,
overridable brake on that exponential — raise it explicitly if a larger
problem is intended.

**A second, algorithm-only route.** :func:`entailment_bounds` takes a
``strategy`` keyword: ``"direct"`` (above, the default, unchanged) or
``"column_generation"`` (:mod:`unicode_fol_kit.prob._column_gen`), which
never materialises a ``2^n``-sized world array — it grows a small subset of
worlds on demand, using a Z3 Boolean-SAT search (over the ``n`` atoms
directly, never ``2^n`` enumerated) as the pricing subproblem that decides
which world to add next, so it can answer problems with far more than
``max_atoms`` distinct atoms. Both strategies solve the EXACT SAME linear
program and are held to agreeing exactly (never a tolerance) wherever both
can answer — see :func:`entailment_bounds`'s own docstring and
:mod:`unicode_fol_kit.prob._column_gen`'s module docstring for the algorithm and its
termination/optimality proof.

Public API: :class:`ProbConstraint`, :class:`ProbBounds`,
:func:`entailment_bounds`.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Literal, Optional, Sequence

import z3

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff

__all__ = ["ProbConstraint", "ProbBounds", "entailment_bounds"]


# ---------------------------------------------------------------------------
# Exact-rational helpers
# ---------------------------------------------------------------------------

def _as_exact_prob(value, label: str) -> Fraction:
    """Coerce ``value`` to an exact :class:`~fractions.Fraction` (range checked by the caller).

    Accepts ``Fraction`` and ``int`` (both lossless); rejects ``float``
    outright rather than silently rounding it into a Fraction — this module
    performs EXACT probabilistic logic, and ``Fraction(0.7)`` is not ``7/10``
    (it is the nearest IEEE-754 double, a long ugly binary fraction), so
    accepting a float would quietly smuggle sampling-grade imprecision into a
    supposedly exact bound.
    """
    if isinstance(value, bool) or not isinstance(value, (Fraction, int)):
        raise TypeError(
            f"ProbConstraint: {label} must be an exact Fraction (or int, coerced "
            f"losslessly) — got {type(value).__name__} {value!r}. Pass "
            f"Fraction({label}) explicitly (e.g. Fraction(7, 10)); a float is refused "
            "because this module never approximates a probability."
        )
    return Fraction(value)


# ---------------------------------------------------------------------------
# Constraints and bounds
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProbConstraint:
    """One Nilsson probability constraint: ``lower ≤ P(formula [| given]) ≤ upper``.

    ``given=None`` (the default) is an UNconditional constraint on
    ``P(formula)``; a non-``None`` ``given`` makes it the CONDITIONAL
    ``P(formula | given)`` (see the module docstring for how each is encoded
    as a linear constraint, and the ``P(given) = 0`` vacuity case). ``lower``
    and ``upper`` are coerced to exact ``Fraction`` (int accepted, float
    rejected — see :func:`_as_exact_prob`) and validated as
    ``0 ≤ lower ≤ upper ≤ 1``.
    """

    formula: Node
    lower: Fraction
    upper: Fraction
    given: Optional[Node] = None

    def __post_init__(self):
        lower = _as_exact_prob(self.lower, "lower")
        upper = _as_exact_prob(self.upper, "upper")
        object.__setattr__(self, "lower", lower)
        object.__setattr__(self, "upper", upper)
        if not (Fraction(0) <= lower <= upper <= Fraction(1)):
            raise ValueError(
                "ProbConstraint: bounds must satisfy 0 <= lower <= upper <= 1; "
                f"got lower={lower}, upper={upper}."
            )

    @classmethod
    def exact(cls, formula: Node, value, given: Optional[Node] = None) -> "ProbConstraint":
        """Convenience constructor pinning ``P(formula [| given])`` to a single exact value."""
        p = _as_exact_prob(value, "value")
        return cls(formula, p, p, given)

    def _describe(self) -> str:
        """Render as ``P(φ) ∈ [lo, hi]`` / ``P(φ | ψ) ∈ [lo, hi]`` for error messages."""
        target = self.formula.to_unicode_str()
        if self.given is not None:
            target = f"{target} | {self.given.to_unicode_str()}"
        return f"P({target}) ∈ [{self.lower}, {self.upper}]"


@dataclass(frozen=True)
class ProbBounds:
    """The tightest ``[lower, upper]`` probability bounds a constraint set entails.

    ``n_worlds`` is ``2**n`` for the ``n`` distinct atoms collected from the
    constraints and the conclusion — the size of the world enumeration the
    bounds were computed over.
    """

    lower: Fraction
    upper: Fraction
    n_worlds: int

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict; bounds as exact ``"num/den"`` strings."""
        return {"lower": str(self.lower), "upper": str(self.upper), "n_worlds": self.n_worlds}


# ---------------------------------------------------------------------------
# Own propositional evaluator / atom collector (classical connectives only).
# ---------------------------------------------------------------------------

_UNSUPPORTED = (
    "nilsson: unsupported node type {cls} in a probability formula. Only the "
    "classical propositional connectives (¬ ∧ ∨ → ↔ ⊕) over Atom leaves are "
    "supported — in particular a QUANTIFIED formula has no finite space of "
    "possible worlds and is refused rather than silently approximated (e.g. by "
    "skolemising or grounding over an implicit domain)."
)


def _collect_atoms(formula: Node, atoms: set) -> None:
    """Add every distinct atom (by ``to_unicode_str()``) in ``formula`` to ``atoms``.

    Raises ``ValueError`` on anything other than Atom/¬/∧/∨/→/↔/⊕ — in
    particular on any quantifier, loudly, per the module's scope contract.
    """
    if isinstance(formula, Atom):
        atoms.add(formula.to_unicode_str())
        return
    if isinstance(formula, Not):
        _collect_atoms(formula.formula, atoms)
        return
    if isinstance(formula, (And, Or, Xor, Implies, Iff)):
        _collect_atoms(formula.left, atoms)
        _collect_atoms(formula.right, atoms)
        return
    raise ValueError(_UNSUPPORTED.format(cls=type(formula).__name__))


def _eval(formula: Node, valuation: dict) -> bool:
    """Evaluate ``formula`` (¬ ∧ ∨ → ↔ ⊕ over Atom leaves) under ``valuation``.

    ``valuation`` maps each atom's ``to_unicode_str()`` to a bool. Raises
    ``ValueError`` on an unsupported node type (defensive: :func:`_collect_atoms`
    already rejects these upstream of every call site in this module).
    """
    if isinstance(formula, Atom):
        return valuation[formula.to_unicode_str()]
    if isinstance(formula, Not):
        return not _eval(formula.formula, valuation)
    if isinstance(formula, And):
        return _eval(formula.left, valuation) and _eval(formula.right, valuation)
    if isinstance(formula, Or):
        return _eval(formula.left, valuation) or _eval(formula.right, valuation)
    if isinstance(formula, Xor):
        return _eval(formula.left, valuation) != _eval(formula.right, valuation)
    if isinstance(formula, Implies):
        return (not _eval(formula.left, valuation)) or _eval(formula.right, valuation)
    if isinstance(formula, Iff):
        return _eval(formula.left, valuation) == _eval(formula.right, valuation)
    raise ValueError(_UNSUPPORTED.format(cls=type(formula).__name__))


def _to_z3_bool(formula: Node, atom_vars: dict):
    """Translate ``formula`` (¬ ∧ ∨ → ↔ ⊕ over Atom leaves) into a Z3 Bool expression.

    The exact structural mirror of :func:`_eval`, one recursive case for
    one recursive case, with ``atom_vars`` (mapping each atom's
    ``to_unicode_str()`` to its own :func:`z3.Bool` variable) standing in
    for the Python ``valuation`` dict — so a world is no longer a fixed
    Python bool assignment to evaluate against, but a Z3 model Z3 itself
    gets to choose, which is exactly what :mod:`unicode_fol_kit.prob._column_gen`'s pricing
    subproblem needs (searching over all ``2^n`` worlds via SAT rather than
    enumerating them). Used only by ``strategy="column_generation"``; the
    default ``strategy="direct"`` path never calls this (it evaluates
    formulas against concrete Python valuations via :func:`_eval` alone).
    Raises the same ``ValueError`` as :func:`_eval` on an unsupported node
    (defensive: :func:`_collect_atoms` already rejects these upstream).
    """
    if isinstance(formula, Atom):
        return atom_vars[formula.to_unicode_str()]
    if isinstance(formula, Not):
        return z3.Not(_to_z3_bool(formula.formula, atom_vars))
    if isinstance(formula, And):
        return z3.And(_to_z3_bool(formula.left, atom_vars), _to_z3_bool(formula.right, atom_vars))
    if isinstance(formula, Or):
        return z3.Or(_to_z3_bool(formula.left, atom_vars), _to_z3_bool(formula.right, atom_vars))
    if isinstance(formula, Xor):
        return z3.Xor(_to_z3_bool(formula.left, atom_vars), _to_z3_bool(formula.right, atom_vars))
    if isinstance(formula, Implies):
        return z3.Implies(_to_z3_bool(formula.left, atom_vars), _to_z3_bool(formula.right, atom_vars))
    if isinstance(formula, Iff):
        return _to_z3_bool(formula.left, atom_vars) == _to_z3_bool(formula.right, atom_vars)
    raise ValueError(_UNSUPPORTED.format(cls=type(formula).__name__))


# ---------------------------------------------------------------------------
# The linear program
# ---------------------------------------------------------------------------

def _z3_to_fraction(value) -> Fraction:
    """Read a Z3 numeral back as an exact Python Fraction.

    A Real-valued optimum that happens to be a whole number comes back from
    Z3 as an ``IntNumRef`` (no ``as_fraction()``) rather than a ``RatNumRef``
    — both are exact, so this dispatches on whichever accessor is present
    instead of assuming one numeral type.
    """
    if hasattr(value, "as_fraction"):
        return value.as_fraction()
    return Fraction(value.as_long())


def _infeasible_error(constraints: Sequence["ProbConstraint"]) -> ValueError:
    """The ``ValueError`` raised when no distribution satisfies ``constraints`` at once.

    Shared by both strategies (see :mod:`unicode_fol_kit.prob._column_gen`'s phase-1 termination)
    so an inconsistent constraint set is refused with the identical message
    regardless of which algorithm found the inconsistency.
    """
    detail = "; ".join(c._describe() for c in constraints)
    return ValueError(
        "entailment_bounds: probabilistically inconsistent — no probability "
        f"distribution over the possible worlds satisfies all of: {detail}"
    )


def _solve(base_constraints, objective, minimize: bool, constraints: Sequence[ProbConstraint]) -> Fraction:
    """Minimize or maximize ``objective`` subject to ``base_constraints`` (a fresh Optimize)."""
    opt = z3.Optimize()
    for c in base_constraints:
        opt.add(c)
    handle = opt.minimize(objective) if minimize else opt.maximize(objective)
    if opt.check() != z3.sat:
        raise _infeasible_error(constraints)
    value = opt.lower(handle) if minimize else opt.upper(handle)
    return _z3_to_fraction(value)


def entailment_bounds(constraints: Sequence[ProbConstraint], conclusion: Node,
                      *, max_atoms: int = 12,
                      strategy: Literal["direct", "column_generation"] = "direct",
                      max_columns: int = 500) -> ProbBounds:
    """Return the tightest ``[lower, upper]`` bounds :func:`ProbConstraint`\\ s entail for ``conclusion``.

    ``strategy`` selects the solving ALGORITHM, never the semantics — both
    solve the exact same LP (one nonnegative real per possible world, summing
    to 1, subject to the constraints; see the module docstring) and are held
    to agreeing EXACTLY (``Fraction`` equality, never a tolerance) on every
    problem either can answer, which is what this module's own differential
    test suite (``tests/test_nilsson_colgen.py``) checks directly.

    ``"direct"`` (the default, UNCHANGED from before ``strategy`` existed)
    builds one nonnegative real variable per possible world (``2^n`` for the
    ``n`` distinct atoms across every constraint and ``conclusion``), then
    minimizes and maximizes ``P(conclusion)`` over that polytope with two
    separate :class:`z3.Optimize` calls. Every probability in the result is
    an EXACT :class:`~fractions.Fraction` read back from Z3's rational model
    — never routed through ``float``. ``max_atoms`` (12 by default) is an
    explicit, overridable brake on the ``2^n`` blow-up.

    ``"column_generation"`` (:mod:`unicode_fol_kit.prob._column_gen`) never
    materialises a world: it grows a small ``columns`` subset of worlds on
    demand, pricing a candidate world in via one small exact LP plus one Z3
    Boolean-SAT search over the ``n`` atoms — polynomial per iteration
    regardless of ``n`` — so it can answer problems with far more than
    ``max_atoms`` distinct atoms (``max_atoms`` is not enforced under this
    strategy; the only brake is ``max_columns``, 500 by default, raising
    ``ValueError`` rather than ever returning an unproven bound). See
    :func:`unicode_fol_kit.prob._column_gen.solve` for the two-phase
    primal/dual column-generation algorithm and its termination/optimality
    proof.

    Raises:
        ValueError: if ``conclusion`` or any constraint's ``formula``/``given``
            is quantified or otherwise outside ¬/∧/∨/→/↔/⊕-over-Atom; under
            ``strategy="direct"``, if the distinct-atom count exceeds
            ``max_atoms`` (the world count is ``2^n`` — an explicit,
            overridable brake on that exponential); under
            ``strategy="column_generation"``, if column generation does not
            certify optimality within ``max_columns`` generated columns; an
            unrecognised ``strategy``; or (either strategy, identical message)
            if the constraint set is probabilistically inconsistent (no
            distribution satisfies every constraint at once).
    """
    if strategy not in ("direct", "column_generation"):
        raise ValueError(
            f"entailment_bounds: unknown strategy {strategy!r}; expected "
            "'direct' or 'column_generation'."
        )

    atoms: set = set()
    for c in constraints:
        _collect_atoms(c.formula, atoms)
        if c.given is not None:
            _collect_atoms(c.given, atoms)
    _collect_atoms(conclusion, atoms)

    atom_list = sorted(atoms)
    n = len(atom_list)

    if strategy == "column_generation":
        return _entailment_bounds_column_generation(constraints, conclusion, atom_list, max_columns)

    if n > max_atoms:
        raise ValueError(
            f"entailment_bounds: {n} distinct atoms exceeds max_atoms={max_atoms}. "
            f"The world enumeration is O(2^n) — {n} atoms means 2**{n} = {2 ** n} "
            "probability variables. Reduce the formulas, or pass a larger max_atoms "
            "explicitly if that blow-up is intended."
        )

    worlds = list(product((False, True), repeat=n))
    valuations = [dict(zip(atom_list, w)) for w in worlds]

    p = [z3.Real(f"nilsson!p_{i}") for i in range(len(worlds))]
    base = [pi >= z3.RealVal(0) for pi in p]
    base.append(z3.Sum(p) == z3.RealVal(1))

    def indicator_sum(formula: Node):
        idxs = [i for i, val in enumerate(valuations) if _eval(formula, val)]
        if not idxs:
            return z3.RealVal(0)
        return z3.Sum([p[i] for i in idxs])

    for c in constraints:
        if c.given is None:
            p_phi = indicator_sum(c.formula)
            base.append(p_phi >= z3.RealVal(c.lower))
            base.append(p_phi <= z3.RealVal(c.upper))
        else:
            idxs_given = [i for i, val in enumerate(valuations) if _eval(c.given, val)]
            idxs_both = [i for i in idxs_given if _eval(c.formula, valuations[i])]
            p_given = z3.Sum([p[i] for i in idxs_given]) if idxs_given else z3.RealVal(0)
            p_both = z3.Sum([p[i] for i in idxs_both]) if idxs_both else z3.RealVal(0)
            base.append(p_both >= z3.RealVal(c.lower) * p_given)
            base.append(p_both <= z3.RealVal(c.upper) * p_given)

    p_concl = indicator_sum(conclusion)

    lower = _solve(base, p_concl, True, constraints)
    upper = _solve(base, p_concl, False, constraints)
    return ProbBounds(lower, upper, len(worlds))


# ---------------------------------------------------------------------------
# strategy="column_generation" dispatch
# ---------------------------------------------------------------------------

def _entailment_bounds_column_generation(constraints: Sequence[ProbConstraint], conclusion: Node,
                                         atom_list, max_columns: int) -> ProbBounds:
    """``entailment_bounds(..., strategy="column_generation")``'s dispatch target.

    A lazy, function-local import of :mod:`unicode_fol_kit.prob._column_gen` (not a module-level
    one): that module imports several names FROM this one (:class:`ProbConstraint`,
    :func:`_eval`, :func:`_to_z3_bool`, :func:`_z3_to_fraction`,
    :func:`_infeasible_error`) to build its rows and pricing subproblem, so a
    module-level import here in the other direction would be circular — the
    same lazy-import shape :func:`~unicode_fol_kit.atp.z3_input.to_smtlib`
    already uses for an analogous reason (see its own module docstring).

    ``n_worlds`` on the returned :class:`ProbBounds` is still ``2**n`` — the
    SAME nominal meaning it has under ``strategy="direct"`` (the polytope's
    world count), even though column generation never materialises anywhere
    near that many worlds — so a :class:`ProbBounds` from either strategy
    means the same thing and the differential tests' ``.lower``/``.upper``
    equality checks compare like with like.
    """
    from . import _column_gen

    result = _column_gen.solve(atom_list, constraints, conclusion, max_columns)
    return ProbBounds(result.lower, result.upper, 2 ** len(atom_list))
