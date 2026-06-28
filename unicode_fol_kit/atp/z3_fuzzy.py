"""Łukasiewicz fuzzy SAT / validity via Z3 reals.

Decides propositional Łukasiewicz formulas by encoding them into Z3 with one
``Real`` variable per distinct ground atom, each constrained to the unit
interval [0, 1]. The truth *degree* of a formula is built as a piecewise-linear
Z3 ``Real`` expression using ``z3.If`` for the min / max / clamp operations.

Atom semantics over [0, 1]:

* ``LukNegation``        ¬a       = 1 − a
* ``WeakConjunction``    a ∧ b    = min(a, b)
* ``WeakDisjunction``    a ∨ b    = max(a, b)
* ``StrongConjunction``  a ⊗ b    = max(0, a + b − 1)
* ``StrongDisjunction``  a ⊕ b    = min(1, a + b)
* ``LukImplication``     a → b    = min(1, 1 − a + b)
* ``LukEquivalence``     a ↔ b    = 1 − |a − b|

This v1 is propositional: a quantifier anywhere in the formula raises a clear
``NotImplementedError`` suggesting that the formula be grounded first.

Public API:
    fuzzy_is_satisfiable(formula, threshold=1.0, strict=False, timeout=10000)
    fuzzy_is_valid(formula, timeout=10000)
    fuzzy_get_model(formula, threshold=1.0, timeout=10000)
"""

from fractions import Fraction

from z3 import Solver, Real, RealVal, If, And as Z3And, sat, unsat

from ..fol.nodes import (
    Node, Atom,
    Quantifier, SortedQuantifier,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
)


# =========================
# Z3 helpers
# =========================

def _z3_min(a, b):
    """min(a, b) as a Z3 expression."""
    return If(a <= b, a, b)


def _z3_max(a, b):
    """max(a, b) as a Z3 expression."""
    return If(a >= b, a, b)


def _z3_tnorm_ops(tnorm: str) -> dict:
    """Z3 builders for the strong connectives of ``tnorm``.

    Only the **piecewise-linear** t-norms are deciders here: Łukasiewicz and Gödel
    encode into linear real arithmetic (with ``If``), which Z3 decides completely.
    The product t-norm needs nonlinear arithmetic (``x·y`` / ``y/x``) that Z3 cannot
    decide completely, so it is rejected with a pointer to the evaluator.
    """
    one, zero = RealVal(1), RealVal(0)
    if tnorm == "lukasiewicz":
        return {
            "neg": lambda a: one - a,
            "sconj": lambda a, b: _z3_max(zero, a + b - one),
            "sdisj": lambda a, b: _z3_min(one, a + b),
            "impl": lambda a, b: _z3_min(one, one - a + b),
        }
    if tnorm == "godel":
        return {
            "neg": lambda a: If(a <= zero, one, zero),
            "sconj": _z3_min,
            "sdisj": _z3_max,
            "impl": lambda a, b: If(a <= b, one, b),
        }
    if tnorm == "product":
        raise NotImplementedError(
            "z3_fuzzy: the product t-norm needs nonlinear real arithmetic (x·y, y/x) "
            "that Z3 cannot decide completely; use semantics.fuzzy.evaluate(..., "
            "tnorm='product') for evaluation, or the lukasiewicz / godel deciders.")
    raise ValueError(f"z3_fuzzy: unknown t-norm {tnorm!r} (use lukasiewicz / godel).")


# =========================
# Atom collection & degree encoding
# =========================

def _collect_atoms(formula: Node, atom_vars: dict) -> None:
    """Populate atom_vars: {atom-key -> z3 Real} for every ground atom in formula.

    The key is the atom's ``to_unicode_str()`` so two structurally identical
    ground atoms share a single Z3 variable. Mutates atom_vars in place (it is
    private working state owned by the caller, never a user input).
    """
    if isinstance(formula, (Quantifier, SortedQuantifier)):
        raise NotImplementedError(
            "z3_fuzzy handles propositional (quantifier-free) Łukasiewicz "
            "formulas only. Ground the quantifier(s) into a finite "
            "conjunction/disjunction over the domain first, then decide the "
            "resulting propositional formula."
        )
    if isinstance(formula, Atom):
        key = formula.to_unicode_str()
        if key not in atom_vars:
            atom_vars[key] = Real(f"fuzzy!{key}")
        return
    if isinstance(formula, LukNegation):
        _collect_atoms(formula.formula, atom_vars)
        return
    if isinstance(formula, (WeakConjunction, WeakDisjunction,
                            StrongConjunction, StrongDisjunction,
                            LukImplication, LukEquivalence)):
        _collect_atoms(formula.left, atom_vars)
        _collect_atoms(formula.right, atom_vars)
        return
    raise TypeError(
        f"z3_fuzzy: unsupported node type {type(formula).__name__}. "
        "Expected a propositional Łukasiewicz formula (parse with "
        "MSFLParser(fuzzy=True))."
    )


def _degree(formula: Node, atom_vars: dict, ops: dict):
    """Return a Z3 Real expression for the fuzzy degree of formula under ``ops``.

    atom_vars must already map every ground atom to its Z3 Real (see
    _collect_atoms); ``ops`` are the t-norm's strong-connective builders (see
    :func:`_z3_tnorm_ops`). The weak ∧/∨ are min/max regardless. Pure function over
    the AST: never mutates its inputs.
    """
    if isinstance(formula, Atom):
        return atom_vars[formula.to_unicode_str()]

    if isinstance(formula, LukNegation):
        return ops["neg"](_degree(formula.formula, atom_vars, ops))

    if isinstance(formula, WeakConjunction):
        return _z3_min(_degree(formula.left, atom_vars, ops),
                       _degree(formula.right, atom_vars, ops))

    if isinstance(formula, WeakDisjunction):
        return _z3_max(_degree(formula.left, atom_vars, ops),
                       _degree(formula.right, atom_vars, ops))

    if isinstance(formula, StrongConjunction):
        a = _degree(formula.left, atom_vars, ops)
        b = _degree(formula.right, atom_vars, ops)
        return ops["sconj"](a, b)

    if isinstance(formula, StrongDisjunction):
        a = _degree(formula.left, atom_vars, ops)
        b = _degree(formula.right, atom_vars, ops)
        return ops["sdisj"](a, b)

    if isinstance(formula, LukImplication):
        a = _degree(formula.left, atom_vars, ops)
        b = _degree(formula.right, atom_vars, ops)
        return ops["impl"](a, b)

    if isinstance(formula, LukEquivalence):
        a = _degree(formula.left, atom_vars, ops)
        b = _degree(formula.right, atom_vars, ops)
        # biconditional = min(a → b, b → a), uniform across t-norms.
        return _z3_min(ops["impl"](a, b), ops["impl"](b, a))

    if isinstance(formula, (Quantifier, SortedQuantifier)):
        raise NotImplementedError(
            "z3_fuzzy: a quantifier reached the encoder ungrounded — pass "
            "domain=/sort_universes= so it is grounded into a finite ∧/∨ first."
        )

    raise TypeError(
        f"z3_fuzzy: unsupported node type {type(formula).__name__}. "
        "Expected a propositional Łukasiewicz formula (parse with "
        "MSFLParser(fuzzy=True))."
    )


def degree_expr(formula: Node, tnorm: str = "lukasiewicz",
                domain=None, sort_universes=None):
    """Build the Z3 degree expression and unit-interval constraints for formula.

    Returns a triple ``(expr, constraints, atom_vars)`` where:

    * ``expr`` is a Z3 ``Real`` expression for the formula's truth degree under
      the chosen ``tnorm`` (``"lukasiewicz"`` or ``"godel"``),
    * ``constraints`` is a list of ``0 <= v`` and ``v <= 1`` bounds, one pair
      per distinct ground atom,
    * ``atom_vars`` maps each atom key (its ``to_unicode_str()``) to its Z3
      ``Real`` variable.

    A quantified formula is first **grounded** over ``domain`` (unsorted ∀x/∃x) and
    ``sort_universes`` (sorted quantifiers) into a finite weak ∧/∨, so quantified
    fuzzy validity / satisfiability becomes decidable. Without the matching universe
    a quantifier raises ``ValueError``.
    """
    ops = _z3_tnorm_ops(tnorm)
    if formula.count(Quantifier) or formula.count(SortedQuantifier):
        from ..semantics.fuzzy import ground_quantifiers
        formula = ground_quantifiers(formula, domain=domain, sort_universes=sort_universes)
    atom_vars: dict = {}
    _collect_atoms(formula, atom_vars)
    expr = _degree(formula, atom_vars, ops)
    constraints = []
    for v in atom_vars.values():
        constraints.append(v >= RealVal(0))
        constraints.append(v <= RealVal(1))
    return expr, constraints, atom_vars


# =========================
# Internal numeric helpers
# =========================

def _to_fraction(threshold) -> Fraction:
    """Coerce a Python number to an exact Fraction for a rational Z3 bound."""
    return Fraction(threshold).limit_denominator(10 ** 9)


def _rng_value(model, var):
    """Read a Z3 Real assignment as an exact Python Fraction.

    Z3 may leave a variable unconstrained (don't-care); model.eval with
    completion fills such a variable with a concrete rational so the returned
    degree map is always total.
    """
    val = model.eval(var, model_completion=True)
    num = val.numerator_as_long()
    den = val.denominator_as_long()
    return Fraction(num, den)


# =========================
# Public API
# =========================

def fuzzy_is_satisfiable(formula: Node, threshold: float = 1.0,
                         strict: bool = False, timeout: int = 10000,
                         tnorm: str = "lukasiewicz",
                         domain=None, sort_universes=None) -> bool:
    """Return True iff some atom-valuation makes the degree reach the threshold.

    With ``strict=False`` (default) the requirement is ``degree >= threshold``;
    with ``strict=True`` it is ``degree > threshold``. Each ground atom ranges
    over [0, 1]. A Z3 ``unknown`` result (e.g. on timeout) returns False.

    ``tnorm`` selects the strong-connective semantics (``"lukasiewicz"`` / ``"godel"``);
    a quantified formula is grounded over ``domain`` / ``sort_universes`` first.
    """
    expr, constraints, _ = degree_expr(formula, tnorm, domain, sort_universes)
    thr = RealVal(_to_fraction(threshold))

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Z3And(*constraints) if constraints else True)
    solver.add(expr > thr if strict else expr >= thr)
    return solver.check() == sat


def fuzzy_is_valid(formula: Node, timeout: int = 10000,
                   tnorm: str = "lukasiewicz",
                   domain=None, sort_universes=None) -> bool:
    """Return True iff the formula has degree 1 under every atom-valuation.

    Checks validity by asserting ``degree < 1`` together with the [0, 1] atom
    bounds: if that is unsatisfiable, no valuation drops the degree below 1, so
    the formula is valid. A Z3 ``unknown`` result returns False.

    ``tnorm`` selects the strong-connective semantics (``"lukasiewicz"`` / ``"godel"``);
    a quantified formula is grounded over ``domain`` / ``sort_universes`` first.
    """
    expr, constraints, _ = degree_expr(formula, tnorm, domain, sort_universes)

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Z3And(*constraints) if constraints else True)
    solver.add(expr < RealVal(1))
    return solver.check() == unsat


def fuzzy_get_model(formula: Node, threshold: float = 1.0,
                    timeout: int = 10000, tnorm: str = "lukasiewicz",
                    domain=None, sort_universes=None):
    """Return an atom->degree assignment reaching the threshold, or None.

    On success the returned dict maps each ground-atom key (its
    ``to_unicode_str()``) to a float degree in [0, 1], plus a ``'degree'`` entry
    giving the formula's resulting degree. Returns None if no valuation reaches
    the threshold (``degree >= threshold``) or Z3 cannot decide within timeout.

    ``tnorm`` selects the strong-connective semantics (``"lukasiewicz"`` / ``"godel"``);
    a quantified formula is grounded over ``domain`` / ``sort_universes`` first.
    """
    expr, constraints, atom_vars = degree_expr(formula, tnorm, domain, sort_universes)
    thr = RealVal(_to_fraction(threshold))

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Z3And(*constraints) if constraints else True)
    solver.add(expr >= thr)
    if solver.check() != sat:
        return None

    model = solver.model()
    result = {key: float(_rng_value(model, var))
              for key, var in atom_vars.items()}
    result["degree"] = float(_rng_value(model, expr))
    return result
