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


def _degree(formula: Node, atom_vars: dict):
    """Return a Z3 Real expression for the Łukasiewicz degree of formula.

    atom_vars must already map every ground atom to its Z3 Real (see
    _collect_atoms). Pure function over the AST: never mutates its inputs.
    """
    if isinstance(formula, Atom):
        return atom_vars[formula.to_unicode_str()]

    if isinstance(formula, LukNegation):
        return RealVal(1) - _degree(formula.formula, atom_vars)

    if isinstance(formula, WeakConjunction):
        return _z3_min(_degree(formula.left, atom_vars),
                       _degree(formula.right, atom_vars))

    if isinstance(formula, WeakDisjunction):
        return _z3_max(_degree(formula.left, atom_vars),
                       _degree(formula.right, atom_vars))

    if isinstance(formula, StrongConjunction):
        a = _degree(formula.left, atom_vars)
        b = _degree(formula.right, atom_vars)
        return _z3_max(RealVal(0), a + b - RealVal(1))

    if isinstance(formula, StrongDisjunction):
        a = _degree(formula.left, atom_vars)
        b = _degree(formula.right, atom_vars)
        return _z3_min(RealVal(1), a + b)

    if isinstance(formula, LukImplication):
        a = _degree(formula.left, atom_vars)
        b = _degree(formula.right, atom_vars)
        return _z3_min(RealVal(1), RealVal(1) - a + b)

    if isinstance(formula, LukEquivalence):
        a = _degree(formula.left, atom_vars)
        b = _degree(formula.right, atom_vars)
        # 1 - |a - b|, with |a - b| spelled via If to keep it piecewise-linear.
        return RealVal(1) - If(a >= b, a - b, b - a)

    if isinstance(formula, (Quantifier, SortedQuantifier)):
        raise NotImplementedError(
            "z3_fuzzy handles propositional (quantifier-free) Łukasiewicz "
            "formulas only. Ground the quantifier(s) first."
        )

    raise TypeError(
        f"z3_fuzzy: unsupported node type {type(formula).__name__}. "
        "Expected a propositional Łukasiewicz formula (parse with "
        "MSFLParser(fuzzy=True))."
    )


def degree_expr(formula: Node):
    """Build the Z3 degree expression and unit-interval constraints for formula.

    Returns a triple ``(expr, constraints, atom_vars)`` where:

    * ``expr`` is a Z3 ``Real`` expression for the formula's truth degree,
    * ``constraints`` is a list of ``0 <= v`` and ``v <= 1`` bounds, one pair
      per distinct ground atom,
    * ``atom_vars`` maps each atom key (its ``to_unicode_str()``) to its Z3
      ``Real`` variable.

    Raises ``NotImplementedError`` if the formula contains a quantifier.
    """
    atom_vars: dict = {}
    _collect_atoms(formula, atom_vars)
    expr = _degree(formula, atom_vars)
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
                         strict: bool = False, timeout: int = 10000) -> bool:
    """Return True iff some atom-valuation makes the degree reach the threshold.

    With ``strict=False`` (default) the requirement is ``degree >= threshold``;
    with ``strict=True`` it is ``degree > threshold``. Each ground atom ranges
    over [0, 1]. A Z3 ``unknown`` result (e.g. on timeout) returns False.

    Raises ``NotImplementedError`` if the formula contains a quantifier.
    """
    expr, constraints, _ = degree_expr(formula)
    thr = RealVal(_to_fraction(threshold))

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Z3And(*constraints) if constraints else True)
    solver.add(expr > thr if strict else expr >= thr)
    return solver.check() == sat


def fuzzy_is_valid(formula: Node, timeout: int = 10000) -> bool:
    """Return True iff the formula has degree 1 under every atom-valuation.

    Checks validity by asserting ``degree < 1`` together with the [0, 1] atom
    bounds: if that is unsatisfiable, no valuation drops the degree below 1, so
    the formula is valid. A Z3 ``unknown`` result returns False.

    Raises ``NotImplementedError`` if the formula contains a quantifier.
    """
    expr, constraints, _ = degree_expr(formula)

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Z3And(*constraints) if constraints else True)
    solver.add(expr < RealVal(1))
    return solver.check() == unsat


def fuzzy_get_model(formula: Node, threshold: float = 1.0,
                    timeout: int = 10000):
    """Return an atom->degree assignment reaching the threshold, or None.

    On success the returned dict maps each ground-atom key (its
    ``to_unicode_str()``) to a float degree in [0, 1], plus a ``'degree'`` entry
    giving the formula's resulting degree. Returns None if no valuation reaches
    the threshold (``degree >= threshold``) or Z3 cannot decide within timeout.

    Raises ``NotImplementedError`` if the formula contains a quantifier.
    """
    expr, constraints, atom_vars = degree_expr(formula)
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
