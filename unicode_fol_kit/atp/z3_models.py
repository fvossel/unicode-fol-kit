"""Satisfiability / validity checks and model (counterexample) extraction via Z3."""

from ..fol.nodes import Node
from z3 import Solver, sat, unsat, Not


def is_satisfiable(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula has a model (Z3 reports sat).

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-satisfiable and returns False.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(formula.to_z3())
    return solver.check() == sat


def is_valid(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula is valid, i.e. its negation is unsatisfiable.

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-valid and returns False.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Not(formula.to_z3()))
    return solver.check() == unsat


def get_model(formula: Node, timeout: int = 10000):
    """Return a satisfying assignment as a dict, or None if unsat/unknown.

    The dict maps each Z3 declaration name (constants, uninterpreted
    functions/predicates) to the string form of its interpretation. For an
    invalid equivalence or entailment, ``get_model(Not(...))`` yields the
    concrete counterexample. Returns None when the formula is unsatisfiable or
    Z3 cannot decide it within the timeout.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(formula.to_z3())
    if solver.check() != sat:
        return None
    model = solver.model()
    return {str(decl.name()): str(model[decl]) for decl in model.decls()}
