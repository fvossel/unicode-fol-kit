from ..fol.nodes import Node
from z3 import Solver, unsat, set_param, Not


def formulas_are_equivalent(formula1: Node, formula2: Node, timeout: int=10000) -> bool:
    """Return True iff ``formula1`` and ``formula2`` are logically equivalent.

    Asks Z3 to refute ¬(φ ↔ ψ): the two formulas are equivalent exactly when
    that negation is unsatisfiable. The arguments are interchangeable (the check
    is symmetric). Returns False if Z3 finds a model of the negation (the
    formulas differ) or returns ``unknown`` within ``timeout`` milliseconds.
    """

    phi = formula1.to_z3()
    psi = formula2.to_z3()

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(Not(phi==psi))

    result = solver.check()
    if result == unsat:
        return True

    return False
