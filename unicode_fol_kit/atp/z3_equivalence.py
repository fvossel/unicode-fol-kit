from ..fol.nodes import Node
from ..fol._msfl_nodes import nonempty_sort_axioms
from z3 import Solver, unsat, set_param, Not


def formulas_are_equivalent(formula1: Node, formula2: Node, timeout: int=10000) -> bool:
    """Return True iff ``formula1`` and ``formula2`` are logically equivalent.

    Asks Z3 to refute ¬(φ ↔ ψ): the two formulas are equivalent exactly when
    that negation is unsatisfiable. The arguments are interchangeable (the check
    is symmetric). Returns False if Z3 finds a model of the negation (the
    formulas differ) or returns ``unknown`` within ``timeout`` milliseconds.

    Every sort occurring in either formula is asserted non-empty alongside the
    negation, as :func:`~unicode_fol_kit.atp.z3_models.is_valid` does: the
    equivalence is decided over legal many-sorted structures, not over ones
    that make a sort empty.
    """

    phi = formula1.to_z3()
    psi = formula2.to_z3()

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    for axiom in nonempty_sort_axioms(formula1, formula2):
        solver.add(axiom.to_z3())
    solver.add(Not(phi==psi))

    result = solver.check()
    if result == unsat:
        return True

    return False
