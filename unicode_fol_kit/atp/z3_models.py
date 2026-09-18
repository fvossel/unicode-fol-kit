"""Satisfiability / validity checks and model (counterexample) extraction via Z3.

**Many-sorted (MSFOL) soundness.** ``Node.to_z3()`` relativises a sorted
quantifier/constant/count to plain classical FOL (``fol.nodes.to_fol``,
auto-run by ``SortedQuantifier.to_z3`` etc.) but that relativisation alone
does NOT guarantee a sort's universe is non-empty — and MSFOL, by
convention, never gives a sort an empty one (see the classical-reasoning
guide's many-sorted section). Left unaddressed, Z3 is free to interpret a
sort predicate as always-false, which can turn a genuinely valid many-sorted
formula invalid (or a genuinely unsatisfiable one satisfiable) via a
spurious empty-sort "model" no legal MSFOL structure would ever be. Every
function below closes that gap the same way: it collects
``unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms(formula)`` and adds
them as their own extra, UNCONDITIONAL, never-negated assertions on the
solver — never folded inside ``to_z3()`` itself, which is polarity-blind and
shared with every OTHER caller (see that function's docstring for why). For
an unsorted formula the axiom list is empty, so the Z3 query — and every
one of these functions' return values — is unchanged from before this
soundness fix.
"""

from ..fol._msfl_nodes import nonempty_sort_axioms
from ..fol.nodes import Node
from z3 import Solver, sat, unsat, Not


def _add_nonempty_sort_axioms(solver: Solver, *formulas: Node) -> None:
    """Assert ``nonempty_sort_axioms(*formulas)`` on ``solver``, unconditionally.

    Shared by every function in this module so they can never drift apart on
    how the axioms are added (see the module docstring). A no-op — literally
    zero calls to ``solver.add`` — when none of ``formulas`` is many-sorted.
    """
    for axiom in nonempty_sort_axioms(*formulas):
        solver.add(axiom.to_z3())


def is_satisfiable(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula has a model (Z3 reports sat).

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-satisfiable and returns False. A
    many-sorted ``formula``'s sorts are asserted non-empty alongside it — see
    the module docstring.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(formula.to_z3())
    _add_nonempty_sort_axioms(solver, formula)
    return solver.check() == sat


def is_valid(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula is valid, i.e. its negation is unsatisfiable.

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-valid and returns False. A many-sorted
    ``formula``'s sorts are asserted non-empty as extra, UNNEGATED premises
    alongside the negated goal — see the module docstring; this is what
    makes ``is_valid`` agree with ``semantics.modelfinder`` on many-sorted
    input instead of exploiting an empty-sort loophole modelfinder never
    considers a legal structure.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    _add_nonempty_sort_axioms(solver, formula)
    solver.add(Not(formula.to_z3()))
    return solver.check() == unsat


def get_model(formula: Node, timeout: int = 10000):
    """Return a satisfying assignment as a dict, or None if unsat/unknown.

    The dict maps each Z3 declaration name (constants, uninterpreted
    functions/predicates) to the string form of its interpretation. For an
    invalid equivalence or entailment, ``get_model(Not(...))`` yields the
    concrete counterexample. Returns None when the formula is unsatisfiable or
    Z3 cannot decide it within the timeout. Every many-sorted node's sort
    anywhere in ``formula`` — including under a ``Not(...)`` a caller wraps
    it in — is asserted non-empty alongside it, so a returned model is always
    a legal MSFOL structure (see the module docstring); the returned dict may
    therefore also carry an interpretation for a sort's own predicate.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(formula.to_z3())
    _add_nonempty_sort_axioms(solver, formula)
    if solver.check() != sat:
        return None
    model = solver.model()
    return {str(decl.name()): str(model[decl]) for decl in model.decls()}
