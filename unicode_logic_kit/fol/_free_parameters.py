"""A free variable is a parameter of the problem: one unknown element, the same everywhere.

The consequence relation the kit reads is the assignment-wise one of the textbooks:
``Γ ⊨ φ`` iff every structure AND assignment that satisfies ``Γ`` satisfies ``φ``. A
variable that is free in a premise or in the conclusion therefore names ONE element,
the same in every formula of the problem. It is not a universally quantified variable
of its own formula: ``P(x) ⊢ P(alpha)`` is not valid (universe ``{0, 1}``, ``x`` ↦ 1,
``alpha`` ↦ 0, ``P`` = ``{1}``), while ``P(x) ⊢ ∃y P(y)`` and ``∀y P(y) ⊢ P(x)`` are.

A route that has no free variables of its own (a resolution prover, a model finder, a
writer for a target that closes every formula) reads this by replacing every free
variable of the whole problem by a constant, before it does anything else:
``Γ(x) ⊨ φ(x)`` assignment-wise iff ``Γ(c) ⊨ φ(c)`` for a constant ``c`` that no
symbol of the problem has. :func:`parameterize` does that, once, for every route that
needs it. For a problem with no premise the reading coincides with the universal
closure of the conclusion.
"""

from typing import Dict, Iterable, List, Sequence, Tuple

from ._identifiers import symbol_names
from .nodes import Node, Constant, SortedConstant, Variable, free_variables, substitute

__all__ = ["free_parameter_names", "parameterize"]


def _free_names(formula: Node) -> frozenset:
    """The names of the object variables that are free in ``formula``."""
    return frozenset(v.name for v in free_variables(formula) if isinstance(v, Variable))


def free_parameter_names(formulas: Iterable[Node]) -> Tuple[str, ...]:
    """The names of the variables that are free in at least one of ``formulas``, sorted.

    A variable is free in a formula when no quantifier, counting quantifier,
    cardinality term or IF-logic binder of that formula binds it; a name that is bound
    in one formula and free in another is in the result. A lambda-bound variable is not
    an object variable and is never in it.
    """
    names: set = set()
    for formula in formulas:
        names |= _free_names(formula)
    return tuple(sorted(names))


def parameterize(formulas: Sequence[Node], *, avoid: Iterable[str] = (),
                 after_variables: bool = False) -> Tuple[List[Node], Dict[str, Constant]]:
    """Replace every free variable of ``formulas`` by a constant, the same one in all of them.

    Returns ``(closed, parameters)``: the formulas with every free occurrence of a
    variable replaced, and a mapping from each variable's name to the constant that
    stands for it. A variable that is bound inside a formula is left alone there (the
    substitution is capture-avoiding), and a name that is free in one formula and bound
    in another is replaced only where it is free. Formulas without a free variable
    come back as they are.

    By default the constants are minted (``_p0``, ``_p1``, …) and none of them has the
    spelling of any name that ``formulas`` carry -- a predicate, function, constant,
    sort, variable or nominal -- nor of any name in ``avoid``, so no constant of the
    problem is captured by a parameter. Pass ``avoid`` for names of a vocabulary the
    problem will be read together with.

    With ``after_variables=True`` the constant carries the variable's own name, so that
    a structure found for the closed formulas reports the parameter under the name the
    caller wrote. A parameter that would then have the name of a constant of the
    problem (``Constant('x')`` next to a free variable ``x``: the Unicode text tells the
    two apart, ``P(x) ∧ Q('x')``, but a structure holds one entry per name) cannot be
    told from that constant in a table keyed by name, so it is refused.

    Raises:
        NotImplementedError: ``after_variables`` is true and a free variable has the
            name of a constant (plain or sorted) of ``formulas``.
    """
    formulas = list(formulas)
    free_per_formula = [_free_names(formula) for formula in formulas]
    names = sorted(set().union(*free_per_formula)) if free_per_formula else []
    if not names:
        return formulas, {}
    parameters: Dict[str, Constant] = {}
    if after_variables:
        constants = {node.name for formula in formulas for node in formula.walk()
                     if isinstance(node, (Constant, SortedConstant))}
        for name in names:
            if name in constants:
                raise NotImplementedError(
                    f"a free variable {name!r} and a constant {name!r} are in one problem: "
                    "a structure holds one entry per name, so the parameter that stands "
                    "for the variable could not be told from the constant. Rename one of "
                    "them.")
            parameters[name] = Constant(name)
    else:
        taken = set(symbol_names(*formulas)) | set(avoid)
        index = 0
        for name in names:
            while f"_p{index}" in taken:
                index += 1
            parameters[name] = Constant(f"_p{index}")
            taken.add(f"_p{index}")
            index += 1
    closed = []
    for formula, free in zip(formulas, free_per_formula):
        for name in sorted(free):
            formula = substitute(formula, Variable(name), parameters[name])
        closed.append(formula)
    return closed, parameters
