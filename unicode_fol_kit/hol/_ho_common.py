"""Shared machinery for the two third-order HOL exporters.

:mod:`unicode_fol_kit.hol.thirdorder` (classical) and
:mod:`unicode_fol_kit.hol.ho_modal` (the shallow modal embedding) differ in
exactly one thing: whether a proposition is a truth value or a function from
worlds to truth values. Everything BEFORE that decision is the same work —
renaming bound predicate variables apart so a theory-wide signature analysis
answers the right question, collecting the free symbols that need declaring, and
peeling λ-binders off a property argument — so it lives here rather than twice.
"""

from typing import Dict, List, Sequence, Set, Tuple

from ..fol.nodes import (
    Node, Atom, Quantifier, SecondOrderQuantifier, PredicateTerm,
    Variable, Constant, Function, LambdaVar, Lambda,
)


class UnsupportedHigherOrderNode(NotImplementedError):
    """Raised for an AST node a third-order embedding has no reading for.

    Subclasses NotImplementedError, matching the kit's other export refusals: a
    route that cannot carry a construct says so by name instead of dropping it.
    """


#: Infix comparison predicates become uninterpreted relations, the convention
#: the kit's other HOL exports already follow — NOT primitive HOL identity,
#: which in the modal embedding would additionally be world-independent and so
#: a different logic.
EQUALITY = {"=": "feq", "≠": "fneq", "<": "flt", ">": "fgt", "≤": "fle", "≥": "fge"}


def peel_lambdas(node: Node) -> Tuple[List[str], Node]:
    """Split a (possibly nested) Lambda into its binder names and its body.

    ``λx. λy. φ`` denotes a binary relation, so the number of binders IS the
    arity of the property the argument denotes.
    """
    names = []
    while isinstance(node, Lambda):
        names.append(node.param.name)
        node = node.body
    return names, node


def rename_bound_pred(node: Node, old: str, new: str) -> Node:
    """Rename every occurrence of the predicate variable ``old`` to ``new``.

    Renames it in HEAD position (``Atom``) and in ARGUMENT position
    (``PredicateTerm``) alike, and stops at an inner binder over the same name,
    whose occurrences belong to that binding rather than this one.
    """
    if isinstance(node, SecondOrderQuantifier) and node.predicate == old:
        return node
    if isinstance(node, Atom) and node.predicate == old:
        return Atom(new, [rename_bound_pred(a, old, new) for a in node.args])
    if isinstance(node, PredicateTerm) and node.name == old:
        return PredicateTerm(new)
    return node.map_children(lambda child: rename_bound_pred(child, old, new))


def rename_apart(formulas: Sequence[Node]) -> Tuple[List[Node], Dict[str, str]]:
    """Give every second-order binder a name unique across ``formulas``.

    A theory-wide signature analysis merges by NAME, and a bound variable's name
    is scoped to its own formula: two axioms may each bind ``P`` at a different
    arity without disagreeing about anything, and a binder may even shadow
    another of the same name inside one formula. Renaming apart first is what
    keeps the analysis answering the question that was actually asked — what the
    FREE symbols are, and what arity each binding really has — instead of a
    false conflict between two local bindings.

    Returns the renamed formulas and a ``{fresh name: original name}`` map. The
    renaming is for the ANALYSIS; emission renders the renamed tree but prints
    the original names back through that map, which is sound because the emitted
    binders reproduce the original scoping exactly.
    """
    counter = [0]
    original: Dict[str, str] = {}

    def walk(node: Node) -> Node:
        if isinstance(node, SecondOrderQuantifier):
            counter[0] += 1
            fresh = f"Bound{counter[0]}"
            original[fresh] = node.predicate
            renamed = rename_bound_pred(node.formula, node.predicate, fresh)
            return SecondOrderQuantifier(node.type, fresh, node.arity, walk(renamed))
        return node.map_children(walk)

    return [walk(f) for f in formulas], original


def bound_pred_names(node: Node, acc: Set[str] = None) -> Set[str]:
    """Collect every predicate-variable name bound by a second-order quantifier."""
    acc = set() if acc is None else acc
    if isinstance(node, SecondOrderQuantifier):
        acc.add(node.predicate)
    for child in node._child_nodes():
        bound_pred_names(child, acc)
    return acc


def atom_predicates(node: Node, acc: Set[str] = None) -> Set[str]:
    """Collect every predicate name applied in ``node``."""
    acc = set() if acc is None else acc
    if isinstance(node, Atom):
        acc.add(node.predicate)
    for child in node._child_nodes():
        atom_predicates(child, acc)
    return acc


def function_symbols(formulas: Sequence[Node], acc: Dict[str, int] = None) -> Dict[str, int]:
    """Collect ``{function name: arity}`` over ``formulas``."""
    acc = {} if acc is None else acc
    for node in formulas:
        if isinstance(node, Function):
            acc[node.name] = len(node.args)
        function_symbols(list(node._child_nodes()), acc)
    return acc


def free_individuals(formulas: Sequence[Node]) -> Set[str]:
    """Return the names of individual symbols bound by no quantifier or λ.

    A bare NAME parses to a Constant, and an object variable left unbound by any
    quantifier denotes a particular individual too; a closed HOL theory has no
    free variables, so both are declared as individual constants.
    """
    found: Set[str] = set()

    def walk(node: Node, bound: frozenset) -> None:
        if isinstance(node, Constant):
            found.add(node.name)
            return
        if isinstance(node, Variable):
            if node.name not in bound:
                found.add(node.name)
            return
        if isinstance(node, LambdaVar):
            return
        if isinstance(node, Quantifier):
            walk(node.formula, bound | {node.variable.name})
            return
        if isinstance(node, Lambda):
            walk(node.body, bound | {node.param.name})
            return
        for child in node._child_nodes():
            walk(child, bound)

    for formula in formulas:
        walk(formula, frozenset())
    return found
