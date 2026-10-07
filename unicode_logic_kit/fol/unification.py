"""Robinson first-order term unification (with occurs-check).

Computes a most-general unifier (MGU) of two terms, or of two atoms, over the
classical term language: Variable, Constant, Number, Function (and Atom for the
literal case). A substitution is a plain dict mapping a variable NAME (str) to a
term Node. The algorithm is functional: inputs are never mutated, and the input
substitution is copied before any binding is added.

Unification rules:
  - A Variable unifies with any term t, binding its name to t, provided the
    occurs-check passes (the variable does not occur in t under the current
    substitution).
  - Constant and Number unify iff they are equal (same value).
  - Function unify iff they share name and arity and their arguments unify
    pairwise.
  - Atom unify iff they share predicate and arity and their arguments unify
    pairwise.
"""

from typing import Dict, Optional

from .nodes import Variable, Constant, Number, Function, Atom, Node, Measure


def apply_subst(node: Node, subst: Dict[str, Node]) -> Node:
    """Apply substitution subst to node, returning a new node.

    Recurses into Function/Atom arguments. A Variable is replaced by its bound
    term when its name is a key of subst (the replacement is itself substituted
    into, so chained bindings resolve fully); otherwise it is returned
    unchanged. Constants and Numbers are returned unchanged. The input node is
    never mutated.
    """
    if isinstance(node, Variable):
        if node.name in subst:
            return apply_subst(subst[node.name], subst)
        return node
    if isinstance(node, (Constant, Number)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [apply_subst(a, subst) for a in node.args])
    if isinstance(node, Measure):
        # μ(entity, dimension) is an ordinary binary term (lowered to the
        # function measure/2 by the exports): substitute into both slots.
        return Measure(apply_subst(node.entity, subst),
                       apply_subst(node.dimension, subst))
    if isinstance(node, Atom):
        return Atom(node.predicate, [apply_subst(a, subst) for a in node.args])
    raise TypeError(f"apply_subst: unsupported node type {type(node).__name__}")


def _occurs(name: str, term: Node, subst: Dict[str, Node]) -> bool:
    """Return True if the variable name occurs in term after applying subst.

    Used by the occurs-check to reject bindings such as x ↦ f(x) that would
    create an infinite (cyclic) term.
    """
    term = apply_subst(term, subst)
    if isinstance(term, Variable):
        return term.name == name
    if isinstance(term, (Function, Atom)):
        return any(_occurs(name, a, subst) for a in term.args)
    if isinstance(term, Measure):
        return (_occurs(name, term.entity, subst)
                or _occurs(name, term.dimension, subst))
    return False


def _bind(name: str, term: Node, subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Extend subst with the binding name ↦ term, with occurs-check.

    Returns a new substitution dict (the input is copied, never mutated), or
    None if the occurs-check fails. Binding a variable to itself is a no-op that
    leaves the substitution unchanged.
    """
    if isinstance(term, Variable) and term.name == name:
        return subst
    if _occurs(name, term, subst):
        return None
    new_subst = dict(subst)
    new_subst[name] = apply_subst(term, subst)
    return new_subst


def unify(t1: Node, t2: Node, subst: Optional[Dict[str, Node]] = None) -> Optional[Dict[str, Node]]:
    """Most-general unifier of t1 and t2, or None if they do not unify.

    Robinson's algorithm with occurs-check. The result is a dict mapping
    variable NAME -> term such that applying it to t1 and t2 (via apply_subst)
    yields structurally equal nodes. An empty dict means the terms are already
    equal / trivially unifiable.

    Accepts Variable, Constant, Number, Function term nodes, or two Atoms (which
    unify iff they share predicate and arity and their arguments unify
    pairwise). The optional subst argument is treated as immutable: it is copied
    before extension, never modified in place.
    """
    if subst is None:
        subst = {}

    t1 = apply_subst(t1, subst)
    t2 = apply_subst(t2, subst)

    # Variable on either side: bind it (occurs-check inside _bind).
    if isinstance(t1, Variable):
        return _bind(t1.name, t2, subst)
    if isinstance(t2, Variable):
        return _bind(t2.name, t1, subst)

    # Constants / Numbers: unify iff equal in value.
    if isinstance(t1, (Constant, Number)) or isinstance(t2, (Constant, Number)):
        if type(t1) is type(t2) and _leaf_value(t1) == _leaf_value(t2):
            return subst
        return None

    # Function applications: same name + arity, then unify arguments pairwise.
    if isinstance(t1, Function) and isinstance(t2, Function):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        return _unify_args(t1.args, t2.args, subst)

    # Measure terms: a fixed binary function symbol — unify slot-wise. Purely
    # syntactic: a Measure never unifies with a Function (even one literally
    # named "measure"); the measure/2 spelling is an EXPORT convention, not an
    # AST identity.
    if isinstance(t1, Measure) and isinstance(t2, Measure):
        return _unify_args((t1.entity, t1.dimension),
                           (t2.entity, t2.dimension), subst)

    # Atoms (literal-level unification): same predicate + arity, then args.
    if isinstance(t1, Atom) and isinstance(t2, Atom):
        if t1.predicate != t2.predicate or len(t1.args) != len(t2.args):
            return None
        return _unify_args(t1.args, t2.args, subst)

    return None


def _leaf_value(node: Node):
    """Return the comparable payload of a leaf node (Constant name / Number value)."""
    if isinstance(node, Constant):
        return node.name
    if isinstance(node, Number):
        return node.value
    return None


def _unify_args(args1, args2, subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Unify two equal-length argument lists left-to-right, threading the substitution.

    Returns the accumulated substitution, or None as soon as any pair fails.
    """
    for a, b in zip(args1, args2):
        subst = unify(a, b, subst)
        if subst is None:
            return None
    return subst
