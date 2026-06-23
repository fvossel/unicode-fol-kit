"""Lambda elimination, single-step reduction, and well-formedness for the export pipeline.

Lambda terms (``Lambda`` / ``Application`` / ``LambdaVar``) cannot be exported to
Z3, Prover9, or TPTP, nor fed to the classical normal-form passes, because those
back-ends understand only first-order constructs. This module bridges the gap:

- ``has_lambdas``    — predicate: does any lambda construct occur anywhere?
- ``eliminate_lambdas`` — beta-eta normalize, fold residual applied predicates /
  functions back into ``Atom`` / ``Function`` calls, and verify the result is
  lambda-free (raising ``ValueError`` on a stuck / partially-applied term).
- ``beta_reduce_step`` — contract exactly ONE leftmost-outermost beta-redex.
- ``reduce_trace``    — the list of intermediate terms from the original to the
  beta-normal form, one ``beta_reduce_step`` apart (teaching / debugging aid).

All functions are purely functional: inputs are never mutated and every returned
node is freshly built.  ``eliminate_lambdas`` produces a node ready for
``to_fol`` / ``to_z3`` / ``to_prover9`` / ``to_tptp`` and the normal-form API.
"""

from .nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    substitute, beta_eta_normalize, ReductionLimitError,
)


# ---------------------------------------------------------------------------
# Lambda detection
# ---------------------------------------------------------------------------

def has_lambdas(node: Node) -> bool:
    """Return True iff any Lambda, Application, or LambdaVar occurs anywhere in node.

    Pure structural scan; the input is never mutated.
    """
    if isinstance(node, (Lambda, Application, LambdaVar)):
        return True
    if isinstance(node, (Variable, Constant, Number, SortedConstant)):
        return False
    if isinstance(node, (Atom, Function)):
        return any(has_lambdas(a) for a in node.args)
    if isinstance(node, (Not, LukNegation)):
        return has_lambdas(node.formula)
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                         WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        return has_lambdas(node.left) or has_lambdas(node.right)
    if isinstance(node, (Quantifier, SortedQuantifier)):
        return has_lambdas(node.formula)
    return False


# ---------------------------------------------------------------------------
# Applicative collapse (fold residual Applications back into Atom/Function calls)
# ---------------------------------------------------------------------------
#
# Beta-reduction can leave an Application whose head is an applied predicate or
# symbol rather than a Lambda, e.g. substituting the nullary predicate
# Atom('Q', []) for P in (λP. P(x))(Q) yields Application(Atom('Q', []), x).
# That is not a redex, but it is the curried spelling of the first-order call
# Q(x).  This pass un-curries such spines back into Atom / Function nodes so the
# result is lambda-free and exportable.  A spine whose head is a (free) LambdaVar
# is genuinely stuck and is left untouched for eliminate_lambdas to reject.

def _spine(node: Application):
    """Uncurry a left-nested Application into (head, [arg0, arg1, ...])."""
    args = []
    n: Node = node
    while isinstance(n, Application):
        args.append(n.arg)
        n = n.func
    args.reverse()
    return n, args


def _collapse(node: Node) -> Node:
    """Recursively fold residual applied-predicate / applied-symbol spines.

    Returns a new node.  Application spines headed by an Atom (a predicate name)
    become Atom calls; spines headed by a first-order symbol (Constant / Variable
    / Function) become Function calls.  Spines headed by a Lambda or LambdaVar are
    rebuilt unchanged (the Lambda case cannot survive normalization; the LambdaVar
    case is the stuck term reported later).
    """
    if isinstance(node, (Variable, LambdaVar, Constant, Number, SortedConstant)):
        return node
    if isinstance(node, Atom):
        return Atom(node.predicate, [_collapse(a) for a in node.args])
    if isinstance(node, Function):
        return Function(node.name, [_collapse(a) for a in node.args])
    if isinstance(node, Application):
        head, args = _spine(node)
        head = _collapse(head)
        args = [_collapse(a) for a in args]
        if isinstance(head, Atom) and not head.args:
            # Applied predicate name: Q  ·  args  →  Q(args)
            return Atom(head.predicate, args)
        if isinstance(head, Constant):
            # Applied first-order constant: f  ·  args  →  f(args)
            return Function(head.name, args)
        if isinstance(head, (Variable, Function)):
            name = head.name
            existing = head.args if isinstance(head, Function) else []
            return Function(name, list(existing) + args)
        # head is a Lambda or LambdaVar: rebuild the spine verbatim.
        result: Node = head
        for a in args:
            result = Application(result, a)
        return result
    if isinstance(node, Lambda):
        return Lambda(node.param, _collapse(node.body))
    if isinstance(node, (Not, LukNegation)):
        return type(node)(_collapse(node.formula))
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                         WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        return type(node)(_collapse(node.left), _collapse(node.right))
    if isinstance(node, Quantifier):
        return Quantifier(node.type, node.variable, _collapse(node.formula))
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _collapse(node.formula))
    return node


def _find_leftover(node: Node):
    """Return the first Lambda / Application / LambdaVar found (pre-order), or None."""
    if isinstance(node, (Lambda, Application, LambdaVar)):
        return node
    if isinstance(node, (Variable, Constant, Number, SortedConstant)):
        return None
    if isinstance(node, (Atom, Function)):
        for a in node.args:
            found = _find_leftover(a)
            if found is not None:
                return found
        return None
    if isinstance(node, (Not, LukNegation)):
        return _find_leftover(node.formula)
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                         WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        return _find_leftover(node.left) or _find_leftover(node.right)
    if isinstance(node, (Quantifier, SortedQuantifier)):
        return _find_leftover(node.formula)
    return None


# ---------------------------------------------------------------------------
# Lambda elimination
# ---------------------------------------------------------------------------

def eliminate_lambdas(node: Node) -> Node:
    """Return a lambda-free node ready for the FOL export / normal-form pipeline.

    The node is first beta-eta normalized, then residual applied-predicate and
    applied-symbol spines are folded back into Atom / Function calls.  If any
    Lambda, Application, or LambdaVar still remains (a partially applied or stuck
    term — e.g. a free higher-order variable applied to arguments), a ValueError
    naming the leftover construct is raised.

    Raises:
        ReductionLimitError: if normalization does not terminate within limits.
        ValueError: if the normalized node is not lambda-free.

    Returns:
        A lambda-free Node; the input is never mutated.
    """
    normalized = beta_eta_normalize(node)   # may raise ReductionLimitError
    collapsed = _collapse(normalized)
    leftover = _find_leftover(collapsed)
    if leftover is not None:
        raise ValueError(
            f"eliminate_lambdas: term is not lambda-free after normalization; "
            f"leftover {type(leftover).__name__} "
            f"(a partially applied / stuck lambda term): {leftover}"
        )
    return collapsed


# ---------------------------------------------------------------------------
# Single-step (leftmost-outermost) beta-reduction
# ---------------------------------------------------------------------------

def beta_reduce_step(node: Node) -> tuple:
    """Contract the single leftmost-outermost beta-redex in node.

    Performs at most ONE contraction: it walks the term in normal order (the
    whole application before its sub-terms), and contracts the first
    Application(Lambda(p, body), arg) it meets via capture-avoiding substitute().

    Returns:
        (new_node, reduced) where reduced is True iff a redex was contracted.
        When reduced is False the node is already in beta-normal form and is
        returned unchanged (the same object).  The input is never mutated.
    """
    if isinstance(node, Application):
        func, reduced = beta_reduce_step(node.func)
        if reduced:
            # A redex strictly to the left (inside func) is contracted first.
            return Application(func, node.arg), True
        if isinstance(node.func, Lambda):
            # This application itself is the leftmost-outermost redex.
            contracted = substitute(node.func.body, node.func.param, node.arg)
            return contracted, True
        arg, reduced = beta_reduce_step(node.arg)
        if reduced:
            return Application(node.func, arg), True
        return node, False

    if isinstance(node, Lambda):
        body, reduced = beta_reduce_step(node.body)
        return (Lambda(node.param, body), True) if reduced else (node, False)

    if isinstance(node, Quantifier):
        formula, reduced = beta_reduce_step(node.formula)
        return (Quantifier(node.type, node.variable, formula), True) if reduced else (node, False)

    if isinstance(node, SortedQuantifier):
        formula, reduced = beta_reduce_step(node.formula)
        if reduced:
            return SortedQuantifier(node.type, node.variable, node.sort, formula), True
        return node, False

    if isinstance(node, (Not, LukNegation)):
        formula, reduced = beta_reduce_step(node.formula)
        return (type(node)(formula), True) if reduced else (node, False)

    if isinstance(node, (And, Or, Xor, Implies, Iff,
                         WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        left, reduced = beta_reduce_step(node.left)
        if reduced:
            return type(node)(left, node.right), True
        right, reduced = beta_reduce_step(node.right)
        if reduced:
            return type(node)(node.left, right), True
        return node, False

    if isinstance(node, (Atom, Function)):
        new_args = list(node.args)
        for i, a in enumerate(node.args):
            new_arg, reduced = beta_reduce_step(a)
            if reduced:
                new_args[i] = new_arg
                if isinstance(node, Atom):
                    return Atom(node.predicate, new_args), True
                return Function(node.name, new_args), True
        return node, False

    # Variable / LambdaVar / Constant / Number / SortedConstant and unknowns.
    return node, False


# ---------------------------------------------------------------------------
# Reduction trace
# ---------------------------------------------------------------------------

def reduce_trace(node: Node, limit: int = 1000) -> list:
    """Return the leftmost-outermost reduction trace from node to beta-normal form.

    The result is [original, after step 1, after step 2, ...], each element one
    ``beta_reduce_step`` apart, ending once no redex remains.  A term already in
    beta-normal form yields a single-element list ``[node]``.

    Args:
        node: the term to reduce.
        limit: maximum number of reduction steps before giving up.

    Raises:
        ReductionLimitError: if more than ``limit`` steps are taken (the term is
            likely not normalizing under this strategy).

    Returns:
        A list of Node snapshots; the input is never mutated.
    """
    trace = [node]
    current = node
    for _ in range(limit):
        nxt, reduced = beta_reduce_step(current)
        if not reduced:
            return trace
        trace.append(nxt)
        current = nxt
    raise ReductionLimitError(
        f"reduce_trace exceeded {limit} steps; term may not be normalizing."
    )
