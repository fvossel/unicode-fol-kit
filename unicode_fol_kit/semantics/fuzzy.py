"""Łukasiewicz fuzzy evaluator: truth DEGREE in [0, 1] of an FL/MSFL formula.

The evaluator interprets the Łukasiewicz operators over the real interval
[0, 1] under a *valuation* — a mapping from ground atoms (keyed by their
canonical ``to_unicode_str()`` rendering, e.g. ``'P(alice)'``) to degrees.

Łukasiewicz semantics::

    ¬φ            = 1 − x
    weak ∧        = min(x, y)        (WeakConjunction)
    weak ∨        = max(x, y)        (WeakDisjunction)
    strong ⊗      = max(0, x+y−1)    (StrongConjunction, t-norm)
    strong ⊕      = min(1, x+y)      (StrongDisjunction, t-conorm)
    →             = min(1, 1−x+y)    (LukImplication)
    ↔             = 1 − |x−y|        (LukEquivalence)

Quantifiers range over a domain of constant names: ``∀`` is the infimum (min
over the domain) and ``∃`` the supremum (max). The bound variable is grounded
by substituting ``Variable(v.name)`` with ``Constant(d)`` for each domain
element ``d`` before recursing.

Classical boolean nodes (And/Or/Not/Implies/Iff/Xor) are intentionally
rejected: a formula meant for fuzzy evaluation must be parsed in FL or MSFL
mode so its connectives carry unambiguous Łukasiewicz semantics. Lambda nodes,
numeric literals, and comparison atoms are likewise rejected.

Parse inputs with::

    MSFLParser(fuzzy=True)                    # FL  (unsorted)
    MSFLParser(many_sorted=True, fuzzy=True)  # MSFL (sorted)
"""

from typing import Optional, Set, Dict

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function, Atom,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

# Comparison predicates have no Łukasiewicz reading under a propositional
# valuation; they are rejected rather than silently treated as opaque atoms.
_COMPARISON_PREDS = frozenset({"=", "≠", "<", ">", "≤", "≥"})

# Classical connective classes that must not appear in fuzzy input.
_CLASSICAL_CONNECTIVES = (And, Or, Not, Implies, Iff, Xor)

# Lambda-calculus classes that have no truth degree.
_LAMBDA_NODES = (LambdaVar, Lambda, Application)


def _clamp(x: float) -> float:
    """Defensively clamp a degree into the closed interval [0, 1]."""
    if x < 0.0:
        return 0.0
    if x > 1.0:
        return 1.0
    return x


def _ground_term(node: Node, var_name: str, const_name: str) -> Node:
    """Replace every free ``Variable(var_name)`` in a *term* with ``Constant(const_name)``.

    Operates on term-position nodes (Variable, Constant, Number, Function,
    SortedConstant). Returns a new node; the input is never mutated.
    """
    if isinstance(node, Variable):
        return Constant(const_name) if node.name == var_name else node
    if isinstance(node, Function):
        return Function(node.name,
                        [_ground_term(a, var_name, const_name) for a in node.args])
    # Constant, Number, SortedConstant and anything else carry no free Variable.
    return node


def _ground(node: Node, var_name: str, const_name: str) -> Node:
    """Substitute free ``Variable(var_name)`` with ``Constant(const_name)`` throughout.

    Recurses through the full formula structure, stopping at an inner binder
    that rebinds the same variable name (the inner binding shadows ours).
    Returns a new node; the input is never mutated.
    """
    if isinstance(node, Atom):
        return Atom(node.predicate,
                    [_ground_term(a, var_name, const_name) for a in node.args])
    if isinstance(node, (Not, LukNegation)):
        return type(node)(_ground(node.formula, var_name, const_name))
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                         WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        return type(node)(_ground(node.left, var_name, const_name),
                          _ground(node.right, var_name, const_name))
    if isinstance(node, Quantifier):
        if node.variable.name == var_name:
            return node  # inner binder shadows the variable we are grounding
        return Quantifier(node.type, node.variable,
                          _ground(node.formula, var_name, const_name))
    if isinstance(node, SortedQuantifier):
        if node.variable.name == var_name:
            return node
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _ground(node.formula, var_name, const_name))
    # Term-position nodes (rare at formula top level) and leaves pass through
    # the term grounder so a bare quantified variable is still handled.
    return _ground_term(node, var_name, const_name)


def _eval_quantifier(qtype: str, var_name: str, body: Node,
                     universe: Set[str], valuation: Dict[str, float],
                     domain: Optional[Set[str]],
                     sort_universes: Optional[Dict[str, Set[str]]],
                     descriptor: str) -> float:
    """Evaluate a quantifier by grounding ``var_name`` over ``universe``.

    ``qtype`` is ``'∀'`` (infimum = min) or ``'∃'`` (supremum = max).
    ``descriptor`` names the universe source for error messages.
    """
    if not universe:
        raise ValueError(
            f"Cannot evaluate quantifier over an empty {descriptor}; "
            "provide at least one element."
        )
    degrees = [
        evaluate(_ground(body, var_name, d), valuation,
                 domain=domain, sort_universes=sort_universes)
        for d in universe
    ]
    if qtype in ("∀", "forall"):
        return min(degrees)
    if qtype in ("∃", "exists"):
        return max(degrees)
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def evaluate(node: Node,
             valuation: Dict[str, float],
             domain: Optional[Set[str]] = None,
             sort_universes: Optional[Dict[str, Set[str]]] = None) -> float:
    """Compute the Łukasiewicz truth degree in [0, 1] of an FL/MSFL formula.

    Args:
        node: an FL or MSFL formula node. Build it with
            ``MSFLParser(fuzzy=True)`` (unsorted FL) or
            ``MSFLParser(many_sorted=True, fuzzy=True)`` (sorted MSFL).
        valuation: maps a ground atom's canonical key — its
            ``to_unicode_str()`` rendering, e.g. ``'P(alice)'`` — to a degree in
            [0, 1]. A missing key raises ``KeyError`` with a helpful message.
        domain: a set of constant-name strings over which unsorted quantifiers
            range. Required whenever a ``Quantifier`` is evaluated.
        sort_universes: maps each sort name to its set of constant-name strings;
            ``SortedQuantifier`` ranges over the universe of its sort.

    Returns:
        The truth degree as a float clamped to [0, 1].

    Raises:
        KeyError: a ground atom's key is absent from the valuation.
        ValueError: a quantifier lacks its domain / sort universe, or one is empty.
        TypeError: the node carries a classical connective, lambda construct,
            numeric literal, comparison atom, or otherwise unsupported type.
    """
    # --- Atoms (the base case) --------------------------------------------
    if isinstance(node, Atom):
        if node.predicate in _COMPARISON_PREDS:
            raise TypeError(
                f"Comparison atom {node.to_unicode_str()!r} has no Łukasiewicz "
                "truth degree; the fuzzy evaluator only handles propositional "
                "predicate atoms."
            )
        key = node.to_unicode_str()
        if key not in valuation:
            raise KeyError(
                f"No degree for ground atom {key!r} in the valuation. "
                "Provide valuation[{!r}] as a number in [0, 1].".format(key)
            )
        return _clamp(float(valuation[key]))

    # --- Łukasiewicz negation ---------------------------------------------
    if isinstance(node, LukNegation):
        x = evaluate(node.formula, valuation, domain, sort_universes)
        return _clamp(1.0 - x)

    # --- Łukasiewicz binary connectives -----------------------------------
    if isinstance(node, (WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        x = evaluate(node.left, valuation, domain, sort_universes)
        y = evaluate(node.right, valuation, domain, sort_universes)
        if isinstance(node, WeakConjunction):
            return _clamp(min(x, y))
        if isinstance(node, WeakDisjunction):
            return _clamp(max(x, y))
        if isinstance(node, StrongConjunction):
            return _clamp(max(0.0, x + y - 1.0))
        if isinstance(node, StrongDisjunction):
            return _clamp(min(1.0, x + y))
        if isinstance(node, LukImplication):
            return _clamp(min(1.0, 1.0 - x + y))
        # LukEquivalence
        return _clamp(1.0 - abs(x - y))

    # --- Quantifiers -------------------------------------------------------
    if isinstance(node, Quantifier):
        if domain is None:
            raise ValueError(
                "Evaluating an unsorted Quantifier requires a 'domain' "
                "(a set of constant-name strings)."
            )
        return _eval_quantifier(node.type, node.variable.name, node.formula,
                                set(domain), valuation, domain, sort_universes,
                                descriptor="domain")

    if isinstance(node, SortedQuantifier):
        if sort_universes is None or node.sort not in sort_universes:
            raise ValueError(
                f"Evaluating a SortedQuantifier over sort {node.sort!r} requires "
                f"'sort_universes[{node.sort!r}]' (a set of constant-name strings)."
            )
        return _eval_quantifier(node.type, node.variable.name, node.formula,
                                set(sort_universes[node.sort]), valuation,
                                domain, sort_universes,
                                descriptor=f"sort universe {node.sort!r}")

    # --- Rejected node classes (informative errors) -----------------------
    if isinstance(node, _CLASSICAL_CONNECTIVES):
        raise TypeError(
            f"Classical connective {type(node).__name__} is not valid in fuzzy "
            "input; parse the formula in FL/MSFL mode "
            "(MSFLParser(fuzzy=True) or MSFLParser(many_sorted=True, fuzzy=True)) "
            "so its connectives carry Łukasiewicz semantics."
        )
    if isinstance(node, _LAMBDA_NODES):
        raise TypeError(
            f"{type(node).__name__} (a lambda-calculus construct) has no truth "
            "degree; beta-reduce and eliminate lambdas before fuzzy evaluation."
        )
    if isinstance(node, Number):
        raise TypeError(
            "A bare Number has no truth degree; the fuzzy evaluator expects a "
            "propositional FL/MSFL formula, not an arithmetic term."
        )
    if isinstance(node, (Variable, Constant, SortedConstant, Function)):
        raise TypeError(
            f"{type(node).__name__} is a term, not a formula; the fuzzy "
            "evaluator can only score a formula's truth degree."
        )

    raise TypeError(f"evaluate: unsupported node type {type(node).__name__}")
