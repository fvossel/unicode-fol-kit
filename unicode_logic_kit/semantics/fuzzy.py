"""Łukasiewicz fuzzy evaluator: truth DEGREE in [0, 1] of an FL/MSFL formula.

The evaluator interprets the Łukasiewicz operators over the real interval
[0, 1] under a *valuation* — a mapping from ground atoms (keyed by their
canonical ``to_unicode_str()`` rendering, e.g. ``'P(alice)'``) to degrees. A sorted constant
``alice:Person`` is the constant ``alice``, so ``Tall(alice:Person)`` has the key
``'Tall(alice)'`` -- the key the grounding of ``∀x:Person Tall(x)`` gives its instance at
``alice`` -- and two different atoms that print alike (the numeral ``1`` and a constant named
``1``) are refused by name.

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
from ..fol._atom_keys import AtomKeys, atom_key
from ..fol._truth_constants import truth_value as _truth_value
from .tnorm import get_tnorm

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
                     descriptor: str, tnorm: str,
                     keys: Optional[AtomKeys] = None) -> float:
    """Evaluate a quantifier by grounding ``var_name`` over ``universe``.

    ``qtype`` is ``'∀'`` (infimum = min) or ``'∃'`` (supremum = max) — the lattice
    inf/sup, independent of the t-norm. ``descriptor`` names the universe source for
    error messages.
    """
    if not universe:
        raise ValueError(
            f"Cannot evaluate quantifier over an empty {descriptor}; "
            "provide at least one element."
        )
    degrees = [
        _evaluate(_ground(body, var_name, d), valuation, domain, sort_universes, tnorm, keys)
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
             sort_universes: Optional[Dict[str, Set[str]]] = None,
             tnorm: str = "lukasiewicz") -> float:
    """Compute the fuzzy truth degree in [0, 1] of an FL/MSFL formula.

    Args:
        node: an FL or MSFL formula node. Build it with
            ``MSFLParser(fuzzy=True)`` (unsorted FL) or
            ``MSFLParser(many_sorted=True, fuzzy=True)`` (sorted MSFL).
        valuation: maps a ground atom's canonical key — its
            ``to_unicode_str()`` rendering, e.g. ``'P(alice)'`` — to a degree in
            [0, 1]. A missing key raises ``KeyError`` with a helpful message. A sorted
            constant ``alice:Person`` is the constant ``alice``: ``Tall(alice:Person)``
            has the key ``'Tall(alice)'``, the key the grounding of ``∀x:Person Tall(x)``
            gives its instance at ``alice``.
        domain: a set of constant-name strings over which unsorted quantifiers
            range. Required whenever a ``Quantifier`` is evaluated.
        sort_universes: maps each sort name to its set of constant-name strings;
            ``SortedQuantifier`` ranges over the universe of its sort.
        tnorm: which continuous t-norm fixes the **strong** connectives ⊗ ⊕ → ¬ ↔
            — ``"lukasiewicz"`` (default), ``"godel"`` or ``"product"``. The weak
            ∧ / ∨ are always min / max, and ∀ / ∃ always inf / sup, regardless.

    Returns:
        The truth degree as a float clamped to [0, 1].

    Raises:
        KeyError: a ground atom's key is absent from the valuation.
        ValueError: a quantifier lacks its domain / sort universe, or one is empty,
            or ``tnorm`` is unknown.
        TypeError: the node carries a classical connective, lambda construct,
            numeric literal, comparison atom, or otherwise unsupported type.
        NotImplementedError: two different atoms print alike (the numeral ``1`` and a
            constant named ``1``, a free variable ``x`` and a constant named ``x``), which
            one key of the valuation could not tell apart.
        ValueError: also for a sorted constant ``c:S`` whose name ``sort_universes[S]``
            does not hold (see :func:`check_sorted_constants`).
    """
    check_sorted_constants(node, sort_universes, "evaluate")
    return _evaluate(node, valuation, domain, sort_universes, tnorm, AtomKeys("evaluate"))


def check_sorted_constants(node: Node, sort_universes: Optional[Dict[str, Set[str]]],
                           where: str) -> None:
    """Refuse a sorted constant that the universe given for its sort does not hold.

    ``c:S`` denotes an element of ``S``, and here an element of a universe is named by its
    constant. A universe for ``S`` without ``c`` therefore contradicts the formula, and
    deciding it anyway reads ``c`` as something outside ``S``: over ``Person = {carol}``
    the valid ``(∀x:Person Tall(x)) → Tall(alice:Person)`` would come out not valid
    (``Tall(carol) = 1``, ``Tall(alice) = 0``). A sort with no universe given puts no
    condition on its constants.

    Raises:
        ValueError: ``node`` holds a sorted constant ``c:S``, ``sort_universes`` has an
            entry for ``S``, and ``c`` is not in it.
    """
    if not sort_universes:
        return
    for term in node.walk():
        if (isinstance(term, SortedConstant) and term.sort in sort_universes
                and term.name not in sort_universes[term.sort]):
            raise ValueError(
                f"{where}: the sorted constant {term.name}:{term.sort} names an element that "
                f"sort_universes[{term.sort!r}] = {sorted(sort_universes[term.sort])} does not "
                f"hold. A sorted constant is an element of its sort, so the universe and the "
                f"formula contradict each other: add {term.name!r} to that universe, or write "
                f"the constant without the sort.")


def _reject_comparison_atom(node: Node, route: str = "the fuzzy evaluator") -> None:
    """Refuse a comparison atom (``=``, ``≠``, ``<``, ``>``, ``≤``, ``≥``) by name.

    A comparison has no Łukasiewicz truth degree under a propositional valuation, and a
    route that read one as a letter of its own would decide ``a = a`` as it decides ``P``
    (not valid). The evaluator and the Z3 deciders of the fuzzy route share this refusal.

    Raises:
        TypeError: ``node`` is an atom whose predicate is a comparison symbol.
    """
    if isinstance(node, Atom) and node.predicate in _COMPARISON_PREDS:
        raise TypeError(
            f"Comparison atom {node.to_unicode_str()!r} has no Łukasiewicz "
            f"truth degree; {route} only handles propositional predicate atoms."
        )


def _evaluate(node: Node, valuation: Dict[str, float], domain: Optional[Set[str]],
              sort_universes: Optional[Dict[str, Set[str]]], tnorm: str,
              keys: Optional[AtomKeys]) -> float:
    """The body of :func:`evaluate`; ``keys`` records and checks the key of every atom reached."""
    t = get_tnorm(tnorm)
    # --- Atoms (the base case) --------------------------------------------
    if isinstance(node, Atom):
        constant = _truth_value(node)
        if constant is not None:
            # `$true` / `$false` are the top and the bottom degree under every valuation.
            return 1.0 if constant else 0.0
        _reject_comparison_atom(node)
        key = atom_key(node) if keys is None else keys.key(node)
        if key not in valuation:
            raise KeyError(
                f"No degree for ground atom {key!r} in the valuation. "
                "Provide valuation[{!r}] as a number in [0, 1].".format(key)
            )
        return _clamp(float(valuation[key]))

    # --- strong negation (t-norm residual negation; involutive for Łukasiewicz) -
    if isinstance(node, LukNegation):
        x = _evaluate(node.formula, valuation, domain, sort_universes, tnorm, keys)
        return _clamp(t.neg(x))

    # --- binary connectives (weak ∧/∨ are min/max; strong ⊗⊕→↔ are the t-norm's) -
    if isinstance(node, (WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        x = _evaluate(node.left, valuation, domain, sort_universes, tnorm, keys)
        y = _evaluate(node.right, valuation, domain, sort_universes, tnorm, keys)
        if isinstance(node, WeakConjunction):
            return _clamp(min(x, y))
        if isinstance(node, WeakDisjunction):
            return _clamp(max(x, y))
        if isinstance(node, StrongConjunction):
            return _clamp(t.conj(x, y))
        if isinstance(node, StrongDisjunction):
            return _clamp(t.disj(x, y))
        if isinstance(node, LukImplication):
            return _clamp(t.impl(x, y))
        # LukEquivalence
        return _clamp(t.equiv(x, y))

    # --- Quantifiers -------------------------------------------------------
    if isinstance(node, Quantifier):
        if domain is None:
            raise ValueError(
                "Evaluating an unsorted Quantifier requires a 'domain' "
                "(a set of constant-name strings)."
            )
        return _eval_quantifier(node.type, node.variable.name, node.formula,
                                set(domain), valuation, domain, sort_universes,
                                descriptor="domain", tnorm=tnorm, keys=keys)

    if isinstance(node, SortedQuantifier):
        if sort_universes is None or node.sort not in sort_universes:
            raise ValueError(
                f"Evaluating a SortedQuantifier over sort {node.sort!r} requires "
                f"'sort_universes[{node.sort!r}]' (a set of constant-name strings)."
            )
        return _eval_quantifier(node.type, node.variable.name, node.formula,
                                set(sort_universes[node.sort]), valuation,
                                domain, sort_universes,
                                descriptor=f"sort universe {node.sort!r}", tnorm=tnorm,
                                keys=keys)

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


def ground_quantifiers(node: Node,
                       domain: Optional[Set[str]] = None,
                       sort_universes: Optional[Dict[str, Set[str]]] = None) -> Node:
    """Return a quantifier-free copy of ``node`` by grounding ∀/∃ over their universe.

    ``∀x φ`` becomes the **weak**-conjunction fold (min = infimum) of ``φ[x:=d]`` over
    the domain, ``∃x φ`` the weak-disjunction fold (max = supremum) — the finite-domain
    reading of the fuzzy quantifiers. This lets the Z3 decider (:mod:`atp.z3_fuzzy`)
    handle quantified fuzzy formulas: ground first, then decide the propositional result.

    ``domain`` supplies the universe for unsorted ``∀x``/``∃x``; ``sort_universes`` maps
    each sort to its universe for ``SortedQuantifier``. Raises ValueError if a needed
    universe is missing or empty.
    """
    if isinstance(node, Quantifier):
        if not domain:
            raise ValueError("Grounding an unsorted Quantifier requires a non-empty 'domain'.")
        insts = [ground_quantifiers(_ground(node.formula, node.variable.name, d),
                                    domain, sort_universes) for d in sorted(domain)]
        return _fold_quantifier(node.type, insts)
    if isinstance(node, SortedQuantifier):
        if sort_universes is None or not sort_universes.get(node.sort):
            raise ValueError(
                f"Grounding a SortedQuantifier over sort {node.sort!r} requires a "
                f"non-empty 'sort_universes[{node.sort!r}]'.")
        insts = [ground_quantifiers(_ground(node.formula, node.variable.name, d),
                                    domain, sort_universes)
                 for d in sorted(sort_universes[node.sort])]
        return _fold_quantifier(node.type, insts)
    if isinstance(node, LukNegation):
        return LukNegation(ground_quantifiers(node.formula, domain, sort_universes))
    if isinstance(node, (WeakConjunction, WeakDisjunction,
                         StrongConjunction, StrongDisjunction,
                         LukImplication, LukEquivalence)):
        return type(node)(ground_quantifiers(node.left, domain, sort_universes),
                          ground_quantifiers(node.right, domain, sort_universes))
    # Atoms and terms have no quantifier to ground.
    return node


def _fold_quantifier(qtype: str, insts) -> Node:
    """Fold instances with weak ∧ (∀ = inf) or weak ∨ (∃ = sup)."""
    op = WeakConjunction if qtype in ("∀", "forall") else WeakDisjunction
    acc = insts[0]
    for nxt in insts[1:]:
        acc = op(acc, nxt)
    return acc
