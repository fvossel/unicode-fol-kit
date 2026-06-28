"""Three-valued (Kleene K3 / Priest LP) evaluation of classical FOL formulas.

The strong-Kleene tables interpret the classical connectives over the chain
``{0.0, 0.5, 1.0}`` — read as *false*, *undefined/both*, *true*::

    ¬x       = 1 − x
    a ∧ b    = min(a, b)
    a ∨ b    = max(a, b)
    a → b    = max(1 − a, b)                     (material implication)
    a ↔ b    = min(a → b, b → a)
    a ⊕ b    = min(max(a, b), 1 − min(a, b))     (a ∨ b) ∧ ¬(a ∧ b)

These are the *same* truth functions for K3 and LP; the two logics differ only
in which values count as **designated** (truth-preserved):

    K3 designates {1.0}            — only plain truth
    LP designates {0.5, 1.0}       — "true" or "both" (Priest's paraconsistent LP)

That single choice produces the headline contrasts: the law of excluded middle
``P ∨ ¬P`` is K3-invalid but LP-valid, and LP is paraconsistent — ``P, ¬P`` does
*not* entail an arbitrary ``Q`` — while K3 fails non-contradiction validity.

This module operates on **classical** AST nodes (Atom, Not, And, Or, Xor,
Implies, Iff, Quantifier) parsed by ``MSFLParser()`` — no new grammar. Truth
values are the floats ``0.0``, ``0.5`` and ``1.0``. A *valuation* maps a ground
atom's canonical ``to_unicode_str()`` key (e.g. ``'P'`` or ``'P(a)'``) to one of
those three values.

Quantifiers are read substitutionally over a finite ``domain`` of constant
names, exactly as in the fuzzy evaluator: ``∀`` is the minimum and ``∃`` the
maximum of the body's value over the domain (∀ = "all", ∃ = "some"). A domain
is required whenever a quantifier is present.

Łukasiewicz (fuzzy), sorted, lambda, and modal nodes carry no classical
three-valued reading here and raise ``NotImplementedError``.

Parse inputs with ``MSFLParser()`` (classical propositional / FOL).
"""

from itertools import product
from typing import Dict, List, Optional, Sequence, Set

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function, Atom,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
    Lambda, LambdaVar, Application,
    Box, Diamond, Always, Eventually, Next, Until,
    Historically, Once, Previous, Since, Knows, Believes,
)

# The three truth values, smallest first: false < undefined/both < true.
FALSE = 0.0
UNDEFINED = 0.5
TRUE = 1.0
TRUTH_VALUES = (FALSE, UNDEFINED, TRUE)

# Designated (truth-preserved) value sets keyed by logic name.
#   K3 — only plain truth is designated.
#   LP — Priest's Logic of Paradox: both "true" and "both" are designated.
DESIGNATED: Dict[str, frozenset] = {
    "K3": frozenset({TRUE}),
    "LP": frozenset({UNDEFINED, TRUE}),
}

# Safety cap for the validity/satisfiability/entailment enumeration: those
# routines visit 3 ** (#distinct ground atoms) assignments. Past this many the
# enumeration is hopeless in practice, so it raises a clear error instead of
# hanging. Raise this module attribute if you genuinely need a larger run.
MAX_MODELS = 3_000_000

# Łukasiewicz / sorted / lambda / modal node groups, rejected with a clear
# NotImplementedError: none has a strong-Kleene three-valued reading here.
_FUZZY_NODES = (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
)
_SORTED_NODES = (SortedQuantifier, SortedConstant)
_LAMBDA_NODES = (Lambda, LambdaVar, Application)
_MODAL_NODES = (Box, Diamond, Always, Eventually, Next, Until,
                Historically, Once, Previous, Since, Knows, Believes)


def _snap(x: float) -> float:
    """Snap a raw number to the nearest of {0.0, 0.5, 1.0}, or reject it.

    Tiny floating drift around the three legal values is tolerated and snapped;
    anything genuinely outside ``[0, 1]`` or far from a legal value raises
    ``ValueError`` so a malformed valuation is caught early rather than silently
    distorting a result.
    """
    for v in TRUTH_VALUES:
        if abs(x - v) < 1e-9:
            return v
    raise ValueError(
        f"Three-valued truth value must be one of {{0.0, 0.5, 1.0}}; got {x!r}."
    )


def _ground_term(node: Node, var_name: str, const_name: str) -> Node:
    """Replace every free ``Variable(var_name)`` in a *term* with ``Constant(const_name)``.

    Operates on term-position nodes (Variable, Constant, Number, Function).
    Returns a new node; the input is never mutated.
    """
    if isinstance(node, Variable):
        return Constant(const_name) if node.name == var_name else node
    if isinstance(node, Function):
        return Function(node.name,
                        [_ground_term(a, var_name, const_name) for a in node.args])
    # Constant, Number and anything else carry no free Variable.
    return node


def _ground(node: Node, var_name: str, const_name: str) -> Node:
    """Substitute free ``Variable(var_name)`` with ``Constant(const_name)`` throughout.

    Recurses the classical formula structure, stopping at an inner quantifier
    that rebinds the same variable name (the inner binding shadows ours).
    Returns a new node; the input is never mutated.
    """
    if isinstance(node, Atom):
        return Atom(node.predicate,
                    [_ground_term(a, var_name, const_name) for a in node.args])
    if isinstance(node, Not):
        return Not(_ground(node.formula, var_name, const_name))
    if isinstance(node, (And, Or, Xor, Implies, Iff)):
        return type(node)(_ground(node.left, var_name, const_name),
                          _ground(node.right, var_name, const_name))
    if isinstance(node, Quantifier):
        if node.variable.name == var_name:
            return node  # inner binder shadows the variable we are grounding
        return Quantifier(node.type, node.variable,
                          _ground(node.formula, var_name, const_name))
    # Term-position leaves pass through the term grounder.
    return _ground_term(node, var_name, const_name)


def _eval_quantifier(qtype: str, var_name: str, body: Node,
                     valuation: Dict[str, float], domain: Set[str]) -> float:
    """Evaluate a quantifier substitutionally: ∀ = min, ∃ = max over the domain."""
    if not domain:
        raise ValueError(
            "Cannot evaluate a quantifier over an empty domain; provide at "
            "least one constant name."
        )
    values = [
        kleene_value(_ground(body, var_name, d), valuation, domain=domain)
        for d in domain
    ]
    if qtype in ("∀", "forall"):
        return min(values)
    if qtype in ("∃", "exists"):
        return max(values)
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def kleene_value(formula: Node,
                 valuation: Dict[str, float],
                 domain: Optional[Set[str]] = None) -> float:
    """Strong-Kleene three-valued truth value of a classical formula.

    Args:
        formula: a classical FOL formula node (Atom, Not, And, Or, Xor, Implies,
            Iff, Quantifier). Build it with ``MSFLParser()``.
        valuation: maps a ground atom's canonical key — its
            ``to_unicode_str()`` rendering, e.g. ``'P'`` or ``'P(a)'`` — to a
            value in ``{0.0, 0.5, 1.0}``. A missing key raises ``KeyError``.
        domain: a set of constant-name strings over which quantifiers range
            (∀ = min, ∃ = max). Required whenever a ``Quantifier`` is present.

    Returns:
        The truth value as one of ``0.0``, ``0.5`` or ``1.0``.

    Raises:
        KeyError: a ground atom's key is absent from the valuation.
        ValueError: a quantifier lacks a domain (or the domain is empty), or a
            valuation entry is not snappable to ``{0.0, 0.5, 1.0}``.
        NotImplementedError: the node is a Łukasiewicz, sorted, lambda or modal
            construct, which has no strong-Kleene three-valued reading here.
        TypeError: the node is a bare term, not a formula, or otherwise
            unsupported.
    """
    # --- Atoms (the base case) --------------------------------------------
    if isinstance(formula, Atom):
        key = formula.to_unicode_str()
        if key not in valuation:
            raise KeyError(
                f"No truth value for ground atom {key!r} in the valuation. "
                f"Provide valuation[{key!r}] as one of 0.0, 0.5 or 1.0."
            )
        return _snap(float(valuation[key]))

    # --- Negation ----------------------------------------------------------
    if isinstance(formula, Not):
        x = kleene_value(formula.formula, valuation, domain)
        return 1.0 - x

    # --- Binary classical connectives -------------------------------------
    if isinstance(formula, (And, Or, Xor, Implies, Iff)):
        a = kleene_value(formula.left, valuation, domain)
        b = kleene_value(formula.right, valuation, domain)
        if isinstance(formula, And):
            return min(a, b)
        if isinstance(formula, Or):
            return max(a, b)
        if isinstance(formula, Implies):
            return max(1.0 - a, b)              # material: ¬a ∨ b
        if isinstance(formula, Iff):
            a_to_b = max(1.0 - a, b)
            b_to_a = max(1.0 - b, a)
            return min(a_to_b, b_to_a)
        # Xor: (a ∨ b) ∧ ¬(a ∧ b) = min(max(a, b), 1 − min(a, b))
        return min(max(a, b), 1.0 - min(a, b))

    # --- Quantifiers -------------------------------------------------------
    if isinstance(formula, Quantifier):
        if domain is None:
            raise ValueError(
                "Evaluating a Quantifier requires a 'domain' (a set of "
                "constant-name strings)."
            )
        return _eval_quantifier(formula.type, formula.variable.name,
                                formula.formula, valuation, set(domain))

    # --- Rejected node classes (informative errors) -----------------------
    _reject_if_unsupported(formula)


def _reject_if_unsupported(formula: Node) -> None:
    """Raise the error kleene_value uses for a node with no three-valued reading.

    Shared by :func:`kleene_value` and the compiled enumerator (:func:`_compile`)
    so both reject the same node classes with identical messages. The supported
    nodes (Atom, Not, And, Or, Xor, Implies, Iff, Quantifier) are dispatched by
    the caller before this is reached, so reaching here is always an error.
    """
    if isinstance(formula, _FUZZY_NODES):
        raise NotImplementedError(
            f"{type(formula).__name__} (a Łukasiewicz operator) has no "
            "strong-Kleene three-valued reading; parse classical input with "
            "MSFLParser() so connectives carry classical semantics."
        )
    if isinstance(formula, _SORTED_NODES):
        raise NotImplementedError(
            f"{type(formula).__name__} (a sorted construct) is not supported by "
            "the three-valued evaluator; the K3/LP evaluator is unsorted."
        )
    if isinstance(formula, _LAMBDA_NODES):
        raise NotImplementedError(
            f"{type(formula).__name__} (a lambda-calculus construct) has no "
            "truth value; beta-reduce and eliminate lambdas first."
        )
    if isinstance(formula, _MODAL_NODES):
        raise NotImplementedError(
            f"{type(formula).__name__} (a modal/temporal/epistemic operator) is "
            "not supported by the three-valued evaluator; it is non-modal."
        )
    if isinstance(formula, (Variable, Constant, Number, Function)):
        raise TypeError(
            f"{type(formula).__name__} is a term, not a formula; the "
            "three-valued evaluator can only score a formula's truth value."
        )

    raise TypeError(
        f"kleene_value: unsupported node type {type(formula).__name__}"
    )


def _designated_set(logic: str) -> frozenset:
    """Look up the designated-value set for a logic name, with a clear error."""
    try:
        return DESIGNATED[logic]
    except KeyError:
        raise ValueError(
            f"Unknown logic {logic!r}; choose one of {sorted(DESIGNATED)}."
        )


def _atom_keys(*formulas: Node) -> List[str]:
    """Distinct ground-atom keys across the formulas, in first-seen order.

    The key is each atom's canonical ``to_unicode_str()`` — these are the
    independent variables enumerated over ``{0.0, 0.5, 1.0}``.
    """
    keys: List[str] = []
    seen: Set[str] = set()
    for formula in formulas:
        for atom in formula.atoms():
            key = atom.to_unicode_str()
            if key not in seen:
                seen.add(key)
                keys.append(key)
    return keys


def _instantiate(node: Node, domain: Set[str]) -> Node:
    """Replace every quantifier by the ∧/∨ of its domain instances.

    ``∀x φ`` becomes the conjunction and ``∃x φ`` the disjunction of ``φ`` with
    the bound variable grounded to each domain element. The result is
    quantifier-free, so its atom set is exactly the ground atoms an assignment
    must fix. Used only to discover assignment variables — the actual value is
    computed by ``kleene_value`` so the two stay in lock-step.
    """
    if isinstance(node, Atom):
        return node
    if isinstance(node, Not):
        return Not(_instantiate(node.formula, domain))
    if isinstance(node, (And, Or, Xor, Implies, Iff)):
        return type(node)(_instantiate(node.left, domain),
                          _instantiate(node.right, domain))
    if isinstance(node, Quantifier):
        instances = [
            _instantiate(_ground(node.formula, node.variable.name, d), domain)
            for d in domain
        ]
        combine = And if node.type in ("∀", "forall") else Or
        result = instances[0]
        for inst in instances[1:]:
            result = combine(result, inst)
        return result
    return node


def _compile(node: Node, index: Dict[str, int]):
    """Compile a quantifier-free classical formula into ``fn(values) -> float``.

    ``values`` is a tuple of truth values positionally aligned with ``index``
    (atom key → tuple position). The returned closure computes the strong-Kleene
    value with no per-assignment AST walk and no per-atom ``to_unicode_str()``
    rendering — those happen once, here, at compile time. It is the enumeration
    fast path; it is exhaustively cross-checked against :func:`kleene_value` in the
    test suite (they must agree on every assignment), and uses the SAME strong-
    Kleene truth functions and the SAME rejection (:func:`_reject_if_unsupported`).
    """
    if isinstance(node, Atom):
        i = index[node.to_unicode_str()]
        return lambda values: values[i]
    if isinstance(node, Not):
        inner = _compile(node.formula, index)
        return lambda values: 1.0 - inner(values)
    if isinstance(node, (And, Or, Xor, Implies, Iff)):
        fa = _compile(node.left, index)
        fb = _compile(node.right, index)
        if isinstance(node, And):
            return lambda values: min(fa(values), fb(values))
        if isinstance(node, Or):
            return lambda values: max(fa(values), fb(values))
        if isinstance(node, Implies):
            return lambda values: max(1.0 - fa(values), fb(values))
        if isinstance(node, Iff):
            return lambda values: min(max(1.0 - fa(values), fb(values)),
                                      max(1.0 - fb(values), fa(values)))
        # Xor: (a ∨ b) ∧ ¬(a ∧ b) = min(max(a, b), 1 − min(a, b))
        return lambda values: min(max(fa(values), fb(values)),
                                  1.0 - min(fa(values), fb(values)))
    # A Quantifier never reaches here (callers instantiate it away); any other
    # node is rejected exactly as kleene_value would reject it.
    _reject_if_unsupported(node)


def _prepare_enumeration(formulas: Sequence[Node], domain: Optional[Set[str]]):
    """Ground quantifiers, collect ground-atom keys, and compile each formula.

    Returns ``(keys, compiled)`` with ``compiled[i](values) == kleene_value(
    formulas[i], dict(zip(keys, values)), domain=domain)`` for every assignment.
    Raises ValueError if a quantified formula is given without a domain, or if the
    ``3 ** len(keys)`` enumeration would exceed :data:`MAX_MODELS`.
    """
    grounded: List[Node] = []
    for formula in formulas:
        if formula.count(Quantifier):
            if not domain:
                raise ValueError(
                    "Enumerating a quantified formula requires a non-empty 'domain'."
                )
            grounded.append(_instantiate(formula, set(domain)))
        else:
            grounded.append(formula)
    keys = _atom_keys(*grounded)
    total = 3 ** len(keys)
    if total > MAX_MODELS:
        raise ValueError(
            f"Three-valued enumeration would visit 3**{len(keys)} = {total} "
            f"assignments, above MAX_MODELS = {MAX_MODELS}. Reduce the number of "
            "distinct ground atoms, or raise manyvalued.MAX_MODELS if you really "
            "want to wait."
        )
    index = {key: i for i, key in enumerate(keys)}
    compiled = [_compile(g, index) for g in grounded]
    return keys, compiled


def is_valid(formula: Node, logic: str = "K3",
             domain: Optional[Set[str]] = None) -> bool:
    """True iff the formula is designated under *every* three-valued assignment.

    Enumerates all ``3**n`` assignments of the formula's ``n`` distinct ground
    atoms to ``{0.0, 0.5, 1.0}`` (after grounding quantifiers over ``domain``)
    and checks the value is designated for ``logic`` in each. ``n`` is the number
    of ground atoms; cost is exponential in ``n``, so keep formulas (and the
    domain) small. Each assignment is scored by a compiled evaluator (built once
    from the formula); above :data:`MAX_MODELS` assignments a ValueError is raised
    rather than hanging.

    Args:
        formula: a classical FOL formula node (built with ``MSFLParser()``).
        logic: ``"K3"`` (designate {1.0}) or ``"LP"`` (designate {0.5, 1.0}).
        domain: constant names for any quantifiers; required if quantified.
    """
    designated = _designated_set(logic)
    keys, (evaluate,) = _prepare_enumeration([formula], domain)
    return all(
        evaluate(values) in designated
        for values in product(TRUTH_VALUES, repeat=len(keys))
    )


def is_satisfiable(formula: Node, logic: str = "K3",
                   domain: Optional[Set[str]] = None) -> bool:
    """True iff *some* three-valued assignment designates the formula.

    Enumerates the same ``3**n`` assignments as :func:`is_valid` and returns
    True as soon as one yields a value designated for ``logic``.
    """
    designated = _designated_set(logic)
    keys, (evaluate,) = _prepare_enumeration([formula], domain)
    return any(
        evaluate(values) in designated
        for values in product(TRUTH_VALUES, repeat=len(keys))
    )


def entails(premises: Sequence[Node], conclusion: Node, logic: str = "K3",
            domain: Optional[Set[str]] = None) -> bool:
    """Designation-preserving entailment: every model of the premises models the conclusion.

    True iff for every three-valued assignment that designates *all* premises,
    the conclusion is also designated (for ``logic``). The enumeration ranges
    over the ground atoms of the premises *and* the conclusion together.

    This is where K3 and LP diverge sharply: under LP the explosion inference
    ``entails([P, ¬P], Q, "LP")`` is False (at P=0.5, Q=0.0 both premises are
    designated yet Q is not), so LP is paraconsistent; under K3 it holds
    vacuously because ``P`` and ``¬P`` are never both designated.

    Args:
        premises: a sequence of classical formula nodes.
        conclusion: a classical formula node.
        logic: ``"K3"`` or ``"LP"``.
        domain: constant names for any quantifiers; required if quantified.
    """
    designated = _designated_set(logic)
    premises = list(premises)
    keys, compiled = _prepare_enumeration([*premises, conclusion], domain)
    *premise_fns, conclusion_fn = compiled
    for values in product(TRUTH_VALUES, repeat=len(keys)):
        if all(f(values) in designated for f in premise_fns):
            if conclusion_fn(values) not in designated:
                return False
    return True
