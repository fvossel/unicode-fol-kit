"""Second-order finite-model semantics: Tarskian satisfaction with ∀P / ∃P.

This evaluator extends classical Tarskian satisfaction (see
:mod:`semantics.tarski`) with second-order quantification over PREDICATE
variables: ``∀P φ`` and ``∃P φ``, where ``P`` ranges over every relation of its
arity on a FINITE domain. It reuses :class:`semantics.tarski.Structure` and
:func:`semantics.tarski.term_value` unchanged; only satisfaction is re-defined,
so that a bound predicate variable can be interpreted by a transient
``pred_binding`` rather than by the structure's fixed predicate tables.

A ``pred_binding`` maps a bound predicate-variable name → its current
interpretation: a set of argument tuples (a relation on the domain). It is the
predicate-level analogue of the first-order variable ``assignment``. Both are
threaded immutably — extended into a fresh copy for each bound symbol, never
mutated in place.

Second-order quantification is interpreted by brute-force enumeration over the
powerset of ``domain ** arity`` (every relation of the right arity). This is
``2 ** (n ** k)`` relations for a domain of size ``n`` and arity ``k`` — doubly
exponential, and intended ONLY for very small finite models (a handful of
elements, arity ≤ 2). Arity 0 is the propositional/Boolean case: the two
"relations" are ``frozenset()`` (false) and ``frozenset({()})`` (true), so
``∀P``/``∃P`` over an arity-0 ``P`` quantifies over ``P``'s truth value.

Scope of the second order here: this is second-order PREDICATE (relation)
quantification only. Quantification over functions, over relations-of-relations
(third order and up), and a full higher-order type system are OUT OF SCOPE; the
lambda layer (:class:`fol.nodes.Lambda` / ``Application``) already supplies
higher-order TERMS and is intentionally rejected by this evaluator — beta-reduce
and lambda-eliminate first. Łukasiewicz (fuzzy) and modal nodes are likewise
rejected: use the fuzzy / Kripke evaluators.
"""

from itertools import product
from typing import Any, FrozenSet, Iterable, Mapping, Optional, Tuple

from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier,
    SecondOrderQuantifier,
)
from .tarski import (
    Structure, term_value, _atom_value, _extend,
    _FORALL, _EXISTS, _FUZZY_TYPES, _LAMBDA_TYPES,
)

# A relation interpretation for a bound predicate variable: a (frozen)set of
# argument tuples of domain individuals. Mapping name -> relation.
Relation = FrozenSet[Tuple[Any, ...]]
PredBinding = Mapping[str, Relation]

# Safety cap for second-order enumeration. A ∀P/∃P over an arity-k predicate on
# an n-element domain ranges over 2 ** (n ** k) relations. Past this many the
# enumeration cannot finish in practice, so it raises a clear error instead of
# hanging. Raise this module attribute if you really mean to enumerate more.
MAX_RELATIONS = 1 << 22  # ~4.2 million


def satisfies_so(
    formula: Node,
    structure: Structure,
    assignment: Optional[Mapping[str, Any]] = None,
    pred_binding: Optional[PredBinding] = None,
) -> bool:
    """Return whether ``structure`` satisfies ``formula`` (second-order Tarski).

    ``assignment`` maps object-variable names to individuals (as in
    :func:`semantics.tarski.satisfies`); ``pred_binding`` maps a *bound*
    predicate-variable name to its current relation (a set of argument tuples).
    Both default to empty and are threaded immutably.

    Recursion:

    - **Atom** ``A(t1..tk)``: if ``A`` is currently bound (``A in pred_binding``),
      it is true iff the tuple of evaluated term values is in ``pred_binding[A]``
      (an arity-0 bound ``A`` is true iff ``() in pred_binding[A]``). Otherwise
      satisfaction falls back to the structure exactly as
      :func:`semantics.tarski.satisfies` does — including ``=`` as identity and
      ``≠`` as non-identity.
    - **Not/And/Or/Xor/Implies/Iff**: the classical truth tables.
    - **Quantifier / SortedQuantifier** (object-level): range over the domain
      (or the named sort), threading the same ``pred_binding``.
    - **SecondOrderQuantifier** ``∀P/k φ`` / ``∃P/k φ``: range ``P`` over every
      relation ``R ⊆ domain ** k`` (the powerset of all ``k``-tuples). ``∀``
      holds iff ``φ`` holds for all such ``R``; ``∃`` iff for some. See the
      module docstring for the ``2 ** (n ** k)`` complexity.

    Raises:
        ValueError: on a Łukasiewicz node (use the fuzzy evaluator), an unknown
            quantifier type / node type, or when a ``∀P`` / ``∃P`` would enumerate
            more than :data:`MAX_RELATIONS` relations (a clear error instead of a
            hang — see the module docstring for the ``2 ** (n ** k)`` cost).
        NotImplementedError: on a lambda or modal node — these are out of scope
            for second-order predicate semantics (lambda: beta-reduce and
            lambda-eliminate first).
    """
    if assignment is None:
        assignment = {}
    if pred_binding is None:
        pred_binding = {}

    if isinstance(formula, Atom):
        return _so_atom_value(formula, structure, assignment, pred_binding)

    if isinstance(formula, Not):
        return not satisfies_so(formula.formula, structure, assignment, pred_binding)

    if isinstance(formula, And):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                and satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Or):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                or satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Xor):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                != satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Implies):
        return ((not satisfies_so(formula.left, structure, assignment, pred_binding))
                or satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Iff):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                == satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Quantifier):
        return _eval_object_quantifier(
            formula.type, formula.variable.name, structure.domain,
            formula.formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, SortedQuantifier):
        universe = structure.sort_universe(formula.sort)
        return _eval_object_quantifier(
            formula.type, formula.variable.name, universe,
            formula.formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, SecondOrderQuantifier):
        return _eval_second_order_quantifier(
            formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, _FUZZY_TYPES):
        raise ValueError(
            f"Cannot evaluate Łukasiewicz node {type(formula).__name__} with the "
            "two-valued second-order evaluator; use the fuzzy evaluator instead."
        )

    if isinstance(formula, _LAMBDA_TYPES):
        raise NotImplementedError(
            f"Lambda node {type(formula).__name__} is out of scope for the "
            "second-order evaluator (it handles second-order PREDICATE "
            "quantification, not higher-order terms); beta-reduce and "
            "lambda-eliminate the formula first."
        )

    # Modal nodes (Box / Diamond) live in the modal AST and have no class here;
    # they fall through to this generic rejection alongside any other unknown
    # node type. Modal formulas need the Kripke evaluator.
    if type(formula).__name__ in ("Box", "Diamond"):
        raise NotImplementedError(
            f"Modal node {type(formula).__name__} is out of scope for the "
            "second-order evaluator; use the Kripke (modal) evaluator instead."
        )

    raise ValueError(
        f"satisfies_so: unsupported node type {type(formula).__name__}."
    )


def _so_atom_value(
    atom: Atom,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Truth value of an atom, consulting ``pred_binding`` for bound predicates.

    If the atom's predicate name is currently bound to a relation, the atom is
    true iff the tuple of evaluated argument values is in that relation. (For an
    arity-0 bound predicate the relevant tuple is the empty tuple ``()``.)
    Otherwise satisfaction is delegated to the first-order
    :func:`semantics.tarski._atom_value`, which handles ``=`` / ``≠`` and the
    structure's predicate tables. The ``=`` / ``≠`` builtins are never treated
    as bindable predicate variables.
    """
    if atom.predicate in pred_binding and atom.predicate not in ("=", "≠"):
        relation = pred_binding[atom.predicate]
        values = tuple(
            term_value(a, structure, assignment) for a in atom.args
        )
        return values in relation
    return _atom_value(atom, structure, assignment)


def _eval_object_quantifier(
    qtype: str,
    var_name: str,
    universe: Iterable[Any],
    body: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Evaluate an object-level ∀/∃ over a universe, threading ``pred_binding``.

    Mirrors :func:`semantics.tarski._eval_quantifier` but recurses through
    :func:`satisfies_so` so the predicate binding survives object quantifiers.
    """
    if qtype in _FORALL:
        return all(
            satisfies_so(body, structure, _extend(assignment, var_name, d), pred_binding)
            for d in universe
        )
    if qtype in _EXISTS:
        return any(
            satisfies_so(body, structure, _extend(assignment, var_name, d), pred_binding)
            for d in universe
        )
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def _all_relations(domain: Tuple[Any, ...], arity: int) -> Iterable[Relation]:
    """Yield every relation R ⊆ domain ** arity (the powerset of all arity-tuples).

    The base set is all ``arity``-tuples of domain elements (``len ==
    n ** arity``); a relation is any subset of it, so there are ``2 ** (n **
    arity)`` of them. For ``arity == 0`` the base set is the single empty tuple
    ``{()}``, giving exactly two relations — ``frozenset()`` (Boolean false) and
    ``frozenset({()})`` (Boolean true).

    Each subset is yielded as a ``frozenset`` so it is hashable and immutable.
    """
    base = list(product(domain, repeat=arity))
    # Enumerate subsets via the bitmask 0 .. 2**len(base) - 1.
    for mask in range(1 << len(base)):
        subset = frozenset(
            base[i] for i in range(len(base)) if (mask >> i) & 1
        )
        yield subset


def _eval_second_order_quantifier(
    node: SecondOrderQuantifier,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Evaluate ∀P/k or ∃P/k by enumerating every relation R ⊆ domain ** k.

    The bound predicate name is interpreted, in turn, by each candidate relation
    added to a *copy* of ``pred_binding`` (shadowing any outer binding of the
    same name). ``∀`` holds iff the body holds under every candidate; ``∃`` iff
    under some. See the module docstring for the doubly-exponential cost.

    Raises ValueError if the 2 ** (n ** k) relation count exceeds
    :data:`MAX_RELATIONS`, rather than enumerating a hopelessly large space.
    """
    num_tuples = len(structure.domain) ** node.arity
    num_relations = 1 << num_tuples  # 2 ** (n ** k)
    if num_relations > MAX_RELATIONS:
        raise ValueError(
            f"Second-order quantifier {node.type}{node.predicate}/{node.arity} "
            f"over a {len(structure.domain)}-element domain would enumerate "
            f"2 ** ({len(structure.domain)} ** {node.arity}) = 2 ** {num_tuples} "
            f"relations, above MAX_RELATIONS = {MAX_RELATIONS}. Shrink the domain "
            "or the arity (or raise secondorder.MAX_RELATIONS)."
        )
    relations = _all_relations(structure.domain, node.arity)
    if node.type in _FORALL:
        return all(
            satisfies_so(
                node.formula, structure, assignment,
                _extend(pred_binding, node.predicate, relation),
            )
            for relation in relations
        )
    if node.type in _EXISTS:
        return any(
            satisfies_so(
                node.formula, structure, assignment,
                _extend(pred_binding, node.predicate, relation),
            )
            for relation in relations
        )
    raise ValueError(
        f"Unknown second-order quantifier type: {node.type!r}"
    )


def holds(formula: Node, structure: Structure) -> bool:
    """Convenience: ``satisfies_so(formula, structure, {}, {})`` for a sentence.

    Reads as "structure satisfies the (closed) second-order formula": the empty
    object assignment and empty predicate binding are appropriate when the
    formula has no free object or predicate variables.
    """
    return satisfies_so(formula, structure, {}, {})


# ---------------------------------------------------------------------------
# Bounded second-order validity / (counter)model search
# ---------------------------------------------------------------------------
#
# Second-order logic has no complete proof system and SO validity is not even
# semi-decidable, so this is a *bounded finite-model* search (the SO analogue of
# semantics.modelfinder): it enumerates finite structures interpreting the FREE
# symbols — the SO-quantified predicates are NOT interpreted by the structure, the
# satisfies_so evaluator ranges them over every relation — and evaluates the SO
# sentence in each. A found model/counter-model is genuine; "none up to size N" is
# bounded evidence, not a proof.


def _so_bound_predicate_names(formula: Node) -> set:
    """Names bound by a second-order quantifier anywhere in ``formula``."""
    return {n.predicate for n in formula.walk()
            if isinstance(n, SecondOrderQuantifier)}


def _so_signature(sentence: Node):
    """The structure signature of ``sentence`` minus its SO-bound predicates."""
    from .modelfinder import _Signature
    bound = _so_bound_predicate_names(sentence)
    sig = _Signature()
    sig.scan(sentence)
    sig.predicates = {(name, ar) for (name, ar) in sig.predicates if name not in bound}
    return sig


def _so_structures(sentence: Node, max_size: int, max_candidates: int):
    """Yield every candidate :class:`Structure` over domains ``1 .. max_size``."""
    from .modelfinder import _interpretations, _candidate_count
    sig = _so_signature(sentence)
    for k in range(1, max_size + 1):
        if _candidate_count(sig, k) > max_candidates:
            continue
        domain = tuple(range(k))
        for constants, functions, predicates in _interpretations(sig, domain):
            yield Structure(domain, constants=constants,
                            functions=functions, predicates=predicates)


def so_find_model(formula: Node, max_size: int = 3,
                  max_candidates: int = MAX_RELATIONS) -> Optional[Structure]:
    """Return a finite structure in which the SO ``formula`` holds, or None (bounded)."""
    from .modelfinder import _universal_closure
    sentence = _universal_closure(formula)
    for structure in _so_structures(sentence, max_size, max_candidates):
        if holds(sentence, structure):
            return structure
    return None


def so_find_countermodel(formula: Node, max_size: int = 3,
                         max_candidates: int = MAX_RELATIONS) -> Optional[Structure]:
    """Return a finite structure in which the SO ``formula`` FAILS, or None (bounded).

    A returned structure witnesses that ``formula`` is not second-order valid (free
    object variables are universally closed, so it refutes the closed reading).
    """
    from .modelfinder import _universal_closure
    sentence = _universal_closure(formula)
    for structure in _so_structures(sentence, max_size, max_candidates):
        if not holds(sentence, structure):
            return structure
    return None


def so_is_satisfiable_finite(formula: Node, max_size: int = 3,
                             max_candidates: int = MAX_RELATIONS) -> bool:
    """True iff the SO ``formula`` has a finite model of size ≤ ``max_size`` (bounded)."""
    return so_find_model(formula, max_size, max_candidates) is not None


def so_is_valid_finite(formula: Node, max_size: int = 3,
                       max_candidates: int = MAX_RELATIONS) -> bool:
    """True iff no finite counter-model of the SO ``formula`` is found up to ``max_size``.

    Bounded and one-sided: ``True`` is strong evidence of second-order validity (not a
    proof — SO validity is not semi-decidable); ``False`` is a genuine refutation, with
    the witness available from :func:`so_find_countermodel`.
    """
    return so_find_countermodel(formula, max_size, max_candidates) is None
