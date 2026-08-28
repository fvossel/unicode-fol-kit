"""Third-order finite-model semantics: satisfaction where an argument can be a property.

:mod:`semantics.secondorder` quantifies over relations on the domain. This
evaluator adds the level above: a predicate whose ARGUMENT is a relation —
``Positive(G)``, ``Essence(G, x)``, ``Positive(λx. ¬G(x))`` — and quantification
over such predicates. It reuses :class:`semantics.tarski.Structure` and
:func:`semantics.tarski.term_value` unchanged; what changes is that an argument
slot may now be filled by a relation rather than an individual, so a "tuple in
the extension" may have relations among its components.

**Slots, not just arities.** At second order a bound predicate variable is fully
described by its arity. At third order it is not: ``Positive`` and ``G`` can both
have arity 1 and mean entirely different things, because ``G``'s slot holds an
individual and ``Positive``'s holds a property. What each slot holds is inferred
by :func:`unicode_fol_kit.fol.nodes.analyse_signatures` and threaded through the
evaluation, which is why this module's quantifier case enumerates over a
SIGNATURE where the second-order one enumerates over an arity.

**Cost.** An individual slot ranges over the ``n`` domain elements; a property
slot of arity ``j`` over the ``2 ** (n ** j)`` relations of that arity. A
predicate of a given signature is any subset of the product of its slots, so a
monadic third-order predicate over a domain of ``n`` has ``2 ** (2 ** n)``
interpretations: 16 for ``n = 2``, 256 for 3, 65 536 for 4, about 4·10⁹ for 5.
Small, then suddenly not — which is what :data:`MAX_INTERPRETATIONS` guards, by
raising a clear error rather than hanging.

**Scope.** Two-valued, classical, constant-domain. Łukasiewicz and modal nodes
are rejected by name, as in the second-order evaluator — a third-order MODAL
formula is not evaluated here but exported by
:mod:`unicode_fol_kit.hol.ho_modal`. λ-abstractions are NOT rejected here,
unlike at second order: in argument position a λ is precisely how an anonymous
property is written, and it is evaluated to its extension. A λ anywhere else
still has no reading.
"""

from itertools import product
from typing import Any, FrozenSet, Iterable, List, Mapping, Optional, Tuple

from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SecondOrderQuantifier,
    Lambda, LambdaVar, PredicateTerm, Variable,
    analyse_signatures,
)
from ..fol._ho_nodes import INDIVIDUAL, Signatures
from .tarski import (
    Structure, term_value, _atom_value, _extend,
    _FORALL, _EXISTS, _FUZZY_TYPES,
)

#: A relation: a (frozen)set of argument tuples. A component of one of those
#: tuples is an individual at first/second order, and may be another relation at
#: third order — which is the whole difference.
Relation = FrozenSet[Tuple[Any, ...]]
PredBinding = Mapping[str, Relation]

#: Safety cap on one quantifier's enumeration. See the module docstring for how
#: fast the count grows; raise this attribute if you really mean to enumerate
#: more.
MAX_INTERPRETATIONS = 1 << 20  # ~1.05 million


def slot_values(kind, domain: Tuple[Any, ...]) -> Tuple[Any, ...]:
    """Return everything one argument slot can hold.

    ``kind`` is :data:`unicode_fol_kit.fol._ho_nodes.INDIVIDUAL` — in which case
    the answer is the domain — or ``("p", j)``, in which case it is every
    ``j``-ary relation on the domain, i.e. every subset of ``domain ** j``.
    """
    if kind == INDIVIDUAL:
        return domain
    arity = kind[1]
    base = list(product(domain, repeat=arity))
    return tuple(
        frozenset(base[i] for i in range(len(base)) if (mask >> i) & 1)
        for mask in range(1 << len(base))
    )


def all_interpretations(signature: Tuple[Any, ...],
                        domain: Tuple[Any, ...]) -> Iterable[Relation]:
    """Yield every interpretation of a predicate with the given argument ``signature``.

    An interpretation is any subset of the product of the slots' value sets, so
    the count is ``2 ** prod(len(slot_values(kind)) for kind in signature)``. An
    empty signature (a propositional variable) has the single-element product
    ``{()}``, hence exactly the two interpretations false and true — matching
    the second-order evaluator's arity-0 case.
    """
    columns = [slot_values(kind, domain) for kind in signature]
    base = list(product(*columns)) if columns else [()]
    for mask in range(1 << len(base)):
        yield frozenset(base[i] for i in range(len(base)) if (mask >> i) & 1)


def interpretation_count(signature: Tuple[Any, ...], domain_size: int) -> int:
    """How many interpretations :func:`all_interpretations` would yield.

    Computed without enumerating anything, so a caller (and the evaluator's own
    guard) can refuse an impossible enumeration before starting it.
    """
    width = 1
    for kind in signature:
        width *= (domain_size if kind == INDIVIDUAL
                  else 1 << (domain_size ** kind[1]))
    return 1 << width


def satisfies_to(formula: Node,
                 structure: Structure,
                 assignment: Optional[Mapping[str, Any]] = None,
                 pred_binding: Optional[PredBinding] = None,
                 signatures: Optional[Signatures] = None) -> bool:
    """Return whether ``structure`` satisfies ``formula`` (third-order Tarski).

    ``assignment`` maps object-variable names to individuals; ``pred_binding``
    maps a bound predicate name to its current interpretation. ``signatures``
    is the argument-slot analysis; it is computed from ``formula`` when omitted,
    and threaded unchanged through the recursion so every occurrence of a symbol
    is read at the same type.

    The recursion differs from :func:`semantics.secondorder.satisfies_so` in
    exactly two places, both about arguments:

    - an **atom's** arguments are evaluated with :func:`argument_value`, so an
      argument may be a :class:`~unicode_fol_kit.fol.nodes.PredicateTerm` or a
      λ-abstraction and evaluate to a RELATION. When every argument is an
      ordinary term the atom is handed to the first-order
      :func:`semantics.tarski._atom_value` unchanged, so ``=`` / ``≠`` and the
      arithmetic fallbacks behave exactly as they do at first order;
    - a **predicate quantifier** enumerates over the bound symbol's SIGNATURE
      rather than its arity, which is what makes ``∀Positive`` range over
      predicates of properties instead of over relations on the domain.

    Raises:
        ValueError: on a Łukasiewicz node, an unknown quantifier or node type,
            or when a quantifier's enumeration would exceed
            :data:`MAX_INTERPRETATIONS`.
        NotImplementedError: on a modal node (use the Kripke evaluator, or
            export a third-order modal formula with ``hol.ho_modal``), or on a
            λ outside argument position.
    """
    if assignment is None:
        assignment = {}
    if pred_binding is None:
        pred_binding = {}
    if signatures is None:
        signatures = analyse_signatures([formula])

    if isinstance(formula, Atom):
        return _atom_truth(formula, structure, assignment, pred_binding, signatures)

    if isinstance(formula, Not):
        return not satisfies_to(formula.formula, structure, assignment,
                                pred_binding, signatures)
    if isinstance(formula, And):
        return (satisfies_to(formula.left, structure, assignment, pred_binding, signatures)
                and satisfies_to(formula.right, structure, assignment, pred_binding, signatures))
    if isinstance(formula, Or):
        return (satisfies_to(formula.left, structure, assignment, pred_binding, signatures)
                or satisfies_to(formula.right, structure, assignment, pred_binding, signatures))
    if isinstance(formula, Xor):
        return (satisfies_to(formula.left, structure, assignment, pred_binding, signatures)
                != satisfies_to(formula.right, structure, assignment, pred_binding, signatures))
    if isinstance(formula, Implies):
        return ((not satisfies_to(formula.left, structure, assignment, pred_binding, signatures))
                or satisfies_to(formula.right, structure, assignment, pred_binding, signatures))
    if isinstance(formula, Iff):
        return (satisfies_to(formula.left, structure, assignment, pred_binding, signatures)
                == satisfies_to(formula.right, structure, assignment, pred_binding, signatures))

    if isinstance(formula, Quantifier):
        return _object_quantifier(formula.type, formula.variable.name,
                                  structure.domain, formula.formula, structure,
                                  assignment, pred_binding, signatures)
    if isinstance(formula, SortedQuantifier):
        return _object_quantifier(formula.type, formula.variable.name,
                                  structure.sort_universe(formula.sort),
                                  formula.formula, structure, assignment,
                                  pred_binding, signatures)
    if isinstance(formula, SecondOrderQuantifier):
        return _predicate_quantifier(formula, structure, assignment,
                                     pred_binding, signatures)

    if isinstance(formula, _FUZZY_TYPES):
        raise ValueError(
            f"Cannot evaluate Łukasiewicz node {type(formula).__name__} with the "
            "two-valued third-order evaluator; use the fuzzy evaluator instead.")
    if isinstance(formula, Lambda):
        raise NotImplementedError(
            "A λ-abstraction denotes a PROPERTY, not a truth value; it has a "
            "reading here only in argument position (Positive(λx. ¬G(x))).")
    if type(formula).__name__ in ("Box", "Diamond"):
        raise NotImplementedError(
            f"Modal node {type(formula).__name__} is out of scope for the "
            "third-order evaluator; use the Kripke evaluator, or export the "
            "formula with hol.ho_modal for a higher-order prover.")
    raise ValueError(f"satisfies_to: unsupported node type {type(formula).__name__}.")


def argument_value(node: Node, structure: Structure,
                   assignment: Mapping[str, Any],
                   pred_binding: PredBinding,
                   signatures: Signatures) -> Any:
    """Evaluate a node in ARGUMENT position — to an individual or to a relation.

    A :class:`~unicode_fol_kit.fol.nodes.PredicateTerm` denotes the relation its
    name stands for: the current binding if the name is bound, otherwise the
    structure's table for it (a missing table is the empty relation, matching
    the first-order convention). A λ-abstraction denotes its EXTENSION, computed
    by evaluating the body at every tuple of individuals its binders range over.
    Anything else is an ordinary term.
    """
    if isinstance(node, PredicateTerm):
        if node.name in pred_binding:
            return pred_binding[node.name]
        arity = signatures.arity.get(node.name, 1)
        return frozenset(structure.predicates.get((node.name, arity), ()))
    if isinstance(node, Lambda):
        names: List[str] = []
        body: Node = node
        while isinstance(body, Lambda):
            names.append(body.param.name)
            body = body.body
        body = _lambda_vars_as_variables(body)
        extension = []
        for values in product(structure.domain, repeat=len(names)):
            local = dict(assignment)
            local.update(zip(names, values))
            if satisfies_to(body, structure, local, pred_binding, signatures):
                extension.append(values)
        return frozenset(extension)
    return term_value(node, structure, assignment)


def _lambda_vars_as_variables(node: Node) -> Node:
    """Turn every LambdaVar in ``node`` back into an ordinary object Variable.

    The parser resolves a λ binder's occurrences to LambdaVar, which the
    first-order term evaluator has no reading for -- correctly, since a
    λ-abstraction is not a term it can evaluate. Here the binder IS being
    interpreted: its variables are about to range over the domain through the
    assignment, which is exactly what an object variable does. Converting them
    is sound including under nesting, because an inner λ's own binder is
    re-bound by name on the way in, so the shadowing the LambdaVars encoded is
    reproduced by the assignment.
    """
    if isinstance(node, LambdaVar):
        return Variable(node.name)
    return node.map_children(_lambda_vars_as_variables)


def _atom_truth(atom: Atom, structure: Structure,
                assignment: Mapping[str, Any], pred_binding: PredBinding,
                signatures: Signatures) -> bool:
    """Truth of an atom, consulting ``pred_binding`` and allowing property arguments.

    An atom whose arguments are all ordinary terms and whose predicate is not
    currently bound is delegated to the first-order
    :func:`semantics.tarski._atom_value` verbatim — so nothing about first-order
    satisfaction is re-implemented, and ``=`` / ``≠`` are never treated as
    bindable.
    """
    higher_order = any(isinstance(a, (PredicateTerm, Lambda)) for a in atom.args)
    if atom.predicate in pred_binding and atom.predicate not in ("=", "≠"):
        values = tuple(argument_value(a, structure, assignment, pred_binding, signatures)
                       for a in atom.args)
        return values in pred_binding[atom.predicate]
    if not higher_order:
        return _atom_value(atom, structure, assignment)
    values = tuple(argument_value(a, structure, assignment, pred_binding, signatures)
                   for a in atom.args)
    extension = structure.predicates.get((atom.predicate, len(atom.args)), ())
    return values in extension


def _object_quantifier(qtype: str, var_name: str, universe: Iterable[Any],
                       body: Node, structure: Structure,
                       assignment: Mapping[str, Any], pred_binding: PredBinding,
                       signatures: Signatures) -> bool:
    """Evaluate an object-level ∀/∃, threading the predicate binding and signatures."""
    if qtype in _FORALL:
        return all(satisfies_to(body, structure, _extend(assignment, var_name, d),
                                pred_binding, signatures) for d in universe)
    if qtype in _EXISTS:
        return any(satisfies_to(body, structure, _extend(assignment, var_name, d),
                                pred_binding, signatures) for d in universe)
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def _predicate_quantifier(node: SecondOrderQuantifier, structure: Structure,
                          assignment: Mapping[str, Any],
                          pred_binding: PredBinding,
                          signatures: Signatures) -> bool:
    """Evaluate ∀P / ∃P by enumerating every interpretation of P's SIGNATURE.

    The signature — not the arity — is what decides the range: an arity-1 ``P``
    whose slot holds an individual ranges over the ``2 ** n`` subsets of the
    domain (the second-order case), while an arity-1 ``P`` whose slot holds a
    monadic property ranges over the ``2 ** (2 ** n)`` sets of such properties.
    Both fall out of the same enumeration.
    """
    signature = signatures.slots.get(node.predicate)
    if signature is None:
        signature = tuple(INDIVIDUAL for _ in range(node.arity))
    count = interpretation_count(signature, len(structure.domain))
    if count > MAX_INTERPRETATIONS:
        raise ValueError(
            f"Predicate quantifier {node.type}{node.predicate} with signature "
            f"{signature} over a {len(structure.domain)}-element domain would "
            f"enumerate {count} interpretations, above MAX_INTERPRETATIONS = "
            f"{MAX_INTERPRETATIONS}. Shrink the domain (or raise "
            "thirdorder.MAX_INTERPRETATIONS).")
    candidates = all_interpretations(signature, structure.domain)
    if node.type in _FORALL:
        return all(satisfies_to(node.formula, structure, assignment,
                                _extend(pred_binding, node.predicate, candidate),
                                signatures)
                   for candidate in candidates)
    if node.type in _EXISTS:
        return any(satisfies_to(node.formula, structure, assignment,
                                _extend(pred_binding, node.predicate, candidate),
                                signatures)
                   for candidate in candidates)
    raise ValueError(f"Unknown predicate quantifier type: {node.type!r}")


def holds_to(formula: Node, structure: Structure) -> bool:
    """Convenience: ``satisfies_to(formula, structure)`` for a closed formula.

    Reads as "structure satisfies the third-order sentence": the empty
    assignment and empty predicate binding are what a formula with no free
    object or predicate variables needs.
    """
    return satisfies_to(formula, structure)
