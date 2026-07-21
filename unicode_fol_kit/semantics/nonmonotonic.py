"""Non-monotonic reasoning — minimal-model entailment (predicate circumscription).

Classical entailment is *monotonic*: adding premises never retracts a conclusion.
Common-sense reasoning is not — "Tweety is a bird" lets you conclude "Tweety flies"
until you learn "Tweety is a penguin". **Circumscription** (McCarthy) captures this by
believing only what holds in the **minimal** models of a theory: those that make the
*circumscribed* predicates as small (false of as many things) as possible.

``Γ ⊨_circ φ`` (circumscribing the predicates in ``circumscribed``) holds iff ``φ`` is
true in every model of ``Γ`` that is ≤-minimal — where ``M ≤ M'`` means ``M`` and ``M'``
share a domain, constants, functions and the *non-circumscribed* (fixed) predicates,
and every circumscribed predicate's extension in ``M`` is a subset of its extension in
``M'``. With ``circumscribed=None`` *all* predicates are minimised (closed-world-style
minimal-model semantics), so e.g. ``∅ ⊨_circ ¬P(a)``.

The search reuses the finite model finder, so it is **bounded** (domains up to
``max_size``): ``True`` is minimal-model entailment over models within the bound, not a
proof over all (possibly infinite) models. The relation is genuinely non-monotonic —
adding premises can flip a ``True`` to ``False``.

**Second-order circumscription axiom.** :func:`circumscription_formula` builds McCarthy's
textbook SO sentence for the same ``Γ ⊨_circ φ`` relation — ``T(P) ∧ ∀P'((T(P') ∧ P'⊆P) →
P⊆P')`` — so it can be checked (or exported to Isabelle/THF via
:mod:`unicode_fol_kit.hol.secondorder`) with the finite second-order evaluator
:mod:`unicode_fol_kit.semantics.secondorder` instead of the bounded model search above; the
two are cross-checked against each other in the test suite.

Public API: :func:`minimal_models`, :func:`minimal_entails`, :func:`circumscription_formula`,
:func:`circumscription_entails_so`.
"""

from typing import Dict, Iterable, List, Optional, Tuple, Union

from ..fol.nodes import (
    Node, Atom, And, Implies, Quantifier, Variable, SecondOrderQuantifier,
)
from .tarski import Structure, models
from .modelfinder import (
    _Signature, _interpretations, _candidate_count, _universal_closure, MAX_CANDIDATES,
)

#: A circumscribed-predicate spec: either a bare name (arity inferred from the
#: premises) or an explicit ``(name, arity)`` pair (needed when the predicate is
#: never applied in the premises, e.g. with empty premises).
CircSpec = Union[str, Tuple[str, int]]


def _func_key(functions) -> tuple:
    """A hashable key for a function interpretation."""
    return tuple(sorted((sig, tuple(sorted(table.items())))
                        for sig, table in functions.items()))


def _fixed_key(constants, functions, predicates, pred_sig, circ) -> tuple:
    """The 'fixed part' (everything not minimised) two comparable models must share."""
    fixed_preds = tuple(
        (name, ar, frozenset(predicates.get((name, ar), frozenset())))
        for (name, ar) in pred_sig if name not in circ)
    return (tuple(sorted(constants.items())), _func_key(functions), fixed_preds)


def _circ_profile(predicates, pred_sig, circ) -> dict:
    """The extensions of the circumscribed predicates (what minimality compares)."""
    return {(name, ar): frozenset(predicates.get((name, ar), frozenset()))
            for (name, ar) in pred_sig if name in circ}


def _strictly_below(prof_a: dict, prof_b: dict) -> bool:
    """True iff ``prof_a`` ≤ ``prof_b`` componentwise with at least one strict ⊂."""
    if any(not (prof_a[k] <= prof_b[k]) for k in prof_a):
        return False
    return any(prof_a[k] < prof_b[k] for k in prof_a)


def minimal_models(premises, circumscribed: Optional[set] = None,
                   max_size: int = 4,
                   max_candidates: int = MAX_CANDIDATES,
                   extra_signature=()) -> List[Structure]:
    """Return the ≤-minimal finite models of ``premises`` up to ``max_size`` (bounded).

    ``circumscribed`` names the predicates to minimise (default: every predicate).
    Models are compared only within a shared domain and fixed part, so the result is
    the union of the minimal models found at each domain size. ``extra_signature`` adds
    formulas whose symbols the models must interpret without being constrained by them
    (so a goal's constants/predicates are total in every enumerated model).
    """
    sentences = [_universal_closure(p) for p in premises]
    sig = _Signature()
    for s in sentences:
        sig.scan(s)
    for f in extra_signature:
        sig.scan(_universal_closure(f))
    pred_sig = sorted(sig.predicates)
    circ = set(circumscribed) if circumscribed is not None else {n for n, _ in pred_sig}

    result: List[Structure] = []
    for k in range(1, max_size + 1):
        if _candidate_count(sig, k) > max_candidates:
            continue
        domain = tuple(range(k))
        found = []
        for constants, functions, predicates in _interpretations(sig, domain):
            structure = Structure(domain, constants=constants,
                                  functions=functions, predicates=predicates)
            if all(models(s, structure) for s in sentences):
                found.append((constants, functions, predicates, structure))
        # Group by fixed part; keep the circ-minimal models of each group.
        groups = {}
        for entry in found:
            constants, functions, predicates, _ = entry
            key = _fixed_key(constants, functions, predicates, pred_sig, circ)
            profile = _circ_profile(predicates, pred_sig, circ)
            groups.setdefault(key, []).append((entry, profile))
        for grp in groups.values():
            for (entry, profile) in grp:
                if not any(_strictly_below(other, profile)
                           for (e2, other) in grp if e2 is not entry):
                    result.append(entry[3])
    return result


def minimal_entails(premises, conclusion: Node, circumscribed: Optional[set] = None,
                    max_size: int = 4, max_candidates: int = MAX_CANDIDATES) -> bool:
    """Return whether ``premises`` circumscriptively entail ``conclusion`` (bounded).

    ``True`` iff the (universally closed) ``conclusion`` holds in *every* minimal model
    of ``premises`` found up to ``max_size`` (see :func:`minimal_models`). Non-monotonic:
    strengthening ``premises`` can turn a ``True`` into a ``False``.
    """
    goal = _universal_closure(conclusion)
    for structure in minimal_models(premises, circumscribed, max_size, max_candidates,
                                    extra_signature=[conclusion]):
        if not models(goal, structure):
            return False
    return True


# ---------------------------------------------------------------------------
# Second-order circumscription axiom (McCarthy's textbook SO formula).
# ---------------------------------------------------------------------------
#
# T(P) ∧ ∀P'((T(P') ∧ P'⊆P) → P⊆P'): T holds of P, and no relation P' that is a
# PROPER subset of P (in a model that otherwise agrees on the domain, constants,
# functions, and every FIXED — non-circumscribed — predicate, since those occur
# as the SAME free symbol in both T(P) and T(P') and so are literally the same
# extension in any one structure the SO evaluator checks) also satisfies T. This
# is exactly what minimal_models compares within one ``_fixed_key`` group at one
# domain size, which is why the two are cross-checked against each other below.
#
# Predicate substitution T(P) -> T(P') is just a global RENAME of the predicate
# symbol P to a fresh P' (same arity, so no comprehension/lambda machinery is
# needed) — reused, lazily, from the sequent calculus's predicate-substitution
# helpers (atp.sequent) to avoid re-implementing capture-avoiding renaming.

def _pred_arity(sentences: List[Node], name: str) -> Optional[int]:
    """Infer ``name``'s arity from its applications in ``sentences`` (or ``None``).

    Raises ValueError if ``name`` is applied at more than one arity (an
    ill-formed signature for a single circumscribed predicate).
    """
    sig = _Signature()
    for s in sentences:
        sig.scan(s)
    arities = {ar for (nm, ar) in sig.predicates if nm == name}
    if len(arities) > 1:
        raise ValueError(
            f"circumscription_formula: predicate {name!r} occurs at conflicting "
            f"arities {sorted(arities)} in the premises."
        )
    return next(iter(arities), None)


def _subset_formula(sub_name: str, sup_name: str, arity: int) -> Node:
    """Build ``sub ⊆ sup``: ``∀x̄ (sub(x̄) → sup(x̄))``, or a bare Implies at arity 0."""
    if arity == 0:
        return Implies(Atom(sub_name, ()), Atom(sup_name, ()))
    xs = tuple(Variable(f"_circ_x{i}") for i in range(arity))
    body = Implies(Atom(sub_name, xs), Atom(sup_name, xs))
    return _forall_chain_circ(xs, body)


def _forall_chain_circ(xs, body: Node) -> Node:
    """Fold ``∀x1 ∀x2 … body`` over ``xs`` (local helper, mirrors modelfinder's style)."""
    result = body
    for x in reversed(xs):
        result = Quantifier("∀", x, result)
    return result


def _conjoin_all(sentences: List[Node]) -> Optional[Node]:
    """Left-fold ``sentences`` into a binary And-tree, or ``None`` if the list is empty."""
    if not sentences:
        return None
    result = sentences[0]
    for s in sentences[1:]:
        result = And(result, s)
    return result


def circumscription_formula(premises, circumscribed: Iterable[CircSpec], varied: tuple = ()) -> Node:
    """Build the second-order circumscription axiom for ``premises`` w.r.t. ``circumscribed``.

    ``T(P̄) ∧ ∀P̄'((T(P̄') ∧ P̄'⊆P̄) → P̄⊆P̄')`` — ``T`` is the conjunction of the
    (universally closed) ``premises``; ``P̄`` are the ``circumscribed`` predicates
    (one or more), each replaced by a FRESH predicate ``P'`` inside a second copy
    of ``T``, with that ``P'`` bound by a second-order quantifier — **universal**
    (``∀P'``), since the axiom says NO strictly-smaller ``P'`` also satisfies
    ``T``. Every OTHER
    predicate is FIXED automatically: it occurs as the same free symbol in both
    copies of ``T``, so it denotes the same extension in any one structure a
    second-order evaluator checks — no extra bookkeeping is needed for the
    "everything else fixed" reading.

    ``circumscribed`` is a non-empty iterable of predicate specs: a bare name
    (its arity is inferred from an application in ``premises``) or an explicit
    ``(name, arity)`` pair (needed when the predicate is never applied in
    ``premises`` — e.g. empty premises; see :func:`circumscription_entails_so`,
    which also scans the conclusion for the arity).

    Only ``varied=()`` (the default) is implemented: every non-circumscribed
    predicate is FIXED. Passing a non-empty ``varied`` (letting some predicates
    float freely — neither minimised nor held fixed) raises ``NotImplementedError``;
    that reading needs a second family of second-order-quantified predicates kept
    OUTSIDE the ``⊆`` comparison, which this builder does not construct.

    Raises:
        NotImplementedError: for a non-empty ``varied``.
        ValueError: if ``circumscribed`` is empty, or a bare name's arity cannot
            be inferred (never applied in ``premises``), or a predicate is
            applied at conflicting arities in ``premises``.
    """
    if tuple(varied):
        raise NotImplementedError(
            "circumscription_formula: only the simple reading — every predicate "
            "NOT circumscribed is FIXED — is implemented; a non-empty `varied` "
            "(letting some predicates float freely, neither minimised nor held "
            "fixed) needs a second family of second-order-quantified predicates "
            "kept OUTSIDE the P'⊆P / P⊆P' comparison, which this builder does "
            "not construct. Pass varied=() (the default)."
        )
    from ..atp.sequent import _rename_pred, _all_pred_names, _fresh_pred_name

    sentences = [_universal_closure(p) for p in premises]

    circ_list = sorted(circumscribed, key=lambda e: e[0] if isinstance(e, tuple) else e)
    if not circ_list:
        raise ValueError("circumscription_formula: `circumscribed` must name at least one predicate.")

    resolved: List[Tuple[str, int]] = []
    for entry in circ_list:
        if isinstance(entry, tuple):
            name, arity = entry
        else:
            name = entry
            arity = _pred_arity(sentences, name)
            if arity is None:
                raise ValueError(
                    f"circumscription_formula: cannot infer the arity of "
                    f"circumscribed predicate {name!r} — it is never applied in "
                    "`premises`. Pass an explicit (name, arity) pair in "
                    "`circumscribed`, or build the axiom via "
                    "circumscription_entails_so(premises, circumscribed, "
                    "conclusion), which also scans the conclusion for the arity."
                )
        resolved.append((name, arity))

    avoid = {name for name, _ in resolved}
    for s in sentences:
        avoid |= _all_pred_names(s)

    primed: Dict[str, str] = {}
    for name, _ in resolved:
        p2 = _fresh_pred_name(name, avoid)
        avoid.add(p2)
        primed[name] = p2

    conj = _conjoin_all(sentences)
    conj_primed = conj
    if conj_primed is not None:
        for name, _ in resolved:
            conj_primed = _rename_pred(conj_primed, name, primed[name])

    le_primed_orig = _conjoin_all([_subset_formula(primed[n], n, ar) for n, ar in resolved])
    le_orig_primed = _conjoin_all([_subset_formula(n, primed[n], ar) for n, ar in resolved])

    antecedent = le_primed_orig if conj_primed is None else And(conj_primed, le_primed_orig)
    minimality = Implies(antecedent, le_orig_primed)

    quantified = minimality
    for name, arity in resolved:
        quantified = SecondOrderQuantifier("∀", primed[name], arity, quantified)

    return quantified if conj is None else And(conj, quantified)


def circumscription_entails_so(premises, circumscribed: Iterable[CircSpec], conclusion: Node) -> Node:
    """Build ``circumscription_formula(premises, circumscribed) → conclusion`` (universally closed).

    The caller decides validity — e.g. with
    :func:`unicode_fol_kit.semantics.secondorder.so_is_valid_finite` (bounded, but
    the natural finite oracle for a second-order sentence) — or exports the
    result with :mod:`unicode_fol_kit.hol.secondorder`. This function only BUILDS
    the implication node; it never evaluates it.

    Unlike :func:`circumscription_formula`, a bare predicate name in
    ``circumscribed`` has its arity inferred from BOTH ``premises`` and
    ``conclusion`` — so e.g. ``circumscription_entails_so([], {"P"}, ¬P(b))``
    (empty premises, ``P``'s arity known only from the conclusion) works.
    """
    sentences = [_universal_closure(p) for p in premises]
    closed_conclusion = _universal_closure(conclusion)

    resolved_circumscribed: List[Tuple[str, int]] = []
    for entry in circumscribed:
        if isinstance(entry, tuple):
            resolved_circumscribed.append(entry)
            continue
        arity = _pred_arity(sentences + [closed_conclusion], entry)
        if arity is None:
            raise ValueError(
                f"circumscription_entails_so: predicate {entry!r} is never "
                "applied in the premises or the conclusion, so its arity "
                "cannot be inferred."
            )
        resolved_circumscribed.append((entry, arity))

    axiom = circumscription_formula(premises, resolved_circumscribed)
    return Implies(axiom, closed_conclusion)
