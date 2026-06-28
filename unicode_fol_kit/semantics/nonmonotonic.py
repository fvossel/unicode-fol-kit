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

Public API: :func:`minimal_models`, :func:`minimal_entails`.
"""

from typing import List, Optional

from ..fol.nodes import Node
from .tarski import Structure, models
from .modelfinder import (
    _Signature, _interpretations, _candidate_count, _universal_closure, MAX_CANDIDATES,
)


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
