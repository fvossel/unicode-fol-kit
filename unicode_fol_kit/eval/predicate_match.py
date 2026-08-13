"""Predicate-aligned string matching for NL→FOL evaluation.

When scoring a model that translates natural language to FOL, two formulas may
denote the same thing while using *different predicate names* — a model might
write ``Wins(x)`` where the reference writes ``IsWinner(x)``. A plain string
comparison (or even a structural one) counts that as wrong, even though the
logical *shape* is identical and only the lexical choice of predicate symbol
differs. ``match_predicates`` closes that gap: it greedily renames each
predicate/function symbol in the prediction to the closest reference symbol
(by **normalised Levenshtein distance**, accepting a match at or below a
distance threshold) and returns the rewritten string, so a subsequent string
comparison rewards a structurally-correct answer that merely renamed its
predicates.

This is a deliberately **lexical / string-level** notion, complementary to the
AST-level :func:`unicode_fol_kit.eval.canonical.exact_match`:

* :func:`exact_match` (canonical) quotients out α-renaming, commutativity /
  associativity, operand duplication, and double negation, but treats two
  *different predicate names* as a genuine mismatch.
* :func:`match_predicates` / :func:`formulas_are_matched_identical` quotient out
  *predicate-name* differences (and, via :func:`formulas_are_identical`,
  whitespace and case), but not the structural rewrites above.

The two are orthogonal and are typically reported as separate metrics
(``EXACT_MATCH`` vs ``PREDICATE_MATCHED_EXACT_MATCH``). The matcher is
parser-independent: it operates directly on the surface strings, so it also
applies to raw model output that does not (yet) parse.

The Levenshtein distance is computed in pure Python (classical unit-cost
insertion / deletion / substitution dynamic program), so this module adds no
third-party dependency.
"""

import re
from dataclasses import replace
from typing import Dict, FrozenSet, Tuple

from unicode_fol_kit.fol.nodes import (
    Node, Atom, Function, Constant, SortedConstant,
)
# Single source of truth for which symbols are built-in operators rather than
# user vocabulary (=, ≠, <, … and +, -, *, /) — shared with validate's walk.
from .validate import _BUILTIN_PREDS, _BUILTIN_FUNCS

__all__ = [
    "formulas_are_identical",
    "match_predicates",
    "formulas_are_matched_identical",
    "align_symbols",
    "aligned_exact_match",
]

# A predicate or function symbol is a maximal word immediately followed by an
# opening parenthesis, e.g. the ``P`` in ``P(x)`` or the ``loves`` in
# ``loves(a, b)``. Nullary predicates written without parentheses are not
# captured (there is nothing lexical to realign), and neither are bare terms.
_SYMBOL_BEFORE_PAREN = re.compile(r"\b\w+(?=\()")

_WHITESPACE = re.compile(r"\s+")


def _levenshtein(a: str, b: str) -> int:
    """Return the Levenshtein edit distance between ``a`` and ``b``.

    Classical unit-cost dynamic program (insertion, deletion, and substitution
    each cost 1), computed with a single rolling row in O(len(a)·len(b)) time
    and O(len(b)) space. Matches the value of ``Levenshtein.distance`` for the
    same inputs, so results are identical whether or not the optional
    ``python-Levenshtein`` C extension is installed.
    """
    if a == b:
        return 0
    if not a:
        return len(b)
    if not b:
        return len(a)

    previous = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        current = [i]
        for j, cb in enumerate(b, start=1):
            insertion = current[j - 1] + 1
            deletion = previous[j] + 1
            substitution = previous[j - 1] + (ca != cb)
            current.append(min(insertion, deletion, substitution))
        previous = current
    return previous[len(b)]


def _normalised_distance(a: str, b: str) -> float:
    """Levenshtein distance scaled by the longer string's length, in [0, 1].

    Normalising by ``max(len(a), len(b))`` makes the threshold length-agnostic:
    a one-character edit weighs more between two short names than between two
    long ones. Both names are predicate/function symbols matched by
    :data:`_SYMBOL_BEFORE_PAREN`, hence always non-empty, so the denominator is
    never zero.
    """
    return _levenshtein(a, b) / max(len(a), len(b))


def formulas_are_identical(prediction: str, reference: str) -> bool:
    """Return whether two formula strings are equal ignoring whitespace and case.

    Both strings are stripped of all whitespace and lower-cased before
    comparison, so ``"∀x P(x)"`` and ``"∀x  p( x )"`` are considered identical.
    This is the plain ``EXACT_MATCH`` notion; it does **not** realign predicate
    names — use :func:`formulas_are_matched_identical` for that.
    """
    cleaned_prediction = _WHITESPACE.sub("", prediction).lower()
    cleaned_reference = _WHITESPACE.sub("", reference).lower()
    return cleaned_prediction == cleaned_reference


def _map_predicates(
    prediction_symbols: list,
    reference_symbols: list,
    max_norm_distance: float = 0.6,
) -> list:
    """Map each prediction symbol to its nearest reference symbol, or keep it.

    For every symbol in ``prediction_symbols`` the closest symbol in
    ``reference_symbols`` (smallest normalised Levenshtein distance) is found.
    If that distance is at or below ``max_norm_distance`` the reference symbol is
    used; otherwise the original prediction symbol is kept unchanged (the match
    is too weak to trust). Ties are broken by the reference symbol's position,
    matching ``min``'s first-minimum semantics.
    """
    mapped = []
    for symbol in prediction_symbols:
        best_match = min(
            reference_symbols,
            key=lambda candidate: _normalised_distance(symbol, candidate),
        )
        if _normalised_distance(symbol, best_match) <= max_norm_distance:
            mapped.append(best_match)
        else:
            mapped.append(symbol)
    return mapped


def match_predicates(
    prediction: str,
    reference: str,
    max_norm_distance: float = 0.6,
) -> str:
    """Rewrite ``prediction``'s predicate/function names toward ``reference``.

    Every symbol that appears immediately before a ``(`` in ``prediction`` is
    realigned to the lexically-closest such symbol in ``reference`` (see
    :func:`_map_predicates`), and the rewrite is applied to the surface string
    as a ``"<old>(" → "<new>("`` substitution. Symbols with no sufficiently
    close reference counterpart (normalised distance above ``max_norm_distance``)
    are left as they are. If either side has no parenthesised symbols, the
    prediction is returned unchanged.

    The result is a string in the same surface syntax as the input, suitable for
    a subsequent :func:`formulas_are_identical` comparison or for re-parsing.
    """
    matched_formula = prediction
    prediction_symbols = _SYMBOL_BEFORE_PAREN.findall(prediction)
    reference_symbols = _SYMBOL_BEFORE_PAREN.findall(reference)

    if prediction_symbols and reference_symbols:
        mapped_symbols = _map_predicates(
            prediction_symbols, reference_symbols, max_norm_distance
        )
        for old_symbol, new_symbol in zip(prediction_symbols, mapped_symbols):
            matched_formula = matched_formula.replace(
                old_symbol + "(", new_symbol + "("
            )

    return matched_formula


def formulas_are_matched_identical(
    prediction: str,
    reference: str,
    max_norm_distance: float = 0.6,
) -> bool:
    """Return whether ``prediction`` equals ``reference`` after predicate realignment.

    Realigns the prediction's predicate/function names to the reference's with
    :func:`match_predicates`, then compares with :func:`formulas_are_identical`
    (whitespace- and case-insensitive). This is the ``PREDICATE_MATCHED_EXACT``
    notion: it forgives a structurally-correct answer that merely chose different
    predicate symbol names.
    """
    matched_prediction = match_predicates(prediction, reference, max_norm_distance)
    return formulas_are_identical(matched_prediction, reference)


# ---------------------------------------------------------------------------
# AST-level symbol alignment: separate namespaces, arity-aware, injective.
# ---------------------------------------------------------------------------
#
# The lexical matcher above deliberately works on surface strings (so it also
# applies to output that does not parse), but that comes with three known
# blind spots: predicates and functions share one regex, arity is ignored, and
# the greedy per-occurrence mapping can collapse two distinct prediction
# symbols onto the same reference symbol — which CHANGES the logical content.
# ``align_symbols`` is the parsed-AST counterpart without those blind spots.

# A predicate/function symbol key: (name, arity). Constants key on the name.
_SymKey = Tuple[str, int]


def _symbol_inventory(node: Node):
    """Collect the user vocabulary of ``node`` per namespace.

    Returns ``(preds, funcs, consts)`` where ``preds`` / ``funcs`` are sets of
    ``(name, arity)`` keys (built-in operators excluded, mirroring
    ``validate``'s classification) and ``consts`` is a set of constant names
    (``Constant`` and ``SortedConstant`` — a sorted constant is renamed in
    place, its sort annotation is untouched). Variables are deliberately NOT
    collected: bound-variable naming is ``canonicalize``'s job (α-renaming),
    not a vocabulary difference.
    """
    preds: set = set()
    funcs: set = set()
    consts: set = set()
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in _BUILTIN_PREDS:
                preds.add((n.predicate, len(n.args)))
        elif isinstance(n, Function):
            if n.name not in _BUILTIN_FUNCS:
                funcs.add((n.name, len(n.args)))
        elif isinstance(n, (Constant, SortedConstant)):
            consts.add(n.name)
    return preds, funcs, consts


def _greedy_injective(pred_keys, ref_keys, taken_names: FrozenSet[str],
                      max_norm_distance: float) -> Dict:
    """Best-first injective assignment prediction-key → reference-key.

    Candidate pairs are restricted to EQUAL ARITY (for ``(name, arity)`` keys;
    plain constant names always pair), filtered by the normalised-Levenshtein
    threshold, and sorted by (distance, names) for determinism. Each
    prediction key maps to at most one reference key and vice versa
    (injectivity: two distinct prediction symbols are never merged, which
    would change the logical content). Identity pairs have distance 0, so a
    symbol present on both sides always claims itself first and cannot be
    captured by a near-miss neighbour.

    ``taken_names`` are the names the prediction already uses in this
    namespace: a key is never renamed INTO one of them (identity excepted) —
    otherwise the rewrite could manufacture a name clash the prediction never
    had (e.g. renaming ``Foo/2`` to ``Fo`` while the prediction already uses
    ``Fo/1`` would create a mixed-arity symbol out of thin air).
    """
    def name_of(key):
        return key if isinstance(key, str) else key[0]

    def arity_of(key):
        return None if isinstance(key, str) else key[1]

    pairs = []
    for p in pred_keys:
        for r in ref_keys:
            if arity_of(p) != arity_of(r):
                continue
            if name_of(r) in taken_names and r != p:
                continue
            d = _normalised_distance(name_of(p), name_of(r))
            if d <= max_norm_distance:
                pairs.append((d, name_of(p), name_of(r), p, r))
    pairs.sort(key=lambda t: (t[0], t[1], t[2]))

    mapping: Dict = {}
    used_targets: set = set()
    for _d, _pn, _rn, p, r in pairs:
        if p in mapping or r in used_targets:
            continue
        mapping[p] = r
        used_targets.add(r)
    # Identity entries are no-ops for the rewrite — drop them.
    return {p: r for p, r in mapping.items() if p != r}


def align_symbols(prediction: Node, reference: Node,
                  max_norm_distance: float = 0.6) -> Node:
    """Rename ``prediction``'s vocabulary toward ``reference``, AST-safely.

    The parsed-AST counterpart of :func:`match_predicates` with three
    guarantees the lexical matcher cannot give:

    * **separate namespaces** — predicate, function, and constant symbols are
      aligned independently (a predicate ``foo`` never interferes with a
      function ``foo``);
    * **arity-aware** — ``P/1`` is only ever aligned to a reference symbol of
      arity 1;
    * **injective + capture-free** — two distinct prediction symbols are never
      merged onto one reference symbol, and a symbol is never renamed into a
      name the prediction already uses. The result is the image of the
      prediction under an injective renaming of its vocabulary, so its logical
      content is preserved up to that renaming — the alignment can make a
      formula *equal* to the reference, never *more true*.

    Bound variables are untouched (α-renaming is ``canonicalize``'s job).
    The distance measure and default threshold match :func:`match_predicates`.
    """
    p_preds, p_funcs, p_consts = _symbol_inventory(prediction)
    r_preds, r_funcs, r_consts = _symbol_inventory(reference)

    pred_map = _greedy_injective(
        p_preds, r_preds, frozenset(n for n, _a in p_preds), max_norm_distance)
    func_map = _greedy_injective(
        p_funcs, r_funcs, frozenset(n for n, _a in p_funcs), max_norm_distance)
    const_map = _greedy_injective(
        p_consts, r_consts, frozenset(p_consts), max_norm_distance)

    def rec(n: Node) -> Node:
        n = n.map_children(rec)
        if isinstance(n, Atom):
            key = (n.predicate, len(n.args))
            if key in pred_map:
                return replace(n, predicate=pred_map[key][0])
        elif isinstance(n, Function):
            key = (n.name, len(n.args))
            if key in func_map:
                return replace(n, name=func_map[key][0])
        elif isinstance(n, (Constant, SortedConstant)):
            if n.name in const_map:
                return replace(n, name=const_map[n.name])
        return n

    return rec(prediction)


def aligned_exact_match(prediction: Node, reference: Node,
                        max_norm_distance: float = 0.6) -> bool:
    """Canonical exact match after AST-level symbol alignment.

    Combines the two orthogonal quotients: :func:`align_symbols` forgives
    lexical vocabulary differences (namespace- and arity-aware), then
    :func:`unicode_fol_kit.eval.canonical.exact_match` forgives α-renaming,
    commutativity/associativity, operand duplication, and double negation.
    """
    from .canonical import exact_match

    return exact_match(align_symbols(prediction, reference, max_norm_distance),
                       reference)
