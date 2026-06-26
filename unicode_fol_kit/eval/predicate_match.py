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

__all__ = [
    "formulas_are_identical",
    "match_predicates",
    "formulas_are_matched_identical",
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
