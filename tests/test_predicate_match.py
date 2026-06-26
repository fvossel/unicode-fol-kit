"""Tests for unicode_fol_kit.eval.predicate_match — predicate-aligned string match."""

from unicode_fol_kit import (
    formulas_are_identical,
    match_predicates,
    formulas_are_matched_identical,
)
from unicode_fol_kit.eval.predicate_match import _levenshtein, _normalised_distance


# ---------------------------------------------------------------------------
# _levenshtein — parity with the classical unit-cost edit distance
# ---------------------------------------------------------------------------

def test_levenshtein_known_values():
    """Hand-checked distances, including the textbook kitten/sitting case."""
    assert _levenshtein("", "") == 0
    assert _levenshtein("abc", "abc") == 0
    assert _levenshtein("abc", "") == 3
    assert _levenshtein("", "abc") == 3
    assert _levenshtein("kitten", "sitting") == 3
    assert _levenshtein("flaw", "lawn") == 2
    assert _levenshtein("Wins", "Win") == 1
    assert _levenshtein("Red", "Tall") == 4


def test_levenshtein_symmetric():
    """Edit distance is symmetric."""
    for a, b in [("Human", "Humann"), ("Loves", "Likes"), ("abc", "xyz")]:
        assert _levenshtein(a, b) == _levenshtein(b, a)


def test_levenshtein_matches_reference_brute_force():
    """Agreement with an independent (naive recursive) edit-distance oracle."""
    from functools import lru_cache

    def naive(a, b):
        @lru_cache(maxsize=None)
        def rec(i, j):
            if i == 0:
                return j
            if j == 0:
                return i
            cost = 0 if a[i - 1] == b[j - 1] else 1
            return min(rec(i - 1, j) + 1, rec(i, j - 1) + 1, rec(i - 1, j - 1) + cost)
        return rec(len(a), len(b))

    samples = ["", "a", "Win", "Wins", "Winner", "Happy", "Tall", "Red",
               "distance", "dist", "IsWinner", "Loves", "Likes"]
    for a in samples:
        for b in samples:
            assert _levenshtein(a, b) == naive(a, b), (a, b)


def test_normalised_distance_in_unit_interval():
    """Normalised distance is 0 for equal symbols and in [0, 1] otherwise."""
    assert _normalised_distance("Win", "Win") == 0.0
    assert _normalised_distance("Wins", "Win") == 1 / 4
    assert _normalised_distance("Red", "Tall") == 1.0


# ---------------------------------------------------------------------------
# formulas_are_identical — whitespace- and case-insensitive string equality
# ---------------------------------------------------------------------------

def test_identical_ignores_whitespace_and_case():
    assert formulas_are_identical("∀x P(x)", "∀x  P( x )") is True
    assert formulas_are_identical("P(X)", "p(x)") is True


def test_identical_negative():
    assert formulas_are_identical("P(x)", "Q(x)") is False
    assert formulas_are_identical("∀x (P(x) ∧ Q(x))", "∀x (P(x) ∨ Q(x))") is False


# ---------------------------------------------------------------------------
# match_predicates — predicate/function realignment
# ---------------------------------------------------------------------------

def test_match_renames_close_predicate():
    """A close lexical match (Wins → Win) is applied; identical names stay."""
    pred = "∀x (Wins(x) → Happy(x))"
    ref = "∀x (Win(x) → Happy(x))"
    assert match_predicates(pred, ref) == "∀x (Win(x) → Happy(x))"


def test_match_keeps_distant_predicate():
    """A symbol with no close reference counterpart is left untouched."""
    assert match_predicates("Red(x)", "Tall(x)") == "Red(x)"


def test_match_realigns_function_symbols_too():
    """The matcher realigns any name before '(', including function symbols."""
    assert match_predicates("dist(a, b)", "distance(a, b)") == "distance(a, b)"


def test_match_noop_when_reference_has_no_symbols():
    """If the reference has no parenthesised symbols, the prediction is returned as-is."""
    assert match_predicates("Foo(x)", "y + 1 = z") == "Foo(x)"


def test_match_noop_when_prediction_has_no_symbols():
    """If the prediction has no parenthesised symbols, it is returned unchanged."""
    assert match_predicates("x = y", "P(x)") == "x = y"


def test_match_identity_when_equal():
    """Matching a formula against itself is a no-op."""
    s = "∀x (Human(x) → Mortal(x))"
    assert match_predicates(s, s) == s


def test_match_multiple_predicates():
    """Several predicates are each realigned to their nearest reference name."""
    # "Dogs" → "Dog": distance 1, normalised 0.25 (≤ 0.6), so it is realigned.
    pred = "Cat(x) ∧ Dogs(x)"
    ref = "Cat(x) ∧ Dog(x)"
    assert match_predicates(pred, ref) == "Cat(x) ∧ Dog(x)"


def test_match_threshold_is_configurable():
    """A strict threshold rejects a match the default (0.6) would accept."""
    # Wins → Win has normalised distance 0.25: accepted by default, rejected at 0.0.
    assert match_predicates("Wins(x)", "Win(x)") == "Win(x)"
    assert match_predicates("Wins(x)", "Win(x)", max_norm_distance=0.0) == "Wins(x)"


# ---------------------------------------------------------------------------
# formulas_are_matched_identical — realign then compare
# ---------------------------------------------------------------------------

def test_matched_identical_true_for_renamed_predicates():
    pred = "∀x (Wins(x) → Happy(x))"
    ref = "∀x (Win(x) → Happy(x))"
    assert formulas_are_matched_identical(pred, ref) is True


def test_matched_identical_false_for_distant_predicates():
    assert formulas_are_matched_identical("∀x (Red(x))", "∀x (Tall(x))") is False


def test_matched_identical_false_for_structural_difference():
    """Predicate realignment does not paper over a real structural difference."""
    # Same predicate names, different connective — must remain a mismatch.
    assert formulas_are_matched_identical(
        "∀x (P(x) ∧ Q(x))", "∀x (P(x) ∨ Q(x))"
    ) is False
