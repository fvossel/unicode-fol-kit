"""Tests for unicode_logic_kit.eval.predicate_match — predicate-aligned string match."""

import pytest

from unicode_logic_kit import (
    formulas_are_identical,
    match_predicates,
    formulas_are_matched_identical,
    align_symbols,
)
from unicode_logic_kit.eval.predicate_match import (
    _levenshtein, _normalised_distance, _symbol_inventory,
)
from unicode_logic_kit.fol.signature import inventory_of, Signature
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Variable, And


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


# ---------------------------------------------------------------------------
# _symbol_inventory — the LENIENT (never-raising) inventory shared with
# unicode_logic_kit.fol.signature.inventory_of (roadmap item C5).
# ---------------------------------------------------------------------------
#
# These are adversarial cases Signature.from_formulas REFUSES outright (see
# tests/test_signature.py's own from_formulas conflict tests): predicate_
# match's whole purpose is scoring possibly-malformed model output, so its
# inventory walk must keep tolerating exactly what it tolerated before the
# swap onto the shared unicode_logic_kit.fol.signature.inventory_of walk.

def test_symbol_inventory_is_exactly_inventory_of():
    """_symbol_inventory is a pure delegation, not a coincidentally-agreeing
    second implementation — same object identity as fol.signature's walk."""
    from unicode_logic_kit.eval import predicate_match
    assert predicate_match._symbol_inventory is inventory_of


def test_symbol_inventory_tolerates_arity_conflict():
    """P used at arity 1 and arity 2 in ONE tree: Signature.from_formulas
    refuses this outright; _symbol_inventory keeps BOTH (name, arity)
    entries and never raises."""
    n = And(Atom("P", [Constant("a")]),
            Atom("P", [Constant("a"), Constant("b")]))
    with pytest.raises(ValueError, match="conflicting arities"):
        Signature.from_formulas([n])
    preds, funcs, consts = _symbol_inventory(n)
    assert preds == {("P", 1), ("P", 2)}
    assert funcs == set()
    assert consts == {"a", "b"}


def test_symbol_inventory_tolerates_constant_vs_function_clash():
    """'alice' used as a bare constant AND as an applied function in ONE
    tree: Signature.from_formulas refuses this; _symbol_inventory records
    'alice' in BOTH the constants set and the functions set."""
    x = Variable("x")
    n = And(Atom("S", [Constant("alice")]),
            Atom("T", [Function("alice", [x])]))
    with pytest.raises(ValueError, match="used both as a constant and as a function"):
        Signature.from_formulas([n])
    preds, funcs, consts = _symbol_inventory(n)
    assert funcs == {("alice", 1)}
    assert consts == {"alice"}


def test_symbol_inventory_allows_predicate_and_function_sharing_a_name():
    """A predicate 'Foo' and a function 'Foo' coexisting is not a clash in
    either implementation (separate namespaces) — sanity check that the
    lenient walk does not over-tolerate by conflating namespaces."""
    x = Variable("x")
    n = And(Atom("Foo", [x]), Atom("Q", [Function("Foo", [x])]))
    preds, funcs, consts = _symbol_inventory(n)
    assert preds == {("Foo", 1), ("Q", 1)}
    assert funcs == {("Foo", 1)}


def test_symbol_inventory_excludes_builtin_operators():
    """'=' and '+' are the kit's built-in operators, never user vocabulary —
    matches Signature's identical classification (see signature.py)."""
    from unicode_logic_kit.fol.nodes import Number
    n = Atom("=", [Function("+", [Constant("a"), Number(1)]), Constant("b")])
    preds, funcs, consts = _symbol_inventory(n)
    assert preds == set()
    assert funcs == set()
    assert consts == {"a", "b"}


def test_align_symbols_never_raises_on_a_vocabulary_conflict_input():
    """align_symbols (which calls _symbol_inventory on both sides) must not
    raise on a prediction with an internal vocabulary conflict — this is
    the property the whole lenient-inventory swap exists to preserve; the
    formula is malformed model output, not something align_symbols should
    refuse, since Signature.from_formulas already refuses it upstream for
    callers that want that check."""
    n = And(Atom("P", [Constant("a")]),
            Atom("P", [Constant("a"), Constant("b")]))
    aligned = align_symbols(n, n)
    assert aligned == n
