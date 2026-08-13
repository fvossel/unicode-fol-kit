"""Tests for AST-level symbol alignment (eval.predicate_match.align_symbols).

Every expectation below is hand-checked against the documented guarantees:
separate namespaces, arity-awareness, injectivity, capture-freedom, and the
identity-first property of the greedy assignment.
"""

from unicode_fol_kit import (
    MSFLParser, align_symbols, aligned_exact_match, exact_match,
)

_P = MSFLParser()


def _fol(text: str):
    return _P.parse(text)


# ---------------------------------------------------------------------------
# The happy path: vocabulary differences disappear, structure decides.
# ---------------------------------------------------------------------------

def test_predicate_renaming_reaches_reference():
    """Wins→IsWinner, Plays→Playing: aligned prediction equals the reference.

    Hand-check of the distances (normalised Levenshtein):
    Wins→IsWinner = 5/8 = 0.625 > 0.6 would FAIL — so use Winner→IsWinner
    (2/8 = 0.25) and Plays→Playing (3/7 ≈ 0.43), both under the threshold.
    """
    prediction = _fol("∀x (Plays(x) → Winner(x))")
    reference = _fol("∀x (Playing(x) → IsWinner(x))")
    assert aligned_exact_match(prediction, reference)


def test_constant_renaming():
    """sokrates→socrates (d = 1/8) is aligned; the predicate is already equal."""
    prediction = _fol("Mortal(sokrates)")
    reference = _fol("Mortal(socrates)")
    assert align_symbols(prediction, reference) == reference


def test_function_and_predicate_namespaces_are_separate():
    """Predicate Foo and function foo align independently in their namespaces.

    (The grammar requires uppercase predicate symbols and lowercase function
    symbols, so the namespaces are exercised with case-distinct names.)
    """
    prediction = _fol("Foo(a) ∧ P(foo(a))")   # predicate Foo/1 AND function foo/1
    reference = _fol("Fooo(a) ∧ P(fooo(a))")
    assert align_symbols(prediction, reference) == reference


def test_modal_formula_atoms_align():
    """Alignment reaches atoms nested under modal operators."""
    mp = MSFLParser(modal=True)
    prediction = mp.parse("□Winner(a) → ◇Winner(a)")
    reference = mp.parse("□IsWinner(a) → ◇IsWinner(a)")
    assert align_symbols(prediction, reference) == reference


def test_alignment_with_itself_is_identity():
    """Aligning a formula against itself changes nothing (identity pairs win)."""
    f = _fol("∀x (P(x) → Q(f(x, c)))")
    assert align_symbols(f, f) == f


# ---------------------------------------------------------------------------
# The guarantees the lexical matcher cannot give.
# ---------------------------------------------------------------------------

def test_arity_mismatch_blocks_alignment():
    """P/1 is never aligned to the reference's P/2 (same name, wrong arity)."""
    prediction = _fol("P(a)")
    reference = _fol("P(b, c)")
    aligned = align_symbols(prediction, reference)
    assert aligned == prediction          # nothing to align at arity 1


def test_injectivity_two_symbols_never_merge():
    """Winner and Winners must not both collapse onto the reference's Winner.

    Merging them would make ``Winner(a) ∧ ¬Winners(a)`` contradictory — an
    alignment must never change the logical content. The identity pair
    Winner→Winner claims the target; Winners keeps its own name.
    """
    prediction = _fol("Winner(a) ∧ ¬Winners(a)")
    reference = _fol("Winner(a)")
    aligned = align_symbols(prediction, reference)
    assert aligned == prediction


def test_capture_freedom_never_rename_into_used_name():
    """Foo/2 is not renamed to Fo when the prediction already uses Fo/1.

    Renaming would manufacture a mixed-arity symbol Fo (arities 1 and 2) that
    the prediction never contained — validate() would flag it as a defect the
    alignment itself created.
    """
    prediction = _fol("Foo(a, b) ∧ Fo(a)")
    reference = _fol("Fo(a, b)")
    aligned = align_symbols(prediction, reference)
    assert aligned == prediction


def test_distance_threshold_is_respected():
    """Wins→IsWinner is 5/8 = 0.625 > 0.6: no alignment at the default threshold."""
    prediction = _fol("Wins(a)")
    reference = _fol("IsWinner(a)")
    assert align_symbols(prediction, reference) == prediction
    # ... but an explicit looser threshold accepts it.
    assert align_symbols(prediction, reference, max_norm_distance=0.7) == reference


def test_builtin_operators_are_never_aligned():
    """= is a built-in, not vocabulary: nothing to align between = and a predicate."""
    prediction = _fol("a = b")
    reference = _fol("Eq(a, b)")
    assert align_symbols(prediction, reference) == prediction


def test_aligned_exact_match_composes_with_canonical():
    """Vocabulary noise AND commutativity noise disappear together."""
    prediction = _fol("Winner(a) ∧ Playing(b)")
    reference = _fol("Plays(b) ∧ IsWinner(a)")     # swapped operands + renamed
    assert not exact_match(prediction, reference)  # canonical alone: vocabulary blocks
    assert aligned_exact_match(prediction, reference)
