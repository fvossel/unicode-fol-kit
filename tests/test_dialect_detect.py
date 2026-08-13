"""Tests for fol.dialect_detect — the detection order parse_any consumes.

Each expectation is hand-derived from the documented signals: which regex
fires on the text, whether the ASCII-only detectors participate, and the
invariant that ``"unicode"`` is always the terminal candidate.
"""

from unicode_fol_kit import api
from unicode_fol_kit.fol.dialect_detect import DIALECT_SIGNALS, detect_dialects


def test_smtlib_command_head_nominated_first():
    """'(assert (p a))' hits the smtlib signal; '(...)' alone hits nothing
    else (no =>, no ->, no fof(), no backslash), so: smtlib, unicode."""
    assert detect_dialects("(assert (p a))") == ("smtlib", "unicode")


def test_annotated_tptp_wrapper():
    """fof( … ) hits the tptp signal AND '=>'/… may hit tptp_bare: the fof
    fixture here contains '!' quantifier block too — hand-check: 'fof(a,
    axiom, ![X]: p(X)).' has 'fof(' (tptp) and '![' (tptp_bare, ASCII), no
    smt head, no latex, no prover9 signal ('->' absent; '&' absent; ' all '
    absent — but wait: '|' absent too). Order: tptp, tptp_bare, unicode."""
    assert detect_dialects("fof(a, axiom, ![X]: p(X)).") == (
        "tptp", "tptp_bare", "unicode")


def test_latex_backslash_commands():
    r"""'\forall x. P(x)' hits latex only (ASCII text without =>, ->, &, |,
    ~, ![, and 'x.' — note ' all ' does not occur)."""
    assert detect_dialects(r"\forall x. P(x)") == ("latex", "unicode")


def test_prover9_word_quantifier():
    """'all x (P(x) -> Q(x))' is ASCII with '->' (prover9) — '->' is NOT a
    tptp_bare signal ('=>' is), so: prover9, unicode."""
    assert detect_dialects("all x (P(x) -> Q(x))") == ("prover9", "unicode")


def test_bare_tptp_connectives():
    """'![X]: (p(X) => q(X))' hits tptp_bare; no annotated wrapper; no
    prover9 signal? Hand-check: '->' absent BUT '|' absent, '&' absent,
    ' all ' absent, 'exists ' absent — so exactly tptp_bare, unicode."""
    assert detect_dialects("![X]: (p(X) => q(X))") == ("tptp_bare", "unicode")


def test_non_ascii_skips_the_ascii_only_detectors():
    """'∀x (P(x) → Q(x))' is non-ASCII: tptp_bare/prover9 are skipped even
    though '→' is no signal anyway; nothing else fires → straight to
    unicode."""
    assert detect_dialects("∀x (P(x) → Q(x))") == ("unicode",)


def test_non_ascii_with_tilde_still_skips_ascii_only():
    """'¬P ∧ ~Q' contains '~' (a tptp_bare signal) but the TEXT is
    non-ASCII, so the ASCII-only detector stays out: unicode only."""
    assert detect_dialects("¬P ∧ ~Q") == ("unicode",)


def test_unicode_is_always_last_and_always_present():
    for text in ("", "P(x)", "(assert x)", "fof(a, axiom, p).", "x => y"):
        candidates = detect_dialects(text)
        assert candidates[-1] == "unicode"
        assert len(set(candidates)) == len(candidates)


def test_signal_table_is_the_documented_five():
    assert [name for name, _, _ in DIALECT_SIGNALS] == [
        "smtlib", "tptp", "latex", "tptp_bare", "prover9"]
    assert [ascii_only for _, _, ascii_only in DIALECT_SIGNALS] == [
        False, False, False, True, True]


def test_parse_any_agrees_with_the_nomination_winner():
    """End-to-end: for texts whose FIRST nominated dialect parses, parse_any
    must report exactly that dialect — the facade really consumes this
    order."""
    cases = {
        "(declare-fun p (Int) Bool)(assert (p 1))": "smtlib",
        "fof(a, axiom, p(alice)).": "tptp",
        r"\forall x (P(x) \rightarrow Q(x))": "latex",
        "all x (P(x) -> Q(x)).": "prover9",
        "![X]: (p(X) => q(X))": "tptp_bare",
        "∀x (P(x) → Q(x))": "fol",       # unicode ladder, classical mode
    }
    for text, expected in cases.items():
        result = api.parse_any(text)
        assert result.ok, (text, result.errors)
        assert result.dialect == expected, text
