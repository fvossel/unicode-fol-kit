"""Tests for the unicode_fol_kit command-line interface."""

import json
import sys

from unicode_fol_kit.__main__ import main


def test_tptp_output(capsys):
    """--to tptp renders the implication arrow as '=>'."""
    rc = main(["∀x (P(x) → Q(x))", "--to", "tptp"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "=>" in out


def test_latex_output(capsys):
    """--to latex emits the LaTeX \\forall command."""
    rc = main(["∀x P(x)", "--to", "latex"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "\\forall" in out


def test_msfl_strong_conjunction_unicode(capsys):
    """--mode msfl with a strong-conjunction formula renders '⊗' in unicode."""
    rc = main(["P(x) ⊗ Q(x)", "--mode", "msfl", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "⊗" in out


def test_invalid_formula_returns_1(capsys):
    """A syntactically invalid formula returns 1 and writes to stderr."""
    rc = main(["∀x (P(x)"])  # unbalanced parenthesis -> ParsingError
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


def test_default_mode_and_format_is_tree(capsys):
    """With no flags the default rendering is the ASCII tree."""
    rc = main(["P(x)"])
    assert rc == 0
    out = capsys.readouterr().out
    # tree_str of an atom starts with the 'Atom:' label.
    assert "Atom: P" in out


def test_unicode_round_trip(capsys):
    """--to unicode reproduces the parsed formula."""
    rc = main(["∀x (P(x) → Q(x))", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "∀x (P(x) → Q(x))"


def test_json_output_is_valid_json(capsys):
    """--to json prints a parseable JSON object carrying the node type."""
    rc = main(["P(x)", "--to", "json"])
    assert rc == 0
    out = capsys.readouterr().out
    data = json.loads(out)
    assert data["_type"] == "Atom"


def test_prover9_output(capsys):
    """--to prover9 renders the implication as Prover9's '->'."""
    rc = main(["P(x) → Q(x)", "--to", "prover9"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "->" in out


def test_dot_output(capsys):
    """--to dot emits a Graphviz digraph header."""
    rc = main(["P(x)", "--to", "dot"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "digraph" in out


def test_invalid_character_returns_1(capsys):
    """A lexer-level failure (stray character) also returns 1."""
    rc = main(["P(x) @ Q(x)"])
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""


def test_msfol_sorted_quantifier_round_trip(capsys):
    """--mode msfol parses sort annotations and round-trips them in unicode."""
    rc = main(["∀x:Nat P(x)", "--mode", "msfol", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert out == "∀x:Nat P(x)"


def test_fl_strong_disjunction_unicode(capsys):
    """--mode fl (unsorted Łukasiewicz) renders strong disjunction '⊕'."""
    rc = main(["P(x) ⊕ Q(x)", "--mode", "fl", "--to", "unicode"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "⊕" in out


def test_circle_plus_is_xor_in_fol_but_strong_disjunction_in_fl(capsys):
    """The '⊕' glyph is mode-dependent: Xor in fol, StrongDisjunction in fl.

    The CLI must defer this to the parser mode rather than fixing one meaning.
    """
    rc = main(["P(x) ⊕ Q(x)", "--mode", "fol", "--to", "json"])
    assert rc == 0
    fol_data = json.loads(capsys.readouterr().out)
    assert fol_data["_type"] == "Xor"

    rc = main(["P(x) ⊕ Q(x)", "--mode", "fl", "--to", "json"])
    assert rc == 0
    fl_data = json.loads(capsys.readouterr().out)
    assert fl_data["_type"] == "StrongDisjunction"


def test_default_argv_reads_sys_argv(capsys, monkeypatch):
    """main() with no argument falls back to sys.argv[1:]."""
    monkeypatch.setattr(sys, "argv", ["unicode_fol_kit", "P(x)", "--to", "json"])
    rc = main()
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["_type"] == "Atom"


def test_msfol_mode_rejects_strong_conjunction(capsys):
    """⊗ is not a classical operator: msfol mode must reject it (returns 1)."""
    rc = main(["P(x) ⊗ Q(x)", "--mode", "msfol"])
    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err.strip() != ""
