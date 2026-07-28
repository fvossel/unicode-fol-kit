"""Tests for TPTP header-comment metadata extraction (``TptpHeader`` / ``TptpProblem``).

TPTP problem files carry a standardised ``%``-comment block (``% Status``,
``% Rating``, ``% Domain``, ``% Problem``, ``% File``, plus free-form lines like
``% Refs``/``% Version``/banner dashes). The Lark grammar in ``tptp_input.py``
``%``-ignores every comment, so :func:`parse_tptp` never sees any of it; the header
reader added here scans the *raw* text for it independently, then delegates formula
parsing unchanged to :func:`parse_tptp`. This file also pins the old
``parse_tptp`` / ``parse_tptp_formula`` / ``load_tptp`` / ``TptpFormula`` API exactly
as it was, per the task's "must not change" requirement.
"""

import dataclasses

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, Or, Variable, Constant
from unicode_fol_kit.fol.tptp_input import (
    parse_tptp,
    parse_tptp_formula,
    load_tptp,
    TptpFormula,
    parse_tptp_problem,
    load_tptp_problem,
    TptpHeader,
    TptpProblem,
)


# ---------------------------------------------------------------------------
# A realistic TPTP header block (modelled on the real TPTP library layout,
# e.g. PUZ001-1.p / GRP001-1.p) + 3 fof statements, built line-by-line so the
# expected `comments` tuple below can be hand-counted exactly.
# ---------------------------------------------------------------------------

_HEADER_LINES = [
    "%--------------------------------------------------------------------------",
    "% File     : PUZ001-1 : TPTP v8.1.0. Released v1.0.0.",
    "% Domain   : Puzzles",
    "% Problem  : Dreadbury Mansion",
    "% Version  : Especial.",
    "% English  : Someone who lives in Dreadbury Mansion killed Aunt Agatha.",
    "%",
    "% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing ATPs.",
    "% Source   : [TPTP]",
    "% Names    : Problem 55 [Pel86]",
    "%",
    "% Status   : Theorem",
    "% Rating   : 0.43 v8.1.0, 0.36 v7.4.0, 0.29 v7.3.0",
    "% Syntax   : Number of formulae    :    9 (   0 unit)",
    "%--------------------------------------------------------------------------",
]
_FOF_LINES = [
    "fof(ax1, axiom, ![X]: (man(X) => mortal(X))).",
    "fof(ax2, hypothesis, man(socrates)).",
    "fof(goal, conjecture, mortal(socrates)).",
]
TEXT_A = "\n".join(_HEADER_LINES + _FOF_LINES) + "\n"


# ---------------------------------------------------------------------------
# (a) full header + 3 fof statements: every field extracted correctly, and the
#     formula list is identical to plain parse_tptp on the same text.
# ---------------------------------------------------------------------------

def test_tptp_header_full_block():
    result = parse_tptp_problem(TEXT_A)
    assert isinstance(result, TptpProblem)
    h = result.header
    assert isinstance(h, TptpHeader)
    assert h.status == "Theorem"
    assert h.rating == pytest.approx(0.43)
    assert h.domain == "Puzzles"
    assert h.problem == "Dreadbury Mansion"
    assert h.file == "PUZ001-1 : TPTP v8.1.0. Released v1.0.0."
    # every raw '%' line is preserved verbatim, in order, trailing newline stripped
    assert h.comments == tuple(_HEADER_LINES)

    assert len(result.formulas) == 3
    # formula-list equality with plain parse_tptp on the same text
    assert list(result.formulas) == parse_tptp(TEXT_A)
    assert result.formulas[0].name == "ax1" and result.formulas[0].role == "axiom"
    assert result.formulas[1].formula == Atom("Man", [Constant("socrates")])
    assert result.formulas[2].role == "conjecture"


# ---------------------------------------------------------------------------
# (b) headerless input -> all-None header except comments, which reflect any
#     stray '%' lines that aren't field lines.
# ---------------------------------------------------------------------------

def test_tptp_header_absent_no_percent_lines():
    text = "fof(a, axiom, p(a)).\n"
    result = parse_tptp_problem(text)
    assert result.header == TptpHeader(None, None, None, None, None, ())
    assert len(result.formulas) == 1


def test_tptp_header_stray_comments_not_field_lines():
    text = (
        "% just a stray remark, not a field line\n"
        "fof(a, axiom, p(a)).\n"
        "% another stray one\n"
    )
    result = parse_tptp_problem(text)
    h = result.header
    assert h.status is None
    assert h.rating is None
    assert h.domain is None
    assert h.problem is None
    assert h.file is None
    assert h.comments == (
        "% just a stray remark, not a field line",
        "% another stray one",
    )


# ---------------------------------------------------------------------------
# (c) rating '?' -> None (no float parses).
# ---------------------------------------------------------------------------

def test_tptp_header_rating_unknown():
    text = "% Status   : Open\n% Rating   : ?\nfof(a, axiom, p(a)).\n"
    h = parse_tptp_problem(text).header
    assert h.status == "Open"
    assert h.rating is None


# ---------------------------------------------------------------------------
# (d) multiple Status lines -> first wins.
# ---------------------------------------------------------------------------

def test_tptp_header_first_status_wins():
    text = (
        "% Status   : Theorem\n"
        "% Status   : CounterSatisfiable\n"
        "fof(a, axiom, p(a)).\n"
    )
    h = parse_tptp_problem(text).header
    assert h.status == "Theorem"
    # both lines are still preserved verbatim in comments
    assert h.comments == ("% Status   : Theorem", "% Status   : CounterSatisfiable")


# ---------------------------------------------------------------------------
# (e) arbitrary spacing/alignment variants around '%' / field name / ':' all parse.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("line", [
    "% Status   : Theorem",
    "% Status : Theorem",
    "%Status:Theorem",
    "%   Status   :   Theorem",
    "% Status:Theorem",
    "%    Status    :Theorem",
    "  % Status : Theorem",   # leading whitespace before the '%' itself
])
def test_tptp_header_status_spacing_variants(line):
    text = line + "\nfof(a, axiom, p(a)).\n"
    assert parse_tptp_problem(text).header.status == "Theorem"


# ---------------------------------------------------------------------------
# (f) CNF-format file with header.
# ---------------------------------------------------------------------------

def test_tptp_header_with_cnf_statements():
    text = (
        "% Status   : Unsatisfiable\n"
        "% Rating   : 1.00 v8.1.0\n"
        "cnf(cl1, axiom, (~p(X) | q(X))).\n"
    )
    result = parse_tptp_problem(text)
    assert result.header.status == "Unsatisfiable"
    assert result.header.rating == pytest.approx(1.00)
    assert len(result.formulas) == 1
    assert result.formulas[0].formula == Or(
        Not(Atom("P", [Variable("x")])), Atom("Q", [Variable("x")]))


# ---------------------------------------------------------------------------
# (g) regression: the old API (parse_tptp / parse_tptp_formula / load_tptp /
#     TptpFormula) is completely untouched by this task.
# ---------------------------------------------------------------------------

def test_tptp_regression_parse_tptp_untouched():
    result = parse_tptp(TEXT_A)
    assert len(result) == 3
    assert all(isinstance(r, TptpFormula) for r in result)
    # TptpFormula still has exactly its original 3 fields, nothing added/removed
    field_names = tuple(f.name for f in dataclasses.fields(TptpFormula))
    assert field_names == ("name", "role", "formula")
    assert result[0].name == "ax1" and result[0].role == "axiom"
    assert result[1].name == "ax2" and result[1].role == "hypothesis"
    assert result[2].name == "goal" and result[2].role == "conjecture"
    assert result[1].formula == Atom("Man", [Constant("socrates")])


def test_tptp_regression_parse_tptp_formula_untouched():
    assert parse_tptp_formula("p(a)") == Atom("P", [Constant("a")])
    assert parse_tptp_formula("![X]: (p(X) => q(X))") == parse_tptp_formula(
        "![X]: (p(X) => q(X))")


def test_tptp_regression_load_tptp_untouched(tmp_path):
    p = tmp_path / "regression.p"
    p.write_text(TEXT_A, encoding="utf-8")
    result = load_tptp(str(p))
    assert len(result) == 3
    assert all(isinstance(r, TptpFormula) for r in result)
    assert result[0].name == "ax1" and result[0].role == "axiom"


# ---------------------------------------------------------------------------
# (h) load_tptp_problem from an actual temp file on disk.
# ---------------------------------------------------------------------------

def test_tptp_load_problem_from_file(tmp_path):
    p = tmp_path / "puz001.p"
    p.write_text(TEXT_A, encoding="utf-8")
    result = load_tptp_problem(str(p))
    assert isinstance(result, TptpProblem)
    assert result.header.status == "Theorem"
    assert result.header.rating == pytest.approx(0.43)
    assert result.header.domain == "Puzzles"
    assert len(result.formulas) == 3
    # matches load_tptp on the same file (formula-list equality)
    assert list(result.formulas) == load_tptp(str(p))
