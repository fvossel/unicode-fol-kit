"""Which formulas each of the three matrices designates under every valuation.

Derived by hand. K3 has the values 0, 1/2, 1 with 1 designated; LP the same with 1/2 and 1
designated; FDE has T, F, N (neither), B (both) with T and B designated.

* K3 has no valid formula built from letters alone: the valuation that gives every letter 1/2
  gives every such formula 1/2 (``¬1/2 = 1/2``, ``min`` and ``max`` of 1/2 and 1/2 are 1/2), and
  1/2 is not designated. ``p → p`` and ``p ∨ ¬p`` are therefore K3-invalid.
* FDE has none either, for the same reason with N: ``¬N = N``, ``N ∧ N = N``, ``N ∨ N = N``,
  and N is not designated.
* LP has some: ``max(p, 1 - p) ≥ 1/2`` for every ``p``, so ``p ∨ ¬p`` is designated everywhere.
* With the truth constants K3 and FDE have valid formulas: ``⊤`` is T (1), and ``⊥ → p`` is
  ``¬⊥ ∨ p = T ∨ p = T``, ``p → ⊤`` is ``¬p ∨ T = T``. ``⊥`` is valid in none.
"""

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import matrix as mx

PARSER = MSFLParser()

#: formula -> (K3, LP, FDE) validity
TABLE = {
    "P → P": (False, True, False),
    "P ∨ ¬P": (False, True, False),
    "P ↔ P": (False, True, False),
    "⊤": (True, True, True),
    "⊥ → P": (True, True, True),
    "P → ⊤": (True, True, True),
    "⊥": (False, False, False),
    "(P ∧ ¬P) → Q": (False, True, False),
}


@pytest.mark.parametrize("text", list(TABLE))
def test_the_validity_of_a_formula_in_each_matrix(text):
    formula = PARSER.parse(text)
    k3, lp, fde = TABLE[text]
    assert mx.matrix_is_valid(formula, mx.K3_MATRIX) is k3
    assert mx.matrix_is_valid(formula, mx.LP_MATRIX) is lp
    assert mx.matrix_is_valid(formula, mx.FDE_MATRIX) is fde


@pytest.mark.parametrize("text", ["P → P", "P ∨ ¬P", "¬P ∧ (Q ∨ P)", "(P → Q) ↔ (¬Q → ¬P)", "¬¬P"])
def test_a_formula_of_letters_alone_takes_the_value_neither_when_every_letter_does(text):
    formula = PARSER.parse(text)
    assert mx.matrix_value(formula, {"P": "N", "Q": "N"}, mx.FDE_MATRIX) == "N"
    assert mx.matrix_value(formula, {"P": 0.5, "Q": 0.5}, mx.K3_MATRIX) == 0.5
