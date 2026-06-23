"""Regression tests for export/rendering fixes (TPTP, Prover9, LaTeX).

These cover the previously untested export paths:
- Xor.to_tptp must use the TPTP non-equivalence operator <~>, not ~| (NOR).
- TPTP arithmetic comparisons (<, >, ≤, ≥) are prefix dollar-word predicates.
- Equality / disequality stay infix in TPTP.
- Nullary predicates render as bare propositional atoms in Prover9 (not P()).
- Prover9 variables are uppercased so they are recognised under
  set(prolog_style_variables); constants stay lowercase.
- to_latex() escapes the underscore in c_-prefixed constants.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol._fol_nodes import Atom, Number, Xor, Constant

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)


class TestTptpXor:
    def test_xor_uses_non_equivalence(self):
        assert FOL.parse("P ⊕ Q").to_tptp() == "(p <~> q)"

    def test_xor_not_nor(self):
        # ~| is NOR in TPTP, which is truth-functionally distinct from XOR.
        assert "~|" not in FOL.parse("P ⊕ Q").to_tptp()


class TestTptpComparisons:
    @pytest.mark.parametrize("op, expected", [
        ("<", "$less(1,2)"),
        (">", "$greater(1,2)"),
        ("≤", "$lesseq(1,2)"),
        ("≥", "$greatereq(1,2)"),
    ])
    def test_arithmetic_comparisons_are_prefix(self, op, expected):
        assert Atom(op, [Number(1), Number(2)]).to_tptp() == expected

    @pytest.mark.parametrize("op, expected", [
        ("=", "(1 = 2)"),
        ("≠", "(1 != 2)"),
    ])
    def test_equality_stays_infix(self, op, expected):
        assert Atom(op, [Number(1), Number(2)]).to_tptp() == expected

    def test_end_to_end(self):
        assert (FOL.parse("∀x (x ≤ 2 → x < 3)").to_tptp()
                == "(![X]: ($lesseq(X,2) => $less(X,3)))")


class TestProver9NullaryAtom:
    def test_nullary_atom_is_bare(self):
        assert Atom("Rain", []).to_prover9() == "Rain"

    def test_nullary_atom_in_conjunction(self):
        assert FOL.parse("Rain ∧ Wind").to_prover9() == "(Rain & Wind)"


class TestProver9Variables:
    def test_quantified_variable_is_uppercased(self):
        # Under set(prolog_style_variables) a variable must start uppercase.
        assert (FOL.parse("∀x (Human(x) → Mortal(x))").to_prover9()
                == "(all X (Human(X) -> Mortal(X)))")

    def test_constant_stays_lowercase(self):
        assert FOL.parse("Human(socrates)").to_prover9() == "Human(socrates)"


class TestLatexUnderscore:
    def test_c_constant_underscore_escaped(self):
        assert FOL.parse("P(c_zero)").to_latex() == "P(c\\_zero)"

    def test_c_constant_comparison(self):
        assert FOL.parse("c_a = c_b").to_latex() == "c\\_a = c\\_b"

    def test_sorted_c_constant(self):
        assert MSFOL.parse("P(c_a:Human)").to_latex() == "P(c\\_a{:}\\mathrm{Human})"

    def test_plain_constant_unaffected(self):
        # Names without underscores are emitted verbatim.
        assert Constant("alice").to_latex() == "alice"
