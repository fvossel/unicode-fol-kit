"""Regression tests for export/rendering fixes (TPTP, Prover9, LaTeX).

These cover the previously untested export paths:
- Xor.to_tptp must use the TPTP non-equivalence operator <~>, not ~| (NOR).
- TPTP arithmetic comparisons (<, >, ≤, ≥) are prefix dollar-word predicates.
- Equality / disequality stay infix in TPTP.
- Nullary predicates render as bare propositional atoms in Prover9 (not P()).
- Prover9 variables are uppercased so they are recognised under
  set(prolog_style_variables); constants stay lowercase.
- to_latex() escapes the underscore in c_-prefixed constants.
- TPTP name folding (Atom/Function/Constant) touches only the FIRST
  character, mirroring tptp_input.py's _cap() exactly, instead of
  lower-casing the whole name.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol._fol_nodes import Atom, Function, Number, Variable, Xor, Constant
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula

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


class TestTptpNameFolding:
    """``Node.to_tptp`` used to fold a predicate/function/constant name to
    TPTP's required lowercase-initial form by calling ``.lower()`` on the
    WHOLE string. That is wrong two ways: it is not the true inverse of
    ``tptp_input.py``'s ``_cap()`` (which capitalises only the FIRST
    character of a parsed predicate name on import), and it mangles a
    mixed-case function/constant name that needed no folding at all (those
    are never touched by ``_cap()`` on import in the first place). The fix
    folds only the first character (see ``fol._fol_nodes.tptp_fold_first_letter``).
    """

    # -- predicate names (Atom) ------------------------------------------------

    def test_atom_predicate_folds_only_first_letter(self):
        # 'BDouble' would have collapsed to 'bdouble' under the old whole-
        # string .lower() — only the leading 'B' is touched now.
        assert Atom("BDouble", [Variable("a")]).to_tptp() == "bDouble(A)"

    def test_atom_predicate_already_lower_first_letter_is_unchanged(self):
        # A predicate whose first letter is already lower-case (reachable
        # only via the Python API, e.g. unicode_fol_kit.chem.mol — the
        # PREDICATE grammar token always capitalises the first letter for a
        # parsed atom) is emitted byte-for-byte, not touched at all.
        assert Atom("bDOUBLE", []).to_tptp() == "bDOUBLE"

    def test_atom_predicate_nullary_folds_only_first_letter(self):
        assert Atom("ChiralR", []).to_tptp() == "chiralR"

    # -- function / constant names --------------------------------------------

    def test_function_name_folds_only_first_letter(self):
        assert (Function("hasBondTo", [Variable("a"), Variable("b")]).to_tptp()
                == "hasBondTo(A,B)")

    def test_constant_name_folds_only_first_letter(self):
        # A mixed-case constant survives unmangled beyond its first letter
        # (which is already lower-case per the kit's own NAME-token
        # convention, so this is in fact a no-op fold).
        assert Constant("hasBond").to_tptp() == "hasBond"

    # -- round-trip: to_tptp() -> parse_tptp_formula() recovers the SAME symbol -

    @pytest.mark.parametrize("predicate_name", ["BDouble", "HasBondTo", "ChiralR"])
    def test_atom_predicate_round_trips_through_tptp(self, predicate_name):
        """Reproduces the reported bug: under the old whole-string .lower(),
        'bDOUBLE'.to_tptp() -> 'bdouble', which re-parses (tptp_input._cap
        capitalises only the first letter) to 'Bdouble' — a DIFFERENT
        symbol than the original 'bDOUBLE'/'BDouble'. With only-the-first-
        letter folding, to_tptp() and _cap() are exact inverses of each
        other, so the round trip recovers the identical predicate name.
        """
        original = Atom(predicate_name, [Variable("a")])
        reparsed = parse_tptp_formula(original.to_tptp())
        assert reparsed == original
        assert reparsed.predicate == predicate_name

    @pytest.mark.parametrize("name", ["hasBond", "hasBondTo", "aliceSmith"])
    def test_constant_name_round_trips_through_tptp(self, name):
        """Function/Constant names are never touched by _cap() on import (only
        Atom predicates are), so they need NO folding at all — a mixed-case
        constant name must survive to_tptp() -> parse_tptp_formula()
        completely unchanged, which the old whole-string .lower() broke.

        Wrapped in an equality atom (rather than parsed bare) because a bare
        TPTP identifier in FORMULA position parses as a 0-ary predicate
        (``prop_atom``, ``_cap()``-folded), not a term — an equality atom's
        two sides are the term position that actually exercises the
        ``constant()`` import handler this is testing.
        """
        original = Atom("=", [Constant(name), Constant(name)])
        reparsed = parse_tptp_formula(original.to_tptp())
        assert reparsed == original
        assert reparsed.args[0].name == name

    # -- documented residual: folding alone is not injective -------------------

    def test_first_letter_fold_alone_still_collides_on_case_of_first_letter(self):
        """'Foo' and 'foo' differ ONLY in the case of their first letter, so
        folding just that one character still maps both to 'foo' — this
        residual collision is exactly what the collision guard in
        atp._tptp_problem.generate_tptp_problem (and atp.tptp_ncl.to_tptp_ncl)
        exists to catch across a WHOLE problem's formulas; a single node's
        to_tptp() has no way to detect it in isolation. See
        tests/test_tptp_problem.py for the guard itself.
        """
        assert (Atom("Foo", [Variable("a")]).to_tptp()
                == Atom("foo", [Variable("a")]).to_tptp()
                == "foo(A)")


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
