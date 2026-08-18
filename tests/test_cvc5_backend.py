"""Tests for the cvc5 backend (atp/cvc5_backend.py).

Hand-checked contracts, each justified inline:

* PROVED / REFUTED are exactly as trustworthy as Z3Backend's — a modus-ponens
  instance is a textbook valid formula (Theorem), ``∀x P(x)`` is refutable by
  the one-element structure where ``P`` holds nowhere (a genuine
  countermodel, not a guess);
* an entailment with premises folds to the same ``(∧ premises) → φ`` shape
  Z3Backend uses, so a premise set that classically forces ``Q(a)`` must come
  back PROVED;
* linear-logic connectives have NO classical ``to_z3`` export by design (see
  ``fol/_linear_nodes.py``'s ``_NO_LINEAR_EXPORT``) — the backend must report
  that honestly as UNKNOWN/"unsupported", not silently drop to some other
  answer;
* every Verdict carries backend="cvc5", a derived szs_status, and a positive
  wall_time (the backend actually ran cvc5, it did not short-circuit).

Skipped entirely (module-level ``importorskip``) on a machine without the
``cvc5`` package installed — ``available()``/``decide()`` handle that
gracefully at runtime, but exercising PROVED/REFUTED/etc. genuinely needs a
working cvc5 binding.
"""

import pytest

cvc5 = pytest.importorskip("cvc5")

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, ERROR

_P = MSFLParser()
_LIN = MSFLParser(linear=True)

# Modus-ponens instance: ∀x(P(x)→Q(x)) ∧ P(a) → Q(a) is valid in every
# classical structure (instantiate the universal at a, then modus ponens) —
# a textbook Theorem, independent of any prover's search strategy.
_VALID = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")

# ∀x P(x) is refutable: the one-element structure {e} with P^I = ∅ satisfies
# ¬∀x P(x) (there is no witness making P true), so this is CounterSatisfiable,
# not a Theorem.
_INVALID = _P.parse("∀x P(x)")

_backend = Cvc5Backend()


def test_available_when_cvc5_importable():
    # The test module only gets this far if `import cvc5` already succeeded
    # (importorskip above), so pure-discovery availability must agree.
    assert _backend.available() is True


def test_proved_modus_ponens_instance():
    v = _backend.decide(_VALID)
    assert v.status == PROVED
    assert v.backend == "cvc5"
    assert v.szs_status == "Theorem"
    assert v.wall_time > 0


def test_refuted_universal_with_model_witness():
    v = _backend.decide(_INVALID)
    assert v.status == REFUTED
    assert v.szs_status == "CounterSatisfiable"
    assert v.countermodel["kind"] == "cvc5_model"
    # The negated goal ∃x ¬P(x) declares exactly one uninterpreted symbol
    # (the predicate P — x is existentially bound, not a free declaration),
    # so the witness assignment must name it; cvc5 must interpret P as false
    # somewhere (a constant-true P would satisfy the original ∀x P(x) and
    # this formula would not be refutable at all).
    assignment = v.countermodel["assignment"]
    assert "P" in assignment
    assert "false" in assignment["P"].lower()


def test_entailment_with_premises_forces_conclusion():
    # ∀x(P(x)→Q(x)) and P(a) classically entail Q(a) (universal instantiation
    # at a, then modus ponens) — the same textbook derivation as _VALID, just
    # split across the premises argument instead of folded into one formula.
    premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)")]
    conclusion = _P.parse("Q(a)")
    v = _backend.decide(conclusion, premises)
    assert v.status == PROVED
    assert v.agreement == ("cvc5",)


def test_entailment_with_premises_that_do_not_force_conclusion_is_refuted():
    # P(a) alone does NOT entail Q(a) (no link between P and Q is asserted) —
    # the structure {a} with P(a) true and Q(a) false is a countermodel to
    # the entailment, so this must be REFUTED, not UNKNOWN.
    premises = [_P.parse("P(a)")]
    conclusion = _P.parse("Q(a)")
    v = _backend.decide(conclusion, premises)
    assert v.status == REFUTED


def test_unsupported_linear_logic_formula_reports_honestly():
    # A ⊗ B (multiplicative conjunction) has no classical collapse — Node.to_z3
    # raises NotImplementedError by design (fol/_linear_nodes.py), so the
    # backend must surface UNKNOWN/"unsupported", never guess PROVED/REFUTED
    # and never let the NotImplementedError escape decide().
    tensor = _LIN.parse("A ⊗ B")
    v = _backend.decide(tensor)
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert v.szs_status == "Inappropriate"


def test_verdict_fields_are_fully_populated():
    v = _backend.decide(_VALID)
    d = v.to_dict()
    assert d["backend"] == "cvc5"
    assert d["logic"] == "fol"
    assert d["status"] == "proved"
    assert d["wall_time"] > 0
    assert d["agreement"] == ["cvc5"]


def test_decide_never_raises_on_a_crash_inducing_bad_option():
    # A garbage `logic=` string is rejected by cvc5's own option validation —
    # the backend must convert that into an ERROR/"infra" Verdict rather than
    # letting the exception propagate (the ProverBackend contract: decide()
    # must never raise for an in-contract Node).
    v = _backend.decide(_VALID, logic="NOT_A_REAL_SMTLIB_LOGIC")
    assert v.status == ERROR
    assert v.reason == "infra"


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — digit-leading names, which used to SEGFAULT
# the whole process (Z3's own to_smt2() does not quote a pure-ASCII
# digit-leading name, so the replayed SMT-LIB2 text was malformed, and cvc5's
# native parser crashed on it rather than raising a catchable Python
# exception — reproduced live before this fix, exit code 139). Every claim
# below is EXECUTED, never just asserted: against the real cvc5 backend
# (module-level importorskip already gates the whole file on cvc5 being
# importable) and, separately, against z3.parse_smt2_string as the R5
# ground truth for "is this SMT-LIB2 text actually legal".
# ---------------------------------------------------------------------------

from unicode_fol_kit.fol.msflparser import MSFLParser as _MSFLParser
from unicode_fol_kit.fol.nodes import Constant as _Constant
from unicode_fol_kit.atp.cvc5_backend import _sanitize_for_smtlib, _implication

_UPARSE = _MSFLParser().parse


class TestDigitLeadingNamesNoLongerCrash:
    def test_digit_leading_constant_does_not_segfault_and_returns_a_verdict(self):
        # Historically this line never returned at all (the process died) —
        # simply completing without an OS-level crash IS the regression
        # test; the assertions below check the answer is also correct.
        f = _UPARSE("P(2008SummerOlympics)")
        v = _backend.decide(f)
        assert v.status in ("proved", "refuted", "unknown", "error")

    def test_digit_leading_constant_reports_a_genuine_countermodel(self):
        f = _UPARSE("∀x P(x)")  # refutable, same shape as _INVALID
        premises = [_UPARSE("Q(2008SummerOlympics)")]  # forces the sort non-empty, name in scope
        v = _backend.decide(f, premises)
        assert v.status == REFUTED
        assert "2008SummerOlympics" in v.countermodel["assignment"]

    def test_digit_leading_predicate_name_does_not_crash_either(self):
        # A digit-leading identifier is ALWAYS term-valued in the grammar
        # (see fol._identifiers's module docstring: predicate-hood needs an
        # uppercase-signalling first character, which a digit cannot carry),
        # so this is reachable only via a programmatically built node, not
        # through the parser — exactly the pre-existing reachability path
        # the task's STAND note describes for every one of these gaps.
        from unicode_fol_kit.fol.nodes import Atom, Constant
        f = Atom("2008Wins", [Constant("alice")])
        v = _backend.decide(f)
        assert v.status in ("proved", "refuted", "unknown", "error")


class TestSmtlib2TextIsValidPerZ3sOwnParser:
    """R5: the sanitised SMT-LIB2 text round-trips through z3.parse_smt2_string
    — the actual bug reproduction/fix, independent of cvc5 being installed."""

    def test_digit_leading_name_smt2_text_parses(self):
        import z3

        f = _UPARSE("P(2008SummerOlympics)")
        goal = _implication(f, [])
        sanitised, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["2008SummerOlympics"][0].isalpha()
        z3_goal = sanitised.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        z3.parse_smt2_string(text)  # must not raise

    def test_unsanitised_digit_leading_name_smt2_text_does_NOT_parse(self):
        # Negative control: confirms the bug this module fixes is real and
        # that the test above is actually exercising the fix, not a formula
        # that was never broken.
        import z3

        f = _UPARSE("P(2008SummerOlympics)")
        goal = _implication(f, [])          # UNSANITISED goal
        z3_goal = goal.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        with pytest.raises(z3.Z3Exception):
            z3.parse_smt2_string(text)


class TestNonAsciiNamesAlreadyWorkedAndStayUntouched:
    """R1: a non-ASCII name already round-trips through Z3's own SMT-LIB2
    quoting correctly (verified live before this module's sanitisation
    existed) — _sanitize_for_smtlib must leave it identity-mapped, not
    rename something that already worked."""

    def test_non_ascii_constant_is_identity_mapped(self):
        f = _UPARSE("P(świątek)")
        goal = _implication(f, [])
        _, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["świątek"] == "świątek"

    def test_non_ascii_constant_still_decides_and_names_itself_in_countermodel(self):
        f = _UPARSE("∀x P(x)")
        premises = [_UPARSE("Q(świątek)")]
        v = _backend.decide(f, premises)
        assert v.status == REFUTED
        # R3 polish: the pipe-quoting cvc5's str(term) reproduces
        # ("|świątek|") is stripped, so the caller sees the TRUE original
        # name, not SMT-LIB2 quoting syntax wrapped around it.
        assert "świątek" in v.countermodel["assignment"]
        assert "|świątek|" not in v.countermodel["assignment"]


class TestR2CollisionAvoidance:
    def test_two_different_digit_leading_names_get_distinct_tokens(self):
        from unicode_fol_kit.fol.nodes import Atom
        goal = _implication(
            Atom("=", [_Constant("2008SummerOlympics"), _Constant("2012London")]), [])
        _, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["2008SummerOlympics"] != mapping.mapping["2012London"]

    def test_synthesised_token_never_collides_with_an_already_legal_name(self):
        from unicode_fol_kit.fol.nodes import Atom
        # "n2008x" is what a naive synthesis of "2008x" would target; a
        # literal constant ALREADY named "n2008x" must not be clobbered,
        # regardless of which one this walk reaches first.
        for args in ([_Constant("n2008x"), _Constant("2008x")],
                    [_Constant("2008x"), _Constant("n2008x")]):
            goal = _implication(Atom("=", args), [])
            _, mapping = _sanitize_for_smtlib(goal)
            assert mapping.mapping["n2008x"] == "n2008x"
            assert mapping.mapping["2008x"] != "n2008x"
