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
