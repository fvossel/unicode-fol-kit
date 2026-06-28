"""LIVE Isabelle build checks for the NON-modal exporters.

Skipped unless a real Isabelle/HOL is found (``isabelle_available()``). Each test
emits a known-status formula and asserts ``isabelle build`` discharges (or, for the
honest ``oops`` case, loads) the emitted theory. These catch proof bugs that text
tests cannot — e.g. the K3/LP validity lemma used to emit ``by (simp add: des_def)``,
which does NOT close the goal (``simp`` cannot reduce ``kneg v`` for abstract ``v``).
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, Or, Implies, Constant, Quantifier, Variable,
)
from unicode_fol_kit.hol.classical import to_isabelle_fol, to_isabelle_msfol
from unicode_fol_kit.hol.manyvalued import to_isabelle_k3lp, to_isabelle_k3lp_entailment
from unicode_fol_kit.hol.intuitionistic import to_isabelle_intuitionistic
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

pytestmark = pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")

p, q = Atom("p", ()), Atom("q", ())
pa = Atom("P", [Constant("a")])
x = Variable("x")


def _build_ok(theory_text, theory_name, session=None):
    r = check_theory(theory_text, theory_name, session=session, session_timeout=60)
    assert r.ok, f"build failed (exit {r.exit_code}):\n{r.output[-1200:]}"
    return r


# --- classical FOL / MSFOL ------------------------------------------------- #

def test_fol_valid_proves_by_auto():
    _build_ok(to_isabelle_fol(Implies(pa, pa), theory_name="FOL_Export",
                              proof="by auto"), "FOL_Export")


def test_msfol_valid_proves_by_auto():
    _build_ok(to_isabelle_msfol(Implies(pa, pa), theory_name="MSFOL_Export",
                                proof="by auto"), "MSFOL_Export")


# --- many-valued K3 / LP (the proof-bug regression) ------------------------ #

def test_k3lp_lp_valid_forall_discharges():
    # LP-valid p ∨ ¬p: ∀-form must close via case exhaustion (not bare simp).
    _build_ok(to_isabelle_k3lp(Or(p, Not(p)), "LP"), "K3LP_Validity")


def test_k3lp_k3_invalid_exists_discharges():
    # K3-invalid p ∨ ¬p: ∃-refutation must close via the exI witness.
    _build_ok(to_isabelle_k3lp(Or(p, Not(p)), "K3"), "K3LP_Validity")


def test_k3lp_invalid_two_variable_exists_discharges():
    # 2-variable ∃ witness (p → q is K3-invalid).
    _build_ok(to_isabelle_k3lp(Implies(p, q), "K3"), "K3LP_Validity")


def test_k3lp_entailment_valid_and_invalid_discharge():
    _build_ok(to_isabelle_k3lp_entailment([p, Not(p)], q, "K3"),
              "K3LP_Entailment", session="S_entail_k3")   # explosion valid in K3 (∀)
    _build_ok(to_isabelle_k3lp_entailment([p, Not(p)], q, "LP"),
              "K3LP_Entailment", session="S_entail_lp")   # invalid in LP (∃ witness)


# --- intuitionistic (GMT → S4): real proof for valid, oops for invalid ----- #

def test_intuitionistic_valid_formula_proves():
    # p → p is IPL-valid: the emitted theory carries a real proof that discharges.
    _build_ok(to_isabelle_intuitionistic(Implies(p, p)), "IPL_GMT")


def test_intuitionistic_invalid_formula_loads_as_oops():
    # p ∨ ¬p is IPL-invalid: the theory is left `oops` but still loads.
    _build_ok(to_isabelle_intuitionistic(Or(p, Not(p))), "IPL_GMT")


# Harder IPL validities than p→p: the verdict-dependent proof emits a real battery
# for each, so a *successful build* exercises that the battery actually closes the
# box-nested GMT goal (audit finding: proof-completeness was only tested on p→p).
_HARDER_IPL_VALID = [
    Implies(Implies(p, q), Implies(Not(q), Not(p))),   # contraposition
    Not(Not(Or(p, Not(p)))),                           # ¬¬(p ∨ ¬p)
    Implies(Not(Not(Not(p))), Not(p)),                 # triple negation
    Implies(p, Not(Not(p))),                           # ¬¬ introduction
]


@pytest.mark.parametrize("f", _HARDER_IPL_VALID,
                         ids=["contraposition", "dneg-lem", "triple-neg", "dneg-intro"])
def test_intuitionistic_harder_valid_formulas_prove(f):
    _build_ok(to_isabelle_intuitionistic(f), "IPL_GMT")


def test_intuitionistic_atom_named_r_or_w_builds():
    # atoms `r` / `w` collide with the relation / axiom variables; the de-collision
    # must keep the theory loadable for these valid formulas. Audit regression.
    rr, ww = Atom("r", ()), Atom("w", ())
    _build_ok(to_isabelle_intuitionistic(Implies(rr, rr)), "IPL_GMT", session="S_atom_r")
    _build_ok(to_isabelle_intuitionistic(Implies(ww, ww)), "IPL_GMT", session="S_atom_w")
