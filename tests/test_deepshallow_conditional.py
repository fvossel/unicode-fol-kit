"""Lewis conditional (sphere) deep + maximal/minimal shallow embedding + faithfulness.

Structure tests always run; the live test builds the emitted theory in Isabelle, so
exit 0 certifies the five faithfulness theorems over the sphere semantics — including
the non-trivial CondD (counterfactual) case.
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, And, Implies, Box
from unicode_fol_kit.hol import (
    conditional_faithfulness_theory, counterfactual_to_deep,
)
from unicode_fol_kit.hol.deepshallow._common import AtomConsts
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

p, q = Atom("p", ()), Atom("q", ())


def test_encoder_would_and_might():
    assert counterfactual_to_deep(p, q, AtomConsts(), "would") == "(CondD (Atm p_p) (Atm p_q))"
    assert counterfactual_to_deep(p, q, AtomConsts(), "might") == (
        "(NegD (CondD (Atm p_p) (NegD (Atm p_q))))")


def test_encoder_boolean_antecedent():
    ac = AtomConsts()
    assert counterfactual_to_deep(And(p, q), Not(q), ac, "would") == (
        "(CondD (AndD (Atm p_p) (Atm p_q)) (NegD (Atm p_q)))")


def test_encoder_rejects_bad_kind_and_nonpropositional():
    with pytest.raises(ValueError):
        counterfactual_to_deep(p, q, AtomConsts(), "somehow")
    with pytest.raises(NotImplementedError):
        counterfactual_to_deep(Box(p), q, AtomConsts(), "would")  # modal antecedent


def test_theory_has_sphere_semantics_and_faithfulness():
    t = conditional_faithfulness_theory("CondFaithfulness")
    assert "datatype cpl" in t and "definition nested" in t
    assert "CondD cpl cpl" in t and "definition CondS" in t and "definition CondM" in t
    for thm in ("faithful1a", "faithful1b", "faithful2", "faithful3", "sound_min"):
        assert f"theorem {thm}" in t
    assert "oops" not in t and "sorry" not in t


def test_theory_with_counterfactual_appends_definition():
    t = conditional_faithfulness_theory("CondFaithfulnessEx",
                                        antecedent=And(p, q), consequent=q, kind="might")
    assert 'definition example :: cpl where "example =' in t
    assert "(NegD (CondD" in t


def test_theory_requires_both_or_neither():
    with pytest.raises(ValueError):
        conditional_faithfulness_theory("X", antecedent=p)


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_verifies_in_isabelle():
    t = conditional_faithfulness_theory("CondFaithfulness")
    r = check_theory(t, "CondFaithfulness", session_timeout=180)
    assert r.ok, ("Isabelle failed to discharge conditional faithfulness:\n"
                  + r.output[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_with_counterfactual_verifies_in_isabelle():
    t = conditional_faithfulness_theory("CondFaithfulnessEx",
                                        antecedent=p, consequent=q, kind="would")
    r = check_theory(t, "CondFaithfulnessEx", session_timeout=180)
    assert r.ok, r.output[-2000:]
