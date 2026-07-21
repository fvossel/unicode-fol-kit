"""Relevant logic B deep + maximal/minimal shallow embedding with faithfulness proofs.

Structure tests always run; the live test builds the emitted theory in Isabelle, so
exit 0 certifies the five faithfulness theorems over the simplified Routley–Meyer
semantics — including the star-negation and normal/non-normal implication clauses.
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, And, Or, Implies, Iff, Box, Xor
from unicode_fol_kit.hol import relevant_faithfulness_theory, rel_to_deep
from unicode_fol_kit.hol.deepshallow._common import AtomConsts
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

p, q = Atom("p", ()), Atom("q", ())
# A relevant "paradox" that must NOT be valid in B: p → (q → p).
PARADOX = Implies(p, Implies(q, p))


def test_encoder_maps_relevant_connectives():
    assert rel_to_deep(PARADOX, AtomConsts()) == (
        "(ImpD (Atm p_p) (ImpD (Atm p_q) (Atm p_p)))")


def test_encoder_desugars_iff_to_conjunction_of_implications():
    assert rel_to_deep(Iff(p, q), AtomConsts()) == (
        "(AndD (ImpD (Atm p_p) (Atm p_q)) (ImpD (Atm p_q) (Atm p_p)))")


@pytest.mark.parametrize("node, head", [
    (Not(p), "NegD"), (And(p, q), "AndD"), (Or(p, q), "OrD"), (Implies(p, q), "ImpD"),
])
def test_encoder_constructor_heads(node, head):
    assert rel_to_deep(node, AtomConsts()).startswith(f"({head} ")


def test_encoder_rejects_modalities_and_xor():
    for bad in (Box(p), Xor(p, q)):
        with pytest.raises(NotImplementedError):
            rel_to_deep(bad, AtomConsts())


def test_theory_has_routley_meyer_and_faithfulness():
    t = relevant_faithfulness_theory("RelFaithfulness")
    assert "datatype rpl" in t
    assert "definition involutive" in t and "definition rsource" in t
    # star-negation and the two-branch implication
    assert "NegM f \\<equiv> \\<lambda>x. \\<not> f (Star x)" in t
    assert "Nrm x \\<longrightarrow>" in t and "\\<not> Nrm x \\<longrightarrow>" in t
    for thm in ("faithful1a", "faithful1b", "faithful2", "faithful3", "sound_min"):
        assert f"theorem {thm}" in t
    assert "oops" not in t and "sorry" not in t


def test_theory_with_formula_appends_definition():
    t = relevant_faithfulness_theory("RelFaithfulnessEx", formula=PARADOX)
    assert 'definition example :: rpl where "example =' in t


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_verifies_in_isabelle():
    t = relevant_faithfulness_theory("RelFaithfulness")
    r = check_theory(t, "RelFaithfulness", session_timeout=180)
    assert r.ok, ("Isabelle failed to discharge relevant-B faithfulness:\n"
                  + r.output[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_with_formula_verifies_in_isabelle():
    t = relevant_faithfulness_theory("RelFaithfulnessEx", formula=PARADOX)
    r = check_theory(t, "RelFaithfulnessEx", session_timeout=180)
    assert r.ok, r.output[-2000:]
