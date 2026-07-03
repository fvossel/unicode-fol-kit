"""Intuitionistic deep + maximal/minimal shallow embedding with faithfulness proofs.

Structure tests always run; the live test builds the emitted theory in Isabelle, so
exit 0 certifies the five faithfulness theorems (faithful1a/1b/2/3, sound_min) over
the intuitionistic Kripke semantics.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Box, Xor, Variable, Quantifier,
)
from unicode_fol_kit.hol import intuitionistic_faithfulness_theory, int_to_deep
from unicode_fol_kit.hol.deepshallow._common import AtomConsts
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

p, q = Atom("p", ()), Atom("q", ())
# Peirce's law: classically valid, intuitionistically not — a good corpus formula.
PEIRCE = Implies(Implies(Implies(p, q), p), p)


def test_encoder_maps_intuitionistic_connectives():
    ac = AtomConsts()
    assert int_to_deep(PEIRCE, ac) == (
        "(ImpD (ImpD (ImpD (Atm p_p) (Atm p_q)) (Atm p_p)) (Atm p_p))")


@pytest.mark.parametrize("node, head", [
    (Not(p), "NegD"), (And(p, q), "AndD"), (Or(p, q), "OrD"),
    (Implies(p, q), "ImpD"), (Iff(p, q), "IffD"),
])
def test_encoder_constructor_heads(node, head):
    assert int_to_deep(node, AtomConsts()).startswith(f"({head} ")


def test_encoder_rejects_modalities_and_xor_and_first_order():
    for bad in (Box(p), Xor(p, q),
                Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))):
        with pytest.raises(NotImplementedError):
            int_to_deep(bad, AtomConsts())


def test_theory_has_all_three_embeddings_and_faithfulness():
    t = intuitionistic_faithfulness_theory("IntFaithfulness")
    assert t.startswith("theory IntFaithfulness")
    assert "datatype ipl" in t and "primrec truthD" in t
    assert "definition preorder" in t and "definition monotone" in t
    # intuitionistic ImpS quantifies over successors
    assert "ImpS f g \\<equiv> \\<lambda>W L V x. \\<forall>y. L x y" in t
    for thm in ("faithful1a", "faithful1b", "faithful2", "faithful3", "sound_min"):
        assert f"theorem {thm}" in t
    assert "oops" not in t and "sorry" not in t


def test_theory_with_formula_appends_definition():
    t = intuitionistic_faithfulness_theory("IntFaithfulnessEx", formula=PEIRCE)
    assert 'consts p_p :: "s"' in t
    assert 'definition example :: ipl where "example =' in t


@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_verifies_in_isabelle():
    t = intuitionistic_faithfulness_theory("IntFaithfulness")
    r = check_theory(t, "IntFaithfulness", session_timeout=180)
    assert r.ok, ("Isabelle failed to discharge intuitionistic faithfulness:\n"
                  + r.output[-2000:])


@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_with_formula_verifies_in_isabelle():
    t = intuitionistic_faithfulness_theory("IntFaithfulnessEx", formula=PEIRCE)
    r = check_theory(t, "IntFaithfulnessEx", session_timeout=180)
    assert r.ok, r.output[-2000:]
