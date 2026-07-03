"""Deep + maximal/minimal shallow modal embedding with faithfulness proofs.

Structure tests (always run) pin the emitted theory text and the AST->deep encoder.
The live test is gated on a real Isabelle/HOL install: it actually builds the
emitted theory, so exit 0 certifies that Isabelle's kernel discharged all five
faithfulness theorems (faithful1a/1b/2/3, sound_min) — the machine-checked
faithfulness the module exists to provide.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Box, Diamond, Variable, Quantifier,
)
from unicode_fol_kit.hol import modal_faithfulness_theory, modal_to_deep
from unicode_fol_kit.hol.deepshallow._common import AtomConsts, sanitize_atom
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

p, q = Atom("p", ()), Atom("q", ())
K_AX = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))


# --------------------------------------------------------------------------- #
# Encoder (structure only — no Isabelle).
# --------------------------------------------------------------------------- #

def test_encoder_maps_connectives_and_modalities():
    ac = AtomConsts()
    term = modal_to_deep(K_AX, ac)
    assert term == ("(ImpD (BoxD (ImpD (Atm p_p) (Atm p_q))) "
                    "(ImpD (BoxD (Atm p_p)) (BoxD (Atm p_q))))")


@pytest.mark.parametrize("node, head", [
    (Not(p), "NegD"), (And(p, q), "AndD"), (Or(p, q), "OrD"),
    (Implies(p, q), "ImpD"), (Iff(p, q), "IffD"),
    (Box(p), "BoxD"), (Diamond(p), "DiaD"),
])
def test_encoder_constructor_heads(node, head):
    assert modal_to_deep(node, AtomConsts()).startswith(f"({head} ")


def test_xor_desugars_to_neg_iff():
    assert modal_to_deep(Xor(p, q), AtomConsts()) == "(NegD (IffD (Atm p_p) (Atm p_q)))"


def test_distinct_atoms_get_distinct_consts():
    ac = AtomConsts()
    modal_to_deep(And(p, q), ac)
    decls = ac.decls()
    assert decls == ['consts p_p :: "s"', 'consts p_q :: "s"']


def test_same_atom_reused_gets_one_const():
    ac = AtomConsts()
    modal_to_deep(And(p, Box(p)), ac)
    assert ac.decls() == ['consts p_p :: "s"']


def test_encoder_rejects_first_order():
    # a quantifier or a variable-bearing atom is not propositional
    with pytest.raises(NotImplementedError):
        modal_to_deep(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])),
                      AtomConsts())
    with pytest.raises(NotImplementedError):
        modal_to_deep(Box(Atom("P", [Variable("x")])), AtomConsts())


def test_sanitize_atom_is_legal_and_prefixed():
    assert sanitize_atom("p") == "p_p"
    assert sanitize_atom("P(a,b)").startswith("p_")
    assert all(c.isalnum() or c == "_" for c in sanitize_atom("α∧β"))


# --------------------------------------------------------------------------- #
# Emitted theory text (structure only).
# --------------------------------------------------------------------------- #

def test_theory_has_all_three_embeddings_and_faithfulness():
    t = modal_faithfulness_theory("ModalFaithfulness")
    assert t.startswith("theory ModalFaithfulness\n  imports Main\nbegin")
    assert t.rstrip().endswith("end")
    # deep, maximal, minimal
    assert "datatype pml" in t and "primrec truthD" in t
    assert "type_synonym sigma" in t and "definition BoxS" in t
    assert "consts Racc" in t and "definition BoxM" in t
    # the five faithfulness theorems, each with a proof (no `oops`/`sorry`)
    for thm in ("faithful1a", "faithful1b", "faithful2", "faithful3", "sound_min"):
        assert f"theorem {thm}:" in t
    assert "oops" not in t and "sorry" not in t


def test_theory_with_formula_appends_definition_and_atom_consts():
    t = modal_faithfulness_theory("ModalFaithfulnessEx", formula=K_AX)
    assert 'consts p_p :: "s"' in t and 'consts p_q :: "s"' in t
    assert 'definition example :: pml where "example =' in t


def test_illegal_theory_name_rejected():
    with pytest.raises(ValueError):
        modal_faithfulness_theory("1bad name")


# --------------------------------------------------------------------------- #
# LIVE: Isabelle machine-checks the faithfulness proofs.
# --------------------------------------------------------------------------- #

@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_verifies_in_isabelle():
    t = modal_faithfulness_theory("ModalFaithfulness")
    r = check_theory(t, "ModalFaithfulness", session_timeout=180)
    assert r.ok, (
        "Isabelle failed to discharge the modal faithfulness proofs:\n"
        + r.output[-2000:])


@pytest.mark.skipif(not isabelle_available(),
                    reason="no Isabelle installation found")
def test_faithfulness_theory_with_formula_verifies_in_isabelle():
    t = modal_faithfulness_theory("ModalFaithfulnessEx", formula=K_AX)
    r = check_theory(t, "ModalFaithfulnessEx", session_timeout=180)
    assert r.ok, r.output[-2000:]
