"""The two third-order HOL exporters: classical, and the shallow modal embedding.

Both take a predicate whose argument is a property and hand a HOL prover the
same thing one type higher — so these tests are about the TYPES more than the
syntax. What each argument slot holds is inferred, and getting it wrong would
produce a theory that typechecks and means something else, which is the failure
mode worth pinning.

The proof-level checks live in ``test_goedel.py``; here nothing runs a prover.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.frames import UnsupportedFrameCondition
from unicode_fol_kit.hol.ho_modal import (
    HoAxiom, HoGoal, ho_modal_definitions, isabelle_ho_modal_theory,
    to_isabelle_ho_modal, to_thf_ho_modal,
)
from unicode_fol_kit.hol._ho_common import UnsupportedHigherOrderNode, rename_apart
from unicode_fol_kit.hol.thirdorder import to_isabelle_to, to_thf_to

TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)


# --- classical: the types ---------------------------------------------------

def test_a_predicate_of_properties_gets_a_predicate_type():
    theory = to_isabelle_to(TO.parse("Pos(G) ∧ G(a)"))
    assert 'consts Pos :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory
    assert 'consts G :: "i \\<Rightarrow> bool"' in theory
    assert 'consts a :: "i"' in theory


def test_a_mixed_slot_signature_keeps_the_positions_apart():
    """``Essence(P, x)`` takes a property THEN an individual, in that order."""
    theory = to_isabelle_to(TO.parse("∀P ∀x (Ess(P, x) → P(x))"))
    assert ('consts Ess :: "(i \\<Rightarrow> bool) \\<Rightarrow> i '
            '\\<Rightarrow> bool"') in theory


def test_thf_types_match_the_isabelle_ones():
    problem = to_thf_to(TO.parse("∀P ∀x (Ess(P, x) → P(x))"))
    assert "thf(Ess_type, type, ( Ess : ( $i > $o ) > $i > $o ))." in problem
    assert "! [P_P: $i > $o]" in problem


def test_assumptions_are_typed_together_with_the_goal():
    """A symbol whose arity only an ASSUMPTION fixes is still typed correctly."""
    theory = to_isabelle_to(TO.parse("Pos(G)"),
                            assumptions=[TO.parse("∀x ∀y G(x, y)")])
    assert 'consts Pos :: "(i \\<Rightarrow> i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory


def test_an_undetermined_property_arity_is_reported_not_hidden():
    theory = to_isabelle_to(TO.parse("Pos(G)"))
    assert "arity defaulted to 1" in theory and "Pos[0]" in theory


def test_the_classical_export_refuses_modal_operators_by_name():
    with pytest.raises(UnsupportedHigherOrderNode, match="ho_modal"):
        to_isabelle_to(TOM.parse("□Pos(G)"))


def test_a_goal_without_a_proof_is_left_open():
    assert "oops" in to_isabelle_to(TO.parse("Pos(G)"))
    assert "by blast" in to_isabelle_to(TO.parse("Pos(G)"), proof="by blast")


# --- modal: the embedding ---------------------------------------------------

def test_the_lifted_vocabulary_is_abbreviations_not_definitions():
    """An abbreviation unfolds at parse time, so the automation sees through it.

    With ``definition`` every proof would first have to unfold the embedding,
    which is the difference between a proof that takes ten seconds and one that
    does not finish -- measured, not assumed (see test_goedel.py).
    """
    definitions = ho_modal_definitions()
    for name in ("mnot", "mand", "mor", "mimp", "miff", "mbox", "mdia",
                 "mall", "mex", "mvalid"):
        assert f"abbreviation {name} ::" in definitions
    assert "definition " not in definitions


def test_one_polymorphic_binder_serves_both_orders():
    """``mall`` at type ``('a => sigma) => sigma`` binds individuals AND properties."""
    assert "abbreviation mall :: \"('a \\<Rightarrow> sigma) \\<Rightarrow> sigma\"" \
        in ho_modal_definitions()
    theory = isabelle_ho_modal_theory(
        "T", (), [HoGoal("g", TOM.parse("∀P ∀x (Pos(P) → P(x))"))])
    assert "mall (\\<lambda>P::i \\<Rightarrow> sigma." in theory
    assert "mall (\\<lambda>x::i." in theory


def test_a_property_is_world_indexed_in_the_modal_embedding():
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))])
    assert 'consts Pos :: "(i \\<Rightarrow> sigma) \\<Rightarrow> sigma"' in theory
    assert 'type_synonym sigma = "world \\<Rightarrow> bool"' in theory


def test_axioms_are_asserted_valid_at_every_world():
    theory = isabelle_ho_modal_theory(
        "T", [HoAxiom("A", TOM.parse("Pos(G)"))],
        [HoGoal("g", TOM.parse("□Pos(G)"))])
    assert 'axiomatization where A: "mvalid (Pos G)"' in theory
    assert 'theorem g: "mvalid (mbox (Pos G))"' in theory


def test_frame_conditions_come_from_the_shared_registry():
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                      frame="S5")
    for condition in ("R_refl", "R_sym", "R_trans"):
        assert f"axiomatization where {condition}:" in theory
    assert "R_refl" not in isabelle_ho_modal_theory(
        "T", (), [HoGoal("g", TOM.parse("Pos(G)"))], frame="K")


def test_a_non_first_order_frame_is_refused_by_name():
    """GL/S4.1/Grz constrain PROPOSITIONS, not R; this embedding constrains R."""
    with pytest.raises(UnsupportedFrameCondition, match="loeb"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                 frame="GL")


def test_an_unknown_frame_is_refused():
    with pytest.raises(ValueError, match="unknown frame"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                 frame="S99")


def test_the_non_alethic_modal_families_are_refused_by_name():
    """The parser accepts them (same AST); this embedding will not pretend to."""
    with pytest.raises(UnsupportedHigherOrderNode, match="ALETHIC"):
        to_isabelle_ho_modal(TOM.parse("∀P (Pos(P) → K_a P(x))"))


def test_thf_and_isabelle_agree_about_the_signature():
    formula = TOM.parse("∀P ∀x (Ess(P, x) → □P(x))")
    assert 'consts Ess :: "(i \\<Rightarrow> sigma) \\<Rightarrow> i \\<Rightarrow> sigma"' \
        in isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    assert "thf(Ess_type, type, ( Ess : ( $i > mu > $o ) > $i > mu > $o ))." \
        in to_thf_ho_modal(formula)


def test_thf_world_binders_are_numbered_rather_than_shadowed():
    problem = to_thf_ho_modal(TOM.parse("∀x ◇∃y G(x)"))
    assert "W0: mu" in problem and "W1: mu" in problem


# --- renaming apart ---------------------------------------------------------

def test_two_axioms_binding_the_same_name_at_different_arities_do_not_collide():
    """A bound name is scoped to its formula; merging them would be a false conflict."""
    unary = TO.parse("∀P (Pos(P) → P(x))")
    binary = TO.parse("∀P (Rel(P) → P(x, y))")
    theory = to_isabelle_to(binary, assumptions=[unary])
    assert 'consts Pos :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory
    assert ('consts Rel :: "(i \\<Rightarrow> i \\<Rightarrow> bool) '
            '\\<Rightarrow> bool"') in theory


def test_the_renaming_is_invisible_in_the_emitted_text():
    """It exists for the ANALYSIS; what is printed is what the caller wrote."""
    theory = to_isabelle_to(TO.parse("∀P (Pos(P) → P(x))"))
    assert "Bound1" not in theory
    assert "\\<forall>P::i \\<Rightarrow> bool." in theory


def test_rename_apart_reports_what_each_fresh_name_stood_for():
    renamed, original = rename_apart([TO.parse("∀P (Pos(P) → P(x))")])
    assert set(original.values()) == {"P"}
    assert all(name.startswith("Bound") for name in original)


# --- goal shapes ------------------------------------------------------------

def test_a_goal_is_either_a_formula_or_a_raw_statement_never_both():
    with pytest.raises(ValueError, match="exactly one"):
        HoGoal("g", TOM.parse("Pos(G)"), statement="False")
    with pytest.raises(ValueError, match="exactly one"):
        HoGoal("g")


def test_a_raw_statement_is_emitted_verbatim_and_needs_no_typing():
    """"These axioms prove falsity" is a claim ABOUT the theory, not in it."""
    theory = isabelle_ho_modal_theory(
        "T", [HoAxiom("A", TOM.parse("Pos(G)"))],
        [HoGoal("bad", statement="False", proof="by blast")])
    assert 'theorem bad: "False"' in theory
