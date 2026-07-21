# -*- coding: utf-8 -*-
"""Round-2 completeness pins (proof-theory sweep over ALL logics).

Each test pins one closed gap from the second exhaustive inventory: the
assertive/bouletic family in every first-order route, quantified-modal input in
the resolution prover, reserved-name/nominal soundness in the THF/Isabelle
exporters, exporter configuration parity (systems=, temporal_closure), and
honest pointer-guards for the substructural/team/second-order/fuzzy families
(which used to crash with bare errors — or worse, silently answer for the
WRONG logic).
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, to_fol, is_valid, is_valid_tableau,
    cf_valid, fuzzy_is_valid, ill_prove,
)
from unicode_fol_kit.atp.resolution import is_valid_resolution, prove
from unicode_fol_kit.atp.fitch_search import is_valid_fitch
from unicode_fol_kit.atp.modal_tableau import modal_decide
from unicode_fol_kit.fol.modal_translation import standard_translation
from unicode_fol_kit.fol.qml import qml_is_valid, to_thf_modal
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Variable,
    And, Implies, Box, Diamond, Quantifier,
    Says, Wants, Knows, Nominal, At, Until,
)
from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory
from unicode_fol_kit.hol.thf_modal import to_thf_modal_full

MODAL = MSFLParser(modal=True)
SO = MSFLParser(second_order=True)
FUZZY = MSFLParser(fuzzy=True)
LINEAR = MSFLParser(linear=True)
LAMBEK = MSFLParser(lambek=True)
DEP = MSFLParser(dependence=True)


class TestAssertiveBouleticFirstOrderRoutes:
    """Says/Wants used to raise from standard_translation and qml (the ONLY
    modal family without a first-order route); now both translate as
    per-agent box relations Rs_/Rw_ (mirroring Rk_/Rb_)."""

    SAY_K = "Say_a (P → Q) → (Say_a P → Say_a Q)"

    def test_standard_translation_says_wants(self):
        st = standard_translation(MODAL.parse(self.SAY_K))
        assert "Rs_a" in st.to_unicode_str()
        st2 = standard_translation(Wants(Constant("bob"), Atom("P", [])))
        assert "Rw_bob" in st2.to_unicode_str()

    def test_resolution_decides_say_k_axiom(self):
        assert prove([], MODAL.parse(self.SAY_K)) is True
        assert prove([], MODAL.parse("Say_a P → P")) is False   # non-factive

    def test_qml_decides_says_wants(self):
        assert qml_is_valid(MODAL.parse(self.SAY_K)) is True
        assert qml_is_valid(MODAL.parse("Want_a P → P")) is False

    def test_qml_systems_assertive(self):
        # systems={"assertive": "T"} makes Say factive in the FO embedding.
        assert qml_is_valid(MODAL.parse("Say_a P → P"),
                            systems={"assertive": "T"}) is True


class TestResolutionFirstOrderModal:
    """Quantified modal input used to raise a stale 'future work' error; now it
    routes through the qml FO shallow embedding (constant domains, frame K)
    with a scaled step budget. False stays 'not proved within the bound'."""

    def test_valid_fo_modal_proved(self):
        x = Variable("x")
        f = Implies(Box(Quantifier("∀", x, Atom("A", [x]))),
                    Quantifier("∀", x, Box(Atom("A", [x]))))
        assert prove([], f, max_steps=3000) is True

    def test_barcan_formulas_proved(self):
        # Deterministic saturation (content-ordered clause selection) closes
        # both Barcan directions in well under the default budget.
        from unicode_fol_kit.fol.qml import BARCAN, CONVERSE_BARCAN
        assert prove([], BARCAN) is True
        assert prove([], CONVERSE_BARCAN) is True

    def test_invalid_fo_modal_not_proved(self):
        x = Variable("x")
        f = Implies(Quantifier("∀", x, Diamond(Atom("A", [x]))),
                    Diamond(Quantifier("∀", x, Atom("A", [x]))))
        assert prove([], f, max_steps=500) is False


class TestQmlSignatureTypingFacts:
    """Constants used to be UNTYPED in the guarded qml embedding: nothing put
    them in Object, so ∀x P(x) → P(c) came out spuriously invalid and an
    Object-guarded agent frame axiom never fired for a NAMED agent."""

    def test_universal_instantiation_at_constant(self):
        x = Variable("x")
        f = Implies(Quantifier("∀", x, Atom("P", [x])),
                    Atom("P", [Constant("cc")]))
        assert qml_is_valid(f) is True

    def test_universal_instantiation_at_function_term(self):
        from unicode_fol_kit.fol.nodes import Function
        x = Variable("x")
        f = Implies(Quantifier("∀", x, Atom("P", [x])),
                    Atom("P", [Function("ff", [Constant("cc")])]))
        assert qml_is_valid(f) is True

    def test_converse_stays_invalid(self):
        x = Variable("x")
        f = Implies(Atom("P", [Constant("cc")]),
                    Quantifier("∀", x, Atom("P", [x])))
        assert qml_is_valid(f) is False

    def test_named_agent_frame_axiom_fires(self):
        f = Implies(Knows(Constant("alice"), Atom("Q", [])), Atom("Q", []))
        assert qml_is_valid(f, systems={"epistemic": "T"}) is True
        assert qml_is_valid(f) is False               # K alone: non-factive


class TestExporterNameSoundness:
    def test_thf_full_nominal_dedup(self):
        # @A P ∧ @a Q: two DISTINCT nominals sanitising alike must stay two
        # distinct world constants (this used to conflate them silently).
        out = to_thf_modal_full(And(At(Nominal("A"), Atom("P", [])),
                                    At(Nominal("a"), Atom("Q", []))))
        assert out.count("thf(nom_a_decl") == 1
        assert out.count("thf(nom_a_2_decl") == 1

    def test_thf_full_user_constant_nom_prefix(self):
        out = to_thf_modal_full(And(At(Nominal("i"), Atom("P", [])),
                                    Atom("Q", [Constant("nom_i")])))
        assert "nom_i_2" in out                       # no conflation either way

    def test_thf_reserved_relation_name(self):
        # A user predicate literally named "r" must not re-declare the
        # accessibility relation at a conflicting type.
        out = to_thf_modal(Box(Atom("r", [])))
        assert out.count("thf(r_decl, type, ( r : ( mu > mu > $o ) )).") == 1
        assert "r_2" in out

    def test_thf_full_reserved_operator_name(self):
        out = to_thf_modal_full(Box(Atom("mbox", [])))
        assert "mbox_2" in out
        assert out.count("thf(mbox, definition") == 1

    def test_isabelle_reserved_says(self):
        thy = isabelle_modal_theory(Says(Constant("alice"), Atom("says", [])))
        assert "consts says_ ::" in thy
        assert thy.count("abbreviation says ::") == 1

    def test_isabelle_reserved_muntil(self):
        thy = isabelle_modal_theory(Until(Atom("muntil", []), Atom("Q", [])))
        assert "muntil_ ::" in thy


class TestExporterConfigurationParity:
    def test_thf_full_temporal_closure_off(self):
        loose = to_thf_modal_full(Until(Atom("P", []), Atom("Q", [])),
                                  temporal_closure=False)
        assert "t_refl" not in loose and "tnext_in_t" in loose

    def test_thf_full_until_still_documented_and_supported(self):
        out = to_thf_modal_full(Until(Atom("P", []), Atom("Q", [])))
        assert "muntil" in out and "t_refl" in out

    def test_isabelle_systems_epistemic_t(self):
        f = Implies(Knows(Constant("alice"), Atom("P", [])), Atom("P", []))
        thy = isabelle_modal_theory(f, systems={"epistemic": "T"})
        assert 'rk_refl: "rk a w w"' in thy
        assert "rk_refl" not in isabelle_modal_theory(f)

    def test_systems_gl_rejected_not_silently_weakened(self):
        # GL needs Löb, which has no per-agent schema; silently emitting only
        # transitivity would answer for a WEAKER logic than requested.
        f = Implies(Knows(Constant("alice"), Atom("P", [])), Atom("P", []))
        with pytest.raises(NotImplementedError, match="per-agent"):
            isabelle_modal_theory(f, systems={"epistemic": "GL"})
        with pytest.raises(NotImplementedError, match="per-agent"):
            to_thf_modal_full(f, systems={"epistemic": "GL"})

    def test_thf_full_systems_assertive(self):
        out = to_thf_modal_full(Says(Constant("alice"), Atom("P", [])),
                                systems={"assertive": "S5"})
        assert "rs_refl" in out and "rs_trans" in out and "rs_sym" in out


class TestHonestGuardsRound2:
    """The generic entry points must answer or point — never silently treat a
    foreign connective as an opaque atom (fitch returned False on the genuine
    ILL theorem A ⊸ A) and never silently decide the wrong logic (fuzzy
    P ∨ ¬P came back classically 'valid')."""

    def test_fuzzy_no_silent_classical_collapse(self):
        lem = FUZZY.parse("P ∨ ¬P")
        assert fuzzy_is_valid(lem) is False           # the real fuzzy verdict
        with pytest.raises(NotImplementedError, match="fuzzy_is_valid"):
            is_valid(lem)
        with pytest.raises(TypeError, match="fuzzy_is_valid"):
            is_valid_resolution(lem)
        with pytest.raises(NotImplementedError, match="fuzzy_is_valid"):
            is_valid_tableau(lem)
        with pytest.raises(NotImplementedError, match="fuzzy_is_valid"):
            is_valid_fitch(lem)

    def test_fuzzy_explicit_collapse_is_the_opt_in(self):
        lem = FUZZY.parse("P ∨ ¬P")
        assert is_valid(to_fol(lem)) is True          # explicit, documented

    def test_linear_pointer_errors(self):
        ill = LINEAR.parse("A ⊸ A")
        with pytest.raises(NotImplementedError, match="ill_prove"):
            is_valid_fitch(ill)
        with pytest.raises(NotImplementedError, match="ill_prove"):
            is_valid_tableau(ill)
        with pytest.raises(TypeError, match="ill_prove"):
            is_valid_resolution(ill)
        assert ill_prove([], ill) is not None         # the pointed-at tool works

    def test_lambek_pointer_errors(self):
        lam = LAMBEK.parse("A \\ A")
        with pytest.raises(NotImplementedError, match="lambek_prove"):
            is_valid_tableau(lam)
        with pytest.raises(TypeError, match="lambek_prove"):
            is_valid_resolution(lam)

    def test_so_and_dependence_guards(self):
        so = SO.parse("∀P (P(a) → P(a))")
        with pytest.raises(NotImplementedError, match="hol.secondorder"):
            is_valid_tableau(so)
        with pytest.raises(NotImplementedError, match="satisfies_so"):
            is_valid_fitch(so)
        dep = DEP.parse("∀x ∃y (=(x, y) ∧ R(x, y))")
        with pytest.raises(NotImplementedError, match="team_satisfies"):
            is_valid_tableau(dep)
        with pytest.raises(TypeError, match="team_satisfies"):
            is_valid_resolution(dep)

    def test_gl_frame_explained_with_pointer(self):
        with pytest.raises(NotImplementedError, match="isabelle_decide_modal"):
            modal_decide(Implies(Box(Atom("P", [])), Atom("P", [])), frame="GL")

    def test_cf_rejects_free_variable_atoms(self):
        f = MODAL.parse("P(x) □→ P(x)")
        with pytest.raises(TypeError, match="propositional"):
            cf_valid(f)
        assert cf_valid(MODAL.parse("P(tom) □→ P(tom)")) is True

    def test_to_thf_modal_points_at_full(self):
        with pytest.raises(NotImplementedError, match="to_thf_modal_full"):
            to_thf_modal(Says(Constant("a_agent"), Atom("P", [])))

    def test_quantified_st_points_at_qml(self):
        x = Variable("x")
        with pytest.raises(NotImplementedError, match="qml_is_valid"):
            standard_translation(Box(Quantifier("∀", x, Atom("P", [x]))))
