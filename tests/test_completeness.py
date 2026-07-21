# -*- coding: utf-8 -*-
"""Completion regression tests: every entry point answers or points, never crashes.

Each test here pins one closed gap from the exhaustive coverage inventory
(v0.17 completion work): either an operator that used to raise now WORKS
(verified against an oracle), or a genuinely-impossible case now raises ONE
clean error naming the right alternative tool. The exact repro formulas from
the inventory are used wherever possible.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, to_fol, is_valid, free_variables,
    is_valid_tableau, prove_tableau,
    cf_valid, cf_countermodel, cf_satisfies,
)
from unicode_fol_kit.atp.resolution import is_valid_resolution, prove
from unicode_fol_kit.atp.fitch_search import (
    fitch_prove, is_valid_fitch, find_fitch_proof,
)
from unicode_fol_kit.atp.modal_tableau import (
    is_modal_valid, modal_decide, modal_countermodel, has_modal,
)
from unicode_fol_kit.fol.nodes import (
    Atom, Not, Constant, Variable, Measure, Would, Might,
)
from unicode_fol_kit.fol.normalforms import to_nnf
from unicode_fol_kit.fol.unification import unify, apply_subst
from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory
from unicode_fol_kit.hol.thf_modal import to_thf_modal_full
from unicode_fol_kit.hol.classical import to_thf_fol, to_isabelle_fol
from unicode_fol_kit.hol.secondorder import to_isabelle_so, to_thf_so

FOL = MSFLParser()
MODAL = MSFLParser(modal=True)
SO = MSFLParser(second_order=True)


# --------------------------------------------------------------------------- #
# to_fol honours its "classical constructs only" contract.
# --------------------------------------------------------------------------- #

class TestToFolContract:
    def test_contrast_reduces_to_and(self):
        assert to_fol(FOL.parse("P Ⓒ Q")).to_unicode_str() == "P ∧ Q"

    def test_count_reduces_to_distinct_witnesses(self):
        out = to_fol(FOL.parse("∃≥2 x (P(x))")).to_unicode_str()
        assert "∃" in out and "≠" in out and "∃≥" not in out

    def test_sorted_count_keeps_its_guard_inside(self):
        ms = MSFLParser(many_sorted=True)
        out = to_fol(ms.parse("∃≥1 x:S P(x)")).to_unicode_str()
        assert out == "∃x_0 (S(x_0) ∧ P(x_0))"


# --------------------------------------------------------------------------- #
# The three classical engines agree — including on the closed gaps.
# --------------------------------------------------------------------------- #

class TestEngineAgreement:
    @pytest.mark.parametrize("src,expect", [
        ("P Ⓒ Q → P", True),                       # Contrast in every engine
        ("P → P Ⓒ Q", False),
        ("∃≥2 x (P(x)) → ∃x P(x)", True),          # Count expansion
        ("∃≥1 x (P(x)) → ∃≥2 x (P(x))", False),
        ("∃=0 x (P(x)) → ¬P(a)", True),            # free-variable γ-seed fix
        ("¬∃x P(x) → ¬P(a)", True),
        ("∀x P(x) → P(a)", True),
    ])
    def test_tableau_resolution_z3_agree(self, src, expect):
        f = FOL.parse(src)
        assert is_valid(f) is expect               # Z3 = ground truth
        assert is_valid_tableau(f) is expect
        assert is_valid_resolution(f) is expect

    def test_measure_terms_survive_resolution_renaming(self):
        # The inventory's exact _rename_term repro (plus apply_subst/unify).
        premise = FOL.parse("∀x (Q(x) → μ(x,h) > μ(x,h))")
        conclusion = FOL.parse("Q(a) → μ(a,h) > μ(a,h)")
        assert prove([premise], conclusion) is True

    def test_measure_unification_is_slotwise_and_syntactic(self):
        m1 = Measure(Variable("x"), Constant("height"))
        m2 = Measure(Constant("tom"), Constant("height"))
        subst = unify(m1, m2)
        assert subst is not None
        assert apply_subst(m1, subst) == m2
        # Never unifies with a Function spelled "measure" — export convention only.
        from unicode_fol_kit.fol.nodes import Function
        assert unify(m1, Function("measure",
                                  [Constant("tom"), Constant("height")])) is None


# --------------------------------------------------------------------------- #
# Modal routing: resolution + fitch decide the propositional-modal fragment.
# --------------------------------------------------------------------------- #

class TestModalRouting:
    @pytest.mark.parametrize("src,expect", [
        ("□(P → Q) → (□P → □Q)", True),            # K axiom
        ("□P → P", False),                          # T: not K-valid
        ("K_a (P → Q) → (K_a P → K_a Q)", True),
        ("◇P → □P", False),
    ])
    def test_resolution_matches_modal_tableau_on_k(self, src, expect):
        f = MODAL.parse(src)
        assert is_valid_resolution(f) is expect
        assert is_modal_valid(f) is expect          # independent oracle

    def test_fitch_no_longer_silently_false_on_the_k_instance(self):
        # The inventory's headline wrong-answer: □(P→Q), □P ⊢ □Q came back False.
        assert fitch_prove([MODAL.parse("□(P → Q)"), MODAL.parse("□P")],
                           MODAL.parse("□Q")) is True
        assert is_valid_fitch(MODAL.parse("□(P → Q) → (□P → □Q)")) is True
        assert is_valid_fitch(MODAL.parse("□P → P")) is False

    def test_find_fitch_proof_refuses_modal_with_pointer(self):
        # It returns Proof objects, which it cannot fabricate for modal input.
        with pytest.raises(NotImplementedError, match="modal tableau"):
            find_fitch_proof([], MODAL.parse("□P → □P"))

    def test_resolution_counterfactual_pointer(self):
        with pytest.raises(NotImplementedError, match="cf_valid|cf_satisfies"):
            is_valid_resolution(MODAL.parse("(P □→ Q) → (P □→ Q)"))

    def test_to_nnf_names_the_right_tool(self):
        with pytest.raises(TypeError, match="standard_translation"):
            to_nnf(MODAL.parse("□P"))
        with pytest.raises(TypeError, match="cf_valid|cf_satisfies"):
            to_nnf(MODAL.parse("P □→ Q"))


# --------------------------------------------------------------------------- #
# cf_valid / cf_countermodel: the internal counterfactual decision path.
# --------------------------------------------------------------------------- #

class TestCounterfactualDecision:
    #: The same battery isabelle_decide_counterfactual certifies live.
    LEWIS = [
        ("A □→ A", True),
        ("((A □→ B) ∧ (A □→ C)) → (A □→ (B ∧ C))", True),   # agglomeration
        ("(A □→ B) → (A □→ (B ∨ C))", True),
        ("(A ◇→ B) → ¬(A □→ ¬B)", True),                    # duality
        ("(A □→ B) → ((A ∧ C) □→ B)", False),               # ant. strengthening
        ("(A □→ B) → (¬B □→ ¬A)", False),                   # contraposition
    ]

    @pytest.mark.parametrize("src,expect", LEWIS)
    def test_cf_valid_matches_the_isabelle_certified_facts(self, src, expect):
        assert cf_valid(MODAL.parse(src)) is expect

    def test_countermodels_are_verified_refutations(self):
        f = MODAL.parse("(A □→ B) → ((A ∧ C) □→ B)")
        model, world = cf_countermodel(f)
        assert cf_satisfies(f, model, world) is False


# --------------------------------------------------------------------------- #
# modal_tableau: sound verdicts, never crashes (see also test_modal_tableau).
# --------------------------------------------------------------------------- #

class TestModalTableauHonesty:
    def test_temporal_closure_gives_verdicts_not_crashes(self):
        assert modal_decide(MODAL.parse("ⒼP")) == "invalid"        # verified
        assert modal_decide(MODAL.parse("ⒼP → P")) == "unknown"    # honest
        assert modal_countermodel(MODAL.parse("ⒼP")) is not None

    def test_would_might_are_visible_and_cleanly_guarded(self):
        assert has_modal(MODAL.parse("P □→ Q")) is True
        for fn in (is_modal_valid, is_valid_tableau):
            with pytest.raises(NotImplementedError, match="cf_valid|cf_satisfies"):
                fn(MODAL.parse("P □→ Q"))


# --------------------------------------------------------------------------- #
# Isabelle / THF exporters: the whole modal family emits.
# --------------------------------------------------------------------------- #

class TestExporterCompleteness:
    #: Every operator shape the inventory reported as raising.
    SHAPES = ["⒣P", "⒫P", "⒴P", "Say_a P", "Want_a P", "@i P",
              "□(P Ⓒ Q)", "P Ⓤ Q", "P ⒮ Q", "(⒴P ∧ Say_a Q) → @i (⒣R)"]

    @pytest.mark.parametrize("src", SHAPES)
    def test_isabelle_modal_emits(self, src):
        thy = isabelle_modal_theory(MODAL.parse(src), theory_name="T")
        assert thy.startswith("theory T")

    @pytest.mark.parametrize("src", SHAPES)
    def test_thf_modal_emits(self, src):
        assert "thf(goal, conjecture" in to_thf_modal_full(MODAL.parse(src))

    def test_entity_type_is_monomorphic(self):
        # A polymorphic 'a gives every agent-constant occurrence its own type
        # instance — two independent rs's — and nitpick then "genuinely" refutes
        # the valid agent-K axiom (a false INVALID observed live). Pin type e.
        thy = isabelle_modal_theory(
            MODAL.parse("Say_a (P → Q) → (Say_a P → Say_a Q)"), theory_name="T")
        assert "typedecl e" in thy and "'a" not in thy

    def test_nominals_use_legal_isabelle_names(self):
        # _safe_name may dodge the reserved world type "i" with a trailing "_",
        # which Isabelle REJECTS as an identifier; the nom_ prefix already
        # disambiguates, so the emitted constant must carry no trailing "_".
        thy = isabelle_modal_theory(MODAL.parse("@i P → @i P"), theory_name="T")
        assert 'consts nom_i :: "i"' in thy and "nom_i_" not in thy

    def test_classical_exports_take_count_measure_contrast(self):
        assert "measure" in to_thf_fol(FOL.parse("μ(tom, height) > μ(sue, height)"))
        assert "measure" in to_isabelle_fol(FOL.parse("μ(tom, height) > μ(sue, height)"))
        assert "student" in to_thf_fol(FOL.parse("∃≥2 x (Student(x))")).lower()
        assert "\\<and>" in to_isabelle_fol(FOL.parse("P Ⓒ Q"))

    def test_so_cardinality_embeds_as_hol_card(self):
        out = to_isabelle_so(SO.parse("|{x : Student(x)}| = 3"))
        assert "(card {x. (student x)})" in out
        out2 = to_isabelle_so(SO.parse("∀P (|{x : P(x)}| ≥ 0)"))
        assert "card {x. (P x)}" in out2

    def test_so_cardinality_comparison_is_numeric_or_a_clear_error(self):
        # An individual operand is a category error the emitter must NAME.
        with pytest.raises(NotImplementedError, match="NUMERIC"):
            to_isabelle_so(SO.parse("|{x : P(x)}| = tom"))

    def test_thf_so_points_at_the_isabelle_embedding(self):
        with pytest.raises(NotImplementedError, match="to_isabelle_so"):
            to_thf_so(SO.parse("|{x : Student(x)}| = 3"))

    def test_would_rejections_point_at_the_sphere_tools(self):
        for exporter in (lambda f: isabelle_modal_theory(f, theory_name="T"),
                         to_thf_modal_full):
            with pytest.raises(NotImplementedError, match="isabelle_conditional"):
                exporter(MODAL.parse("P □→ Q"))

    def test_qml_since_names_its_reason_and_alternatives(self):
        from unicode_fol_kit.fol.qml import qml_translate
        with pytest.raises(NotImplementedError, match="msince"):
            qml_translate(MODAL.parse("P ⒮ Q"))


# --------------------------------------------------------------------------- #
# Live Isabelle differential for the completed operators (isabelle_live).
# --------------------------------------------------------------------------- #

from unicode_fol_kit.hol.isabelle_runner import (          # noqa: E402
    isabelle_available, isabelle_decide_modal,
)

#: Hand-checked Kripke facts per new operator; every one was certified live
#: during development (valid ⇒ kernel proof, invalid ⇒ genuine nitpick model).
_NEW_OP_FACTS = [
    ("⒣P → P", "valid"),        # t reflexive: "always been" includes now
    ("P → ⒫P", "valid"),        # now counts as "once"
    ("⒫P → P", "invalid"),      # past truth need not persist
    ("P → ⒴Q", "invalid"),
    ("Say_a (P → Q) → (Say_a P → Say_a Q)", "valid"),   # agent-K (monomorphic e!)
    ("Say_a P → P", "invalid"),                          # non-factive
    ("Want_a P → P", "invalid"),                         # non-veridical
    ("@i P → ¬@i (¬P)", "valid"),                        # @ self-dual
    ("@i P → P", "invalid"),
    ("⒫P → ◇P", "invalid"),     # temporal past ⊬ alethic possibility
]


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(),
                    reason="no local Isabelle installation found")
@pytest.mark.parametrize("src,expected", _NEW_OP_FACTS)
def test_isabelle_certifies_the_completed_operators(src, expected):
    verdict = isabelle_decide_modal(MODAL.parse(src), frame="K")
    assert verdict.status == expected, f"{src}: {verdict}"
