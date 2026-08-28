"""Gödel's ontological argument, both readings — the third-order machinery's test case.

Two theories one conjunct apart. Scott's reading proves the argument's four
steps, proves modal collapse as a bonus nobody asked for, and has a Nitpick
model (so it proves those things because they follow, not because it proves
everything). Gödel's own reading proves ``False``.

The fast tests here are about the FORMULAS and the emitted text; the two that
matter — does a prover discharge them — are marked ``isabelle_live`` and need a
local Isabelle. Both take about ten seconds each, which is worth saying because
the same theories with one-line automation instead of the shipped structured
proofs do not finish at all.
"""

import pytest

from unicode_fol_kit.hol.goedel import (
    VARIANTS, axiom_texts, axioms, check_variant, conclusions, goedel_theory,
    variant_difference,
)
from unicode_fol_kit.hol.isabelle_runner import isabelle_available
from unicode_fol_kit.fol.nodes import analyse_signatures
from unicode_fol_kit.fol._ho_nodes import INDIVIDUAL


# --- the formulas -----------------------------------------------------------

def test_the_two_variants_differ_in_D2_and_nowhere_else():
    """The whole finding, as an assertion: one conjunct is the difference."""
    scott, goedel = axiom_texts("scott"), axiom_texts("goedel")
    assert set(scott) == set(goedel)
    differing = [name for name in scott if scott[name] != goedel[name]]
    assert differing == ["D2"]
    assert scott["D2"] == goedel["D2"].replace("Ess(P, x) ↔ ", "Ess(P, x) ↔ P(x) ∧ ")


def test_the_difference_is_stated_in_the_kits_own_syntax():
    text = variant_difference()
    assert "∀P ∀x (Ess(P, x) ↔ P(x) ∧" in text
    assert "∀P ∀x (Ess(P, x) ↔ ∀Q" in text


@pytest.mark.parametrize("variant", VARIANTS)
def test_every_axiom_parses_and_roundtrips(variant):
    from unicode_fol_kit import MSFLParser
    parser = MSFLParser(third_order=True, modal=True)
    for name, formula in axioms(variant).items():
        assert parser.parse(formula.to_unicode_str()) == formula, name


def test_the_axiom_set_really_is_third_order():
    """If this were second-order-expressible the whole exercise would be pointless."""
    signatures = analyse_signatures(list(axioms("scott").values()))
    assert signatures.is_third_order()
    assert signatures.slots["Pos"] == (("p", 1),)
    assert signatures.slots["Ess"] == (("p", 1), INDIVIDUAL)
    assert signatures.slots["G"] == (INDIVIDUAL,)
    assert signatures.defaulted == frozenset()


def test_modal_collapse_quantifies_over_propositions_not_properties():
    """``∀Q (Q → □Q)`` binds a NULLARY predicate — a proposition variable."""
    from unicode_fol_kit.fol.nodes import SecondOrderQuantifier
    collapse = conclusions()["MC"]
    assert isinstance(collapse, SecondOrderQuantifier)
    assert collapse.arity == 0


def test_an_unknown_variant_is_refused():
    with pytest.raises(ValueError, match="unknown variant"):
        goedel_theory("leibniz")


# --- the emitted theories ---------------------------------------------------

def test_scott_states_the_four_steps_the_collapse_and_the_consistency_check():
    theory = goedel_theory("scott")
    for name in ("T1", "C", "T2", "T3", "MC"):
        assert f"theorem {name}:" in theory
    assert "nitpick [satisfy, user_axioms, expect = genuine]" in theory
    # The control: Scott's conjunct blocks exactly what breaks Gödel's version.
    assert "theorem essenceImpliesInstance:" in theory
    assert "theorem emptyNotEssence:" in theory


def test_the_original_states_the_empty_essence_and_falsity():
    theory = goedel_theory("goedel")
    assert "theorem emptyEssence:" in theory
    assert 'theorem inconsistent: "False"' in theory
    assert "theorem T3:" not in theory   # it never gets that far


def test_both_theories_are_stated_in_S5():
    for variant in VARIANTS:
        theory = goedel_theory(variant)
        for condition in ("R_refl", "R_sym", "R_trans"):
            assert f"axiomatization where {condition}:" in theory, variant


def test_the_theory_is_emitted_by_the_generic_embedding():
    """Nothing about the argument is special-cased in the exporter."""
    from unicode_fol_kit.hol.ho_modal import ho_modal_definitions
    assert ho_modal_definitions() in goedel_theory("scott")


def test_the_signature_is_read_off_the_axioms():
    theory = goedel_theory("scott")
    assert 'consts Pos :: "(i \\<Rightarrow> sigma) \\<Rightarrow> sigma"' in theory
    assert 'consts Ess :: "(i \\<Rightarrow> sigma) \\<Rightarrow> i \\<Rightarrow> sigma"' in theory
    assert 'consts NE :: "i \\<Rightarrow> sigma"' in theory
    assert "arity defaulted" not in theory


# --- the proofs, run for real ----------------------------------------------

live = pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")


@pytest.mark.isabelle_live
@live
def test_scott_version_goes_through_and_its_axioms_have_a_model():
    """T1, C, T2, T3, modal collapse, the blocking lemma, and a Nitpick model.

    ``ok`` means EVERY lemma in the theory was discharged, the consistency check
    included — so this is not just "the argument is derivable" but "it is
    derivable from a satisfiable axiom set".
    """
    result = check_variant("scott", timeout=600)
    assert result.ok, f"build failed (exit {result.exit_code}):\n{result.output[-2500:]}"


@pytest.mark.isabelle_live
@live
def test_goedels_own_version_proves_falsity():
    """The empty property is an essence of everything, and then ``False`` follows.

    The control is in the other test: under Scott's D2 the same theory proves
    ``Ess(P, x) → P(x)``, hence that the empty property is an essence of
    NOTHING. One conjunct is the whole difference.
    """
    result = check_variant("goedel", timeout=600)
    assert result.ok, f"build failed (exit {result.exit_code}):\n{result.output[-2500:]}"
