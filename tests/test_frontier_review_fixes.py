"""Regression tests for the five findings the 0.12.0 adversarial review confirmed.

Each test pins a concrete defect the review reproduced, so a future refactor that
reintroduces it fails here with a clear pointer.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, Atom, And, Implies, Constant, Variable, At, Nominal,
    exact_match, substitute, free_variables, beta_reduce,
)
from unicode_fol_kit.fol.modal_translation import hybrid_is_valid, standard_translation
from unicode_fol_kit.fol.nodes import SlashedExists

_MODAL = MSFLParser(modal=True)
_DEP = MSFLParser(dependence=True)


# --- Finding [1] HIGH: modal-mode nominal rule broke lambda-application args -----

@pytest.mark.parametrize("text, argtype, argname", [
    ("(λx. P(x))(y)", Variable, "y"),
    ("(λx. P(x))(alice)", Constant, "alice"),
    ("(P)(x)", Variable, "x"),
])
def test_lambda_application_argument_is_a_term_not_a_nominal(text, argtype, argname):
    ast = _MODAL.parse(text)
    assert type(ast.arg) is argtype and ast.arg.name == argname


@pytest.mark.parametrize("text", ["(λx. P(x))(y)", "(λx. P(x))(alice)"])
def test_lambda_redex_beta_reduces_and_exports(text):
    # A genuine redex reduces to a classical atom and exports (no hybrid rejection).
    reduced = beta_reduce(_MODAL.parse(text))
    assert type(reduced) is Atom and reduced.to_z3() is not None


def test_lambda_application_not_routed_to_modal_tableau():
    from unicode_fol_kit.atp.modal_tableau import has_modal
    assert has_modal(_MODAL.parse("(λx. P(x))(y)")) is False


@pytest.mark.parametrize("text", [
    "i", "@i P", "P ∧ i", "@i j", "@i j ↔ @j i", "◇i ∧ @i P → ◇P",
    "here ∧ @here P", "@i (P ∧ ◇j)", "K_a @i P",
    # pre-existing modal constructs must be untouched by the nominal rule
    "B_a ∃≥3 x Pass(x)", "μ(x, d) > μ(y, d)", "|{x : P(x)}| > c",
    "x = y", "∀x (P(x) → K_x Q)",
])
def test_modal_nominal_and_regression_corpus_round_trips(text):
    ast = _MODAL.parse(text)
    assert _MODAL.parse(ast.to_unicode_str()) == ast


# --- Finding [0] MEDIUM: nom_ world-constant collision was unsound ---------------

def test_nominal_world_constant_collision_fails_fast():
    # A user constant literally named nom_i collides with nominal i's world constant.
    phi = Implies(And(At("i", Atom("P", [Constant("nom_i")])), At("i", Nominal("j"))),
                  At("j", Atom("P", [Constant("nom_j")])))
    with pytest.raises(ValueError, match="reserved"):
        standard_translation(phi)
    with pytest.raises(ValueError, match="reserved"):
        hybrid_is_valid(phi, frame="K")


def test_no_false_collision_without_nominals_or_nom_symbols():
    # A pure modal formula with an ordinary constant is unaffected.
    assert isinstance(hybrid_is_valid(_MODAL.parse("@i P → @i P"), frame="K"), bool)
    standard_translation(_MODAL.parse("□P → P"))   # no raise


# --- Findings [2] & [4]: slash-set names must be visible to fv / capture avoidance -

def test_free_slash_name_is_a_free_variable():
    # x occurs ONLY in the slash set — it is still free.
    a = _DEP.parse("∃y/{x} R(y)")
    assert Variable("x") in free_variables(a)


def test_slashed_alpha_equivalence_and_distinctness():
    # alpha-variants (bound var + its slash reference renamed together) match
    assert exact_match(_DEP.parse("∀x ∃y/{x} R(x, y)"),
                       _DEP.parse("∀z ∃w/{z} R(z, w)"))
    # a slash set referring to a genuinely different free variable does NOT match
    assert not exact_match(_DEP.parse("∀x ∃y/{x} R(x, y)"),
                           _DEP.parse("∀x ∃y/{w} R(x, y)"))


def test_canonicalize_does_not_capture_a_free_slash_name():
    from unicode_fol_kit import canonicalize
    # q0 is free and appears only in the slash set; the canonical rename must not
    # mint q0 for the bound variable and capture it.
    a = _DEP.parse("∃y/{q0} R(y)")
    b = _DEP.parse("∃y/{w} R(y)")          # different free slash name
    assert not exact_match(a, b)
    assert canonicalize(canonicalize(a)) == canonicalize(a)   # idempotent


# --- Finding [3]: substitute renames a slashed variable, not drops it ------------

def test_substitute_variable_renames_slash_entry():
    s = _DEP.parse("∃y/{x} R(x, y)")
    out = substitute(s, Variable("x"), Variable("z"))
    assert isinstance(out, SlashedExists) and out.slashed == ("z",)
    assert out == _DEP.parse("∃y/{z} R(z, y)")


def test_substitute_ground_term_drops_slash_entry():
    # A constant has no team-column identity, so "independent of x" is vacuous;
    # the sole slash entry drops and the binder degrades to a plain existential.
    # (Expected built directly: a single-letter name lexes as a Variable, not a
    # Constant, so the substituted Constant('c') has no parseable spelling here.)
    from unicode_fol_kit.fol.nodes import Quantifier
    out = substitute(_DEP.parse("∃y/{x} R(x, y)"), Variable("x"), Constant("c"))
    expected = Quantifier("∃", Variable("y"),
                          Atom("R", [Constant("c"), Variable("y")]))
    assert out == expected


def test_substitute_keeps_other_slash_entries():
    out = substitute(_DEP.parse("∃w/{x, u} R(x, u, w)"), Variable("x"), Variable("z"))
    assert isinstance(out, SlashedExists) and out.slashed == ("z", "u")
