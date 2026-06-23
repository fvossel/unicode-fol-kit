"""Hand-checked tests for the Łukasiewicz fuzzy evaluator (semantics.fuzzy.evaluate)."""

import math

import pytest

from unicode_fol_kit.semantics.fuzzy import evaluate
from unicode_fol_kit.semantics import evaluate as evaluate_pkg
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Variable, Constant, Number, Function, SortedConstant,
    And, Or, Not, Implies, Iff, Xor,
    LukNegation, WeakConjunction,
    Lambda, LambdaVar, Application,
)


def approx(x):
    return pytest.approx(x, abs=1e-9)


@pytest.fixture
def fl():
    return MSFLParser(fuzzy=True)


@pytest.fixture
def msfl():
    return MSFLParser(many_sorted=True, fuzzy=True)


# ---------------------------------------------------------------------------
# Core connective truth tables (the exact numbers from the spec)
# ---------------------------------------------------------------------------

def test_strong_conjunction(fl):
    # P⊗Q with P=0.6, Q=0.7 -> max(0, 0.6+0.7-1) = max(0, 0.3) = 0.3
    f = fl.parse("P ⊗ Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(0.3)


def test_strong_disjunction(fl):
    # P⊕Q -> min(1, 0.6+0.7) = min(1, 1.3) = 1.0
    f = fl.parse("P ⊕ Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(1.0)


def test_luk_negation(fl):
    # ¬P with P=0.6 -> 1-0.6 = 0.4
    f = fl.parse("¬P")
    assert evaluate(f, {"P": 0.6}) == approx(0.4)


def test_luk_implication(fl):
    # P→Q -> min(1, 1-0.6+0.7) = min(1, 1.1) = 1.0
    f = fl.parse("P → Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(1.0)


def test_luk_implication_below_one(fl):
    # P→Q with P=0.7, Q=0.2 -> min(1, 1-0.7+0.2) = min(1, 0.5) = 0.5
    f = fl.parse("P → Q")
    assert evaluate(f, {"P": 0.7, "Q": 0.2}) == approx(0.5)


def test_luk_equivalence(fl):
    # P↔Q -> 1-|0.6-0.7| = 1-0.1 = 0.9
    f = fl.parse("P ↔ Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(0.9)


def test_weak_conjunction(fl):
    # weak P∧Q -> min(0.6, 0.7) = 0.6
    f = fl.parse("P ∧ Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(0.6)


def test_weak_disjunction(fl):
    # weak P∨Q -> max(0.6, 0.7) = 0.7
    f = fl.parse("P ∨ Q")
    assert evaluate(f, {"P": 0.6, "Q": 0.7}) == approx(0.7)


# ---------------------------------------------------------------------------
# Łukasiewicz identities, checked numerically over several P
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("p", [0.0, 0.1, 0.25, 0.5, 0.6, 0.75, 0.9, 1.0])
def test_excluded_middle_strong(fl, p):
    # P ⊕ ¬P == min(1, P + (1-P)) == 1.0 for every P
    f = fl.parse("P ⊕ ¬P")
    assert evaluate(f, {"P": p}) == approx(1.0)


@pytest.mark.parametrize("p", [0.0, 0.1, 0.25, 0.5, 0.6, 0.75, 0.9, 1.0])
def test_non_contradiction_strong(fl, p):
    # P ⊗ ¬P == max(0, P + (1-P) - 1) == 0.0 for every P
    f = fl.parse("P ⊗ ¬P")
    assert evaluate(f, {"P": p}) == approx(0.0)


@pytest.mark.parametrize("p", [0.0, 0.3, 0.5, 0.8, 1.0])
def test_self_equivalence_is_one(fl, p):
    # P ↔ P == 1 - |P - P| == 1.0
    f = fl.parse("P ↔ P")
    assert evaluate(f, {"P": p}) == approx(1.0)


# ---------------------------------------------------------------------------
# Nesting and clamping
# ---------------------------------------------------------------------------

def test_nested_strong_chain(fl):
    # (P ⊗ Q) ⊗ R with P=Q=R=0.8:
    #   P⊗Q = max(0, 0.6) = 0.6 ; (0.6)⊗0.8 = max(0, 0.4) = 0.4
    f = fl.parse("P ⊗ Q ⊗ R")
    assert evaluate(f, {"P": 0.8, "Q": 0.8, "R": 0.8}) == approx(0.4)


def test_double_negation(fl):
    f = fl.parse("¬¬P")
    assert evaluate(f, {"P": 0.3}) == approx(0.3)


def test_strong_disjunction_clamps_at_one(fl):
    f = fl.parse("P ⊕ Q ⊕ R")
    # min(1, 0.5+0.5) = 1 ; then min(1, 1+0.5) = 1
    assert evaluate(f, {"P": 0.5, "Q": 0.5, "R": 0.5}) == approx(1.0)


def test_implication_with_predicate_atoms(fl):
    # Uses applied predicate atoms; keys are 'Tall(alice)' etc.
    f = fl.parse("Tall(alice) → Tall(bob)")
    val = {"Tall(alice)": 0.9, "Tall(bob)": 0.4}
    # min(1, 1-0.9+0.4) = min(1, 0.5) = 0.5
    assert evaluate(f, val) == approx(0.5)


# ---------------------------------------------------------------------------
# Quantifiers — unsorted FL
# ---------------------------------------------------------------------------

def test_forall_is_min(fl):
    f = fl.parse("∀x P(x)")
    val = {"P(a)": 0.3, "P(b)": 0.8}
    # ∀ == inf == min(0.3, 0.8) = 0.3
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.3)


def test_exists_is_max(fl):
    f = fl.parse("∃x P(x)")
    val = {"P(a)": 0.3, "P(b)": 0.8}
    # ∃ == sup == max(0.3, 0.8) = 0.8
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.8)


def test_forall_three_element_domain(fl):
    f = fl.parse("∀x P(x)")
    val = {"P(a)": 0.5, "P(b)": 0.2, "P(c)": 0.9}
    assert evaluate(f, val, domain={"a", "b", "c"}) == approx(0.2)


def test_quantified_body_with_connective(fl):
    # ∃x (P(x) ⊗ Q(x)) over {a, b}
    f = fl.parse("∃x (P(x) ⊗ Q(x))")
    val = {
        "P(a)": 0.9, "Q(a)": 0.5,   # 0.9⊗0.5 = max(0,0.4) = 0.4
        "P(b)": 0.8, "Q(b)": 0.8,   # 0.8⊗0.8 = max(0,0.6) = 0.6
    }
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.6)


def test_quantifier_requires_domain(fl):
    f = fl.parse("∀x P(x)")
    with pytest.raises(ValueError, match="domain"):
        evaluate(f, {"P(a)": 0.5})


def test_grounding_does_not_mutate_input(fl):
    f = fl.parse("∀x P(x)")
    before = f.to_unicode_str()
    evaluate(f, {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})
    assert f.to_unicode_str() == before  # input AST unchanged


def test_inner_binder_shadows_outer(fl):
    # ∀x ∃x P(x): the inner ∃x rebinds x, so the outer ∀ ranges vacuously over
    # a body whose value does not depend on the outer x. Result == ∃x P(x).
    f = fl.parse("∀x ∃x P(x)")
    val = {"P(a)": 0.2, "P(b)": 0.7}
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.7)


# ---------------------------------------------------------------------------
# Quantifiers — sorted MSFL
# ---------------------------------------------------------------------------

def test_sorted_forall_is_min(msfl):
    f = msfl.parse("∀x:Human Mortal(x)")
    val = {"Mortal(socrates)": 0.9, "Mortal(plato)": 0.4}
    out = evaluate(f, val, sort_universes={"Human": {"socrates", "plato"}})
    assert out == approx(0.4)


def test_sorted_exists_is_max(msfl):
    f = msfl.parse("∃x:Human Mortal(x)")
    val = {"Mortal(socrates)": 0.9, "Mortal(plato)": 0.4}
    out = evaluate(f, val, sort_universes={"Human": {"socrates", "plato"}})
    assert out == approx(0.9)


def test_sorted_quantifier_requires_universe(msfl):
    f = msfl.parse("∀x:Human Mortal(x)")
    with pytest.raises(ValueError, match="Human"):
        evaluate(f, {"Mortal(socrates)": 0.9})


# ---------------------------------------------------------------------------
# Error handling
# ---------------------------------------------------------------------------

def test_missing_atom_key_raises(fl):
    f = fl.parse("P ⊗ Q")
    with pytest.raises(KeyError, match="Q"):
        evaluate(f, {"P": 0.5})


def test_classical_connective_rejected():
    # Parse the same surface syntax in classical FOL mode -> And node.
    classical = MSFLParser(fuzzy=False).parse("P ∧ Q")
    assert isinstance(classical, And)
    with pytest.raises(TypeError, match="Łukasiewicz|FL/MSFL"):
        evaluate(classical, {"P": 0.6, "Q": 0.7})


def test_classical_not_rejected():
    classical = MSFLParser(fuzzy=False).parse("¬P")
    assert isinstance(classical, Not)
    with pytest.raises(TypeError):
        evaluate(classical, {"P": 0.5})


def test_xor_rejected():
    classical = MSFLParser(fuzzy=False).parse("P ⊕ Q")
    assert isinstance(classical, Xor)
    with pytest.raises(TypeError):
        evaluate(classical, {"P": 0.5, "Q": 0.5})


def test_comparison_atom_rejected():
    f = Atom("=", [Constant("a"), Constant("b")])
    with pytest.raises(TypeError, match="Comparison"):
        evaluate(f, {})


def test_number_rejected():
    with pytest.raises(TypeError, match="Number"):
        evaluate(Number(3), {})


def test_lambda_rejected():
    f = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
    with pytest.raises(TypeError, match="lambda"):
        evaluate(f, {})


def test_term_rejected():
    with pytest.raises(TypeError, match="term"):
        evaluate(Constant("a"), {})


# ---------------------------------------------------------------------------
# Clamping defensiveness and package re-export
# ---------------------------------------------------------------------------

def test_out_of_range_valuation_is_clamped(fl):
    f = fl.parse("P")
    assert evaluate(f, {"P": 1.7}) == approx(1.0)
    assert evaluate(f, {"P": -0.5}) == approx(0.0)


def test_package_level_evaluate_is_same(fl):
    assert evaluate_pkg is evaluate
    f = fl.parse("P ⊗ Q")
    assert evaluate_pkg(f, {"P": 0.6, "Q": 0.7}) == approx(0.3)


# ---------------------------------------------------------------------------
# Reviewer-added edge cases
# ---------------------------------------------------------------------------

def test_nested_distinct_var_outer_reaches_inner_body(fl):
    # ∀x (P(x) ⊗ ∃y Q(x,y)) over {a, b}. The outer x must be grounded *inside*
    # the inner ∃y body (the inner binder is a different name, so grounding must
    # descend through it). Two-argument atom keys render with a comma+space.
    f = fl.parse("∀x (P(x) ⊗ ∃y Q(x,y))")
    val = {
        "P(a)": 1.0, "P(b)": 1.0,
        "Q(a, a)": 0.3, "Q(a, b)": 0.7,   # x=a: ∃y = max(0.3,0.7)=0.7 ; 1⊗0.7=0.7
        "Q(b, a)": 0.1, "Q(b, b)": 0.2,   # x=b: ∃y = 0.2          ; 1⊗0.2=0.2
    }
    # ∀x => min(0.7, 0.2) = 0.2
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.2)


def test_two_arg_atom_key_uses_comma_space(fl):
    # The canonical key for a 2-ary atom is 'R(a, b)' (comma + space), the same
    # rendering to_unicode_str() produces. A key without the space must miss.
    f = fl.parse("∀x R(x, c)")
    val = {"R(a, c)": 0.4, "R(b, c)": 0.9}
    assert evaluate(f, val, domain={"a", "b"}) == approx(0.4)
    with pytest.raises(KeyError):
        evaluate(fl.parse("R(a, c)"), {"R(a,c)": 0.4})  # no space -> miss


def test_sorted_inner_binder_shadows_outer(msfl):
    # ∀x:Human ∃x:Human P(x): inner ∃x rebinds x; outer ∀ ranges vacuously.
    # Result == ∃x:Human P(x) == max over the Human universe.
    f = msfl.parse("∀x:Human ∃x:Human P(x)")
    val = {"P(socrates)": 0.2, "P(plato)": 0.7}
    out = evaluate(f, val, sort_universes={"Human": {"socrates", "plato"}})
    assert out == approx(0.7)


def test_singleton_domain_forall_equals_exists(fl):
    # Over a one-element domain, ∀ and ∃ both reduce to the single instance.
    fa = fl.parse("∀x P(x)")
    ex = fl.parse("∃x P(x)")
    val = {"P(a)": 0.42}
    assert evaluate(fa, val, domain={"a"}) == approx(0.42)
    assert evaluate(ex, val, domain={"a"}) == approx(0.42)


def test_empty_domain_raises(fl):
    f = fl.parse("∀x P(x)")
    with pytest.raises(ValueError, match="empty"):
        evaluate(f, {}, domain=set())


def test_strong_implication_residuation_identity(fl):
    # Residuation corner: 1 - x + y with x=0.3, y=0.9 -> min(1, 1.6) = 1.0
    # and the genuinely-below-one case x=0.9, y=0.1 -> min(1, 0.2) = 0.2.
    f = fl.parse("P → Q")
    assert evaluate(f, {"P": 0.3, "Q": 0.9}) == approx(1.0)
    assert evaluate(f, {"P": 0.9, "Q": 0.1}) == approx(0.2)
