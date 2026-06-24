"""Hand-checked tests for the three-valued Kleene K3 / Priest LP evaluator.

All oracle values are computed by hand from the strong-Kleene tables::

    ¬x = 1−x ;  a∧b = min ;  a∨b = max ;
    a→b = max(1−a, b) ;  a↔b = min(a→b, b→a) ;
    a⊕b = min(max(a,b), 1−min(a,b))

K3 designates {1.0}; LP (Priest) designates {0.5, 1.0}. The headline contrasts
are excluded middle (K3-invalid, LP-valid) and explosion (LP paraconsistent).
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Constant
from unicode_fol_kit.semantics.manyvalued import (
    kleene_value, is_valid, is_satisfiable, entails,
    DESIGNATED, TRUTH_VALUES, FALSE, UNDEFINED, TRUE,
)
try:  # the package __init__ re-exports are wired by the orchestrator
    from unicode_fol_kit.semantics import (
        kleene_value as kleene_value_pkg,
        is_valid as is_valid_pkg,
        entails as entails_pkg,
    )
    _HAVE_PKG_REEXPORTS = True
except ImportError:  # not yet re-exported — exercise the module path only
    _HAVE_PKG_REEXPORTS = False


@pytest.fixture
def cl():
    """Classical MSFL parser (∧ ∨ ¬ → ↔ ⊕, ∀ ∃)."""
    return MSFLParser()


# ---------------------------------------------------------------------------
# Designated-value sets and the value chain
# ---------------------------------------------------------------------------

def test_designated_sets():
    assert DESIGNATED["K3"] == frozenset({1.0})
    assert DESIGNATED["LP"] == frozenset({0.5, 1.0})


def test_truth_values_chain():
    assert TRUTH_VALUES == (0.0, 0.5, 1.0)
    assert (FALSE, UNDEFINED, TRUE) == (0.0, 0.5, 1.0)


def test_unknown_logic_rejected(cl):
    with pytest.raises(ValueError, match="Unknown logic"):
        is_valid(cl.parse("P"), logic="Lukasiewicz")


# ---------------------------------------------------------------------------
# Strong-Kleene connective truth values (the exact hand-checked numbers)
# ---------------------------------------------------------------------------

def test_negation(cl):
    assert kleene_value(cl.parse("¬P"), {"P": 0.0}) == 1.0
    assert kleene_value(cl.parse("¬P"), {"P": 0.5}) == 0.5   # ¬0.5 = 0.5
    assert kleene_value(cl.parse("¬P"), {"P": 1.0}) == 0.0


@pytest.mark.parametrize("a,b,expected", [
    (0.0, 0.0, 0.0), (0.0, 0.5, 0.0), (0.0, 1.0, 0.0),
    (0.5, 0.5, 0.5), (0.5, 1.0, 0.5), (1.0, 1.0, 1.0),
])
def test_conjunction_min(cl, a, b, expected):
    assert kleene_value(cl.parse("P ∧ Q"), {"P": a, "Q": b}) == expected


@pytest.mark.parametrize("a,b,expected", [
    (0.0, 0.0, 0.0), (0.0, 0.5, 0.5), (0.5, 0.5, 0.5),
    (0.5, 1.0, 1.0), (1.0, 0.0, 1.0), (1.0, 1.0, 1.0),
])
def test_disjunction_max(cl, a, b, expected):
    assert kleene_value(cl.parse("P ∨ Q"), {"P": a, "Q": b}) == expected


@pytest.mark.parametrize("a,b,expected", [
    # a→b = max(1−a, b)
    (0.0, 0.0, 1.0),   # max(1, 0) = 1
    (1.0, 0.0, 0.0),   # max(0, 0) = 0
    (0.5, 0.5, 0.5),   # max(0.5, 0.5) = 0.5  (the 0.5 row)
    (0.5, 0.0, 0.5),   # max(0.5, 0)   = 0.5
    (1.0, 0.5, 0.5),   # max(0, 0.5)   = 0.5
    (0.5, 1.0, 1.0),   # max(0.5, 1)   = 1
    (1.0, 1.0, 1.0),
])
def test_implication_material(cl, a, b, expected):
    assert kleene_value(cl.parse("P → Q"), {"P": a, "Q": b}) == expected


@pytest.mark.parametrize("a,b,expected", [
    # a↔b = min(a→b, b→a)
    (0.0, 0.0, 1.0),
    (1.0, 1.0, 1.0),
    (0.0, 1.0, 0.0),
    (0.5, 0.5, 0.5),   # min(0.5, 0.5) = 0.5  (the 0.5 row)
    (0.5, 1.0, 0.5),   # min(max(0.5,1), max(0,0.5)) = min(1, 0.5) = 0.5
    (0.5, 0.0, 0.5),
    (1.0, 0.0, 0.0),
])
def test_biconditional(cl, a, b, expected):
    assert kleene_value(cl.parse("P ↔ Q"), {"P": a, "Q": b}) == expected


@pytest.mark.parametrize("a,b,expected", [
    # a⊕b = min(max(a,b), 1−min(a,b))
    (0.0, 0.0, 0.0),
    (1.0, 1.0, 0.0),
    (0.0, 1.0, 1.0),
    (1.0, 0.0, 1.0),
    (0.5, 0.5, 0.5),   # min(0.5, 0.5) = 0.5  (the 0.5 row)
    (0.5, 1.0, 0.5),   # min(1, 0.5) = 0.5
    (0.5, 0.0, 0.5),
])
def test_xor(cl, a, b, expected):
    assert kleene_value(cl.parse("P ⊕ Q"), {"P": a, "Q": b}) == expected


# ---------------------------------------------------------------------------
# HEADLINE: excluded middle distinguishes K3 from LP
# ---------------------------------------------------------------------------

def test_excluded_middle_value_at_undefined(cl):
    # At P = 0.5: P ∨ ¬P = max(0.5, 0.5) = 0.5 (NOT 1.0).
    assert kleene_value(cl.parse("P ∨ ¬P"), {"P": 0.5}) == 0.5


def test_excluded_middle_k3_invalid_lp_valid(cl):
    lem = cl.parse("P ∨ ¬P")
    # K3 designates only 1.0 -> the 0.5 case breaks validity.
    assert is_valid(lem, "K3") is False
    # LP designates 0.5 too -> every assignment is designated.
    assert is_valid(lem, "LP") is True


# ---------------------------------------------------------------------------
# HEADLINE: non-contradiction / explosion
# ---------------------------------------------------------------------------

def test_non_contradiction_value_at_undefined(cl):
    # At P = 0.5: ¬(P ∧ ¬P) = ¬(min(0.5,0.5)) = ¬0.5 = 0.5.
    assert kleene_value(cl.parse("¬(P ∧ ¬P)"), {"P": 0.5}) == 0.5


def test_non_contradiction_k3_invalid(cl):
    nc = cl.parse("¬(P ∧ ¬P)")
    assert is_valid(nc, "K3") is False   # 0.5 at P=0.5 is undesignated in K3
    assert is_valid(nc, "LP") is True    # 0.5 is designated in LP


def test_explosion_lp_paraconsistent(cl):
    # entails([P, ¬P], Q): in LP, at P=0.5, Q=0 the premises are designated
    # (0.5 ∈ {0.5,1}) but Q = 0 is not -> NOT entailed.  LP is paraconsistent.
    P, notP, Q = cl.parse("P"), cl.parse("¬P"), cl.parse("Q")
    assert entails([P, notP], Q, "LP") is False
    # In K3, P and ¬P are never both designated (one is always <1), so the
    # entailment holds vacuously.
    assert entails([P, notP], Q, "K3") is True


def test_explosion_witness_values(cl):
    # Pin the exact witness that breaks LP explosion.
    v = {"P": 0.5, "Q": 0.0}
    assert kleene_value(cl.parse("P"), v) == 0.5      # designated in LP
    assert kleene_value(cl.parse("¬P"), v) == 0.5     # designated in LP
    assert kleene_value(cl.parse("Q"), v) == 0.0      # NOT designated


# ---------------------------------------------------------------------------
# Arguments K3 and LP agree on (classically valid, both preserve designation)
# ---------------------------------------------------------------------------

def test_conjunction_elimination_both(cl):
    # P ∧ Q ⊨ P holds in both K3 and LP.
    assert entails([cl.parse("P ∧ Q")], cl.parse("P"), "K3") is True
    assert entails([cl.parse("P ∧ Q")], cl.parse("P"), "LP") is True


def test_addition_both(cl):
    # P ⊨ P ∨ Q holds in both K3 and LP.
    assert entails([cl.parse("P")], cl.parse("P ∨ Q"), "K3") is True
    assert entails([cl.parse("P")], cl.parse("P ∨ Q"), "LP") is True


def test_double_negation_both(cl):
    # P ⊨ ¬¬P and ¬¬P ⊨ P in both logics (¬¬x = x pointwise).
    P, nnP = cl.parse("P"), cl.parse("¬¬P")
    for logic in ("K3", "LP"):
        assert entails([P], nnP, logic) is True
        assert entails([nnP], P, logic) is True


# ---------------------------------------------------------------------------
# Modus ponens: K3 validates it, LP does NOT (material-conditional MP fails in
# LP — the classic Priest result). Hand-checked witness: P=0.5, Q=0.
# ---------------------------------------------------------------------------

def test_modus_ponens_k3_holds_lp_fails(cl):
    prem = [cl.parse("P"), cl.parse("P → Q")]
    Q = cl.parse("Q")
    assert entails(prem, Q, "K3") is True
    assert entails(prem, Q, "LP") is False


def test_modus_ponens_lp_witness(cl):
    # At P=0.5, Q=0: P=0.5 designated; P→Q = max(0.5,0) = 0.5 designated;
    # but Q = 0 is not designated -> MP fails in LP.
    v = {"P": 0.5, "Q": 0.0}
    assert kleene_value(cl.parse("P"), v) == 0.5
    assert kleene_value(cl.parse("P → Q"), v) == 0.5
    assert kleene_value(cl.parse("Q"), v) == 0.0


# ---------------------------------------------------------------------------
# Satisfiability basics
# ---------------------------------------------------------------------------

def test_satisfiable_atom(cl):
    assert is_satisfiable(cl.parse("P"), "K3") is True
    assert is_satisfiable(cl.parse("P"), "LP") is True


def test_contradiction_unsat_k3_but_sat_lp(cl):
    # P ∧ ¬P: in K3 max value over assignments is 0.5 (at P=0.5) -> undesignated
    # -> unsatisfiable. In LP 0.5 is designated -> satisfiable.
    contra = cl.parse("P ∧ ¬P")
    assert is_satisfiable(contra, "K3") is False
    assert is_satisfiable(contra, "LP") is True


def test_tautology_template_satisfiable(cl):
    assert is_satisfiable(cl.parse("P ∨ ¬P"), "K3") is True
    assert is_valid(cl.parse("P → P"), "LP") is True  # max(1−a,a) ∈ {0.5,1}
    # P → P is K3-invalid: at P=0.5 it is 0.5.
    assert is_valid(cl.parse("P → P"), "K3") is False


# ---------------------------------------------------------------------------
# Quantifiers over a tiny domain (∀ = min, ∃ = max)
# ---------------------------------------------------------------------------

def test_forall_is_min(cl):
    fa = cl.parse("∀x P(x)")
    dom = {"a", "b"}
    assert kleene_value(fa, {"P(a)": 1.0, "P(b)": 1.0}, domain=dom) == 1.0
    assert kleene_value(fa, {"P(a)": 1.0, "P(b)": 0.5}, domain=dom) == 0.5
    assert kleene_value(fa, {"P(a)": 1.0, "P(b)": 0.0}, domain=dom) == 0.0


def test_exists_is_max(cl):
    ex = cl.parse("∃x P(x)")
    dom = {"a", "b"}
    assert kleene_value(ex, {"P(a)": 0.0, "P(b)": 0.0}, domain=dom) == 0.0
    assert kleene_value(ex, {"P(a)": 0.0, "P(b)": 0.5}, domain=dom) == 0.5
    assert kleene_value(ex, {"P(a)": 0.0, "P(b)": 1.0}, domain=dom) == 1.0


def test_quantifier_requires_domain(cl):
    with pytest.raises(ValueError, match="requires a 'domain'"):
        kleene_value(cl.parse("∀x P(x)"), {"P(a)": 1.0})


def test_quantified_validity_over_domain(cl):
    # ∀x (P(x) ∨ ¬P(x)) is LP-valid but K3-invalid over a domain.
    f = cl.parse("∀x (P(x) ∨ ¬P(x))")
    dom = {"a", "b"}
    assert is_valid(f, "LP", domain=dom) is True
    assert is_valid(f, "K3", domain=dom) is False


def test_quantified_entailment(cl):
    # ∀x P(x) ⊨ ∃x P(x) over a non-empty domain (both logics).
    fa, ex = cl.parse("∀x P(x)"), cl.parse("∃x P(x)")
    dom = {"a", "b"}
    assert entails([fa], ex, "K3", domain=dom) is True
    assert entails([fa], ex, "LP", domain=dom) is True


# ---------------------------------------------------------------------------
# Input validation and rejection of non-classical nodes
# ---------------------------------------------------------------------------

def test_missing_atom_key_raises(cl):
    with pytest.raises(KeyError):
        kleene_value(cl.parse("P"), {})


def test_illegal_truth_value_raises(cl):
    with pytest.raises(ValueError, match="0.0, 0.5, 1.0"):
        kleene_value(cl.parse("P"), {"P": 0.3})


def test_value_snapping_tolerates_drift(cl):
    # A value within float epsilon of 0.5 snaps cleanly.
    assert kleene_value(cl.parse("P"), {"P": 0.5 + 1e-12}) == 0.5


def test_fuzzy_node_rejected():
    fl = MSFLParser(fuzzy=True)
    with pytest.raises(NotImplementedError, match="Łukasiewicz"):
        kleene_value(fl.parse("P ⊗ Q"), {"P": 1.0, "Q": 1.0})


def test_modal_node_rejected():
    modal = MSFLParser(modal=True)
    with pytest.raises(NotImplementedError, match="modal"):
        kleene_value(modal.parse("□P"), {"P": 1.0})


def test_bare_term_rejected():
    with pytest.raises(TypeError, match="term, not a formula"):
        kleene_value(Constant("a"), {})


# ---------------------------------------------------------------------------
# Package-level re-exports work identically
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not _HAVE_PKG_REEXPORTS,
                    reason="semantics package re-exports wired by orchestrator")
def test_package_reexports(cl):
    lem = cl.parse("P ∨ ¬P")
    assert kleene_value_pkg(lem, {"P": 0.5}) == 0.5
    assert is_valid_pkg(lem, "LP") is True
    assert is_valid_pkg(lem, "K3") is False
    assert entails_pkg([cl.parse("P"), cl.parse("¬P")], cl.parse("Q"), "LP") is False
