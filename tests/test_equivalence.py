"""Tests for the graded equivalence checker (eval/equivalence.py).

Each expectation is hand-checked. The key semantic contracts under test:

* only the SOLVER level may produce a False headline verdict, and only with a
  counterexample in hand (for the routes that yield one);
* a solver "unknown" stays None — it is never collapsed to False (the defect
  of the old formulas_are_equivalent that this module exists to avoid);
* the auto ladder stops at the FIRST level that answers True, so cheap
  structural evidence short-circuits the solver.
"""

import json

import pytest

from unicode_fol_kit import MSFLParser, equivalent

_P = MSFLParser()
_MP = MSFLParser(modal=True)


# ---------------------------------------------------------------------------
# The ladder, level by level.
# ---------------------------------------------------------------------------

def test_exact_level_structural_equality():
    f = _P.parse("P(a) ∧ Q(b)")
    g = _P.parse("P(a) ∧ Q(b)")
    r = equivalent(f, g, method="exact")
    assert r.equivalent is True and r.method_used == "exact"
    assert bool(r) is True


def test_canonical_level_commutativity():
    """Q ∧ P vs P ∧ Q: not exact, but canonically equal."""
    f = _P.parse("Q(b) ∧ P(a)")
    g = _P.parse("P(a) ∧ Q(b)")
    assert equivalent(f, g, method="exact").equivalent is None
    r = equivalent(f, g, method="canonical")
    assert r.equivalent is True and r.structurally_equal is True


def test_predicate_align_level_vocabulary():
    """Winner vs IsWinner (d = 0.25): only the aligned level closes the gap."""
    f = _P.parse("∀x (Plays(x) → Winner(x))")
    g = _P.parse("∀x (Plays(x) → IsWinner(x))")
    assert equivalent(f, g, method="canonical").equivalent is None
    r = equivalent(f, g, method="predicate_align")
    assert r.equivalent is True and r.aligned_equal is True


def test_solver_level_proves_contraposition():
    """P→Q ≡ ¬Q→¬P: no structural level sees it, Z3 proves it."""
    f = _P.parse("P(a) → Q(a)")
    g = _P.parse("¬Q(a) → ¬P(a)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is True and r.logically_equivalent is True
    assert r.counterexample is None


def test_solver_level_refutes_with_counterexample():
    """P∨Q vs P∧Q differ: verdict False plus a Z3 model as witness."""
    f = _P.parse("P(a) ∨ Q(a)")
    g = _P.parse("P(a) ∧ Q(a)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is False
    assert r.counterexample is not None and r.counterexample["kind"] == "z3_model"
    assert bool(r) is False


def test_auto_ladder_stops_at_first_true():
    """auto reports the CHEAPEST level that decided, not the solver."""
    f = _P.parse("Q(b) ∧ P(a)")
    g = _P.parse("P(a) ∧ Q(b)")
    r = equivalent(f, g)                      # method="auto"
    assert r.equivalent is True and r.method_used == "canonical"
    assert r.syntax_equal is False            # the failed cheaper level is recorded
    assert r.logically_equivalent is None     # the solver never ran


def test_auto_falls_through_to_solver_refutation():
    f = _P.parse("∀x P(x)")
    g = _P.parse("∃x P(x)")
    r = equivalent(f, g)
    assert r.equivalent is False and r.method_used == "solver"
    assert r.aligned_equal is False


# ---------------------------------------------------------------------------
# Modal routing.
# ---------------------------------------------------------------------------

def test_modal_solver_proves_dual():
    """□P ≡ ¬◇¬P in K — the propositional modal decider proves it."""
    f = _MP.parse("□P")
    g = _MP.parse("¬◇¬P")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is True


def test_modal_solver_refutes_with_kripke_witness():
    """□P vs ◇P differ in K; the witness is a Kripke counter-model."""
    f = _MP.parse("□P")
    g = _MP.parse("◇P")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is False
    assert r.counterexample is not None and r.counterexample["kind"] == "kripke"


def test_modal_frame_parameter_changes_the_verdict():
    """□P ≡ □□P holds in S4 (4-axiom) but not in K."""
    f = _MP.parse("□P")
    g = _MP.parse("□P ∧ □□P")
    assert equivalent(f, g, method="solver", frame="S4").equivalent is True
    assert equivalent(f, g, method="solver", frame="K").equivalent is False


# ---------------------------------------------------------------------------
# Result hygiene.
# ---------------------------------------------------------------------------

def test_result_to_dict_is_json_compatible():
    f = _P.parse("P(a) ∨ Q(a)")
    g = _P.parse("P(a) ∧ Q(a)")
    d = equivalent(f, g).to_dict()
    json.dumps(d)                              # must not raise
    assert d["equivalent"] is False and d["method_used"] == "solver"


def test_unknown_method_raises():
    f = _P.parse("P(a)")
    with pytest.raises(ValueError, match="unknown method"):
        equivalent(f, f, method="fuzzy-vibes")


# ---------------------------------------------------------------------------
# Partial-credit rubric (eval/equivalence.py: partial_credit /
# partial_credit_components). Every score below is hand-derived from the
# rubric definition in EquivalenceResult's docstring:
#   headline equivalent is True         -> 1.0 (components not computed)
#   else: 0.25 * (s1 + s2 + s3 + s4), where
#     s1 = is_wellformed(prediction) AND is_wellformed(reference)
#     s2 = align_symbols(prediction, reference)'s symbol inventories
#          (predicate/function name+arity, constant names) equal reference's
#     s3 = aligned_exact_match(prediction, reference)
#     s4 = solver verdict is True (None/False both count 0)
#
# NOTE on the parser's naming convention (unicode_fol_kit/fol/grammars/
# terminals.lark): a SINGLE lowercase letter (optionally with trailing
# digits, e.g. "x", "a", "q0") lexes as VARIABLE, not a constant. So "P(a)"
# parses as an OPEN atom with a's a free logical Variable — it is NOT a
# closed sentence. To build genuinely CLOSED example formulas (needed for
# s1=True) the tests below either bind every variable with a quantifier, or
# use a multi-letter lowercase NAME token (e.g. "alice"), which the grammar
# parses as a Constant instead.
# ---------------------------------------------------------------------------

def test_partial_credit_full_when_headline_equivalent():
    """Contraposition (P(alice)->Q(alice) === not Q(alice)->not P(alice)):
    the solver PROVES equivalence, so equivalent=True and, per the rubric's
    first rule, partial_credit is 1.0 outright regardless of the sub-checks;
    the component breakdown is not computed in that branch.
    """
    f = _P.parse("P(alice) → Q(alice)")
    g = _P.parse("¬Q(alice) → ¬P(alice)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is True
    assert r.partial_credit == 1.0
    assert r.partial_credit_components is None

    # method="auto" falls through the structural levels (none match here)
    # and reaches the same solver proof.
    r_auto = equivalent(f, g)
    assert r_auto.equivalent is True and r_auto.method_used == "solver"
    assert r_auto.partial_credit == 1.0
    assert r_auto.partial_credit_components is None


def test_partial_credit_same_vocabulary_logically_different():
    """P(alice)v Q(alice) vs P(alice)^Q(alice): same predicates P/1, Q/1 and
    the same constant 'alice' on both sides, both formulas closed and
    arity-consistent, but Or != And logically (Z3 refutes with a
    counterexample where P holds and Q does not).

    Hand-derived components:
      s1 = True  (both closed: only the constant 'alice' appears, no free
           variables; arity-consistent P/1, Q/1; no lambdas)          -> 1
      s2 = True  (identical vocabulary on both sides -> align_symbols is a
           no-op identity map, inventories trivially match)            -> 1
      s3 = False (aligned prediction ∨-canonical-form != reference's
           ∧-canonical-form -- different connective, not a match)      -> 0
      s4 = False (solver refutes: equivalent is False, not True)       -> 0
    partial_credit = 0.25*(1+1+0+0) = 0.5
    """
    f = _P.parse("P(alice) ∨ Q(alice)")
    g = _P.parse("P(alice) ∧ Q(alice)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is False
    assert r.partial_credit_components == {
        "s1": True, "s2": True, "s3": False, "s4": False,
    }
    assert r.partial_credit == 0.5


def test_partial_credit_unalignable_vocabulary_logically_different():
    """Xyzzyplonk(alice) vs Q(alice): both closed sentences (single constant
    'alice', arity-consistent, no lambdas), but the predicate names
    'Xyzzyplonk' and 'Q' are nowhere near each other under normalised
    Levenshtein distance (default threshold 0.6), so align_symbols leaves
    the prediction's predicate unchanged -- the vocabularies stay disjoint.
    The two claims are also logically different (Z3 refutes: nothing forces
    Xyzzyplonk and Q to agree on 'alice').

    Hand-derived components:
      s1 = True  (both are closed, arity-consistent, lambda-free)      -> 1
      s2 = False (aligned prediction keeps 'Xyzzyplonk/1'; reference has
           'Q/1' -- inventories differ)                                -> 0
      s3 = False (no alignment happened, so the canonical forms of
           Xyzzyplonk(alice) and Q(alice) plainly differ)              -> 0
      s4 = False (solver refutes: equivalent is False, not True)       -> 0
    partial_credit = 0.25*(1+0+0+0) = 0.25
    """
    f = _P.parse("Xyzzyplonk(alice)")
    g = _P.parse("Q(alice)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is False
    assert r.partial_credit_components == {
        "s1": True, "s2": False, "s3": False, "s4": False,
    }
    assert r.partial_credit == 0.25


def test_partial_credit_open_prediction_against_closed_reference():
    """P(x) (x is a free VARIABLE -- see the module note above) as the
    prediction against the closed reference (universally quantified) 'forall
    y P(y)': same predicate P/1 on both sides, but the prediction is an OPEN
    formula, and Z3 refutes logical equivalence (a countermodel where P does
    not hold at every element, but happens to hold at the value picked for
    the free x).

    Hand-derived components:
      s1 = False (is_wellformed(prediction) is False -- x is free, so the
           prediction is not a closed sentence; the AND with reference's
           True is still False)                                        -> 0
      s2 = True  (both use predicate P/1 and nothing else -- identical
           vocabulary, align_symbols is a no-op, inventories match)     -> 1
      s3 = False (P(x) is a bare atom; the reference canonicalizes to a
           quantified formula -- different shape, no match)             -> 0
      s4 = False (solver refutes: equivalent is False, not True)        -> 0
    partial_credit = 0.25*(0+1+0+0) = 0.25
    """
    f = _P.parse("P(x)")
    g = _P.parse("∀y P(y)")
    r = equivalent(f, g, method="solver")
    assert r.equivalent is False
    assert r.partial_credit_components == {
        "s1": False, "s2": True, "s3": False, "s4": False,
    }
    assert r.partial_credit == 0.25


@pytest.mark.parametrize("method", ["exact", "canonical", "predicate_align"])
def test_partial_credit_none_for_purely_structural_methods(method):
    """The rubric's s4 needs a solver verdict, which exact/canonical/
    predicate_align never obtain -- partial_credit (and its components) must
    stay None for these methods, an honest "not computed" rather than a
    score of 0. Uses a pair that is trivially equal under every structural
    level so the headline itself is True, to make sure partial_credit is
    NOT silently set to 1.0 by these methods either (only auto/solver fill
    it in at all).
    """
    f = _P.parse("P(alice) ∧ Q(alice)")
    g = _P.parse("P(alice) ∧ Q(alice)")
    r = equivalent(f, g, method=method)
    assert r.partial_credit is None
    assert r.partial_credit_components is None
