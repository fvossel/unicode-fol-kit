"""Tests for declared converse / argument-permutation axioms (eval/converses.py).

Every expected value below is hand-derived (see each test's docstring for the
by-hand reasoning) and, for the solver-level cases, cross-checked against a
real Z3 run — this is the independent second route the roadmap's test_oracle
names, since the whole point of this feature is a Z3-level bridge and a
tautological "does the code agree with itself" check would prove nothing.

Key soundness properties pinned here, not just asserted in a docstring:

* a converse axiom does not manufacture a false positive between predicates
  it does not mention — a real argument swap (``Loves(b,a)`` vs
  ``Loves(a,b)``) stays refuted with an irrelevant ``LovedBy``/``Loves``
  axiom in scope;
* the bridge works IDENTICALLY under many-sorted (``SortedQuantifier``)
  input, and a WRONG argument order under the same sorts is still refuted —
  proof that the axiom is not a silent no-op there (this kit's whole
  classical Z3 export uses exactly one Z3 sort for every term, so there is
  no separate multi-sort divergence to worry about — see
  ``eval/converses.py``'s module docstring for the by-inspection argument);
* a malformed declaration is refused before any Z3 solver is even
  constructed.
"""

import pytest
import z3

from unicode_fol_kit import MSFLParser, equivalent
from unicode_fol_kit.eval.converses import converse_axioms, validate_converses
from unicode_fol_kit.eval.metric_hf import compute_fol_metrics

_P = MSFLParser()
_MSFOL = MSFLParser(many_sorted=True)
_MP = MSFLParser(modal=True)


# ---------------------------------------------------------------------------
# converse_axioms: the axiom SHAPE, hand-derived.
# ---------------------------------------------------------------------------

def test_converse_axioms_binary_shape_matches_hand_derivation():
    """(LovedBy, Loves, (1, 0)) -> ∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0)).

    By definition (module docstring): A's args are v0..v_{n-1} in natural
    order, B's are the same variables reordered by `permutation`, so
    permutation=(1, 0) puts v1 first and v0 second in B's argument list.
    """
    decl = [(("LovedBy", 2), ("Loves", 2), (1, 0))]
    axioms = converse_axioms(decl)
    assert len(axioms) == 1
    assert axioms[0].to_unicode_str() == "∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0))"


def test_converse_axioms_ternary_shape_matches_hand_derivation():
    """(BetweenRev, Between, (2, 1, 0)) ->
    ∀v0 v1 v2 (BetweenRev(v0,v1,v2) ↔ Between(v2,v1,v0)) — reversal."""
    decl = [(("BetweenRev", 3), ("Between", 3), (2, 1, 0))]
    axioms = converse_axioms(decl)
    assert (axioms[0].to_unicode_str() ==
            "∀v0 ∀v1 ∀v2 (BetweenRev(v0, v1, v2) ↔ Between(v2, v1, v0))")


# ---------------------------------------------------------------------------
# equivalent(..., converses=...): the five brief cases plus the ternary one,
# each independently re-derived and run end-to-end against real Z3.
# ---------------------------------------------------------------------------

_LOVED_BY_LOVES = [(("LovedBy", 2), ("Loves", 2), (1, 0))]


def test_converse_bridges_loves_and_lovedby_reversed():
    """Loves(a,b) vs LovedBy(b,a), declared LovedBy(x,y)<->Loves(y,x):
    the axiom instantiated at v0=b,v1=a gives exactly LovedBy(b,a) <->
    Loves(a,b) -- so the two sides coincide and Z3 proves it (unsat on the
    negated biconditional)."""
    f = _P.parse("Loves(a, b)")
    g = _P.parse("LovedBy(b, a)")
    r = equivalent(f, g, method="solver", converses=_LOVED_BY_LOVES)
    assert r.equivalent is True and r.method_used == "solver_modulo_converses"
    assert r.counterexample is None


def test_converse_axiom_does_not_bridge_the_wrong_argument_order():
    """Loves(a,b) vs LovedBy(a,b) (SAME order, not swapped): the axiom
    relates LovedBy(a,b) to Loves(b,a), not Loves(a,b), so Loves(a,b)=True,
    Loves(b,a)=False is a genuine Z3-found counterexample -- the axiom does
    NOT make every LovedBy/Loves pair equivalent, only the true converse."""
    f = _P.parse("Loves(a, b)")
    g = _P.parse("LovedBy(a, b)")
    r = equivalent(f, g, method="solver", converses=_LOVED_BY_LOVES)
    assert r.equivalent is False
    assert r.counterexample is not None and r.counterexample["kind"] == "z3_model"


def test_converse_axiom_does_not_manufacture_a_false_positive_elsewhere():
    """Loves(b,a) vs Loves(a,b): a REAL argument swap on Loves itself, with
    an irrelevant LovedBy/Loves converse axiom in scope. The axiom is a
    biconditional between LovedBy and Loves and says nothing about Loves(b,a)
    vs Loves(a,b) directly, so this must stay refuted -- proving the bridge
    is conservative, not a blanket permission to swap arguments anywhere."""
    f = _P.parse("Loves(b, a)")
    g = _P.parse("Loves(a, b)")
    r = equivalent(f, g, method="solver", converses=_LOVED_BY_LOVES)
    assert r.equivalent is False
    assert r.counterexample is not None and r.counterexample["kind"] == "z3_model"


def test_converse_bridges_ternary_reversal():
    """Between(a,b,c) vs BetweenRev(c,b,a), declared
    BetweenRev(x,y,z)<->Between(z,y,x): instantiated at v0=c,v1=b,v2=a this
    gives exactly BetweenRev(c,b,a) <-> Between(a,b,c)."""
    decl = [(("BetweenRev", 3), ("Between", 3), (2, 1, 0))]
    f = _P.parse("Between(a, b, c)")
    g = _P.parse("BetweenRev(c, b, a)")
    r = equivalent(f, g, method="solver", converses=decl)
    assert r.equivalent is True and r.method_used == "solver_modulo_converses"


# ---------------------------------------------------------------------------
# converses=None is a strict no-op (byte-identical to omitting the argument).
# ---------------------------------------------------------------------------

def test_converses_none_is_a_strict_noop():
    f = _P.parse("P(a) → Q(a)")
    g = _P.parse("¬Q(a) → ¬P(a)")
    baseline = equivalent(f, g, method="solver")
    with_none = equivalent(f, g, method="solver", converses=None)
    assert with_none.method_used == baseline.method_used == "solver"
    assert with_none.equivalent == baseline.equivalent


# ---------------------------------------------------------------------------
# validate_converses: every structural rejection, plus the allowed chain.
# ---------------------------------------------------------------------------

def test_arity_mismatch_is_rejected():
    with pytest.raises(ValueError, match="arity mismatch"):
        validate_converses([(("LovedBy", 2), ("Loves", 3), (1, 0))])


def test_permutation_wrong_length_is_rejected():
    with pytest.raises(ValueError, match="entries, expected"):
        validate_converses([(("LovedBy", 2), ("Loves", 2), (1, 0, 2))])


def test_permutation_not_a_bijection_is_rejected():
    """(0, 0) repeats index 0 and never uses index 1 -- not a permutation."""
    with pytest.raises(ValueError, match="not a bijection"):
        validate_converses([(("A", 2), ("B", 2), (0, 0))])


def test_self_pair_is_rejected():
    with pytest.raises(ValueError, match="its own converse"):
        validate_converses([(("Loves", 2), ("Loves", 2), (1, 0))])


def test_builtin_predicate_is_rejected():
    with pytest.raises(ValueError, match="built-in predicate"):
        validate_converses([(("=", 2), ("B", 2), (1, 0))])


def test_duplicate_unordered_pair_is_rejected_same_order():
    with pytest.raises(ValueError, match="already declared"):
        validate_converses([
            (("LovedBy", 2), ("Loves", 2), (1, 0)),
            (("LovedBy", 2), ("Loves", 2), (1, 0)),
        ])


def test_contradictory_permutations_for_the_same_pair_are_rejected():
    """Two DIFFERENT permutations for the same {A, B} pair are just as
    contradictory as an exact duplicate, and caught by the same unordered-
    pair check (declared with the operands swapped, too)."""
    with pytest.raises(ValueError, match="already declared"):
        validate_converses([
            (("LovedBy", 2), ("Loves", 2), (1, 0)),
            (("Loves", 2), ("LovedBy", 2), (0, 1)),
        ])


def test_chain_of_distinct_pairs_is_allowed_and_composes():
    """A~B, B~C on DISTINCT pairs is fine (not the same unordered pair
    twice) and the two axioms compose through the shared predicate B:
    A(a,b) vs C(b,a) should be provably equivalent via the chain."""
    decl = [
        (("A", 2), ("B", 2), (1, 0)),
        (("B", 2), ("C", 2), (1, 0)),
    ]
    validate_converses(decl)                        # does not raise
    f = _P.parse("A(a, b)")
    g = _P.parse("C(b, a)")
    r = equivalent(f, g, method="solver", converses=decl)
    # A(a,b) <-> B(b,a) [first axiom, v0=a,v1=b] and B(b,a) <-> C(a,b)
    # [second axiom, v0=b,v1=a] chain to A(a,b) <-> C(a,b) -- NOT C(b,a).
    # So this specific pairing (C(b,a)) is refuted; the point of this test
    # is that BOTH axioms were accepted and BOTH were consulted (a solver
    # that ignored one would likely answer differently) -- checked directly
    # below against the reading the chain DOES license.
    assert r.equivalent is False
    g_correct = _P.parse("C(a, b)")
    r_correct = equivalent(f, g_correct, method="solver", converses=decl)
    assert r_correct.equivalent is True


def test_arity_mismatch_raises_before_any_z3_call(monkeypatch):
    """The independent-route requirement from the roadmap's test_oracle:
    not just pytest.raises, but proof z3.Solver was never even constructed
    for an invalid declaration."""
    def _boom(*_args, **_kwargs):
        raise AssertionError("z3.Solver must not be constructed for an invalid declaration")
    monkeypatch.setattr(z3, "Solver", _boom)

    f = _P.parse("Loves(a, b)")
    g = _P.parse("LovedBy(b, a)")
    bad = [(("LovedBy", 2), ("Loves", 3), (1, 0))]
    with pytest.raises(ValueError, match="arity mismatch"):
        equivalent(f, g, method="solver", converses=bad)


# ---------------------------------------------------------------------------
# method-level integration: which methods honour converses, which refuse.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("method", ["exact", "canonical", "predicate_align"])
def test_structural_methods_refuse_nonempty_converses(method):
    f = _P.parse("Loves(a, b)")
    g = _P.parse("LovedBy(b, a)")
    with pytest.raises(ValueError, match="requires method in"):
        equivalent(f, g, method=method, converses=_LOVED_BY_LOVES)


def test_auto_ladder_tags_solver_modulo_converses_only_when_it_ran():
    """auto still tries the cheap structural levels first; when one of them
    already succeeds, converses is simply unused (method_used stays
    "canonical") -- only when the ladder genuinely reaches the solver with
    axioms declared does the new tag appear."""
    f = _P.parse("P(a) ∧ Q(a)")
    g = _P.parse("Q(a) ∧ P(a)")
    r = equivalent(f, g, converses=[(("Loves", 2), ("LovedBy", 2), (1, 0))])
    assert r.method_used == "canonical"            # commutativity alone decides it

    f2 = _P.parse("Loves(a, b)")
    g2 = _P.parse("LovedBy(b, a)")
    r2 = equivalent(f2, g2, converses=_LOVED_BY_LOVES)
    assert r2.equivalent is True
    assert r2.method_used == "solver_modulo_converses"


def test_modal_pair_with_converses_raises_not_implemented():
    f = _MP.parse("□P")
    g = _MP.parse("□Q")
    with pytest.raises(NotImplementedError, match="modal"):
        equivalent(f, g, method="solver",
                  converses=[(("P", 0), ("Q", 0), ())])


# ---------------------------------------------------------------------------
# Many-sorted input: the SOUNDNESS-TRAP proof — no silent no-op.
#
# This kit's classical Z3 export uses exactly one Z3 sort for every term
# (see eval/converses.py's module docstring), so a plain unsorted converse
# axiom interns to the SAME (name, arity) Z3 predicate the SortedQuantifier-
# relativised formulas themselves use. The two tests below are the
# differential proof: the axiom bridges the CORRECT permutation (True) and
# genuinely refutes the WRONG one (False, with a counterexample) under
# identical sorts on both sides -- if the axiom were silently failing to
# reach the same Z3 predicate, both cases would come back "unknown"/wrongly
# decided instead of these two distinct, correct verdicts.
# ---------------------------------------------------------------------------

def test_converse_bridges_correctly_under_sorted_quantifiers():
    """∀x:Human ∀y:Dog Loves(x,y) vs ∀x:Human ∀y:Dog LovedBy(y,x): the
    declared axiom says LovedBy(y,x) <-> Loves(x,y), so substituting inside
    the sorted quantifiers gives back exactly the left-hand side."""
    f = _MSFOL.parse("∀x:Human ∀y:Dog Loves(x, y)")
    g = _MSFOL.parse("∀x:Human ∀y:Dog LovedBy(y, x)")
    r = equivalent(f, g, method="solver", converses=_LOVED_BY_LOVES)
    assert r.equivalent is True and r.method_used == "solver_modulo_converses"


def test_converse_axiom_refutes_wrong_order_under_sorted_quantifiers():
    """Same sorted setup, but LovedBy keeps the SAME (x, y) order instead of
    the swapped (y, x): via the axiom this reads as "for every human x and
    dog y, the dog loves the human", which is NOT the same claim as "every
    human loves every dog" -- Z3 must refute it, proving the sorted case is
    not vacuously true regardless of the declared permutation."""
    f = _MSFOL.parse("∀x:Human ∀y:Dog Loves(x, y)")
    g_wrong = _MSFOL.parse("∀x:Human ∀y:Dog LovedBy(x, y)")
    r = equivalent(f, g_wrong, method="solver", converses=_LOVED_BY_LOVES)
    assert r.equivalent is False
    assert r.counterexample is not None and r.counterexample["kind"] == "z3_model"


# ---------------------------------------------------------------------------
# compute_fol_metrics: converses=None keeps the 6-key dict; non-empty adds
# converse_matched_rate, hand-computed.
# ---------------------------------------------------------------------------

def test_compute_fol_metrics_converses_none_keeps_six_key_dict():
    result = compute_fol_metrics(["P(a)"], ["P(a)"], converses=None)
    assert set(result.keys()) == {
        "exact_match", "equivalence_accuracy", "mean_partial_credit",
        "parse_failure_rate", "solver_unknown_rate", "n",
    }


def test_compute_fol_metrics_converse_matched_rate_hand_computed():
    """3 pairs, method="auto" (the ladder, not a forced solver call): #1
    P(a) vs P(a) is caught by the EXACT level and never reaches the solver
    (method_used="exact", never tagged); #2 Loves(a,b) vs LovedBy(b,a) is
    the true converse — not exact/canonical/aligned-equal (different
    argument order survives alignment, since align_symbols never touches
    argument order — see predicate_match.py), so it falls through to the
    solver WITH the declared axiom and is proved (tagged, True); #3
    Precedes(a,b) vs Follows(a,b) under a SEPARATE declared Follows/Precedes
    converse is the SAME-order (not swapped) case, so — exactly like the
    equivalence-level "wrong argument order" test above — it also falls
    through to the solver but is REFUTED (tagged, False). "Precedes"/
    "Follows" are lexically far apart (normalised Levenshtein 0.875, checked
    directly) so predicate_align cannot accidentally alias them the way it
    would alias "Loves"/"LovedBy" (0.43) with a coincidentally-matching
    argument order — the whole point of this pair is to reach the solver
    genuinely, not by accident.

    Hand count: converse_matched_rate = 1/3 (only pair #2 is BOTH tagged
    solver_modulo_converses AND True); equivalence_accuracy = 2/3 (pairs #1
    and #2 are True, #3 is False).
    """
    decl = _LOVED_BY_LOVES + [(("Follows", 2), ("Precedes", 2), (1, 0))]
    predictions = ["P(a)", "Loves(a, b)", "Precedes(a, b)"]
    references = ["P(a)", "LovedBy(b, a)", "Follows(a, b)"]
    result = compute_fol_metrics(predictions, references, method="auto",
                                 converses=decl)
    assert result["n"] == 3
    assert result["converse_matched_rate"] == pytest.approx(1 / 3)
    assert result["equivalence_accuracy"] == pytest.approx(2 / 3)


def test_compute_fol_metrics_validates_converses_even_on_empty_batch():
    """A structurally invalid declaration must be refused regardless of
    batch size. _score_pair (the only other call site that reaches
    validate_converses, via equivalent()) never runs for an empty batch, so
    without an explicit validation call at the top of compute_fol_metrics an
    empty batch would silently accept a malformed declaration instead of
    raising -- the same self-pair rejection as
    test_self_pair_is_rejected above, checked here with n=0 AND n=1 to prove
    the n=0 path is not a silent exception."""
    bad = [(("Loves", 2), ("Loves", 2), (1, 0))]      # self-pair, rejected
    with pytest.raises(ValueError, match="its own converse"):
        compute_fol_metrics([], [], converses=bad)
    with pytest.raises(ValueError, match="its own converse"):
        compute_fol_metrics(["P(a)"], ["P(a)"], converses=bad)


def test_compute_fol_metrics_method_gating_has_n0_n1_parity():
    """A STRUCTURALLY VALID converses declaration combined with a
    solver-incompatible method (exact/canonical/predicate_align) must raise
    ValueError regardless of batch size -- not just for n >= 1.

    Before this fix, the method-gating check
    (equivalence.py's ``equivalent()``: "converses requires method in
    {'solver', 'auto'}") only ran inside ``_score_pair`` -> ``equivalent()``,
    which never executes when n == 0, so
    ``compute_fol_metrics([], [], method="exact", converses=decl)`` silently
    returned zeroed metrics instead of raising, while the exact same
    ``method``/``converses`` pair at n == 1 correctly raised. Checked here at
    n=0 AND n=1 (mirroring
    ``test_compute_fol_metrics_validates_converses_even_on_empty_batch``
    above) to pin the parity, and for each of the three gated methods.
    """
    decl = _LOVED_BY_LOVES   # structurally valid -- not a self-pair
    for bad_method in ("exact", "canonical", "predicate_align"):
        with pytest.raises(ValueError, match="requires method in"):
            compute_fol_metrics([], [], method=bad_method, converses=decl)
        with pytest.raises(ValueError, match="requires method in"):
            compute_fol_metrics(["P(a)"], ["P(a)"], method=bad_method,
                                converses=decl)
    # Control: "solver" and "auto" (the only two methods converses supports)
    # must NOT raise at n == 0 -- the gating check must not over-fire.
    for ok_method in ("solver", "auto"):
        result = compute_fol_metrics([], [], method=ok_method, converses=decl)
        assert result["n"] == 0
