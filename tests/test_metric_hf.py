"""Tests for the HuggingFace-``evaluate``-compatible NL→FOL metric
(unicode_fol_kit/eval/metric_hf.py).

Every expectation below is hand-derived from
:func:`unicode_fol_kit.eval.equivalence.equivalent`'s documented ladder and
partial-credit rubric (see that module's docstring, and
``tests/test_equivalence.py`` for the same rubric worked through directly).
The two things this suite exists to pin down beyond ``equivalent`` itself:

* the per-pair AGGREGATION arithmetic in
  :func:`~unicode_fol_kit.eval.metric_hf.compute_fol_metrics` (means and
  rates over a batch, parse failures scored 0.0, ``partial_credit`` floored
  to 0.0 when the requested ladder level never computes one);
* the HONESTY split between ``equivalence_accuracy`` (only a definitive
  ``True``) and ``solver_unknown_rate`` (the solver-reached-but-undecided
  mass) -- these must never be confused, per the module's honesty-contract
  section.

Naming convention carried over from ``test_equivalence.py``: a SINGLE
lowercase letter lexes as a VARIABLE in this grammar, not a constant, so
formulas below use multi-letter names (``alice``) wherever a genuinely
CLOSED sentence is needed for a clean, predictable well-formedness bit.
"""

import importlib
import sys

import pytest

from unicode_fol_kit.eval import metric_hf


# ---------------------------------------------------------------------------
# compute_fol_metrics -- single-pair sanity checks.
# ---------------------------------------------------------------------------

def test_identical_pair_scores_full_marks():
    """Same formula string on both sides: every headline number is 1.0/0.0
    at its best possible value (n=1)."""
    r = metric_hf.compute_fol_metrics(
        ["P(alice) ∧ Q(alice)"], ["P(alice) ∧ Q(alice)"])
    assert r == {
        "exact_match": 1.0,
        "equivalence_accuracy": 1.0,
        "mean_partial_credit": 1.0,
        "parse_failure_rate": 0.0,
        "solver_unknown_rate": 0.0,
        "n": 1,
    }


def test_commuted_conjunction_pair_exact_zero_equivalence_one():
    """P∧Q vs Q∧P: not AST-equal, but the canonical level proves it -- the
    textbook case this metric exists to reward over plain string equality.
    """
    r = metric_hf.compute_fol_metrics(
        ["P(alice) ∧ Q(alice)"], ["Q(alice) ∧ P(alice)"])
    assert r["exact_match"] == 0.0
    assert r["equivalence_accuracy"] == 1.0
    assert r["mean_partial_credit"] == 1.0        # equivalent True -> 1.0 outright
    assert r["parse_failure_rate"] == 0.0
    assert r["solver_unknown_rate"] == 0.0
    assert r["n"] == 1


def test_definitively_nonequivalent_pair():
    """P(alice) vs ¬P(alice): no structural level closes the gap, so the
    ladder falls to the solver, which REFUTES equivalence (a definitive
    False, with a Z3 counterexample) -- never an "unknown".

    Hand-derived partial_credit (equivalence.py's rubric, verdict=False):
      s1 = True  (both closed: 'alice' is a multi-letter NAME token, a
           Constant, not a free Variable; arity-consistent; no lambdas) -> 1
      s2 = True  (identical vocabulary P/1 on both sides)               -> 1
      s3 = False (P(alice) canonicalizes differently from ¬P(alice))    -> 0
      s4 = False (solver refutes: verdict is False, not True)           -> 0
    partial_credit = 0.25*(1+1+0+0) = 0.5
    """
    r = metric_hf.compute_fol_metrics(["P(alice)"], ["¬P(alice)"])
    assert r["exact_match"] == 0.0
    assert r["equivalence_accuracy"] == 0.0
    assert r["mean_partial_credit"] == 0.5
    assert r["parse_failure_rate"] == 0.0
    # Refuted (False) is NOT "unknown" -- the solver gave a definitive
    # answer, it just was not equivalence. This is the crux of the metric's
    # honesty contract: False and None must never share a bucket.
    assert r["solver_unknown_rate"] == 0.0
    assert r["n"] == 1


# ---------------------------------------------------------------------------
# Parse failures.
# ---------------------------------------------------------------------------

def test_parse_failure_pair_prediction_side():
    """"P(" never parses (unclosed paren, every dialect rejects it): the
    pair scores 0.0 across the board and is tallied as a parse failure.
    """
    r = metric_hf.compute_fol_metrics(["P("], ["P"])
    assert r == {
        "exact_match": 0.0,
        "equivalence_accuracy": 0.0,
        "mean_partial_credit": 0.0,
        "parse_failure_rate": 1.0,
        "solver_unknown_rate": 0.0,
        "n": 1,
    }


def test_parse_failure_pair_reference_side():
    """The failure can be on EITHER side -- a parseable prediction against
    an unparseable reference is scored identically to the reverse case."""
    r = metric_hf.compute_fol_metrics(["P"], ["P("])
    assert r["parse_failure_rate"] == 1.0
    assert r["equivalence_accuracy"] == 0.0
    assert r["mean_partial_credit"] == 0.0


# ---------------------------------------------------------------------------
# Mixed batches -- hand-computed aggregate arithmetic.
# ---------------------------------------------------------------------------

def test_mixed_batch_hand_computed_aggregate():
    """Four pairs: identical, commuted-canonical, definitively non-equivalent,
    parse-failure. Per-pair scores (verified against equivalent() directly):

      pair            syntax_equal  equivalent_true  partial_credit  parse_fail
      identical            1              1               1.0            0
      commuted              0              1               1.0            0
      P vs notP             0              0               0.5            0
      "P(" vs "P"           0              0               0.0            1

    exact_match          = (1+0+0+0)/4 = 0.25
    equivalence_accuracy = (1+1+0+0)/4 = 0.5
    mean_partial_credit  = (1.0+1.0+0.5+0.0)/4 = 2.5/4 = 0.625
    parse_failure_rate   = 1/4 = 0.25
    solver_unknown_rate  = 0/4 = 0.0   (the one solver call that ran refuted
                                        definitively, it did not go unknown)
    """
    preds = ["P(alice) ∧ Q(alice)", "P(alice) ∧ Q(alice)", "P(alice)", "P("]
    refs = ["P(alice) ∧ Q(alice)", "Q(alice) ∧ P(alice)", "¬P(alice)", "P"]
    r = metric_hf.compute_fol_metrics(preds, refs)
    assert r["exact_match"] == pytest.approx(0.25)
    assert r["equivalence_accuracy"] == pytest.approx(0.5)
    assert r["mean_partial_credit"] == pytest.approx(0.625)
    assert r["parse_failure_rate"] == pytest.approx(0.25)
    assert r["solver_unknown_rate"] == pytest.approx(0.0)
    assert r["n"] == 4


def test_length_mismatch_raises_value_error():
    with pytest.raises(ValueError, match="same length"):
        metric_hf.compute_fol_metrics(["P(alice)"], ["P(alice)", "Q(alice)"])


def test_empty_batch_returns_zeroed_aggregates_without_dividing_by_zero():
    r = metric_hf.compute_fol_metrics([], [])
    assert r == {
        "exact_match": 0.0,
        "equivalence_accuracy": 0.0,
        "mean_partial_credit": 0.0,
        "parse_failure_rate": 0.0,
        "solver_unknown_rate": 0.0,
        "n": 0,
    }


# ---------------------------------------------------------------------------
# solver_unknown_rate -- the honesty-contract field.
#
# A reliably constructible "solver reaches None" case: a quantified modal
# formula (an object quantifier binding into a modal operator) makes
# equivalence.py's _solver_tristate skip the labelled-tableau route
# entirely (has_modal + _has_object_quantifier) and fall straight to the
# qml_equivalent embedding, which is documented as SOUND BUT
# BOUNDED-INCOMPLETE: it can only ever return "proved" or "not proved" --
# never a refutation -- so its own False maps to the tri-state None (see
# equivalence.py's _solver_tristate docstring). Box vs Diamond under a
# universal object quantifier are not equivalent and the embedding search
# cannot prove they are, so the verdict is a clean, deterministic None.
# ---------------------------------------------------------------------------

def test_solver_unknown_rate_on_a_genuinely_undecided_pair():
    """∀x□P(x) vs ∀x◇P(x): the ladder reaches the solver (no structural
    level agrees) and the solver comes back undecided (None), never a
    refutation. Hand-derived partial_credit (verdict=None, same rubric as
    above): s1=True (both closed), s2=True (both use only P/1), s3=False
    (box != diamond canonically), s4=False (verdict is not True) ->
    0.25*(1+1+0+0) = 0.5.
    """
    r = metric_hf.compute_fol_metrics(["∀x (□P(x))"], ["∀x (◇P(x))"])
    assert r["equivalence_accuracy"] == 0.0     # None is not a "yes"
    assert r["solver_unknown_rate"] == 1.0      # ...but it is visibly "unknown"
    assert r["mean_partial_credit"] == 0.5
    assert r["exact_match"] == 0.0
    assert r["parse_failure_rate"] == 0.0
    assert r["n"] == 1


def test_solver_unknown_rate_is_zero_when_solver_refutes_definitively():
    """Contrast case for the test above: the solver CAN reach a definitive
    False (test_definitively_nonequivalent_pair's pair) -- that must NOT be
    counted as "unknown" just because the solver level ran. This is the
    exact distinction equivalence_accuracy / solver_unknown_rate exist to
    keep separate (see the module's honesty-contract docstring section).
    """
    r = metric_hf.compute_fol_metrics(["P(alice)"], ["¬P(alice)"])
    assert r["solver_unknown_rate"] == 0.0


def test_solver_unknown_rate_field_present_and_zero_on_a_purely_definitive_batch():
    """Every pair in this batch is decided at or before the solver level
    with a definitive answer (True/True/False), so the "undecided mass" is
    verifiably empty -- the field still exists (never omitted) and reports
    0.0, not None/missing."""
    preds = ["P(alice) ∧ Q(alice)", "P(alice) ∧ Q(alice)", "P(alice)"]
    refs = ["P(alice) ∧ Q(alice)", "Q(alice) ∧ P(alice)", "¬P(alice)"]
    r = metric_hf.compute_fol_metrics(preds, refs)
    assert "solver_unknown_rate" in r
    assert r["solver_unknown_rate"] == 0.0


def test_batch_combining_unknown_definitive_false_and_identical():
    """Three pairs: solver-undecided (modal quantified), solver-refuted
    (P vs notP), and identical. Per-pair scores:

      pair                     syntax_equal  equiv_true  partial_credit  unknown
      box vs diamond (quant.)       0             0            0.5          1
      P(alice) vs notP(alice)       0             0            0.5          0
      identical conjunction         1             1            1.0          0

    exact_match          = 1/3
    equivalence_accuracy = 1/3   (only the identical pair is a clean True)
    mean_partial_credit  = (0.5+0.5+1.0)/3 = 2.0/3
    parse_failure_rate   = 0/3 = 0.0
    solver_unknown_rate  = 1/3   (exactly the box-vs-diamond pair)
    """
    preds = ["∀x (□P(x))", "P(alice)", "P(alice) ∧ Q(alice)"]
    refs = ["∀x (◇P(x))", "¬P(alice)", "P(alice) ∧ Q(alice)"]
    r = metric_hf.compute_fol_metrics(preds, refs)
    assert r["exact_match"] == pytest.approx(1 / 3)
    assert r["equivalence_accuracy"] == pytest.approx(1 / 3)
    assert r["mean_partial_credit"] == pytest.approx(2.0 / 3)
    assert r["parse_failure_rate"] == 0.0
    assert r["solver_unknown_rate"] == pytest.approx(1 / 3)
    assert r["n"] == 3


# ---------------------------------------------------------------------------
# method / timeout_ms forwarding.
# ---------------------------------------------------------------------------

def test_default_method_is_auto():
    """Omitting `method` behaves exactly like method="auto" for the same
    pair (both go through the same ladder call)."""
    preds, refs = ["P(alice) ∧ Q(alice)"], ["Q(alice) ∧ P(alice)"]
    default = metric_hf.compute_fol_metrics(preds, refs)
    explicit = metric_hf.compute_fol_metrics(preds, refs, method="auto")
    assert default == explicit


def test_method_canonical_proves_equivalence_but_never_computes_partial_credit():
    """method="canonical" on the commuted pair: the canonical level DOES
    prove equivalence (equivalence_accuracy=1.0, same as "auto" here), but
    equivalence.py's canonical branch never populates partial_credit at all
    (only "auto"/"solver" do -- see EquivalenceResult's docstring), so this
    metric floors it to 0.0 rather than fabricating a 1.0 the ladder never
    computed. This is the module docstring's honesty-contract point about
    "not computed" vs "computed as the minimum" made concrete.
    """
    r = metric_hf.compute_fol_metrics(
        ["P(alice) ∧ Q(alice)"], ["Q(alice) ∧ P(alice)"], method="canonical")
    assert r["equivalence_accuracy"] == 1.0
    assert r["mean_partial_credit"] == 0.0
    # exact_match is computed independently of `method` (direct AST
    # equality), so it still correctly reports 0 here.
    assert r["exact_match"] == 0.0


def test_method_exact_does_not_credit_the_commuted_pair():
    """method="exact" only accepts AST equality -- the commuted pair (which
    "auto"/"canonical" both accept) is NOT credited under this method, and
    the solver is never invoked (method_used stays "exact"), so
    solver_unknown_rate is 0.0 too."""
    preds, refs = ["P(alice) ∧ Q(alice)"], ["Q(alice) ∧ P(alice)"]
    r = metric_hf.compute_fol_metrics(preds, refs, method="exact")
    assert r["equivalence_accuracy"] == 0.0
    assert r["exact_match"] == 0.0
    assert r["solver_unknown_rate"] == 0.0


def test_unknown_method_value_propagates_as_value_error():
    """An invalid `method` is a caller bug, not per-pair noise -- it must
    propagate (mirrors equivalent()'s own contract), not be swallowed like a
    parse failure is."""
    with pytest.raises(ValueError, match="unknown method"):
        metric_hf.compute_fol_metrics(["P(alice)"], ["P(alice)"], method="bogus")


def test_timeout_ms_is_forwarded_to_equivalent(monkeypatch):
    """compute_fol_metrics's timeout_ms reaches equivalent()'s `timeout`
    kwarg unchanged, for every non-parse-failure pair."""
    seen_timeouts = []
    real_equivalent = metric_hf.equivalent

    def spy(prediction, reference, *, method="auto", timeout=10000, **kw):
        seen_timeouts.append(timeout)
        return real_equivalent(prediction, reference, method=method,
                               timeout=timeout, **kw)

    monkeypatch.setattr(metric_hf, "equivalent", spy)
    metric_hf.compute_fol_metrics(["P(alice)"], ["Q(alice)"], timeout_ms=777)
    assert seen_timeouts == [777]


# ---------------------------------------------------------------------------
# FolEquivalence -- the evaluate.Metric wrapper. Skipped whole-group if the
# optional `evaluate` package is not installed in this environment.
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not metric_hf._HAS_EVALUATE, reason="evaluate not installed")
class TestFolEquivalenceWithEvaluateInstalled:

    def test_load_returns_a_fol_equivalence_instance(self):
        m = metric_hf.load()
        assert isinstance(m, metric_hf.FolEquivalence)

    def test_info_metadata_is_sane(self):
        info = metric_hf.load().info
        assert info.description
        assert info.citation == ""       # explicitly allowed to be empty
        assert set(info.features.keys()) == {"predictions", "references"}
        assert info.features["predictions"].dtype == "string"
        assert info.features["references"].dtype == "string"

    def test_compute_matches_plain_function_on_mixed_batch(self):
        """The whole point of the wrapper: it must not diverge from the
        function it delegates to."""
        preds = ["P(alice) ∧ Q(alice)", "P(alice) ∧ Q(alice)", "P(alice)", "P("]
        refs = ["P(alice) ∧ Q(alice)", "Q(alice) ∧ P(alice)", "¬P(alice)", "P"]
        via_metric = metric_hf.load().compute(predictions=preds, references=refs)
        via_function = metric_hf.compute_fol_metrics(preds, refs)
        assert via_metric == via_function

    def test_compute_forwards_method_and_timeout_kwargs(self):
        preds, refs = ["P(alice) ∧ Q(alice)"], ["Q(alice) ∧ P(alice)"]
        via_metric = metric_hf.load().compute(
            predictions=preds, references=refs, method="canonical", timeout_ms=500)
        via_function = metric_hf.compute_fol_metrics(
            preds, refs, method="canonical", timeout_ms=500)
        assert via_metric == via_function


# ---------------------------------------------------------------------------
# Import-time and instantiation-time behaviour WITHOUT `evaluate` installed.
#
# Rather than depending on the venv happening to lack the optional
# dependency, this forces the "absent" branch by making `import evaluate`
# fail (the standard `sys.modules[name] = None` trick makes Python raise
# ImportError for that name) and re-importing metric_hf fresh so its
# module-level `try: import evaluate / except ImportError` actually runs
# down the fallback path. monkeypatch restores both `sys.modules["evaluate"]`
# and `sys.modules["...metric_hf"]` to their original values on teardown, so
# this cannot leak the stubbed-out module into later tests.
# ---------------------------------------------------------------------------

def test_module_importable_and_raises_importerror_without_evaluate(monkeypatch):
    monkeypatch.setitem(sys.modules, "evaluate", None)
    monkeypatch.delitem(sys.modules, "unicode_fol_kit.eval.metric_hf", raising=False)

    fresh = importlib.import_module("unicode_fol_kit.eval.metric_hf")

    assert fresh._HAS_EVALUATE is False
    with pytest.raises(ImportError, match="pip install evaluate"):
        fresh.FolEquivalence()
    with pytest.raises(ImportError, match="pip install evaluate"):
        fresh.load()

    # The plain function needs no optional dependency at all, even in the
    # forced-absent module instance.
    r = fresh.compute_fol_metrics(["P(alice)"], ["P(alice)"])
    assert r["exact_match"] == 1.0
