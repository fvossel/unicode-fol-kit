"""A HuggingFace ``evaluate``-compatible NL→FOL metric.

The `evaluate <https://github.com/huggingface/evaluate>`_ library ships
metrics for classification, translation (BLEU/ROUGE/...), and generic
sequence tasks, but nothing that understands first-order logic: two
syntactically different formulas can denote the very same claim (``P ∧
Q`` / ``Q ∧ P``; ``Winner(x)`` / ``IsWinner(x)``), and a plain
string-equality metric scores that as wrong. This module plugs that gap by
wrapping :func:`unicode_fol_kit.eval.equivalence.equivalent` — the kit's
graded structural→solver equivalence ladder — as a metric.

Per-pair semantics
-------------------
Every ``(prediction, reference)`` row is scored **independently**: the two
strings are parsed on their own (via
:func:`unicode_fol_kit.api.parse_any`, which auto-detects the dialect —
the kit's unicode surface syntax, TPTP, Prover9, LaTeX, or SMT-LIB) and then
compared with :func:`~unicode_fol_kit.eval.equivalence.equivalent`. There is
no cross-row state (no shared vocabulary, no corpus-level normalisation) —
this mirrors how the kit's other evaluation entry points
(:func:`~unicode_fol_kit.eval.batch.batch_decide`) treat a batch as
independent tasks, and it means a caller can freely shuffle, subset, or
parallelise rows without changing any pair's score.

What "equivalent" means
-------------------------
See :mod:`unicode_fol_kit.eval.equivalence` for the full ladder — in
short, ``exact`` (AST ``==``) → ``canonical`` (α-renaming,
commutativity/associativity, double-negation) → ``predicate_align``
(vocabulary renaming on top of canonical) → ``solver`` (genuine logical
equivalence via Z3 or the modal decider, TRI-STATE: proved / refuted /
unknown). ``method="auto"`` (this module's default, matching
:func:`equivalent`'s own default) runs the ladder cheapest-first and stops
at the first level that proves equivalence, falling through to the solver
only when every structural level fails.

The honesty contract
----------------------
The solver's tri-state verdict is the reason this module reports several
numbers instead of one "accuracy":

* ``equivalence_accuracy`` counts ONLY a definitive ``equivalent is True``
  as correct. A refutation (``False``, with a counterexample) and an
  undecided solver call (``None``, the budget/completeness limit was hit
  without an answer either way) are both counted as *not correct* — but
  they are NOT THE SAME THING, and collapsing them together (the defect
  :func:`unicode_fol_kit.atp.formulas_are_equivalent` has, which
  :func:`equivalent` exists to avoid) would silently misreport how often
  the metric actually *knows* the prediction is wrong.
* ``solver_unknown_rate`` makes that hidden mass visible: the fraction of
  pairs where the ladder reached the solver level (i.e. no structural level
  decided the pair, so :class:`~unicode_fol_kit.eval.equivalence
  .EquivalenceResult`'s ``method_used`` is ``"solver"``) and the solver
  came back ``None``. It is deliberately reported alongside
  ``equivalence_accuracy`` rather than folded into it, so a consumer can
  compute honest bounds: the true accuracy lies in
  ``[equivalence_accuracy, equivalence_accuracy + solver_unknown_rate]``.
  (With ``method`` values other than ``"auto"``/``"solver"`` the solver
  never runs at all, so this rate is always ``0.0`` — that is not a claim
  every pair was decided, just that this particular signal has nothing to
  report; see :func:`compute_fol_metrics`'s docstring.)
* A parse failure on either side of a pair is scored ``0.0`` for that pair
  (it cannot be "equivalent" to anything, having never become a formula)
  and is tallied into ``parse_failure_rate`` — never silently dropped
  from the batch (which would inflate every other rate by shrinking the
  denominator) and never counted as a solver "unknown" (it never reached
  the solver, or any level of the ladder, at all).
"""

import importlib.util
from typing import List

from .equivalence import equivalent

__all__ = ["compute_fol_metrics", "FolEquivalence", "load"]


# ---------------------------------------------------------------------------
# compute_fol_metrics -- works with or without the `evaluate` package.
# ---------------------------------------------------------------------------

def _score_pair(prediction: str, reference: str, method: str, timeout_ms: int,
                converses=None) -> dict:
    """Score ONE ``(prediction, reference)`` pair. Never raises.

    Returns ``{"parse_failure", "syntax_equal", "equivalent_true",
    "partial_credit", "solver_unknown", "method_used"}`` (all bool except
    ``partial_credit``, a float, and ``method_used``, a str or ``None``). A
    parse failure on either side reports every bool/float field at its floor
    (``False`` / ``0.0``, ``method_used=None``) — see the module docstring's
    honesty-contract section for why that floor, not a skip, is the correct
    score for text that never became a formula.

    ``converses`` (see :mod:`unicode_fol_kit.eval.converses`) is forwarded
    to :func:`~unicode_fol_kit.eval.equivalence.equivalent` unchanged;
    ``method_used`` is carried back out so :func:`compute_fol_metrics` can
    compute ``converse_matched_rate`` without recomputing the verdict.

    ``syntax_equal`` is computed directly as ``prediction_formula ==
    reference_formula`` rather than read off
    ``EquivalenceResult.syntax_equal``: that field is only populated by the
    ``"exact"`` and ``"auto"`` methods (see ``equivalence.py``'s
    ``equivalent()`` — the ``"canonical"``/``"predicate_align"``/``"solver"``
    branches never set it), so reading it directly would silently under-count
    ``exact_match`` for every other ``method`` value. Computing it ourselves
    keeps ``exact_match`` well-defined for any ``method``.

    ``partial_credit`` reads ``EquivalenceResult.partial_credit`` when the
    ladder computed one (``method="auto"``/``"solver"`` only — see that
    field's docstring) and floors to ``0.0`` otherwise: the metric cannot
    report a score the ladder never computed, so "not computed" and "computed
    as the minimum" must not be conflated into a fabricated high average, and
    ``0.0`` is the conservative choice consistent with the parse-failure floor
    above.
    """
    from .. import api   # lazy: avoid import-time cost/cycles (mirrors eval/batch.py)

    pred_parsed = api.parse_any(prediction)
    ref_parsed = api.parse_any(reference)
    if not pred_parsed.ok or not ref_parsed.ok:
        return {
            "parse_failure": True,
            "syntax_equal": False,
            "equivalent_true": False,
            "partial_credit": 0.0,
            "solver_unknown": False,
            "method_used": None,
        }

    result = equivalent(pred_parsed.formula, ref_parsed.formula,
                        method=method, timeout=timeout_ms, converses=converses)

    # method_used in {"solver", "solver_modulo_converses"} happens exactly
    # when the ladder reached the solver level -- both for method="solver"
    # directly and for the "auto" ladder's fallthrough (see equivalent()'s
    # auto branch: it ALWAYS labels the solver fallthrough this way, whether
    # the tri-state verdict came back True, False, or None) -- the latter
    # tag only ever appears when `converses` was non-empty.
    solver_unknown = (result.method_used in ("solver", "solver_modulo_converses")
                      and result.equivalent is None)

    return {
        "parse_failure": False,
        "syntax_equal": pred_parsed.formula == ref_parsed.formula,
        "equivalent_true": result.equivalent is True,
        "partial_credit": result.partial_credit if result.partial_credit is not None else 0.0,
        "solver_unknown": solver_unknown,
        "method_used": result.method_used,
    }


def compute_fol_metrics(predictions: List[str], references: List[str], *,
                        method: str = "auto", timeout_ms: int = 10000,
                        converses=None) -> dict:
    """Score a batch of NL→FOL predictions against references, per-pair.

    Args:
        predictions: predicted formula strings, any dialect
            :func:`unicode_fol_kit.api.parse_any` can detect.
        references: reference (gold) formula strings, same dialect rules.
            Must be the same length as ``predictions``.
        method: forwarded to :func:`~unicode_fol_kit.eval.equivalence
            .equivalent` for every pair — one of ``"exact"``,
            ``"canonical"``, ``"predicate_align"``, ``"solver"``, ``"auto"``
            (the default: the full ladder, cheapest level first).
        timeout_ms: forwarded as ``equivalent()``'s ``timeout`` (milliseconds)
            for every pair's solver call.
        converses: OPT-IN, default ``None`` — forwarded unchanged to
            :func:`~unicode_fol_kit.eval.equivalence.equivalent` for every
            pair (see that function's ``converses`` parameter and
            :mod:`unicode_fol_kit.eval.converses`). ``None``/empty leaves the
            returned dict's KEY SET unchanged (required — see
            ``tests/test_metric_hf.py``'s full-dict-equality asserts); a
            non-empty sequence adds the ``converse_matched_rate`` key below.

    Returns:
        A dict with six keys (seven when ``converses`` is non-empty):

        * ``exact_match`` — fraction of pairs whose parsed formulas are
          AST-equal (``==``); ``0.0`` for an unparseable pair.
        * ``equivalence_accuracy`` — fraction of pairs where
          ``equivalent(...).equivalent is True``. See the module docstring's
          honesty-contract section: this is NOT ``1 - (fraction refuted)``,
          because undecided pairs are excluded from the numerator without
          being counted as refuted either.
        * ``mean_partial_credit`` — mean of
          ``equivalent(...).partial_credit`` over all pairs, treating an
          unparseable pair or a ``partial_credit`` the requested ``method``
          never computes (see that field's docstring) as ``0.0``.
        * ``parse_failure_rate`` — fraction of pairs where either side
          failed to parse.
        * ``solver_unknown_rate`` — fraction of pairs where the ladder
          reached the solver level and it returned ``None`` (undecided).
          Always ``0.0`` for ``method`` values that never invoke the solver
          (``"exact"``/``"canonical"``/``"predicate_align"``).
        * ``n`` — the batch size (``len(predictions)``).
        * ``converse_matched_rate`` — ONLY present when ``converses`` is
          non-empty: the fraction of pairs where the solver level ran WITH
          the declared axioms (``method_used == "solver_modulo_converses"``)
          AND proved equivalence (``equivalent is True``). A separately
          visible, subtractable slice of ``equivalence_accuracy`` — never
          folded into it silently, matching this module's honesty-contract
          convention for ``solver_unknown_rate`` above.

    Raises:
        ValueError: ``predictions`` and ``references`` have different
            lengths; a malformed ``converses`` declaration (checked
            unconditionally, including for an empty batch); or a non-empty
            ``converses`` combined with a ``method`` that cannot honour it
            (``"exact"``/``"canonical"``/``"predicate_align"`` — also
            checked unconditionally, matching :func:`~unicode_fol_kit.eval
            .equivalence.equivalent`'s own check for ``n >= 1``).
    """
    if len(predictions) != len(references):
        raise ValueError(
            "compute_fol_metrics: predictions and references must have the "
            f"same length (got {len(predictions)} and {len(references)})")

    if converses:
        # Validate unconditionally, even for an empty batch: _score_pair (the
        # only other call site that would reach validate_converses, via
        # equivalent()) never runs when n == 0, so without this a malformed
        # declaration would silently pass through the n == 0 branch below
        # instead of raising -- see this function's own documented contract
        # ("Raises: ValueError ... a malformed converses declaration").
        from .converses import validate_converses
        validate_converses(converses)
        # Mirror equivalent()'s own method-gating check (equivalence.py:
        # "converses requires method in {'solver', 'auto'}") unconditionally
        # too, for the same reason: that check normally runs inside
        # equivalent() via _score_pair, which never executes when n == 0, so
        # without this a solver-incompatible method combined with a
        # (structurally valid) converses declaration would raise for n >= 1
        # but silently return zeroed metrics for n == 0 -- same declaration,
        # same method, different n, different behaviour. Kept as an exact
        # duplicate of equivalent()'s wording (not just "the same class of
        # error") so a caller sees one consistent message regardless of
        # which code path raised it.
        if method in ("exact", "canonical", "predicate_align"):
            raise ValueError(
                f"equivalent: converses requires method in "
                f"{{'solver', 'auto'}} (got {method!r}) — a declared "
                "converse axiom is honoured only by the solver level; a "
                "structural method would silently ignore it")

    n = len(predictions)
    if n == 0:
        result = {
            "exact_match": 0.0,
            "equivalence_accuracy": 0.0,
            "mean_partial_credit": 0.0,
            "parse_failure_rate": 0.0,
            "solver_unknown_rate": 0.0,
            "n": 0,
        }
        if converses:
            result["converse_matched_rate"] = 0.0
        return result

    scores = [_score_pair(p, r, method, timeout_ms, converses)
             for p, r in zip(predictions, references)]

    result = {
        "exact_match": sum(s["syntax_equal"] for s in scores) / n,
        "equivalence_accuracy": sum(s["equivalent_true"] for s in scores) / n,
        "mean_partial_credit": sum(s["partial_credit"] for s in scores) / n,
        "parse_failure_rate": sum(s["parse_failure"] for s in scores) / n,
        "solver_unknown_rate": sum(s["solver_unknown"] for s in scores) / n,
        "n": n,
    }
    if converses:
        result["converse_matched_rate"] = sum(
            s["method_used"] == "solver_modulo_converses" and s["equivalent_true"]
            for s in scores) / n
    return result


# ---------------------------------------------------------------------------
# FolEquivalence -- the evaluate.Metric wrapper (optional dependency).
# ---------------------------------------------------------------------------
#
# `evaluate` is NOT a hard dependency of this module: importing metric_hf.py
# must succeed on a machine that never installed it (mirroring how
# atp/cvc5_backend.py's Cvc5Backend stays importable without cvc5 -- see that
# module's docstring). Only *instantiating* FolEquivalence requires it -- and,
# unlike the eager `try: import evaluate / except ImportError` this used to
# do, that import must not happen just because metric_hf.py itself was
# imported (`evaluate` drags in `datasets`, together well over a second of
# import time -- see the module docstring's own claim, which this section
# makes actually true). `_HAS_EVALUATE` below is pure discovery -- no import
# -- mirroring atp/cvc5_backend.py's `Cvc5Backend.available()`.

_HAS_EVALUATE = (importlib.util.find_spec("evaluate") is not None and
                 importlib.util.find_spec("datasets") is not None)


_INSTALL_HINT = (
    "FolEquivalence requires the optional 'evaluate' package "
    "(pip install evaluate) -- it is not installed in this environment. "
    "unicode_fol_kit.eval.metric_hf.compute_fol_metrics(predictions, "
    "references) gives the same scores without that dependency."
)

_DESCRIPTION = (
    "Graded NL→FOL equivalence: scores each (prediction, reference) pair "
    "with unicode_fol_kit's structural→solver equivalence ladder "
    "(unicode_fol_kit.eval.equivalence.equivalent). Reports exact_match, "
    "equivalence_accuracy (solver-tri-state-aware -- undecided pairs are "
    "counted as neither correct nor refuted), mean_partial_credit, "
    "parse_failure_rate, and solver_unknown_rate (the undecided mass, kept "
    "separate from equivalence_accuracy on purpose -- see "
    "unicode_fol_kit.eval.metric_hf's module docstring)."
)

_KWARGS_DESCRIPTION = """
Args:
    predictions (list of str): predicted FOL formula strings.
    references (list of str): reference (gold) FOL formula strings, same
        length as `predictions`.
    method (str, optional): equivalence-ladder level, one of "exact",
        "canonical", "predicate_align", "solver", "auto" (default).
    timeout_ms (int, optional): per-pair solver budget in milliseconds
        (default 10000).

Returns:
    exact_match (float): fraction of pairs with AST-equal parsed formulas.
    equivalence_accuracy (float): fraction of pairs the ladder proved
        equivalent (a definitive True only -- see the module docstring).
    mean_partial_credit (float): mean heuristic partial-credit score.
    parse_failure_rate (float): fraction of pairs where either side failed
        to parse.
    solver_unknown_rate (float): fraction of pairs where the solver was
        reached and returned an undecided verdict.
    n (int): batch size.

Examples:
    >>> import unicode_fol_kit.eval.metric_hf as metric_hf
    >>> m = metric_hf.load()
    >>> m.compute(predictions=["P(a) ∧ Q(a)"], references=["Q(a) ∧ P(a)"])
    {'exact_match': 0.0, 'equivalence_accuracy': 1.0, ...}
"""

# `FolEquivalence` itself is built lazily: the class body subclasses
# `evaluate.Metric`, so merely *defining* it needs `evaluate` (and, for
# `_info`'s `datasets.Features`, `datasets`) already imported. Building it
# eagerly at module scope -- even behind an `if _HAS_EVALUATE:` -- would
# import both packages the moment metric_hf.py is imported, which is
# exactly the cost this module's docstring already claims does NOT happen.
# `_build_fol_equivalence_class` does the real import (and only it pays that
# cost, once, on first use) and caches the resulting class in
# `_fol_equivalence_class`; the module-level `__getattr__` below (PEP 562)
# routes both `metric_hf.FolEquivalence` and
# `from ... import FolEquivalence` through it transparently.

_fol_equivalence_class = None


def _build_fol_equivalence_class():
    """Import ``evaluate``/``datasets`` and return the real ``FolEquivalence``
    class, building it once and caching it for every later call.

    Raises:
        ImportError: with the install hint, if ``evaluate``/``datasets`` are
            not installed (or fail to import for any other reason) --
            mirroring the message the pre-lazy fallback stub used to raise
            from ``FolEquivalence.__init__``.
    """
    global _fol_equivalence_class
    if _fol_equivalence_class is not None:
        return _fol_equivalence_class

    try:
        import evaluate as _evaluate
        import datasets as _hf_datasets
    except ImportError:
        raise ImportError(_INSTALL_HINT) from None

    class FolEquivalence(_evaluate.Metric):
        """``evaluate.Metric`` wrapper around :func:`compute_fol_metrics`.

        A thin adapter: ``_compute`` delegates entirely to
        :func:`compute_fol_metrics`, so this class adds nothing but the
        ``evaluate``/``datasets`` plumbing (feature schema, description,
        the ``evaluate.load``-shaped ``load()`` entry point below) around
        logic that already works standalone. See the module docstring for
        what the returned numbers mean.
        """

        def _info(self):
            # Returns evaluate.MetricInfo. Deliberately NOT annotated with a
            # `-> "_evaluate.MetricInfo"` string forward reference: `_evaluate`
            # is a local variable of the enclosing `_build_fol_equivalence_class`
            # (that is what keeps the import lazy -- see the section comment
            # above), not a module global, so `typing.get_type_hints()` would
            # raise NameError trying to resolve it. Nothing in this codebase
            # or its test suite calls `get_type_hints` on this method; the
            # type is documented here in prose instead.
            return _evaluate.MetricInfo(
                description=_DESCRIPTION,
                citation="",
                inputs_description=_KWARGS_DESCRIPTION,
                features=_hf_datasets.Features({
                    "predictions": _hf_datasets.Value("string", id="sequence"),
                    "references": _hf_datasets.Value("string", id="sequence"),
                }),
                reference_urls=[
                    "https://unicode-fol-kit.readthedocs.io/",
                ],
            )

        def _compute(self, predictions, references, method: str = "auto",
                    timeout_ms: int = 10000) -> dict:
            return compute_fol_metrics(list(predictions), list(references),
                                       method=method, timeout_ms=timeout_ms)

    # Built inside a function, so Python's default __qualname__ would be
    # "_build_fol_equivalence_class.<locals>.FolEquivalence" -- reset it to
    # the plain module-level name so anything that reads it (repr, pickling
    # by reference, which resolves "module.qualname" via getattr and so
    # works fine through __getattr__ below) sees the same identifier a
    # module-scoped class definition would have had.
    FolEquivalence.__qualname__ = "FolEquivalence"

    _fol_equivalence_class = FolEquivalence
    return _fol_equivalence_class


def __getattr__(name: str):
    """PEP 562 module-level attribute hook.

    Only ``FolEquivalence`` is handled specially: accessing
    ``metric_hf.FolEquivalence`` (attribute access, ``from ... import
    FolEquivalence``, or ``dir()``-following tools) builds -- and, on every
    call after the first, just returns the cached -- real class via
    :func:`_build_fol_equivalence_class`, so `evaluate`/`datasets` are only
    ever imported when this name is actually touched, never merely because
    this module was.
    """
    if name == "FolEquivalence":
        return _build_fol_equivalence_class()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def load():
    """Return a ready-to-use :class:`FolEquivalence` instance.

    Mirrors the shape of ``evaluate.load("metric_name")`` for callers used
    to that entry point. Raises :class:`ImportError` (with the install
    hint) if the optional ``evaluate`` package is not installed -- use
    :func:`compute_fol_metrics` directly in that case.

    Not annotated ``-> "FolEquivalence"``: that name is only ever reachable
    through the module-level ``__getattr__`` above (never bound as a true
    module global -- that is what keeps it lazy), so a string forward
    reference to it would raise NameError from ``typing.get_type_hints()``.
    The return type is documented here in prose instead.
    """
    return _build_fol_equivalence_class()()
