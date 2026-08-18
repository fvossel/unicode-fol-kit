"""Graded equivalence checking for NL→FOL evaluation.

``equivalent(prediction, reference)`` is the one entry point that answers "does
the predicted formula mean the same as the reference?" at every level the kit
can decide, from cheap structural checks to a solver call:

  * ``exact``            — structural equality of the frozen ASTs (``==``);
  * ``canonical``        — :func:`~unicode_fol_kit.eval.canonical.exact_match`
                           (α-renaming, commutativity/associativity, operand
                           de-duplication, double negation quotiented out);
  * ``predicate_align``  — :func:`~unicode_fol_kit.eval.predicate_match.aligned_exact_match`
                           (vocabulary differences quotiented out too:
                           namespace- and arity-aware injective renaming,
                           then canonical match);
  * ``solver``           — genuine logical equivalence. Classical formulas go
                           to Z3 with a TRI-STATE result (``True`` proved /
                           ``False`` refuted with a counterexample /
                           ``None`` unknown — the existing
                           ``formulas_are_equivalent`` collapses unknown to
                           False, which a metric must not do). Modal formulas
                           go to ``modal_decide`` (tri-state, with a Kripke
                           counterexample on refutation) and fall back to the
                           sound-but-bounded-incomplete ``qml_equivalent``
                           (``True`` / ``None``) for fragments the tableau
                           rejects;
  * ``auto``             — the ladder above, cheapest first, stopping at the
                           first level that answers ``True``.

Every result is an :class:`EquivalenceResult` whose ``to_dict()`` is
JSON-compatible, so pipelines and LLM repair loops can consume it without
extra parsing.

``partial_credit`` (``method="auto"`` / ``"solver"`` only) is a heuristic
RANKING signal for use when the headline verdict is not a clean ``True`` —
NOT a probability, just a coarse {0, 0.25, 0.5, 0.75, 1.0} ordinal built from
four binary sub-checks (well-formedness, vocabulary alignability, aligned
structural match, logical equivalence). See :class:`EquivalenceResult` for
the exact rubric.
"""

from dataclasses import dataclass
from typing import Optional

from unicode_fol_kit.fol.nodes import (
    Node, Iff, Quantifier, SortedQuantifier,
)

__all__ = ["EquivalenceResult", "equivalent"]

_METHODS = ("exact", "canonical", "predicate_align", "solver", "auto")


@dataclass(frozen=True)
class EquivalenceResult:
    """Outcome of :func:`equivalent` — one Optional[bool] per level.

    ``None`` always means "not computed" for the structural levels, and
    "could not decide within budget" for ``logically_equivalent``.

    Fields:

    ``equivalent``
        the headline verdict — ``True`` iff the requested method (or, for
        ``auto``, any level of the ladder) established equivalence; ``False``
        iff the strongest level that ran refuted it; ``None`` if undecided.
        Truthiness follows this field.
    ``method_used``
        the level that produced the headline verdict.
    ``syntax_equal`` / ``structurally_equal`` / ``aligned_equal``
        the three rungs of the structural ladder: ``==``, canonical form,
        and alignment followed by canonical form.
    ``logically_equivalent``
        the solver's tri-state verdict.
    ``counterexample``
        THE COUNTERMODEL, as an accessible, documented, JSON-able field —
        set exactly when the solver stage REFUTED equivalence (i.e. whenever
        ``equivalent is False``; for ``method="solver"``/``"auto"`` that is
        the same moment ``logically_equivalent is False``), ``None`` in
        every other case (proved, undecided, or a structural level never
        reached the solver). A caller checks it with
        ``if result.counterexample is not None: ...`` — no separate lookup
        or solver re-invocation needed; the witness that falsified
        equivalence is already attached to the result that reports the
        refutation. Two shapes, keyed by ``"kind"``:
        ``{"kind": "z3_model", "assignment": {var_name: value_repr, …}}``
        for classical formulas (every declared Z3 symbol's value under the
        model that satisfies ``¬(φ ↔ ψ)``), and
        ``{"kind": "kripke", "repr": …}`` for modal ones (the ``repr()`` of
        the Kripke countermodel :func:`~unicode_fol_kit.atp.modal_tableau.modal_countermodel`
        found). Both are plain JSON-compatible dicts of strings, so the
        whole ``EquivalenceResult`` — countermodel included — survives a
        ``pickle`` round-trip and a process boundary undisturbed (it is a
        frozen dataclass over ``Optional[bool]``/``str``/``dict`` fields
        only), which matters for a caller that evaluates candidates in a
        worker pool and inspects failures back in the parent process.
    ``partial_credit``
        a heuristic RANKING signal in ``{0.0, 0.25, 0.5, 0.75, 1.0}`` —
        explicitly NOT a probability of correctness, just a coarse ordinal
        score for sorting or averaging predictions when the headline verdict
        is not a clean ``True``. The rubric: ``equivalent is True`` at ANY
        level of the ladder scores ``1.0`` (the headline already gives the
        strongest possible signal, so the sub-component breakdown is not
        computed and ``partial_credit_components`` stays ``None``); otherwise
        the score is the sum of four independent 0.25-weighted binary checks,
        see ``partial_credit_components``.

        Only computed for ``method="auto"`` and ``method="solver"``: the
        rubric's ``s4`` component needs the solver's tri-state verdict, which
        the purely structural methods (``exact`` / ``canonical`` /
        ``predicate_align``) never obtain — for those, ``partial_credit``
        stays ``None`` (an honest "not computed", never a score of 0).
    ``partial_credit_components``
        the four binary sub-checks behind a summed (non-``1.0``,
        non-``None``) ``partial_credit``, as a JSON-able
        ``{"s1": bool, "s2": bool, "s3": bool, "s4": bool}``. ``None``
        whenever ``partial_credit`` itself is ``None`` or ``1.0`` (see
        above). The four keys:

        * ``s1`` "wellformed" — BOTH prediction and reference are
          ``eval.validate.is_wellformed`` (closed, arity-consistent,
          lambda-free).
        * ``s2`` "vocabulary_alignable" — after
          ``align_symbols(prediction, reference)`` the aligned prediction's
          symbol inventories (predicate name/arity, function name/arity,
          constant names) equal the reference's.
        * ``s3`` "aligned_equal" — ``aligned_exact_match`` holds of the pair.
          This practically implies ``s2`` (a successful vocabulary alignment
          is a prerequisite for the canonical match that follows it) but is
          tracked as an independent bit because it is the STRICTLY stronger
          condition — matching vocabularies is necessary but not sufficient
          for the aligned canonical forms to agree.
        * ``s4`` "logically_equivalent" — the solver's tri-state verdict is
          True; both ``None`` (undecided) and ``False`` (refuted) count as 0,
          per the tri-state discipline the rest of this module enforces (see
          the module docstring). Note: for the two methods that ever reach
          the summed branch, the headline verdict IS the solver verdict, so
          by the time ``s1``–``s4`` are computed that verdict has already
          failed to be ``True`` — meaning ``s4`` is always ``False`` in every
          case this field is actually populated today. It is still evaluated
          against the real verdict (never hard-coded) so it stays correct
          should a future call site ever decouple the two.
    """

    equivalent: Optional[bool]
    method_used: str
    syntax_equal: Optional[bool] = None
    structurally_equal: Optional[bool] = None
    aligned_equal: Optional[bool] = None
    logically_equivalent: Optional[bool] = None
    counterexample: Optional[dict] = None
    partial_credit: Optional[float] = None
    partial_credit_components: Optional[dict] = None

    def __bool__(self) -> bool:
        return self.equivalent is True

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (all fields, field names as keys)."""
        return {
            "equivalent": self.equivalent,
            "method_used": self.method_used,
            "syntax_equal": self.syntax_equal,
            "structurally_equal": self.structurally_equal,
            "aligned_equal": self.aligned_equal,
            "logically_equivalent": self.logically_equivalent,
            "counterexample": self.counterexample,
            "partial_credit": self.partial_credit,
            "partial_credit_components": self.partial_credit_components,
        }


def _has_object_quantifier(node: Node) -> bool:
    """True iff ``node`` binds a first-order object variable anywhere."""
    return any(isinstance(n, (Quantifier, SortedQuantifier)) for n in node.walk())


def _solver_tristate(f1: Node, f2: Node, timeout: int, frame: str, systems):
    """Return ``(verdict, counterexample)`` for genuine logical equivalence.

    Classical route: Z3 on ``¬(φ ↔ ψ)`` — ``unsat`` proves equivalence, ``sat``
    refutes it (the model is the counterexample), ``unknown`` stays ``None``.
    Modal route: ``modal_decide(Iff(φ, ψ))`` for the propositional fragment
    (tri-state; a Kripke counter-model witnesses refutation); quantified or
    tableau-rejected modal formulas fall back to ``qml_equivalent`` — sound but
    bounded-incomplete, so its ``False`` is reported as ``None`` (not proven),
    never as a refutation.
    """
    from unicode_fol_kit.atp.modal_tableau import has_modal

    iff = Iff(f1, f2)

    if has_modal(iff):
        from unicode_fol_kit.fol.qml import qml_equivalent

        if not _has_object_quantifier(iff):
            from unicode_fol_kit.atp.modal_tableau import (
                modal_decide, modal_countermodel,
            )
            try:
                status = modal_decide(iff, frame=frame, systems=systems)
            except NotImplementedError:
                status = None                     # fragment the tableau rejects
            if status == "valid":
                return True, None
            if status == "invalid":
                cm = modal_countermodel(iff, frame=frame, systems=systems)
                witness = {"kind": "kripke", "repr": repr(cm)} if cm is not None else None
                return False, witness
            # "unknown" or rejected: fall through to the QML embedding.
        try:
            proved = qml_equivalent(f1, f2, frame=frame, systems=systems,
                                    timeout=timeout)
        except NotImplementedError:
            return None, None
        return (True, None) if proved else (None, None)

    # Classical route: tri-state Z3 (deliberately NOT formulas_are_equivalent,
    # which collapses unknown to False — unusable as a metric verdict).
    from z3 import Solver, Not as _ZNot, sat, unsat

    try:
        phi, psi = f1.to_z3(), f2.to_z3()
    except NotImplementedError:
        return None, None                         # no Z3 image for this family
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(_ZNot(phi == psi))
    res = solver.check()
    if res == unsat:
        return True, None
    if res == sat:
        model = solver.model()
        assignment = {str(d.name()): str(model[d]) for d in model.decls()}
        return False, {"kind": "z3_model", "assignment": assignment}
    return None, None


def _partial_credit(prediction: Node, reference: Node, verdict: Optional[bool],
                    max_norm_distance: float):
    """Return ``(partial_credit, partial_credit_components)`` for the rubric.

    ``verdict`` is the headline equivalence verdict for the call site — which,
    for both places this is invoked (``method="solver"`` and the auto ladder's
    solver fallthrough), IS the solver's tri-state verdict, i.e. the same
    value that ends up in ``EquivalenceResult.equivalent`` /
    ``.logically_equivalent``. See the ``EquivalenceResult`` docstring for the
    full rubric this implements; this function is deliberately dumb (no
    control flow beyond the ``verdict is True`` short-circuit) so the rubric
    stays easy to audit against that docstring.
    """
    if verdict is True:
        return 1.0, None

    from .validate import is_wellformed
    from .predicate_match import align_symbols, aligned_exact_match, _symbol_inventory

    s1 = is_wellformed(prediction) and is_wellformed(reference)

    aligned = align_symbols(prediction, reference, max_norm_distance)
    ap, af, ac = _symbol_inventory(aligned)
    rp, rf, rc = _symbol_inventory(reference)
    s2 = ap == rp and af == rf and ac == rc

    s3 = aligned_exact_match(prediction, reference, max_norm_distance)

    s4 = verdict is True                       # never True here; see docstring

    components = {"s1": s1, "s2": s2, "s3": s3, "s4": s4}
    score = 0.25 * sum(components.values())
    return score, components


def equivalent(prediction: Node, reference: Node, *, method: str = "auto",
               timeout: int = 10000, max_norm_distance: float = 0.6,
               frame: str = "K", systems=None) -> EquivalenceResult:
    """Decide whether ``prediction`` and ``reference`` are equivalent.

    Args:
        prediction / reference: parsed formulas (any family the requested
            level supports; the solver level covers classical FOL/MSFOL and
            the modal family).
        method: one of ``"exact"``, ``"canonical"``, ``"predicate_align"``,
            ``"solver"``, ``"auto"``. ``auto`` runs the ladder cheapest-first
            and stops at the first ``True``; the solver only runs when the
            structural levels all fail.
        timeout: solver budget in milliseconds.
        max_norm_distance: threshold for the ``predicate_align`` level (see
            :func:`~unicode_fol_kit.eval.predicate_match.align_symbols`).
        frame / systems: modal frame class and per-family systems, forwarded
            to the modal deciders; ignored for classical formulas.

    Returns:
        An :class:`EquivalenceResult`. Note the asymmetry of the levels: the
        structural levels can only *establish* equivalence (their ``False``
        just means "this quotient did not close the gap"), so only the solver
        level can make the headline verdict ``False`` — and only with a
        counterexample in hand.
    """
    if method not in _METHODS:
        raise ValueError(f"equivalent: unknown method {method!r} (use one of {_METHODS})")

    from .canonical import exact_match
    from .predicate_match import aligned_exact_match

    if method == "exact":
        eq = prediction == reference
        return EquivalenceResult(
            equivalent=True if eq else None, method_used="exact", syntax_equal=eq)

    if method == "canonical":
        eq = exact_match(prediction, reference)
        return EquivalenceResult(
            equivalent=True if eq else None, method_used="canonical",
            structurally_equal=eq)

    if method == "predicate_align":
        eq = aligned_exact_match(prediction, reference, max_norm_distance)
        return EquivalenceResult(
            equivalent=True if eq else None, method_used="predicate_align",
            aligned_equal=eq)

    if method == "solver":
        verdict, cex = _solver_tristate(prediction, reference, timeout, frame, systems)
        pc, components = _partial_credit(prediction, reference, verdict, max_norm_distance)
        return EquivalenceResult(
            equivalent=verdict, method_used="solver",
            logically_equivalent=verdict, counterexample=cex,
            partial_credit=pc, partial_credit_components=components)

    # auto: cheapest first, stop at the first True; solver decides the rest.
    # Every branch below computes partial_credit (method="auto" is one of the
    # two rubric-eligible methods) — the early-True branches all score 1.0
    # per the rubric's headline short-circuit.
    syntax_equal = prediction == reference
    if syntax_equal:
        return EquivalenceResult(
            equivalent=True, method_used="exact", syntax_equal=True,
            partial_credit=1.0)

    structurally_equal = exact_match(prediction, reference)
    if structurally_equal:
        return EquivalenceResult(
            equivalent=True, method_used="canonical",
            syntax_equal=False, structurally_equal=True,
            partial_credit=1.0)

    aligned_equal = aligned_exact_match(prediction, reference, max_norm_distance)
    if aligned_equal:
        return EquivalenceResult(
            equivalent=True, method_used="predicate_align",
            syntax_equal=False, structurally_equal=False, aligned_equal=True,
            partial_credit=1.0)

    verdict, cex = _solver_tristate(prediction, reference, timeout, frame, systems)
    pc, components = _partial_credit(prediction, reference, verdict, max_norm_distance)
    return EquivalenceResult(
        equivalent=verdict, method_used="solver",
        syntax_equal=False, structurally_equal=False, aligned_equal=False,
        logically_equivalent=verdict, counterexample=cex,
        partial_credit=pc, partial_credit_components=components)
