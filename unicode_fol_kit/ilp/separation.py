"""Does this formula actually separate the two example sets?

The question to ask **before** running a learner, and again after. Before,
about the reference definition: if the axiom you believe in does not already
tell the positives from the negatives under the kit's own model checker, the
task is broken, and whatever the learner returns — perfect scores included —
would have meant nothing. After, about the learned clause: a hypothesis is
consistent with its examples *inside the learner*, over the ground facts the
learner was given; whether it still is over the structures those facts came
from is a different claim, and this is what checks it.

It is also the natural place to notice that a learner returns the SMALLEST
hypothesis consistent with the examples, so every property the negatives did
not force it to name is a hole. Run this over held-out structures and the
holes show up as false positives.

**Three ways not to be separated, kept apart.** A formula can fail to decide
an example because it is false there (a genuine misclassification), because
the step budget ran out (undecided — never counted as false, the same rule
:func:`~unicode_fol_kit.eval.check_definitions` follows), or because it names
a predicate the structure does not interpret (a vocabulary error, usually a
naming mismatch rather than anything logical). All three block separation, and
each is reported as itself.
"""

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

from ..fol.nodes import Node
from ..semantics.model_eval import (
    UninterpretedSymbol, UnsupportedNode, evaluate_detailed,
)
from .task import IlpTask

__all__ = ["SeparationReport", "check_separation"]


@dataclass(frozen=True)
class SeparationReport:
    """What :func:`check_separation` found, per example and in total."""

    #: One dict per example, in task order, with keys ``id``, ``label``,
    #: ``status`` (``"ok"`` / ``"exhausted"`` / ``"eval_error"``), ``holds``
    #: (``None`` unless ``status == "ok"``), ``steps`` and ``error``.
    rows: Tuple[Dict[str, Any], ...]

    @property
    def counts(self) -> Dict[str, int]:
        """True/false positives and negatives over the DECIDED rows, plus the
        two undecided kinds."""
        decided = [r for r in self.rows if r["status"] == "ok"]
        return {
            "true_positive": sum(1 for r in decided if r["label"] and r["holds"]),
            "false_positive": sum(1 for r in decided
                                  if not r["label"] and r["holds"]),
            "true_negative": sum(1 for r in decided
                                 if not r["label"] and not r["holds"]),
            "false_negative": sum(1 for r in decided
                                  if r["label"] and not r["holds"]),
            "exhausted": sum(1 for r in self.rows if r["status"] == "exhausted"),
            "eval_error": sum(1 for r in self.rows if r["status"] == "eval_error"),
        }

    @property
    def misclassified(self) -> Tuple[Dict[str, Any], ...]:
        """The rows the formula decided the wrong way. Undecided rows are NOT
        in here — they are in :attr:`counts` under their own names, because
        "could not tell" and "told me the opposite" call for different fixes."""
        return tuple(r for r in self.rows
                     if r["status"] == "ok" and r["holds"] != r["label"])

    @property
    def separates(self) -> bool:
        """Every example decided, and decided as labelled.

        ``False`` for an empty report: ``all()`` over nothing is ``True``, and
        answering "this formula separates the sets" about a report that
        decided nothing is the kind of vacuous yes this kit does not hand out.
        :func:`check_separation` cannot produce one (a task needs at least one
        example of each label), but a caller filtering rows can.

        >>> SeparationReport(()).separates
        False
        """
        return bool(self.rows) and all(
            r["status"] == "ok" and r["holds"] == r["label"] for r in self.rows)

    @property
    def precision(self) -> Optional[float]:
        """Over the decided rows; ``None`` when the formula held nowhere —
        never a fabricated ``0.0`` for an undefined ratio."""
        counts = self.counts
        predicted = counts["true_positive"] + counts["false_positive"]
        return counts["true_positive"] / predicted if predicted else None

    @property
    def recall(self) -> Optional[float]:
        """Over the decided rows; ``None`` when there were no decided
        positives."""
        counts = self.counts
        actual = counts["true_positive"] + counts["false_negative"]
        return counts["true_positive"] / actual if actual else None


def check_separation(formula: Node, task: IlpTask, *,
                     all_different: bool = False,
                     budget: Optional[int] = None) -> SeparationReport:
    """Evaluate ``formula`` in every example structure of ``task``.

    Args:
        formula: a parsed formula — ``MSFLParser().parse(text)`` for kit
            syntax, :func:`~unicode_fol_kit.parse_tptp_formula` for TPTP, or
            :func:`~unicode_fol_kit.ilp.clause_to_formula` for a learned
            clause. Deliberately not a string: which dialect a string is in is
            exactly the kind of guess this kit does not make.
        task: supplies the structures and their labels.
        all_different: require distinct variables to denote distinct
            individuals — see
            :mod:`unicode_fol_kit.semantics.model_eval`. A learner's clause
            usually WANTS this: ``bDOUBLE(C,O) ∧ bSINGLE(C,N)`` with ``O`` and
            ``N`` allowed to coincide is a weaker pattern than the one the
            clause looks like.
        budget: evaluation step budget per example. ``None`` is unbounded.

    Returns:
        A :class:`SeparationReport`.
    """
    if isinstance(formula, str):
        raise TypeError(
            "check_separation: formula must be a parsed Node, not text — "
            "parse it first (MSFLParser().parse(...) for kit syntax, "
            "parse_tptp_formula(...) for TPTP), so the dialect is your "
            "decision and not a guess")
    rows = []
    for example in task.examples:
        row: Dict[str, Any] = {"id": example.id, "label": example.label,
                               "status": "ok", "holds": None, "steps": None,
                               "error": None}
        try:
            result = evaluate_detailed(formula, example.structure,
                                       all_different=all_different,
                                       budget=budget)
        except (UninterpretedSymbol, UnsupportedNode) as exc:
            row["status"] = "eval_error"
            row["error"] = f"{type(exc).__name__}: {exc}"
        else:
            row["steps"] = result.steps
            if result.exhausted:
                row["status"] = "exhausted"
            else:
                row["holds"] = result.holds
        rows.append(row)
    return SeparationReport(tuple(rows))
