"""Exact probabilistic logic — no sampling, no floats, every result an exact Fraction.

Two independent, complementary readings of "probabilistic first-order-ish
logic", both decided EXACTLY (rational arithmetic throughout — a probability
enters as a :class:`~fractions.Fraction` and every bound/query result leaves
as one; nothing in this package ever samples, approximates, or routes a
probability through ``float``):

- :mod:`unicode_fol_kit.prob.nilsson` — **Nilsson's probabilistic entailment**
  (Nilsson, *Probabilistic Logic*, Artificial Intelligence 28, 1986). Given
  probability INTERVAL constraints on a set of propositional formulas
  (unconditional ``lower ≤ P(φ) ≤ upper``, or conditional
  ``lower ≤ P(ψ|φ) ≤ upper``), :func:`~unicode_fol_kit.prob.nilsson.entailment_bounds`
  computes the tightest interval those constraints entail for a conclusion —
  an exact linear program over one probability variable per possible world,
  solved with :mod:`z3`'s ``Optimize``. Classical entailment is the corner
  case where every constraint pins probability 1 and the bounds collapse to
  exactly ``(1, 1)``.

- :mod:`unicode_fol_kit.prob.distribution` — **Sato's distribution semantics**
  (Sato, *A Statistical Learning Method for Logic Programs*, ICLP 1995), the
  semantic core of ProbLog (De Raedt, Kimmig & Toivonen, IJCAI 2007). Given a
  set of independent Bernoulli-distributed ground facts and a DEFINITE logic
  program (rules with a single positive-atom head and a positive-atom-only
  body) over a finite Herbrand universe, :func:`~unicode_fol_kit.prob.distribution.query`
  sums the weight of every "total choice" of facts whose resulting (unique)
  least Herbrand model satisfies a query — exactly, over ``2^k`` choices for
  ``k`` relevant facts (with correctness-preserving dependency-cone pruning
  cutting ``k`` down to the facts that could actually matter).

Both modules refuse loudly, with ``ValueError``, rather than silently
approximate: a quantified formula in :mod:`nilsson` (no finite space of
possible worlds), or negation/disjunctive-heads/existentials/free variables in
a :mod:`distribution` rule (outside the definite-clause fragment the
semantics is defined over) — the kit-wide convention that an unsupported
fragment is an error, never a quiet best-effort guess.

Both are PROPOSITIONAL / FINITE-DOMAIN in scope: :mod:`nilsson` evaluates over
the ``2^n`` truth-value assignments to a formula's distinct atoms (no
quantifiers at all); :mod:`distribution` grounds over the finite constants
occurring in the program and goal (no function symbols, no infinite Herbrand
universe). Both document the resulting exponential blow-up honestly and
expose an explicit, overridable brake on it (``max_atoms`` /
``max_choice_facts``) rather than hiding a silent cutoff.
"""

from .nilsson import ProbConstraint, ProbBounds, entailment_bounds
from .distribution import ProbFact, ProbProgram, query

__all__ = [
    "ProbConstraint", "ProbBounds", "entailment_bounds",
    "ProbFact", "ProbProgram", "query",
]
