"""Semantic evaluation of unicode-fol-kit formulas.

Two complementary evaluators:

- Classical **Tarskian** model theory for FOL/MSFOL: define a :class:`Structure`
  (a "world" with a domain of individuals and interpretations of the symbols)
  and compute a formula's two-valued truth value with :func:`satisfies`.
- The **Łukasiewicz fuzzy** evaluator :func:`evaluate`, which computes the truth
  degree in [0, 1] of an FL/MSFL formula under a valuation.
"""

from .tarski import Structure, term_value, satisfies, models
from .fuzzy import evaluate

__all__ = ["Structure", "term_value", "satisfies", "models", "evaluate"]
