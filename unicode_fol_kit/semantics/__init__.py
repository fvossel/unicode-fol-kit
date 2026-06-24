"""Semantic evaluation of unicode-fol-kit formulas.

Two complementary evaluators:

- Classical **Tarskian** model theory for FOL/MSFOL: define a :class:`Structure`
  (a "world" with a domain of individuals and interpretations of the symbols)
  and compute a formula's two-valued truth value with :func:`satisfies`.
- **Second-order** finite-model semantics :func:`satisfies_so` (and :func:`holds`
  for sentences): the same Tarskian satisfaction extended with ∀P / ∃P over
  predicate variables, by brute-force enumeration of relations on a small finite
  domain.
- The **Łukasiewicz fuzzy** evaluator :func:`evaluate`, which computes the truth
  degree in [0, 1] of an FL/MSFL formula under a valuation.
"""

from .tarski import Structure, term_value, satisfies, models
from .secondorder import satisfies_so, holds
from .fuzzy import evaluate
from .kripke import (
    KripkeModel, satisfies_modal, models_at, reflexive_transitive_closure,
)
from .manyvalued import (
    kleene_value, is_valid, is_satisfiable, entails, DESIGNATED,
)

__all__ = [
    "Structure", "term_value", "satisfies", "models",
    # Second-order finite-model semantics (∀P / ∃P over predicate variables).
    "satisfies_so", "holds",
    "evaluate",
    "KripkeModel", "satisfies_modal", "models_at", "reflexive_transitive_closure",
    # Many-valued (Kleene K3 / Priest LP). Note: is_valid/is_satisfiable/entails here are
    # the three-valued versions — distinct from the Z3-based ones at the package top level.
    "kleene_value", "is_valid", "is_satisfiable", "entails", "DESIGNATED",
]
