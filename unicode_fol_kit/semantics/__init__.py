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
from .secondorder import (
    satisfies_so, holds,
    so_find_model, so_find_countermodel, so_is_satisfiable_finite, so_is_valid_finite,
)
from .fuzzy import evaluate, ground_quantifiers
from .tnorm import TNorm, get_tnorm, TNORMS, LUKASIEWICZ, GODEL, PRODUCT
from .kripke import (
    KripkeModel, satisfies_modal, models_at, reflexive_transitive_closure,
)
from .manyvalued import (
    kleene_value, is_valid, is_satisfiable, entails, DESIGNATED,
)
from .truthtable import (
    truth_table, TruthTable, is_tautology, is_contradiction, is_satisfiable_tt,
)
from .modelfinder import (
    find_model, find_countermodel, is_satisfiable_finite, is_valid_finite,
)
from .intuitionistic import IntKripkeModel, int_valid, int_countermodel
from .matrix import (
    TruthMatrix, matrix_value, matrix_is_valid, matrix_is_satisfiable, matrix_entails,
    K3_MATRIX, LP_MATRIX, FDE_MATRIX, MATRICES,
)
from .free_logic import FreeModel, free_satisfies, free_holds, NONDENOTING
from .dynamic_epistemic import announce, box_announce, diamond_announce
from .conditional import CounterfactualModel, would, might
from .nonmonotonic import minimal_models, minimal_entails

__all__ = [
    "Structure", "term_value", "satisfies", "models",
    # Second-order finite-model semantics (∀P / ∃P over predicate variables).
    "satisfies_so", "holds",
    "so_find_model", "so_find_countermodel",
    "so_is_satisfiable_finite", "so_is_valid_finite",
    "evaluate", "ground_quantifiers",
    "TNorm", "get_tnorm", "TNORMS", "LUKASIEWICZ", "GODEL", "PRODUCT",
    "KripkeModel", "satisfies_modal", "models_at", "reflexive_transitive_closure",
    # Many-valued (Kleene K3 / Priest LP). Note: is_valid/is_satisfiable/entails here are
    # the three-valued versions — distinct from the Z3-based ones at the package top level.
    "kleene_value", "is_valid", "is_satisfiable", "entails", "DESIGNATED",
    # Truth tables (classical / K3 / LP).
    "truth_table", "TruthTable", "is_tautology", "is_contradiction", "is_satisfiable_tt",
    # Finite model finder + countermodels.
    "find_model", "find_countermodel", "is_satisfiable_finite", "is_valid_finite",
    # Intuitionistic propositional logic (Kripke semantics).
    "IntKripkeModel", "int_valid", "int_countermodel",
    # Finite-valued logical matrices (K3 / LP re-expressed; Belnap–Dunn FDE).
    "TruthMatrix", "matrix_value", "matrix_is_valid", "matrix_is_satisfiable",
    "matrix_entails", "K3_MATRIX", "LP_MATRIX", "FDE_MATRIX", "MATRICES",
    # Free logic, dynamic epistemic (PAL), counterfactuals, circumscription.
    "FreeModel", "free_satisfies", "free_holds", "NONDENOTING",
    "announce", "box_announce", "diamond_announce",
    "CounterfactualModel", "would", "might",
    "minimal_models", "minimal_entails",
]
