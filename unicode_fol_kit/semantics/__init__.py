"""Semantic evaluation of unicode-fol-kit formulas.

Two complementary evaluators:

- Classical **Tarskian** model theory for FOL/MSFOL: define a :class:`Structure`
  (a "world" with a domain of individuals and interpretations of the symbols)
  and compute a formula's two-valued truth value with :func:`satisfies`.
- **Second-order** finite-model semantics :func:`satisfies_so` (and :func:`holds`
  for sentences): the same Tarskian satisfaction extended with ∀P / ∃P over
  predicate variables, by brute-force enumeration of relations on a small finite
  domain.
- **Third-order** finite-model semantics :func:`satisfies_to` (and
  :func:`holds_to`): the level where an ARGUMENT can be a property —
  ``Positive(G)``, ``Positive(λx. ¬G(x))`` — and a quantifier can range over
  predicates OF properties. It enumerates over each bound symbol's argument
  SIGNATURE rather than its arity, since at this level arity no longer says what
  a predicate is.
- The **Łukasiewicz fuzzy** evaluator :func:`evaluate`, which computes the truth
  degree in [0, 1] of an FL/MSFL formula under a valuation.
"""

from .tarski import Structure, term_value, satisfies, models
from .secondorder import (
    satisfies_so, holds,
    so_find_model, so_find_countermodel, so_is_satisfiable_finite, so_is_valid_finite,
)
from .thirdorder import (
    satisfies_to, holds_to, slot_values, all_interpretations, interpretation_count,
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
from .free_logic import (
    FreeModel, free_satisfies, free_holds, NONDENOTING,
    free_find_model, free_countermodel, free_is_valid, free_entails,
)
from .dynamic_epistemic import announce, box_announce, diamond_announce
from .action_models import (
    ActionModel, product_update, public_announcement_action,
    common_knowledge_holds, everybody_knows,
)
from .conditional import (
    CounterfactualModel, cf_satisfies, cf_countermodel, cf_valid, would, might,
    CENTERING_LEVELS, DEFAULT_MAX_WORLDS,
)
from .nonmonotonic import (
    minimal_models, minimal_entails,
    circumscription_formula, circumscription_entails_so,
)
from .relevant import RelevantModel, rel_satisfies, rel_countermodel, rel_valid
from .team import team_satisfies, team_models, MAX_TEAM_SEARCH
from .team_translation import dependence_to_eso
from .structures import FiniteStructure, structure_from_dict, graph_to_structure
# The structure evaluator's own `evaluate` is re-exported under the explicit
# name `evaluate_in_structure`: this package's bare `evaluate` has meant the
# Łukasiewicz fuzzy evaluator since long before, and silently rebinding an
# established public name would break callers in the quietest possible way.
# `evaluate_detailed` carries no such history and keeps its name.
from .model_eval import (
    evaluate as evaluate_in_structure,
    evaluate_detailed,
    EvalResult, BudgetExhausted, UninterpretedSymbol, UnsupportedNode,
)

__all__ = [
    "Structure", "term_value", "satisfies", "models",
    # Finite structures + the direct structure evaluator (model CHECKING:
    # is this sentence true in THIS given interpretation?).
    "FiniteStructure", "structure_from_dict", "graph_to_structure",
    "evaluate_in_structure", "evaluate_detailed", "EvalResult",
    "BudgetExhausted", "UninterpretedSymbol", "UnsupportedNode",
    # Second-order finite-model semantics (∀P / ∃P over predicate variables).
    "satisfies_so", "holds",
    "satisfies_to", "holds_to",
    "slot_values", "all_interpretations", "interpretation_count",
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
    "free_find_model", "free_countermodel", "free_is_valid", "free_entails",
    "announce", "box_announce", "diamond_announce",
    "ActionModel", "product_update", "public_announcement_action",
    "common_knowledge_holds", "everybody_knows",
    "CounterfactualModel", "cf_satisfies", "cf_countermodel", "cf_valid",
    "would", "might", "CENTERING_LEVELS", "DEFAULT_MAX_WORLDS",
    "minimal_models", "minimal_entails",
    "circumscription_formula", "circumscription_entails_so",
    "RelevantModel", "rel_satisfies", "rel_countermodel", "rel_valid",
    "team_satisfies", "team_models", "MAX_TEAM_SEARCH",
    "dependence_to_eso",
]
