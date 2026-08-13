"""Evaluation utilities for NL→FOL work.

- :func:`canonicalize` puts a formula into a normal form that quotients out
  bound-variable renaming, commutativity/associativity of the commutative
  connectives, operand duplication, and double negation — while staying
  logically equivalent. :func:`exact_match` uses it for a fair "canonical exact
  match" that is stricter than logical equivalence but more forgiving than raw
  string/structural equality.
- :func:`validate` / :func:`is_wellformed` / :func:`validate_text` report the
  common defects in a generated formula (free variables, inconsistent predicate
  or function arity, leftover lambda nodes, unparseable text).
- :func:`match_predicates` / :func:`formulas_are_matched_identical` /
  :func:`formulas_are_identical` provide a lexical, predicate-aligned string
  match (Levenshtein-based predicate renaming) — complementary to the AST-level
  :func:`exact_match`, which instead quotients out the structural rewrites.
- :func:`align_symbols` / :func:`aligned_exact_match` are the parsed-AST
  counterpart of the lexical matcher: separate predicate/function/constant
  namespaces, arity-aware, injective and capture-free — combined with
  :func:`exact_match` they quotient out BOTH vocabulary and structural noise.
- :func:`explain_countermodel` renders any countermodel witness (Kripke,
  Tarski structure, Z3 assignment, Verdict-layer dict) as a few short,
  deterministic English sentences.
- :func:`batch_decide` runs the prover chain over many formulas with a
  content-addressed cache, process parallelism, and JSONL results.
- :mod:`~unicode_fol_kit.eval.datasets` holds the NL→logic benchmark
  adapters (FOLIO, MALLS, …) with a shared example shape and gold-formula
  self-audit.
"""

from .canonical import canonicalize, exact_match
from .validate import validate, is_wellformed, validate_text, ValidationReport
from .predicate_match import (
    formulas_are_identical,
    match_predicates,
    formulas_are_matched_identical,
    align_symbols,
    aligned_exact_match,
)
from .equivalence import EquivalenceResult, equivalent
from .explain import explain_countermodel
from .metric_hf import compute_fol_metrics
from .theory_check import (
    Definitions, CyclicDefinition, UnfoldDepthExceeded,
    dependency_graph, find_cycles, unfold,
    SatisfiabilityResult, check_satisfiable,
    SubsumptionResult, check_subsumption,
    TheoryReport, check_theory,
)
from .generality import (
    MinimalModelResult, minimal_model_size,
    GeneralityReport, generality_report,
    StrictlyStrongerResult, strictly_stronger,
    VacuousSpecialisationResult, is_vacuous_specialisation,
)
from .batch import batch_decide
from . import datasets   # NL→logic benchmark adapters (datasets.load_folio, …)

__all__ = [
    "canonicalize", "exact_match",
    "validate", "is_wellformed", "validate_text", "ValidationReport",
    "formulas_are_identical", "match_predicates", "formulas_are_matched_identical",
    "align_symbols", "aligned_exact_match",
    "EquivalenceResult", "equivalent",
    "explain_countermodel",
    "compute_fol_metrics",
    # Deductive checks over a set of predicate DEFINITIONS: cycles, dead
    # (unsatisfiable) definitions, subclass ⊨ superclass — with a
    # countermodel whenever the answer is "no", not just "not proved".
    "Definitions", "CyclicDefinition", "UnfoldDepthExceeded",
    "dependency_graph", "find_cycles", "unfold",
    "SatisfiabilityResult", "check_satisfiable",
    "SubsumptionResult", "check_subsumption",
    "TheoryReport", "check_theory",
    # Logical generality analysis — how easily is a definition satisfied,
    # and does a "specialisation" actually specialise anything?
    "MinimalModelResult", "minimal_model_size",
    "GeneralityReport", "generality_report",
    "StrictlyStrongerResult", "strictly_stronger",
    "VacuousSpecialisationResult", "is_vacuous_specialisation",
    "batch_decide",
    "datasets",
]
