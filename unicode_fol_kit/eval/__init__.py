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
"""

from .canonical import canonicalize, exact_match
from .validate import validate, is_wellformed, validate_text, ValidationReport
from .predicate_match import (
    formulas_are_identical,
    match_predicates,
    formulas_are_matched_identical,
)

__all__ = [
    "canonicalize", "exact_match",
    "validate", "is_wellformed", "validate_text", "ValidationReport",
    "formulas_are_identical", "match_predicates", "formulas_are_matched_identical",
]
