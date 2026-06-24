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
"""

from .canonical import canonicalize, exact_match
from .validate import validate, is_wellformed, validate_text, ValidationReport

__all__ = [
    "canonicalize", "exact_match",
    "validate", "is_wellformed", "validate_text", "ValidationReport",
]
