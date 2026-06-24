"""Shared "out-of-scope node" rejection helpers for the modal v1 back-ends.

Both the Kripke evaluator (:mod:`kripke`) and the standard translation
(:mod:`..fol.modal_translation`) interpret only the **propositional / ground**
modal fragment in v1. First-order quantifiers, Łukasiewicz (fuzzy) operators,
and lambda-calculus nodes are out of scope and are rejected uniformly here with
a clear NotImplementedError, so the message wording stays consistent across the
two modules.
"""

from typing import NoReturn

from ..fol.nodes import Node
from ..fol._msfl_nodes import (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

# Łukasiewicz (fuzzy) node types — no two-valued modal interpretation in v1.
FUZZY_TYPES = (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
)

# Lambda-calculus node types — must be eliminated before any modal back-end.
LAMBDA_TYPES = (LambdaVar, Lambda, Application)


def reject_quantifier(formula: Node, caller: str) -> NoReturn:
    """Reject a (sorted) quantifier: v1 modal logic is propositional / ground."""
    raise NotImplementedError(
        f"{caller}: {type(formula).__name__} is not supported — v1 modal logic "
        "is propositional / ground; first-order (quantified) modal logic is "
        "future work."
    )


def reject_fuzzy(formula: Node, caller: str) -> NoReturn:
    """Reject a Łukasiewicz node: modal v1 is two-valued, not fuzzy."""
    raise NotImplementedError(
        f"{caller}: Łukasiewicz node {type(formula).__name__} is not supported — "
        "modal v1 is two-valued; fuzzy modal logic is future work."
    )


def reject_lambda(formula: Node, caller: str) -> NoReturn:
    """Reject a lambda node: beta-reduce / lambda-eliminate before modal work."""
    raise NotImplementedError(
        f"{caller}: lambda node {type(formula).__name__} is not supported — "
        "beta-reduce and lambda-eliminate the formula first."
    )
