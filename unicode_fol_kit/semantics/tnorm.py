"""Continuous t-norms for the fuzzy (BL / Hájek basic-logic) family.

A *t-norm* ``T`` fixes the semantics of the **strong** fuzzy connectives over the
real interval ``[0, 1]``:

- strong conjunction ``⊗`` is ``T`` itself;
- strong disjunction ``⊕`` is the dual *t-conorm* ``S(x, y) = 1 − T(1−x, 1−y)``;
- implication ``→`` is the *residuum* ``R(x, y) = sup {z : T(x, z) ≤ y}``;
- negation ``¬x`` is ``R(x, 0)``;
- biconditional ``↔`` is ``min(R(x, y), R(y, x))``.

The *weak* connectives ``∧`` / ``∨`` are always ``min`` / ``max`` (the lattice meet /
join), independent of the t-norm, and so are the quantifiers ``∀`` (infimum) / ``∃``
(supremum). Three continuous t-norms — whose ordinal sums generate every
continuous t-norm (the Mostert–Shields theorem) — ship here:

- **Łukasiewicz** ``T(x, y) = max(0, x + y − 1)`` (the default; involutive negation);
- **Gödel** ``T(x, y) = min(x, y)`` (idempotent; a relative pseudo-complement negation);
- **product** ``T(x, y) = x · y`` (strict; Goguen residuum ``y / x``).

Public API: :class:`TNorm`, the instances :data:`LUKASIEWICZ`, :data:`GODEL`,
:data:`PRODUCT`, the registry :data:`TNORMS`, and :func:`get_tnorm`.
"""

from dataclasses import dataclass
from typing import Callable


@dataclass(frozen=True)
class TNorm:
    """A t-norm and the strong connective operations it induces over ``[0, 1]``.

    ``conj`` / ``disj`` / ``impl`` / ``neg`` are the strong ⊗ / ⊕ / → / ¬; ``equiv``
    is derived as ``min(x→y, y→x)``. (The weak ∧/∨ are min/max regardless and live
    in the evaluator, not here.)
    """

    name: str
    conj: Callable[[float, float], float]
    disj: Callable[[float, float], float]
    impl: Callable[[float, float], float]
    neg: Callable[[float], float]

    def equiv(self, x: float, y: float) -> float:
        """Residuated biconditional ``min(x → y, y → x)``."""
        return min(self.impl(x, y), self.impl(y, x))


LUKASIEWICZ = TNorm(
    "lukasiewicz",
    conj=lambda x, y: max(0.0, x + y - 1.0),
    disj=lambda x, y: min(1.0, x + y),
    impl=lambda x, y: min(1.0, 1.0 - x + y),
    neg=lambda x: 1.0 - x,
)

GODEL = TNorm(
    "godel",
    conj=lambda x, y: min(x, y),
    disj=lambda x, y: max(x, y),
    impl=lambda x, y: 1.0 if x <= y else y,
    neg=lambda x: 1.0 if x <= 0.0 else 0.0,
)

PRODUCT = TNorm(
    "product",
    conj=lambda x, y: x * y,
    disj=lambda x, y: x + y - x * y,
    impl=lambda x, y: 1.0 if x <= y else y / x,
    neg=lambda x: 1.0 if x <= 0.0 else 0.0,
)

TNORMS = {t.name: t for t in (LUKASIEWICZ, GODEL, PRODUCT)}


def get_tnorm(name: str) -> TNorm:
    """Return the :class:`TNorm` for ``name`` (``"lukasiewicz"`` / ``"godel"`` / ``"product"``)."""
    try:
        return TNORMS[name]
    except KeyError:
        raise ValueError(
            f"unknown t-norm {name!r}; use one of {sorted(TNORMS)}.") from None
