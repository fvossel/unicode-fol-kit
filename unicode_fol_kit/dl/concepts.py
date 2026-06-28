"""The description logic **ALC**: concept expressions, roles, and negation normal form.

ALC (*Attributive Language with Complements*) is the smallest propositionally closed
description logic and the notation underlying OWL. Its *concepts* describe sets of
individuals and its *roles* binary relations between them:

- ``Top`` (⊤) — everything; ``Bottom`` (⊥) — nothing;
- ``Atomic("C")`` — a primitive concept name;
- ``Not(C)`` (¬C), ``And(C, D)`` (C ⊓ D), ``Or(C, D)`` (C ⊔ D);
- ``Exists("r", C)`` (∃r.C) — has an ``r``-successor in ``C``;
- ``ForAll("r", C)`` (∀r.C) — all ``r``-successors are in ``C``.

ALC is exactly the multi-modal logic **K** (a role ``r`` is a modality, ``∃r`` its ◇
and ``∀r`` its □), which is why it is decidable. :func:`nnf` rewrites a concept to
*negation normal form* (negation only on atomic concepts), the shape the tableau in
:mod:`unicode_fol_kit.dl.tableau` consumes.

The classes live in the ``dl`` namespace (``import unicode_fol_kit.dl as dl``); the
names ``And`` / ``Or`` / ``Not`` are the concept constructors, distinct from the FOL
AST's connectives.
"""

from dataclasses import dataclass


class Concept:
    """Base class for ALC concept expressions (see the module docstring)."""

    def to_unicode(self) -> str:
        """Render the concept with the standard DL glyphs (⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀)."""
        return _render(self)

    def __str__(self) -> str:
        return self.to_unicode()


@dataclass(frozen=True)
class Top(Concept):
    """The universal concept ⊤ (every individual)."""


@dataclass(frozen=True)
class Bottom(Concept):
    """The empty concept ⊥ (no individual)."""


@dataclass(frozen=True)
class Atomic(Concept):
    """A primitive concept name, e.g. ``Atomic("Person")``."""

    name: str


@dataclass(frozen=True)
class Not(Concept):
    """Concept complement ¬C."""

    concept: Concept


@dataclass(frozen=True)
class And(Concept):
    """Concept intersection C ⊓ D."""

    left: Concept
    right: Concept


@dataclass(frozen=True)
class Or(Concept):
    """Concept union C ⊔ D."""

    left: Concept
    right: Concept


@dataclass(frozen=True)
class Exists(Concept):
    """Existential restriction ∃r.C — at least one ``role``-successor is in ``concept``."""

    role: str
    concept: Concept


@dataclass(frozen=True)
class ForAll(Concept):
    """Value restriction ∀r.C — every ``role``-successor is in ``concept``."""

    role: str
    concept: Concept


def nnf(concept: Concept) -> Concept:
    """Return ``concept`` in negation normal form (negation only on atomic concepts).

    Pushes ¬ inward with the De Morgan / modal dualities:
    ``¬⊤ = ⊥``, ``¬⊥ = ⊤``, ``¬¬C = C``, ``¬(C⊓D) = ¬C⊔¬D``, ``¬(C⊔D) = ¬C⊓¬D``,
    ``¬∃r.C = ∀r.¬C``, ``¬∀r.C = ∃r.¬C``.
    """
    if isinstance(concept, (Top, Bottom, Atomic)):
        return concept
    if isinstance(concept, And):
        return And(nnf(concept.left), nnf(concept.right))
    if isinstance(concept, Or):
        return Or(nnf(concept.left), nnf(concept.right))
    if isinstance(concept, Exists):
        return Exists(concept.role, nnf(concept.concept))
    if isinstance(concept, ForAll):
        return ForAll(concept.role, nnf(concept.concept))
    if isinstance(concept, Not):
        inner = concept.concept
        if isinstance(inner, Top):
            return Bottom()
        if isinstance(inner, Bottom):
            return Top()
        if isinstance(inner, Atomic):
            return concept
        if isinstance(inner, Not):
            return nnf(inner.concept)
        if isinstance(inner, And):
            return Or(nnf(Not(inner.left)), nnf(Not(inner.right)))
        if isinstance(inner, Or):
            return And(nnf(Not(inner.left)), nnf(Not(inner.right)))
        if isinstance(inner, Exists):
            return ForAll(inner.role, nnf(Not(inner.concept)))
        if isinstance(inner, ForAll):
            return Exists(inner.role, nnf(Not(inner.concept)))
    raise TypeError(f"nnf: unsupported concept {type(concept).__name__}")


_PREC = {Or: 1, And: 2, Not: 3, Exists: 3, ForAll: 3, Atomic: 4, Top: 4, Bottom: 4}


def _render(c: Concept) -> str:
    """Render a concept with precedence-aware parenthesisation."""
    if isinstance(c, Top):
        return "⊤"
    if isinstance(c, Bottom):
        return "⊥"
    if isinstance(c, Atomic):
        return c.name
    if isinstance(c, Not):
        return "¬" + _paren(c.concept, 3)
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} ⊓ {_paren(c.right, 2)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} ⊔ {_paren(c.right, 1)}"
    if isinstance(c, Exists):
        return f"∃{c.role}.{_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"∀{c.role}.{_paren(c.concept, 3)}"
    raise TypeError(f"render: unsupported concept {type(c).__name__}")


def _paren(c: Concept, parent_prec: int) -> str:
    """Parenthesise ``c`` when its precedence is below the parent's."""
    inner = _render(c)
    return f"({inner})" if _PREC.get(type(c), 4) < parent_prec else inner
