"""The description logic **ALC** (extended to **ALCQ**): concept expressions, roles,
and negation normal form.

ALC (*Attributive Language with Complements*) is the smallest propositionally closed
description logic and the notation underlying OWL. Its *concepts* describe sets of
individuals and its *roles* binary relations between them:

- ``Top`` (⊤) — everything; ``Bottom`` (⊥) — nothing;
- ``Atomic("C")`` — a primitive concept name;
- ``Not(C)`` (¬C), ``And(C, D)`` (C ⊓ D), ``Or(C, D)`` (C ⊔ D);
- ``Exists("r", C)`` (∃r.C) — has an ``r``-successor in ``C``;
- ``ForAll("r", C)`` (∀r.C) — all ``r``-successors are in ``C``;
- ``AtLeast(n, "r", C)`` (≥n r.C) — at least ``n`` PAIRWISE-DISTINCT ``r``-successors
  are in ``C``;
- ``AtMost(n, "r", C)`` (≤n r.C) — at most ``n`` pairwise-distinct ``r``-successors
  are in ``C``.

ALC alone is exactly the multi-modal logic **K** (a role ``r`` is a modality, ``∃r``
its ◇ and ``∀r`` its □), which is why it is decidable; ``AtLeast``/``AtMost`` add
*qualified number restrictions* (the DL usually written **ALCQ**), decided by the
tableau's dedicated ≥/≤/choose completion rules — see the "Qualified number
restrictions" section of :mod:`unicode_fol_kit.dl.tableau`'s module docstring for the
algorithm, and note the "simple roles" restriction documented there (number
restrictions may not target a transitive role, or one with a transitive sub-role).
:func:`nnf` rewrites a concept to *negation normal form* (negation only on atomic
concepts), the shape the tableau in :mod:`unicode_fol_kit.dl.tableau` consumes.

Inverse roles and nominals (I, O) — represented, but not decided here
------------------------------------------------------------------------
Two more constructs are recognised by this AST but sit OUTSIDE ALCHQ and are
NEVER decided by :mod:`unicode_fol_kit.dl.tableau`'s in-house tableau, which
refuses both by name (see that module's ``_reject_beyond_alc``):

- :class:`InverseRole` (``r⁻``) — a *role expression*, not a concept: it is
  used wherever a plain role NAME (a ``str``) is expected, i.e. as the
  ``role`` field of :class:`Exists`/:class:`ForAll`/:class:`AtLeast`/
  :class:`AtMost` (``Exists(InverseRole("hasChild"), C)`` is ``∃hasChild⁻.C``).
  This is deliberate: that field is never type-checked anywhere in this
  module (see :func:`nnf`'s Exists/ForAll branches), so an
  ``InverseRole``-wrapped role sails through unrecognised rather than
  crashing — which is exactly why :mod:`unicode_fol_kit.dl.tableau` needs its
  own explicit guard rather than relying on this module to reject it "for
  free" (see that module's docstring for the full soundness argument).
- :class:`Nominal` (``{a}``) — the singleton concept containing exactly the
  named individual ``a`` (OWL's ``ObjectOneOf`` restricted to one
  individual; a multi-individual nominal set ``{a, b}`` is expressed as
  ``Or(Nominal("a"), Nominal("b"))`` — semantically identical, since OWL 2
  gives ``ObjectOneOf`` exactly that union reading, and it avoids a second
  AST shape for "a set of names").

Only :mod:`unicode_fol_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner
decides concepts built from either construct — see that module's docstring.
:func:`nnf` refuses EVERY concept containing a ``Nominal`` — bare
(``nnf(Nominal("a"))``) or nested (``nnf(Not(Nominal("a")))``,
``nnf(And(Nominal("a"), C))``, …) — with a :class:`TypeError`, by design (see
:func:`nnf`'s own docstring); this is deliberately NOT weakened anywhere to
give ``Nominal`` "free" passage the way ``Top``/``Bottom``/``Atomic`` get.
``to_unicode``/:func:`_render`, by contrast, DO handle ``Nominal`` (and an
``InverseRole``-valued role), since rendering has no soundness consequence —
a mixed ALCHQ+I/O concept can still be printed for diagnostics even though
the in-house tableau will never reason over it.

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


@dataclass(frozen=True)
class AtLeast(Concept):
    """Qualified at-least number restriction ≥n r.C — at least ``n`` PAIRWISE-DISTINCT
    ``role``-successors are in ``concept``.

    No unique name assumption is in force anywhere in this kit's DL reasoner (see
    :mod:`unicode_fol_kit.dl.tableau`), so "pairwise-distinct" is a genuine semantic
    requirement, not just "n role-successors that happen to carry different names" —
    two successors are only known distinct when something *forces* it (see the
    tableau module docstring). ``n = 0`` is a tautology (every individual vacuously
    has at least zero such successors, so it never constrains anything); ``n = 1``
    is semantically ``Exists(role, concept)`` but kept as a separate constructor
    (the tableau still gives it its own, simpler ∃-rule) rather than folded away.
    """

    n: int
    role: str
    concept: Concept

    def __post_init__(self):
        """Validate that n is a non-negative integer (mirrors Count's own check)."""
        if not (isinstance(self.n, int) and self.n >= 0):
            raise ValueError(f"AtLeast: n must be a non-negative integer, got {self.n!r}")


@dataclass(frozen=True)
class AtMost(Concept):
    """Qualified at-most number restriction ≤n r.C — at most ``n`` pairwise-distinct
    ``role``-successors are in ``concept`` (see :class:`AtLeast` for the "no unique
    name assumption" caveat, which applies here identically). ``n = 0`` forbids any
    ``role``-successor in ``concept`` at all.
    """

    n: int
    role: str
    concept: Concept

    def __post_init__(self):
        """Validate that n is a non-negative integer (mirrors Count's own check)."""
        if not (isinstance(self.n, int) and self.n >= 0):
            raise ValueError(f"AtMost: n must be a non-negative integer, got {self.n!r}")


@dataclass(frozen=True)
class InverseRole:
    """A role EXPRESSION ``r⁻`` (OWL's ``ObjectInverseOf``) — the inverse of the
    named role ``role``: ``x —r⁻→ y`` holds exactly when ``y —r→ x`` does.

    Deliberately NOT a :class:`Concept` subclass: it is used in place of a plain
    role NAME (a ``str``), as the ``role`` field of :class:`Exists`/:class:`ForAll`/
    :class:`AtLeast`/:class:`AtMost` (``Exists(InverseRole("hasChild"), C)`` is
    ``∃hasChild⁻.C``) — see the module docstring's "Inverse roles and nominals"
    section for why that field being untyped is exactly what lets this work
    without any change to :func:`nnf`'s Exists/ForAll/AtLeast/AtMost branches,
    and why that same fact makes it the in-house tableau's job, not this
    module's, to refuse it (:mod:`unicode_fol_kit.dl.tableau`'s
    ``_reject_beyond_alc``).
    """

    role: str


@dataclass(frozen=True)
class Nominal(Concept):
    """The nominal concept ``{a}`` (OWL's ``ObjectOneOf`` restricted to one
    individual) — the singleton concept containing exactly the named individual
    ``individual``, and nothing else, in EVERY model (no unique name assumption
    is needed for this: a nominal fixes membership by naming the element
    directly, not by comparison with another name — see
    :mod:`unicode_fol_kit.dl.tableau`'s "Qualified number restrictions" section
    for how the reasoner treats individual identity elsewhere).

    Outside ALCHQ — see the module docstring's "Inverse roles and nominals"
    section: :func:`nnf` refuses any concept containing one, and only
    :mod:`unicode_fol_kit.dl.owl_reasoner`'s external reasoner decides concepts
    that use it. A multi-individual nominal set ``{a, b}`` is
    ``Or(Nominal("a"), Nominal("b"))`` — see that section for why this needs no
    separate AST shape.
    """

    individual: str


def nnf(concept: Concept) -> Concept:
    """Return ``concept`` in negation normal form (negation only on atomic concepts).

    Pushes ¬ inward with the De Morgan / modal dualities:
    ``¬⊤ = ⊥``, ``¬⊥ = ⊤``, ``¬¬C = C``, ``¬(C⊓D) = ¬C⊔¬D``, ``¬(C⊔D) = ¬C⊓¬D``,
    ``¬∃r.C = ∀r.¬C``, ``¬∀r.C = ∃r.¬C``, and the number-restriction duals
    ``¬(≥n r.C) = ≤(n-1) r.C`` for ``n ≥ 1`` (``¬(≥0 r.C) = ⊥``, since ``≥0`` is a
    tautology), ``¬(≤n r.C) = ≥(n+1) r.C``.

    Raises ``TypeError`` for any concept outside ALCHQ, in particular a
    :class:`Nominal` anywhere in ``concept`` — bare or nested under ``Not``/
    ``And``/``Or``/a restriction. This is INTENTIONAL and must stay this way:
    ``Nominal`` is deliberately left OUT of the top-level ``(Top, Bottom,
    Atomic)`` pass-through tuple below, even though it is "atomic-shaped" and
    could technically be passed through unchanged like they are. Doing so
    would remove a free, structurally-guaranteed second line of defense that
    :mod:`unicode_fol_kit.dl.tableau` relies on: every call this kit makes
    into ``nnf`` from ``tableau.py`` is already guarded by that module's own
    ``_reject_beyond_alc`` walker, so this raise is never *supposed* to fire
    in normal operation — but if that guard ever has a gap (a future call
    site, a missed nested occurrence), a ``Nominal`` reaching here still fails
    LOUDLY instead of silently being treated as an ordinary opaque
    :class:`Atomic` concept and producing a too-permissive verdict. See
    ``tests/test_dl_alc.py``'s dedicated regression test (which calls ``nnf``
    directly, bypassing the tableau's guard on purpose) and
    :mod:`unicode_fol_kit.dl.tableau`'s module docstring for the full
    soundness argument. An ``InverseRole``-valued ``role`` field needs no
    parallel case here at all: ``Exists``/``ForAll``/``AtLeast``/``AtMost``
    never inspect their ``role`` field's type, so it already sails through
    every branch below untouched, for exactly the same reason it is NOT safe
    on its own — see ``tableau.py`` for why that, too, is refused there.
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
    if isinstance(concept, AtLeast):
        return AtLeast(concept.n, concept.role, nnf(concept.concept))
    if isinstance(concept, AtMost):
        return AtMost(concept.n, concept.role, nnf(concept.concept))
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
        if isinstance(inner, AtLeast):
            if inner.n == 0:
                return Bottom()               # ¬(≥0 r.C): ≥0 is a tautology
            return AtMost(inner.n - 1, inner.role, nnf(inner.concept))
        if isinstance(inner, AtMost):
            return AtLeast(inner.n + 1, inner.role, nnf(inner.concept))
    raise TypeError(f"nnf: unsupported concept {type(concept).__name__}")


_PREC = {Or: 1, And: 2, Not: 3, Exists: 3, ForAll: 3, AtLeast: 3, AtMost: 3,
         Atomic: 4, Top: 4, Bottom: 4, Nominal: 4}


def _render_role(role) -> str:
    """Render a ``role`` field (a plain ``str``, or an :class:`InverseRole` —
    see the module docstring's "Inverse roles and nominals" section): ``r⁻``
    for the latter, matching :func:`_render`'s other glyph choices. This is
    display-only, unlike :mod:`unicode_fol_kit.dl.tableau`'s refusal of
    ``InverseRole``: rendering carries no soundness consequence.
    """
    if isinstance(role, InverseRole):
        return f"{role.role}⁻"
    return role


def _render(c: Concept) -> str:
    """Render a concept with precedence-aware parenthesisation."""
    if isinstance(c, Top):
        return "⊤"
    if isinstance(c, Bottom):
        return "⊥"
    if isinstance(c, Atomic):
        return c.name
    if isinstance(c, Nominal):
        return "{" + c.individual + "}"
    if isinstance(c, Not):
        return "¬" + _paren(c.concept, 3)
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} ⊓ {_paren(c.right, 2)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} ⊔ {_paren(c.right, 1)}"
    if isinstance(c, Exists):
        return f"∃{_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"∀{_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, AtLeast):
        return f"≥{c.n} {_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, AtMost):
        return f"≤{c.n} {_render_role(c.role)}.{_paren(c.concept, 3)}"
    raise TypeError(f"render: unsupported concept {type(c).__name__}")


def _paren(c: Concept, parent_prec: int) -> str:
    """Parenthesise ``c`` when its precedence is below the parent's."""
    inner = _render(c)
    return f"({inner})" if _PREC.get(type(c), 4) < parent_prec else inner
