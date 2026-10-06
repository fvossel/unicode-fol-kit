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
  are in ``C``;
- ``HasValue("r", "a")`` (∃r.{a}) — has the named individual ``a`` among its
  ``r``-successors (OWL's ``ObjectHasValue``). A nominal in disguise: the
  in-house tableau refuses it by name, and the first-order image
  (:func:`~unicode_fol_kit.dl.translate.kb_to_fol` with ``api.prove``) and the
  ``dl.external_*`` entry points decide it; see :class:`HasValue` for why it is
  a constructor of its own rather than ``Exists("r", Nominal("a"))``.

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

:class:`HasValue` (``∃r.{a}``) belongs on that list too. It names an
individual inside a concept, so it is a NOMINAL in disguise, and the in-house
tableau refuses it by name exactly as it refuses a bare :class:`Nominal`. An
in-house value rule was built and removed again, because it is unsound under
subset blocking; "Value restrictions (ObjectHasValue)" in
:mod:`unicode_fol_kit.dl.tableau`'s module docstring has the two-axiom
counterexample. What decides a value restriction is the first-order image
(:func:`~unicode_fol_kit.dl.translate.kb_to_fol`, then ``api.prove``) and the
external, HermiT-backed reasoner (the ``dl.external_*`` entry points).
:func:`nnf` passes it through (it refuses a ``Nominal``).

Only :mod:`unicode_fol_kit.dl.owl_reasoner`'s external, HermiT-backed reasoner
decides concepts built from an :class:`InverseRole` or a :class:`Nominal` — see
that module's docstring.
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
from typing import Iterator

from .datatypes import DataRange, Literal, _paren_range


class Concept:
    """Base class for ALC concept expressions (see the module docstring)."""

    def to_unicode(self) -> str:
        """Render the concept with the standard DL glyphs (⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀).

        The text reads back as the same concept with
        :func:`~unicode_fol_kit.dl.parser.parse_concept` (a right operand of the
        same connective is parenthesised: ``And(A, And(B, C))`` is
        ``A ⊓ (B ⊓ C)``), except for the constructors the glyph syntax cannot
        read — see that module's docstring.

        A NAME that holds whitespace or one of the glyphs the syntax reserves
        (``⊓ ⊔ ¬ ⊤ ⊥ ∃ ∀ ≥ ≤ ( ) . ⊑ { }``) has no spelling in the glyph syntax
        (there is no escape), and such a name is written as it is, for display: the
        reader then refuses the text. A name for which it would instead read some
        OTHER concept — ``Atomic("A ⊓ B")`` prints ``A ⊓ B``, which is the
        intersection of two classes — is refused here.

        Raises:
            ValueError: a class, role or individual name makes the text read back
                as a different concept.
        """
        text = _render(self)
        _reject_misread_names(self, text)
        return text

    def __str__(self) -> str:
        # Display only, so it never raises: a name the glyph syntax cannot spell
        # is shown as it is (``to_unicode`` is the one that refuses it).
        return _render(self)


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


@dataclass(frozen=True)
class HasValue(Concept):
    """The value restriction ``∃r.{a}`` (OWL's ``ObjectHasValue(r a)``) — the
    concept of the individuals that have ``individual`` among their
    ``role``-successors.

    OWL 2 direct semantics: ``(ObjectHasValue(P a))^C = { x | <x, a^I> ∈ P^OP }``.
    The standard translation of the equivalent ``∃P.{a}`` is
    ``∃y (P(x, y) ∧ y = a)``, and one-point elimination of the equality-bounded
    existential (``y`` occurs only in that conjunction, so the equivalence is a
    FOL validity) reduces it to the atom ``P(x, a)`` — which is the image
    :mod:`unicode_fol_kit.dl.translate` produces: same models, no minted
    variable, and the individual in the argument position OWL's own reading
    puts it in.

    A node of its OWN rather than ``Exists(role, Nominal(individual))``, for
    two reasons:

    * **Round trip.** ``ObjectHasValue(r a)`` and the (still refused)
      ``ObjectSomeValuesFrom(r ObjectOneOf(a))`` are two distinct OWL 2
      structural objects; folding both into one AST shape would make
      ``parse(render(c)) == c`` stop holding for one of them. Same on the
      Manchester side: ``r value a`` versus the refused ``r some {a}``.
    * **It is the textbook DL reading.** There is no separate glyph for a value
      restriction, so this renders as ``∃r.{a}`` — identical to
      ``Exists(role, Nominal(a))``'s rendering, which is honest, because the
      two say the same thing. The glyph syntax therefore has two AST shapes
      with one rendering, and :mod:`unicode_fol_kit.dl.parser` refuses that
      text by name rather than guessing which was meant.

    Like :class:`Nominal`, this is OUTSIDE the fragment the in-house tableau
    decides: a value restriction is a nominal in disguise, the tableau refuses
    it by name, and the first-order image
    (:func:`~unicode_fol_kit.dl.translate.kb_to_fol`, then ``api.prove``) and the
    ``dl.external_*`` entry points decide it instead — see "Value restrictions (ObjectHasValue)" in
    :mod:`unicode_fol_kit.dl.tableau`'s module docstring for why a tableau rule
    for it is unsound (a two-axiom counterexample). Unlike :class:`Nominal`,
    :func:`nnf` passes it through, and ``Not(HasValue(...))`` is a LITERAL (like
    ``Not(Atomic(...))``) with no dual node — the dual of "has ``a`` as an
    ``r``-successor" is "does not", which is a condition on an EDGE, not a
    concept :func:`nnf` could push inward.
    """

    role: str
    individual: str


# --------------------------------------------------------------------------- #
# Data restrictions: the concept constructors that mention a DATA property.
# --------------------------------------------------------------------------- #
#
# Field named ``prop`` and not ``role`` on purpose: a data property is not an
# object role, and a generic walker that reads ``.role`` (the simple-role check,
# the modal translation, the OWL writers) must NOT take it for one.

@dataclass(frozen=True)
class DataExists(Concept):
    """The data restriction ``∃d.DR`` (OWL's ``DataSomeValuesFrom(d DR)``) — has
    at least one ``prop``-value in the data range ``datarange``.

    OWL 2 direct semantics: ``{ x | ∃v. (x, v) ∈ d^DP ∧ v ∈ DR^DT }``. The
    first-order image is ``∃w (d(x, w) ∧ δ(DR, w))``.

    Outside the fragment the in-house tableau decides: it has no data domain,
    so it REFUSES a concept containing one by name. The first-order image is
    the route that answers (see :func:`unicode_fol_kit.dl.translate.kb_to_fol`
    and :func:`unicode_fol_kit.dl.translate.data_sort_axioms`).
    """

    prop: str
    datarange: DataRange


@dataclass(frozen=True)
class DataForAll(Concept):
    """The data restriction ``∀d.DR`` (OWL's ``DataAllValuesFrom(d DR)``) —
    every ``prop``-value is in the data range ``datarange``. Image:
    ``∀w (d(x, w) → δ(DR, w))``."""

    prop: str
    datarange: DataRange


@dataclass(frozen=True)
class DataHasValue(Concept):
    """The data value restriction (OWL's ``DataHasValue(d lt)``) — has the
    literal ``value`` among its ``prop``-values.

    OWL 2 direct semantics: ``{ x | (x, lt^LT) ∈ d^DP }``. There is no
    quantifier — a literal denotes ONE fixed data value — so the image is the
    ground atom ``d(x, t)`` for the literal's term ``t``: no bound variable and
    no datatype guard (the literal already pins its datatype).
    """

    prop: str
    value: Literal


@dataclass(frozen=True)
class DataAtLeast(Concept):
    """The qualified data number restriction ``≥n d.DR`` (OWL's
    ``DataMinCardinality(n d DR)``) — at least ``n`` PAIRWISE-DISTINCT
    ``prop``-values are in ``datarange``. Image: the same ``Count`` node the
    object ``AtLeast`` uses, over the data atom. ``DataExactCardinality`` is
    not a node of its own: the parsers desugar it to ``DataAtLeast ⊓ DataAtMost``,
    as ``ObjectExactCardinality`` is."""

    n: int
    prop: str
    datarange: DataRange

    def __post_init__(self):
        """Validate that n is a non-negative integer (mirrors AtLeast's check)."""
        if not (isinstance(self.n, int) and self.n >= 0):
            raise ValueError(f"DataAtLeast: n must be a non-negative integer, got {self.n!r}")


@dataclass(frozen=True)
class DataAtMost(Concept):
    """The qualified data number restriction ``≤n d.DR`` (OWL's
    ``DataMaxCardinality(n d DR)``) — at most ``n`` pairwise-distinct
    ``prop``-values are in ``datarange``."""

    n: int
    prop: str
    datarange: DataRange

    def __post_init__(self):
        """Validate that n is a non-negative integer (mirrors AtMost's check)."""
        if not (isinstance(self.n, int) and self.n >= 0):
            raise ValueError(f"DataAtMost: n must be a non-negative integer, got {self.n!r}")


#: Every data restriction class, for the walkers that must treat them alike.
DATA_CONCEPTS = (DataExists, DataForAll, DataHasValue, DataAtLeast, DataAtMost)


def _refuse_data_concept(concept: Concept) -> None:
    """Raise the loud ``TypeError`` :func:`nnf` gives a data restriction."""
    raise TypeError(
        f"nnf: the data restriction {type(concept).__name__} ({_render(concept)}) "
        f"has no negation normal form in this kit: the in-house tableau has no "
        f"data domain, so its dual (a restriction over the COMPLEMENT of the "
        f"data range, taken within the data domain) would be a rule nothing "
        f"implements. The route that answers is the first-order image, which is "
        f"sound for the data layer and not complete: kb = dl.kb_to_fol(tbox, abox, "
        f"query=[concept]) and its goal methods (kb.unsatisfiability_goal, "
        f"kb.subsumption_goal, kb.instance_goal) with api.prove.")


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
    # A LITERAL of its own, like Atomic: a value restriction has no dual
    # concept to push a negation into (see HasValue's class docstring), so both
    # polarities pass through unchanged -- the positive one here, the negative
    # one in the Not(inner) dispatch below. A new literal-shaped concept kind
    # belongs here and there, never in the (Top, Bottom, Atomic) tuple above,
    # whose membership carries the Nominal argument documented in this
    # function's own docstring.
    if isinstance(concept, HasValue):
        return concept
    if isinstance(concept, DATA_CONCEPTS):
        _refuse_data_concept(concept)
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
        if isinstance(inner, HasValue):
            return concept            # a literal; see the positive case above
        if isinstance(inner, DATA_CONCEPTS):
            _refuse_data_concept(inner)
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
         HasValue: 3, DataExists: 3, DataForAll: 3, DataHasValue: 3,
         DataAtLeast: 3, DataAtMost: 3,
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
    if isinstance(c, HasValue):
        # The textbook DL spelling of a value restriction -- there is no glyph
        # of its own, so this is ∃r.{a}, the same text Exists(r, Nominal(a))
        # renders to. Honest (the two concepts have the same models) and the
        # reason dl.parser refuses to read it back: see HasValue's docstring.
        return f"∃{_render_role(c.role)}.{{{c.individual}}}"
    if isinstance(c, Not):
        return "¬" + _paren(c.concept, 3)
    # The reader folds a flat chain of one connective to the LEFT (``A ⊓ B ⊓ C``
    # is ``(A ⊓ B) ⊓ C``), so only a LEFT operand of the same connective may go
    # unparenthesised: the right operand is written one level tighter, and an
    # ``⊓`` inside an ``⊓`` (an ``⊔`` inside an ``⊔``) on the right keeps its
    # parentheses.
    if isinstance(c, And):
        return f"{_paren(c.left, 2)} ⊓ {_paren(c.right, 3)}"
    if isinstance(c, Or):
        return f"{_paren(c.left, 1)} ⊔ {_paren(c.right, 2)}"
    if isinstance(c, Exists):
        return f"∃{_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, ForAll):
        return f"∀{_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, AtLeast):
        return f"≥{c.n} {_render_role(c.role)}.{_paren(c.concept, 3)}"
    if isinstance(c, AtMost):
        return f"≤{c.n} {_render_role(c.role)}.{_paren(c.concept, 3)}"
    # Display-only, like everything here: the glyph parser has no data syntax,
    # so these are read with dl.parse_manchester or dl.parse_owl_functional. A
    # COMPOUND data range is parenthesised, so `∃d.(xsd:integer ⊔ xsd:string)`
    # is not mistaken for `(∃d.xsd:integer) ⊔ xsd:string`.
    if isinstance(c, DataExists):
        return f"∃{c.prop}.{_paren_range(c.datarange)}"
    if isinstance(c, DataForAll):
        return f"∀{c.prop}.{_paren_range(c.datarange)}"
    if isinstance(c, DataHasValue):
        return f"∃{c.prop}.{{{c.value.to_unicode()}}}"
    if isinstance(c, DataAtLeast):
        return f"≥{c.n} {c.prop}.{_paren_range(c.datarange)}"
    if isinstance(c, DataAtMost):
        return f"≤{c.n} {c.prop}.{_paren_range(c.datarange)}"
    raise TypeError(f"render: unsupported concept {type(c).__name__}")


def _paren(c: Concept, parent_prec: int) -> str:
    """Parenthesise ``c`` when its precedence is below the parent's."""
    inner = _render(c)
    return f"({inner})" if _PREC.get(type(c), 4) < parent_prec else inner


def _role_name(role) -> str:
    """The name inside a ``role`` field: the string, or an :class:`InverseRole`'s."""
    return role.role if isinstance(role, InverseRole) else role


def _names_of(c: Concept) -> Iterator[str]:
    """Every class, role, individual and data-property name inside ``c``."""
    if isinstance(c, Atomic):
        yield c.name
    elif isinstance(c, Nominal):
        yield c.individual
    elif isinstance(c, Not):
        yield from _names_of(c.concept)
    elif isinstance(c, (And, Or)):
        yield from _names_of(c.left)
        yield from _names_of(c.right)
    elif isinstance(c, (Exists, ForAll, AtLeast, AtMost)):
        yield _role_name(c.role)
        yield from _names_of(c.concept)
    elif isinstance(c, HasValue):
        yield _role_name(c.role)
        yield c.individual
    elif isinstance(c, DATA_CONCEPTS):
        yield c.prop


def _reject_misread_names(concept: Concept, text: str) -> None:
    """Raise :class:`ValueError` unless ``text``, the glyph rendering of ``concept``,
    is either read back as ``concept`` or refused by the reader.

    A name made of ordinary characters is one NAME token and is read back as
    itself; the only way the text can read as ANOTHER concept is a name that holds
    whitespace or one of the reader's reserved glyphs. So the reader is asked only
    when such a name occurs (the glyph syntax has no escape, and an IRI with a dot
    in it is a common name that the reader refuses, which is fine: that is
    loud). Imported here because the parser module imports this one.
    """
    from .parser import _GLYPH_TOKENS, parse_concept

    odd = sorted({name for name in _names_of(concept)
                  if isinstance(name, str)
                  and (name == "" or any(ch.isspace() or ch in _GLYPH_TOKENS for ch in name))})
    if not odd:
        return
    try:
        back = parse_concept(text)
    except (ValueError, RecursionError):
        return                       # the reader refuses this text: nothing reads it as another concept
    if back != concept:
        raise ValueError(
            f"to_unicode: {text!r} reads back as {back!r}, not as the concept it "
            f"was written from: the name(s) {odd!r} hold whitespace or a glyph the glyph syntax "
            f"reserves, and that syntax has no escape for them. Rename the class or role, or "
            f"write the concept with dl.to_owl_functional_class_expression, whose <...> carries "
            f"any name that has no '>' in it.")
