"""The standard translation of DRT into first-order logic (unicode_fol_kit.drt.export).

The standard translation (Kamp & Reyle, *From Discourse to Logic*, 1993) reads a box's
own referents as existential quantifiers over the conjunction of its conditions, with two
condition types contributing their own quantificational structure:

* ``Pred(name, args)``  ↦  ``name(args...)``   (an atom; each arg is a Variable if it's a
  referent — :func:`~unicode_fol_kit.drt.nodes.is_referent` — else a Constant)
* ``Eq(a, b)``          ↦  ``a = b``
* ``Neg(D)``            ↦  ``¬τ(D)``           where ``τ(D)`` existentially closes D's own
  referents — i.e. ``¬∃...`` : negation-as-failure-to-find-a-witness, matching the
  accessibility rule that D's referents don't escape it (see ``nodes.py``).
* ``Or(D1, D2)``        ↦  ``τ(D1) ∨ τ(D2)``   — each disjunct closes its own referents
  independently, again matching D1/D2's mutually inaccessible referents.
* ``Impl(A, B)``        ↦  ``∀(A's referents) (conj(A's conditions) → τ(B))`` — THE
  donkey-sentence rule. Unlike every other condition, A's referents become UNIVERSAL
  (not existential) quantifiers, and A's own conditions are conjoined DIRECTLY into the
  antecedent (NOT re-wrapped in their own existential closure) — both together are what
  make "Every farmer who owns a donkey beats it" come out as ``∀x∀y((Farmer(x) ∧
  Donkey(y) ∧ Owns(x,y)) → Beats(x,y))`` rather than something existential-then-vacuous.
  ``τ(B)`` (B's OWN translation, i.e. its own referents existentially closed as usual) is
  the consequent — B may introduce further referents of its own beyond what A shares with
  it (accessible to B per the donkey accessibility rule, but not bound by A's ∀ unless
  they ARE A's own referents).

A box with zero conditions translates to a reflexive-equality tautology (``c = c`` for a
fixed reserved constant) — the same "no constraint" idiom
:mod:`unicode_fol_kit.dl.translate` uses for an empty TBox/ABox — so an empty box never
silently vanishes into an ill-typed conjunction of zero formulas.

Closedness, and why :func:`drs_to_fol` always calls :meth:`~unicode_fol_kit.drt.nodes.DRS.validate`
---------------------------------------------------------------------------------------------------
The classical Kamp/Reyle accessibility relation (see ``nodes.py``'s module docstring) is
EXACTLY the condition under which this translation binds every referent it uses: a
referent-shaped argument is accessible to the box it occurs in iff, walking the same
recursive structure this translation walks, some ∃/∀ introduced along the way would bind
it. So an accessibility VIOLATION (a referent used somewhere it isn't accessible)
translates to a genuinely FREE variable in the output formula — silently. To make that
impossible, :func:`drs_to_fol` calls ``drs.validate()`` before translating anything, so an
invalid DRS is refused loudly (``ValueError`` from ``validate()``) rather than handed back
as an FOL formula that fails ``unicode_fol_kit.api.check(...).ok`` for a reason the caller
would have to rediscover by re-deriving accessibility themselves.

Constants
-----------
By the time a DRS reaches this module, every constant-shaped ``Pred``/``Eq`` argument is
ALREADY a legal kit constant name — :mod:`unicode_fol_kit.drt.nodes` refuses anything else
at construction time, and :mod:`unicode_fol_kit.drt.parser` sanitizes quoted/irregular
constants (recording the mapping) before ever building a ``Pred``/``Eq``. So this module
does no sanitization of its own: a non-referent argument becomes
``unicode_fol_kit.fol.nodes.Constant(name)`` verbatim.
"""

from typing import List

from ..fol.nodes import (
    Node, Variable, Constant, Atom, Count, Number,
    Not as _FNot, And as _FAnd, Or as _FOr, Implies, Quantifier,
)
from .nodes import (
    DRS, Card, Condition, Eq, Impl, Neg, Or, Part, Pred, is_referent,
    walk_boxes,
)

__all__ = ["drs_to_fol"]


class _FreshCounters:
    """Fresh counting variables for :class:`Card` translations.

    ``Card(g, ">=", 3)`` becomes ``∃≥3 p (Part_of(p, g))`` and the counting
    variable ``p`` must collide with NOTHING the tree declares — a clash
    would capture. Seeded once per :func:`drs_to_fol` call with every
    declared referent, then hands out ``p1, p2, …`` skipping taken names.
    (``Count`` binds its own variable, so two Cards may NOT share one name
    if one ends up in the scope of the other's matrix — cheap to avoid by
    never reusing any.)
    """

    def __init__(self, drs: DRS):
        self.taken = {r for box, _ in walk_boxes(drs) for r in box.referents}
        self.i = 0

    def next(self) -> str:
        while True:
            self.i += 1
            candidate = f"p{self.i}"
            if candidate not in self.taken:
                self.taken.add(candidate)
                return candidate


#: Card's kit-spelled ops onto Count's op codes; ``>``/``<`` shift the bound
#: (``> n`` ≡ ``≥ n+1``; ``< n`` ≡ ``≤ n-1``, and ``< 0`` is refused at
#: Card construction so the subtraction never goes negative).
_CARD_TO_COUNT = {"=": ("eq", 0), ">=": ("ge", 0), "<=": ("le", 0),
                  ">": ("ge", +1), "<": ("le", -1)}


def _term(name: str) -> Node:
    """A DRS argument (already validated legal by nodes.py) as a FOL term."""
    return Variable(name) if is_referent(name) else Constant(name)


def _tautology() -> Node:
    """The FOL image of "no constraint" — an empty box's condition list. Mirrors
    unicode_fol_kit.dl.translate's empty-TBox/ABox idiom."""
    c = Constant("_")
    return Atom("=", (c, c))


def _conjoin(parts: List[Node]) -> Node:
    """Fold a (possibly empty) list of formulas into a single left-associated conjunction."""
    if not parts:
        return _tautology()
    result = parts[0]
    for p in parts[1:]:
        result = _FAnd(result, p)
    return result


def _translate_cond(cond: Condition, fresh: _FreshCounters) -> Node:
    if isinstance(cond, Pred):
        return Atom(cond.name, tuple(_term(a) for a in cond.args))
    if isinstance(cond, Eq):
        return Atom("=", (_term(cond.a), _term(cond.b)))
    if isinstance(cond, Card):
        op, shift = _CARD_TO_COUNT[cond.op]
        counter = fresh.next()
        return Count(op, Number(cond.n + shift), Variable(counter),
                     Atom("Part_of", (Variable(counter), _term(cond.ref))))
    if isinstance(cond, Part):
        return Atom("Part_of", (_term(cond.member), _term(cond.group)))
    if isinstance(cond, Neg):
        return _FNot(_translate_box(cond.drs, fresh))
    if isinstance(cond, Impl):
        antecedent = _conjoin([_translate_cond(c, fresh)
                               for c in cond.antecedent.conditions])
        result: Node = Implies(antecedent, _translate_box(cond.consequent, fresh))
        for r in reversed(cond.antecedent.referents):
            result = Quantifier("∀", Variable(r), result)
        return result
    if isinstance(cond, Or):
        return _FOr(_translate_box(cond.left, fresh),
                    _translate_box(cond.right, fresh))
    raise TypeError(f"drs_to_fol: unsupported condition {type(cond).__name__}")


def _translate_box(box: DRS, fresh: _FreshCounters) -> Node:
    result: Node = _conjoin([_translate_cond(c, fresh) for c in box.conditions])
    for r in reversed(box.referents):
        result = Quantifier("∃", Variable(r), result)
    return result


def drs_to_fol(drs: DRS) -> Node:
    """The standard translation of ``drs`` into a kit FOL :class:`~unicode_fol_kit.fol.nodes.Node`
    (see the module docstring for the per-condition rules and the donkey-sentence rule
    for ``Impl``).

    Calls ``drs.validate()`` first, so an accessibility violation is refused
    (``ValueError``) here rather than silently producing a formula with a free variable
    (see "Closedness" above). For a CLOSED, accessibility-valid ``drs`` the result is a
    closed formula — ``unicode_fol_kit.api.check(drs_to_fol(drs)).ok`` holds — ready for
    ``unicode_fol_kit.api.prove``.
    """
    drs.validate()
    return _translate_box(drs, _FreshCounters(drs))
