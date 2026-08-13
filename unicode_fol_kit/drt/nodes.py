"""The Discourse Representation Structure (DRS) data model — the classical Kamp/Reyle core.

Discourse Representation Theory (Kamp & Reyle, *From Discourse to Logic*, 1993) represents
a discourse as a **box**: a set of *discourse referents* (the individuals under discussion)
plus a set of *conditions* asserted about them. A box can itself appear as an operand of
another condition (negation, a conditional's antecedent/consequent, a disjunct), which is
how DRT gets recursive structure and — crucially — a notion of which referents are visible
where. This module implements exactly the propositional core of that theory: no tense,
no plurals, no presupposition, no generalized quantifiers beyond the donkey-sentence
universal reading built into the conditional (see ``unicode_fol_kit.drt.export`` for why
that reading is forced rather than optional). Those omissions are deliberate scope limits
of this kit subpackage, not oversights — see ``unicode_fol_kit.drt``'s package docstring.

Conditions (five variants, matching Kamp & Reyle's own inventory)::

    Pred(name, args)              # an atomic condition, e.g. Pred("Farmer", ("x",))
    Eq(a, b)                      # a = b
    Neg(drs)                      # ¬[drs]                (negation)
    Impl(antecedent, consequent)  # [antecedent] => [consequent]  (a "duplex condition")
    Or(left, right)               # [left] or [right]

``DRS(referents, conditions)`` is the box itself: a frozen dataclass pairing a tuple of
referent names with a tuple of conditions.

Referent vs. constant: a single lexical convention, not two vocabularies
--------------------------------------------------------------------------
Every string that appears as a ``Pred``/``Eq`` argument is either a *discourse referent*
(bound by some box's own existential/universal quantifier once translated to FOL) or a
*constant* (a rigid designator, e.g. a proper name). Rather than tagging each argument with
its role explicitly, this module reuses the kit's OWN lexical convention for telling a FOL
Variable from a Constant — see ``unicode_fol_kit/fol/grammars/terminals.lark``:

    VARIABLE.1: /[a-z][0-9]*/                              # single lowercase letter + digits
    NAME.2:     /[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*/     # lowercase-initial, >= 2 letters
    CONSTANT.3: /c_[a-zA-Z0-9]+/ | ...                      # explicit c_-prefixed form

so here: a single lowercase letter optionally followed by digits (``x``, ``y``, ``z1``,
``e12``, ...) is a REFERENT; anything else that is lowercase-initial and at least two
characters (``john``, ``daisy``, ...) or carries the explicit ``c_...`` form is a CONSTANT.
This is a deliberate, load-bearing restriction (not merely descriptive): a single-letter
name is ALWAYS read as a referent, so a one-character constant is not directly expressible
in this notation — the parser's quoted-string / SBN's quoted-constant path sanitizes such
cases into a legal (necessarily >= 2 character) constant name instead of silently colliding
with the referent namespace (see ``unicode_fol_kit.drt.parser``). ``is_referent`` /
``is_predicate_name`` / ``is_constant_name`` below are the single source of truth for this
classification; every other module in this subpackage (and ``unicode_fol_kit.drt.export``'s
standard translation) uses them rather than re-deriving the rule.

A predicate name (``Pred.name``) follows the kit's own PREDICATE convention: uppercase-
initial, alphanumeric (``PREDICATE: /[A-Z][a-zA-Z0-9]*/`` in the same grammar file).

Global referent uniqueness (a deliberate simplification, not part of classical DRT)
-------------------------------------------------------------------------------------
Full Kamp/Reyle DRT allows the same referent-like variable name to be reused in disjoint
boxes (it is a bound variable in each; alpha-renaming makes the reuse harmless). This
module does NOT allow that: :meth:`DRS.validate` requires every referent name appearing
anywhere in one DRS tree to be declared by exactly ONE box. This sidesteps alpha-renaming
bookkeeping entirely (the standard translation in ``export.py`` can use referent names
directly as FOL variable names with no risk of one quantifier accidentally shadowing
another's), at the cost of requiring the caller to pick distinct names across the whole
discourse — a small, explicit, well-documented restriction, very much in the "loud
refusal over silent misreading" spirit of this kit: a shadowing collision is refused with
a clear message rather than silently producing a formula whose nested quantifiers reuse a
name in a way the caller may not have intended.

Construction-time vs. final validation
-----------------------------------------
A condition's referent-shaped arguments must ultimately refer to an ACCESSIBLE box — the
classical Kamp/Reyle accessibility relation, defined below. But construction is necessarily
bottom-up (an inner box, e.g. a conditional's consequent ``[| Beats(x, y)]``, is built
*before* the ``Impl`` that will make its antecedent's referents ``x``/``y`` accessible to
it), so at the moment ``DRS(referents=(), conditions=(Pred("Beats", ("x", "y")),))`` is
constructed there is no way to know yet whether ``x``/``y`` will end up accessible — they
might never become so, if the caller forgets to wrap it in the right ``Impl``. Rejecting
this at ``__init__`` would make the classical donkey-sentence construction pattern
impossible to build piece by piece. So ``__init__`` (on ``DRS`` and on each condition
type) validates only what is knowable locally and independent of assembly order: shapes,
types, no duplicate referents *within one box's own tuple*. The GLOBAL accessibility check
— "is every referent-shaped argument, everywhere in this tree, accessible from the box it
occurs in?" — is :meth:`DRS.validate`, meant to be called once the whole tree is assembled
(and is called automatically by ``unicode_fol_kit.drt.export.drs_to_fol`` and
``unicode_fol_kit.drt.resolve.resolve_anaphora`` before they do anything with the tree).

The accessibility relation
-----------------------------
For a box ``K`` reached by walking down from the root, the referents ACCESSIBLE to K's own
direct conditions are exactly:

* K's own referents, plus
* every referent accessible to K's immediate container (the box housing the condition
  that K sits inside, if any) — accessibility is inherited "outer to inner" recursively, plus
* — the one asymmetric rule, THE donkey-sentence rule — if K is the CONSEQUENT of an
  ``Impl(A, K)``, then A's own referents are ALSO accessible to K (but not vice versa, and
  not to anything outside the ``Impl`` condition).

Concretely, entering each condition type from a box with accessible set ``acc``:

* ``Neg(D)``: D's accessible set is ``acc | D.referents``. D's referents do NOT propagate
  back out — a referent introduced under negation is invisible outside it (the classic "no
  farmer owns a donkey; # it is grey" infelicity).
* ``Impl(A, B)``: A's accessible set is ``acc | A.referents``. B's accessible set is
  ``acc | A.referents | B.referents`` (A's referents leak forward into B — the donkey
  rule — but not backward into A, and neither A's nor B's referents propagate outside the
  ``Impl`` condition).
* ``Or(D1, D2)``: D1's accessible set is ``acc | D1.referents``; D2's is
  ``acc | D2.referents`` — independent alternatives, like ``Neg``: neither leaks into the
  other or outside.

:func:`walk_boxes` computes this relation once for a whole tree (as an outer-to-inner
sequence of referent "layers" per box, so :mod:`unicode_fol_kit.drt.resolve` can also use it
for a recency ordering); :meth:`DRS.validate` is the accessibility checker built on top of it.
"""

import re
from dataclasses import dataclass
from typing import Dict, Iterator, Tuple

_REF_RE = re.compile(r"^[a-z][0-9]*$")
_PRED_RE = re.compile(r"^[A-Z][a-zA-Z0-9]*$")
_BARE_CONST_RE = re.compile(r"^[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*$")
_EXPLICIT_CONST_RE = re.compile(r"^c_[a-zA-Z0-9]+$")


def is_referent(name: str) -> bool:
    """True iff ``name`` is a legal discourse-referent name (a single lowercase letter
    optionally followed by digits — ``x``, ``y``, ``z1``, ``e12``, ...; the kit's own
    FOL Variable convention, see the module docstring)."""
    return isinstance(name, str) and bool(_REF_RE.fullmatch(name))


def is_predicate_name(name: str) -> bool:
    """True iff ``name`` is a legal predicate name (uppercase-initial, alphanumeric —
    the kit's own PREDICATE convention)."""
    return isinstance(name, str) and bool(_PRED_RE.fullmatch(name))


def is_constant_name(name: str) -> bool:
    """True iff ``name`` is a legal constant name: either a bare lowercase-initial
    name of >= 2 characters (the kit's NAME convention, e.g. ``john``) or the explicit
    ``c_...`` form (the kit's CONSTANT convention, for names that don't fit NAME)."""
    return isinstance(name, str) and bool(
        _BARE_CONST_RE.fullmatch(name) or _EXPLICIT_CONST_RE.fullmatch(name))


def _check_term_name(a, *, context: str) -> None:
    """Loudly refuse any Pred/Eq argument that is neither a legal referent nor a legal
    constant name (see the module docstring's "Referent vs. constant" section)."""
    if not isinstance(a, str) or not a:
        raise ValueError(f"{context}: argument must be a non-empty string, got {a!r}")
    if is_referent(a) or is_constant_name(a):
        return
    raise ValueError(
        f"{context}: {a!r} is neither a legal referent name (a single lowercase letter "
        f"optionally followed by digits, e.g. 'x', 'y1') nor a legal constant name (a "
        f"lowercase-initial name of >= 2 characters, e.g. 'john', or the explicit "
        f"'c_...' form). An arbitrary/quoted constant must be sanitized first — see "
        f"unicode_fol_kit.drt.parser's quoted-constant handling.")


class Condition:
    """Base class for the five DRS condition variants (see the module docstring)."""

    def to_dict(self) -> dict:
        raise NotImplementedError

    def to_box_notation(self) -> str:
        """Render this condition in the box notation :func:`unicode_fol_kit.drt.parser.parse_drs`
        accepts, as it would appear inside a box's condition list."""
        raise NotImplementedError


@dataclass(frozen=True)
class Pred(Condition):
    """An atomic condition: ``name`` applied to one or more referent/constant ``args``.

    ``name`` must be a legal predicate name (uppercase-initial, alphanumeric); each of
    ``args`` must be a legal referent or constant name (see the module docstring). At
    least one argument is required — DRT conditions always assert something OF one or
    more discourse referents/constants, so a nullary condition has no discourse content.
    """

    name: str
    args: Tuple[str, ...]

    def __post_init__(self):
        object.__setattr__(self, "args", tuple(self.args))
        if not is_predicate_name(self.name):
            raise ValueError(
                f"Pred: predicate name {self.name!r} must be uppercase-initial "
                f"alphanumeric (the kit PREDICATE convention, e.g. 'Farmer', 'Owns').")
        if not self.args:
            raise ValueError(
                f"Pred({self.name!r}): needs at least one argument.")
        for a in self.args:
            _check_term_name(a, context=f"Pred({self.name!r}, {self.args!r})")

    def to_dict(self) -> dict:
        return {"_type": "Pred", "name": self.name, "args": list(self.args)}

    def to_box_notation(self) -> str:
        return f"{self.name}(" + ", ".join(self.args) + ")"


@dataclass(frozen=True)
class Eq(Condition):
    """An equality condition ``a = b`` between two referents/constants."""

    a: str
    b: str

    def __post_init__(self):
        _check_term_name(self.a, context=f"Eq({self.a!r}, {self.b!r})")
        _check_term_name(self.b, context=f"Eq({self.a!r}, {self.b!r})")

    def to_dict(self) -> dict:
        return {"_type": "Eq", "a": self.a, "b": self.b}

    def to_box_notation(self) -> str:
        return f"{self.a} = {self.b}"


@dataclass(frozen=True)
class Neg(Condition):
    """Negation of a sub-DRS: ``¬[drs]``. ``drs``'s own referents are accessible within
    ``drs`` but do not escape (see the module docstring's accessibility relation)."""

    drs: "DRS"

    def __post_init__(self):
        if not isinstance(self.drs, DRS):
            raise TypeError(f"Neg: operand must be a DRS, got {type(self.drs).__name__}")

    def to_dict(self) -> dict:
        return {"_type": "Neg", "drs": self.drs.to_dict()}

    def to_box_notation(self) -> str:
        return f"~{self.drs.to_box_notation()}"


@dataclass(frozen=True)
class Impl(Condition):
    """A duplex (conditional) condition ``[antecedent] => [consequent]`` — THE
    donkey-sentence construct: ``antecedent``'s referents are accessible in
    ``consequent`` (but nowhere else) — see the module docstring."""

    antecedent: "DRS"
    consequent: "DRS"

    def __post_init__(self):
        for field_name, val in (("antecedent", self.antecedent), ("consequent", self.consequent)):
            if not isinstance(val, DRS):
                raise TypeError(f"Impl: {field_name} must be a DRS, got {type(val).__name__}")

    def to_dict(self) -> dict:
        return {"_type": "Impl", "antecedent": self.antecedent.to_dict(),
                "consequent": self.consequent.to_dict()}

    def to_box_notation(self) -> str:
        return f"{self.antecedent.to_box_notation()} -> {self.consequent.to_box_notation()}"


@dataclass(frozen=True)
class Or(Condition):
    """A disjunctive condition ``[left] or [right]``; each side's referents are
    accessible only within that side (see the module docstring)."""

    left: "DRS"
    right: "DRS"

    def __post_init__(self):
        for field_name, val in (("left", self.left), ("right", self.right)):
            if not isinstance(val, DRS):
                raise TypeError(f"Or: {field_name} must be a DRS, got {type(val).__name__}")

    def to_dict(self) -> dict:
        return {"_type": "Or", "left": self.left.to_dict(), "right": self.right.to_dict()}

    def to_box_notation(self) -> str:
        return f"{self.left.to_box_notation()} ∨ {self.right.to_box_notation()}"


@dataclass(frozen=True)
class DRS:
    """A Discourse Representation Structure (a "box"): ``referents`` declared in this
    box, and ``conditions`` asserted about them (and about whatever is accessible from
    an enclosing box — see the module docstring).

    Construction validates only local shape (each referent is a legal, box-locally-unique
    referent name; each condition is a :class:`Condition` instance) — NOT cross-box
    accessibility, which construction order makes impossible to check here (see the module
    docstring). Call :meth:`validate` once a whole tree is assembled.
    """

    referents: Tuple[str, ...]
    conditions: Tuple[Condition, ...]

    def __post_init__(self):
        object.__setattr__(self, "referents", tuple(self.referents))
        object.__setattr__(self, "conditions", tuple(self.conditions))
        seen = set()
        for r in self.referents:
            if not is_referent(r):
                raise ValueError(
                    f"DRS: referent {r!r} is not a legal referent name (a single "
                    f"lowercase letter optionally followed by digits, e.g. 'x', 'y1').")
            if r in seen:
                raise ValueError(
                    f"DRS: duplicate referent {r!r} within one box's own referent "
                    f"list {self.referents!r}.")
            seen.add(r)
        for c in self.conditions:
            if not isinstance(c, Condition):
                raise TypeError(
                    f"DRS: condition {c!r} is not a Condition instance "
                    f"(got {type(c).__name__}).")

    def to_dict(self) -> dict:
        return {"_type": "DRS", "referents": list(self.referents),
                "conditions": [c.to_dict() for c in self.conditions]}

    def to_box_notation(self) -> str:
        """Render this DRS in the box notation :func:`unicode_fol_kit.drt.parser.parse_drs`
        accepts: ``parse_drs(drs.to_box_notation())`` reproduces an equal ``DRS`` (see
        that module for the exact grammar; a top-level ``Neg``/``Impl``/``Or`` — i.e. a
        DRS built as ``DRS((), (cond,))`` to wrap a bare duplex/negated condition — round
        trips to an equal value, though through one extra bracket layer, since
        ``parse_drs`` always accepts ``[ | <that condition>]`` as a plain box)."""
        refs = ", ".join(self.referents)
        conds = ", ".join(c.to_box_notation() for c in self.conditions)
        return f"[{refs} | {conds}]"

    def validate(self) -> bool:
        """Check the classical Kamp/Reyle accessibility relation over the whole tree
        rooted at ``self`` (see the module docstring), plus global referent-name
        uniqueness (this kit's deliberate simplification, see the module docstring).

        Raises:
            ValueError: a referent name is declared by more than one box, or some
                condition's referent-shaped argument is not accessible where it occurs
                (message names the referent, the condition, and the accessible set).
        Returns:
            True on success (never returns False — failure is always an exception, per
            this kit's "loud refusal over silent misreading" convention).
        """
        boxes = list(walk_boxes(self))

        declared: Dict[str, "DRS"] = {}
        for box, _ in boxes:
            for r in box.referents:
                if r in declared and declared[r] is not box:
                    raise ValueError(
                        f"DRS.validate: referent {r!r} is declared in more than one "
                        f"box in this tree. This DRT implementation requires globally "
                        f"distinct referent names (no shadowing/alpha-renaming, see "
                        f"the module docstring) — rename one of the occurrences.")
                declared[r] = box

        for box, layers in boxes:
            acc = frozenset(n for layer in layers for n in layer)
            for cond in box.conditions:
                if isinstance(cond, Pred):
                    args = cond.args
                elif isinstance(cond, Eq):
                    args = (cond.a, cond.b)
                else:
                    continue
                for a in args:
                    if is_referent(a) and a not in acc:
                        raise ValueError(
                            f"DRS.validate: referent {a!r} in condition "
                            f"{cond.to_box_notation()!r} is not accessible at this "
                            f"point (accessible referents here: {sorted(acc)!r}). See "
                            f"the accessibility relation in the nodes module docstring.")
        return True


def walk_boxes(
    drs: DRS, _layers: Tuple[Tuple[str, ...], ...] = ()
) -> Iterator[Tuple[DRS, Tuple[Tuple[str, ...], ...]]]:
    """Yield every ``(box, layers)`` pair reachable from ``drs`` (``drs`` itself first,
    pre-order), where ``layers`` is the sequence of referent tuples — outermost first,
    ``box``'s own referents last — that together make up the referents ACCESSIBLE to
    ``box``'s own direct conditions per the classical accessibility relation (see the
    module docstring). ``frozenset(n for layer in layers for n in layer)`` is the flat
    accessible SET; the ordered form is kept so
    :mod:`unicode_fol_kit.drt.resolve` can rank candidates by recency (innermost layer,
    then rightmost position within a layer, is "most recent").
    """
    if not isinstance(drs, DRS):
        raise TypeError(f"walk_boxes: expected a DRS, got {type(drs).__name__}")
    my_layers = _layers + (drs.referents,)
    yield drs, my_layers
    for cond in drs.conditions:
        if isinstance(cond, Neg):
            yield from walk_boxes(cond.drs, my_layers)
        elif isinstance(cond, Impl):
            yield from walk_boxes(cond.antecedent, my_layers)
            yield from walk_boxes(cond.consequent, my_layers + (cond.antecedent.referents,))
        elif isinstance(cond, Or):
            yield from walk_boxes(cond.left, my_layers)
            yield from walk_boxes(cond.right, my_layers)
