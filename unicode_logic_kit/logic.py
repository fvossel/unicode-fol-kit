"""Logics as first-class values, and terms that carry their own side conditions.

The kit's translations live in :mod:`unicode_logic_kit.comorphism` as a graph of
edges. This module is the typed surface over that graph: a logic is a value you
can call, and calling it converts::

    from unicode_logic_kit.logic import FOL, MODAL, MSFOL

    f = MODAL(parse("Ⓖ(P) → P"))      # a Sentence in the modal logic
    g = FOL(f)                          # converted, with its side conditions
    api.prove(g)                        # the axioms travel WITH the value

Why this and not a class hierarchy: a translation is NOT an upcast. It changes
the signature (the standard translation appends a world argument), it is only
defined on a fragment (``Until`` has no first-order form), and — the part a
subtype relation gets flatly wrong — the image usually does not answer a
validity question by itself. ``(∀x:Human M(x)) → ∃x:Human M(x)`` is valid in the
kit's many-sorted semantics, and its unsorted image is NOT valid: the sorts
being non-empty is a side condition, not part of the formula (so is a sorted
constant lying in its sort: ``∀x:Human M(x) → M(socrates:Human)`` has the same
trouble). So a converted
term is a term PLUS the axioms that make it mean what it meant, which is what
:class:`Sentence` holds together. Claiming ``modal ⊂ fol`` by inheritance would
license dropping exactly that, silently.

What each conversion preserves is the edge's ``guarantee`` (see
:data:`unicode_logic_kit.comorphism.GUARANTEES`) and it travels along:
:attr:`Sentence.guarantee` is the weakest on the path taken, and ``None`` means
some edge on it makes no promise.

There is deliberately NO implicit coercion: ``MODAL(f) & FOL(g)`` raises rather
than lifting one side, because the lift is where the side conditions would be
lost. Convert explicitly, then combine the terms.
"""

from dataclasses import dataclass, replace
from typing import Any, Optional, Tuple

from .comorphism import DEFAULT_REGISTRY, weakest_guarantee

__all__ = [
    "Sentence", "Logic",
    "FOL", "MSFOL", "MODAL", "QML", "ALC", "DRT", "TEAM", "ESO", "FUZZY",
    "LOGICS",
]


@dataclass(frozen=True)
class Sentence:
    """A term, the logic it is written in, and the side conditions it carries.

    ``axioms`` are SEPARATE premises in the same logic as ``term`` — never
    conjoined onto it (that is what makes a validity question answerable:
    conjoining them would ask a prover to prove the axiom as well). ``path``
    names the edges a conversion took, ``guarantee`` is the weakest one on that
    path, and ``note`` collects the conventions those edges documented (free
    anchors, fragment limits).
    """

    term: Any
    logic: str
    axioms: Tuple[Any, ...] = ()
    guarantee: Optional[str] = "faithful"
    path: Tuple[str, ...] = ()
    note: str = ""

    def __post_init__(self):
        if isinstance(self.term, Sentence):
            raise TypeError(
                "Sentence: term is already a Sentence — pass its .term, or "
                "convert with a logic value (e.g. FOL(sentence))")
        object.__setattr__(self, "axioms", tuple(self.axioms))
        object.__setattr__(self, "path", tuple(self.path))

    def to(self, target: str, **options) -> "Sentence":
        """Convert into the logic labelled ``target`` through the registry.

        ``options`` are forwarded to the edges on the path that declare them
        (e.g. ``frame=``/``systems=`` for the modal edge, ``signature=`` for the
        sorted one); one that no edge on the path declares raises, so an option
        can never be silently ignored into a different question. Side axioms
        accumulate: those of this sentence are carried through the path as well,
        because they are terms of its own logic.
        """
        if target == self.logic:
            return self
        carried = DEFAULT_REGISTRY.translate(self.term, self.logic, target,
                                             **options)
        axioms = tuple(DEFAULT_REGISTRY.carry(a, self.logic, target, **options)
                       for a in self.axioms)
        notes = "; ".join(n for n in (self.note, carried.note) if n)
        return Sentence(
            term=carried.result, logic=target,
            axioms=axioms + carried.axioms,
            guarantee=weakest_guarantee([self.guarantee, carried.guarantee]),
            path=self.path + carried.path, note=notes)

    def with_note(self, note: str) -> "Sentence":
        """A copy with ``note`` appended — conventions a caller wants kept."""
        return replace(self, note="; ".join(n for n in (self.note, note) if n))

    def _no_operators(self, operator: str) -> None:
        raise TypeError(
            f"Sentence: {operator} is not defined on a Sentence (this one is "
            f"in logic {self.logic!r}). A Sentence is a term together with the "
            "side axioms that make it mean what it meant; building a bigger "
            "formula out of two of them is where those axioms get lost — "
            "across logics silently and wrongly, within one logic by just "
            "being dropped. Combine the .term values with the AST's own "
            "constructors and pass the union of the .axioms as premises.")

    def __and__(self, other): self._no_operators("'&'")
    def __or__(self, other): self._no_operators("'|'")
    def __invert__(self): self._no_operators("'~'")

    def __repr__(self) -> str:
        rendered = getattr(self.term, "to_unicode_str", None)
        shown = rendered() if callable(rendered) else repr(self.term)
        extra = f", {len(self.axioms)} axiom(s)" if self.axioms else ""
        return (f"Sentence[{self.logic}]({shown}{extra}, "
                f"guarantee={self.guarantee})")


@dataclass(frozen=True)
class Logic:
    """One logic in the graph, as a callable value.

    ``FOL(x)`` wraps a bare term written in classical FOL, and converts an ``x``
    that is a :class:`Sentence` in another logic — the closest honest reading of
    a cast: it either is already that logic, or there is a registered
    translation and you get the term together with its side conditions.
    """

    label: str
    description: str = ""

    def __call__(self, term: Any, **options) -> Sentence:
        if isinstance(term, Sentence):
            return term.to(self.label, **options)
        if options:
            raise TypeError(
                f"{self.label}: options {sorted(options)} apply to a "
                f"CONVERSION; wrapping a bare term takes none")
        return Sentence(term=term, logic=self.label)

    def __str__(self) -> str:
        return self.label


#: Classical first-order logic — what :func:`unicode_logic_kit.api.prove` decides.
FOL = Logic("fol", "classical first-order logic")
MSFOL = Logic("msfol", "many-sorted first-order logic (sorts are non-empty)")
MODAL = Logic("modal", "propositional modal / temporal / deontic / hybrid")
QML = Logic("qml", "quantified modal logic with a domain regime")
ALC = Logic("alc", "description-logic concepts")
DRT = Logic("drs", "discourse representation structures")
TEAM = Logic("team", "dependence / team-semantic sentences")
ESO = Logic("eso", "existential second-order logic")
FUZZY = Logic("fuzzy", "Łukasiewicz many-valued logic")

#: Every logic value by label — the labels :meth:`Sentence.to` accepts.
LOGICS = {logic.label: logic for logic in
          (FOL, MSFOL, MODAL, QML, ALC, DRT, TEAM, ESO, FUZZY)}
