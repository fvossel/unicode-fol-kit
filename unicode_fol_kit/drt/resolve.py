"""Accessibility-respecting pronoun resolution (unicode_fol_kit.drt.resolve).

This is explicitly NOT an NLP guesser: it has no gender/number agreement, no world
knowledge, and no salience model. What it DOES do — and does precisely — is apply the
classical Kamp/Reyle DISCOURSE STRUCTURE constraint on pronoun resolution: a pronoun can
only corefer with a referent that is ACCESSIBLE to it (see the accessibility relation in
:mod:`unicode_fol_kit.drt.nodes`'s module docstring), and among the accessible candidates,
the "closest" one is preferred — the classical RIGHT-TO-LEFT (most recently mentioned)
default reading.

Marking a pronoun
------------------
The caller marks a referent as an unresolved pronoun with the reserved unary condition
``Pred(PRONOUN, (ref,))`` (``PRONOUN = "PRONOUN"``), placed in the SAME box that declares
``ref`` — exactly like any other condition, using the ordinary five-variant condition
vocabulary from :mod:`unicode_fol_kit.drt.nodes` (no sixth "Condition" subtype is added
for this — a reserved predicate name is enough and keeps the classical Kamp/Reyle
condition inventory exactly as-is). :func:`resolve_anaphora` finds every such marker
(or just the ones named in ``pronouns``, if given) and REPLACES it with
``Eq(ref, antecedent)`` — ``ref`` stays a bound referent in its box (so the standard
translation in :mod:`unicode_fol_kit.drt.export` still existentially/universally quantifies
it, exactly as any other referent), and the added equality forces it to denote the same
individual as its antecedent once translated to FOL.

Recency ranking
------------------
:func:`~unicode_fol_kit.drt.nodes.walk_boxes` gives each box its accessible referents as an
ORDERED sequence of "layers", outermost first, the box's own referents last. A candidate's
recency rank is ``(layer_index, position_within_that_layer)`` — read: prefer the INNERMOST
layer (the pronoun's own box beats an ancestor's, which beats a more distant ancestor's);
within one layer (one box's own referents tuple), prefer the LATER position (the rightmost,
i.e. most recently written, referent in that box's own list). This is a total order with no
ties possible (two distinct referents can never share both coordinates), so "most recent"
always has a single well-defined answer whenever there is at least one candidate — see
"Ambiguity policy" below for what "ambiguous" means instead. Note that within a single box,
EVERY other referent in that box counts as a same-layer candidate regardless of whether it
was written before or after the pronoun in that box's referent tuple — DRT's own theory
treats a box's referents as an unordered set, so intra-box "before/after" is not a
structural distinction; only the WRITTEN tuple position (used purely as a tie-break, not as
an accessibility criterion) makes recency well-defined at that granularity.

Ambiguity policy
-------------------
* Zero accessible candidates: always :class:`ValueError` (there is nothing to resolve to,
  strict or not).
* Exactly one accessible candidate: resolved automatically, regardless of ``strict`` — this
  is the unambiguous case, no heuristic guessing involved.
* Two or more accessible candidates: this module will not silently pick one FOR you (it is
  not a guesser) — with ``strict=True`` (the default) it raises :class:`ValueError` listing
  every candidate, most-recent first, so the caller can disambiguate explicitly. With
  ``strict=False`` it accepts the recency heuristic above and records which referent it
  picked (:attr:`Resolution.ambiguous` is ``True`` in this case, so the choice is always
  visible in the returned report, never silently made).
"""

from dataclasses import dataclass
from typing import Dict, Optional, Sequence, Tuple

from .nodes import DRS, Pred, Eq, Neg, Impl, Or, walk_boxes

__all__ = ["PRONOUN", "Resolution", "ResolutionReport", "resolve_anaphora"]

PRONOUN = "PRONOUN"


@dataclass(frozen=True)
class Resolution:
    """The outcome of resolving one pronoun.

    ``candidates`` lists every accessible referent that was considered, MOST RECENT
    FIRST (so ``candidates[0] == antecedent`` always); ``ambiguous`` is True iff there
    was more than one (i.e. ``antecedent`` was chosen by the recency heuristic rather
    than being the sole option).
    """

    referent: str
    antecedent: str
    candidates: Tuple[str, ...]
    ambiguous: bool

    def to_dict(self) -> dict:
        return {"referent": self.referent, "antecedent": self.antecedent,
                "candidates": list(self.candidates), "ambiguous": self.ambiguous}


@dataclass(frozen=True)
class ResolutionReport:
    """The result of :func:`resolve_anaphora`: the resolved DRS (every processed
    ``PRONOUN`` marker replaced by an ``Eq``) plus one :class:`Resolution` per pronoun,
    in the order they were resolved."""

    drs: DRS
    resolutions: Tuple[Resolution, ...]

    def to_dict(self) -> dict:
        return {"drs": self.drs.to_dict(),
                "resolutions": [r.to_dict() for r in self.resolutions]}


def _recency_sorted_candidates(layers, pronoun: str):
    """Every OTHER referent visible in ``layers``, most-recent-first (see the module
    docstring's recency ranking)."""
    ranked = []
    for i, layer in enumerate(layers):
        for j, name in enumerate(layer):
            if name != pronoun:
                ranked.append((i, j, name))
    ranked.sort(key=lambda t: (t[0], t[1]), reverse=True)
    return tuple(name for _, _, name in ranked)


def _replace_markers(box: DRS, replacements: Dict[str, Eq]) -> DRS:
    """Rebuild ``box`` with every resolved ``PRONOUN`` marker condition replaced by its
    ``Eq``, recursing into every nested sub-DRS (Neg/Impl/Or operands)."""
    new_conditions = []
    for cond in box.conditions:
        if (isinstance(cond, Pred) and cond.name == PRONOUN
                and cond.args[0] in replacements):
            new_conditions.append(replacements[cond.args[0]])
        elif isinstance(cond, Neg):
            new_conditions.append(Neg(_replace_markers(cond.drs, replacements)))
        elif isinstance(cond, Impl):
            new_conditions.append(Impl(_replace_markers(cond.antecedent, replacements),
                                       _replace_markers(cond.consequent, replacements)))
        elif isinstance(cond, Or):
            new_conditions.append(Or(_replace_markers(cond.left, replacements),
                                     _replace_markers(cond.right, replacements)))
        else:
            new_conditions.append(cond)
    return DRS(box.referents, tuple(new_conditions))


def resolve_anaphora(drs: DRS, pronouns: Optional[Sequence[str]] = None, *,
                     strict: bool = True) -> ResolutionReport:
    """Resolve every ``PRONOUN``-marked referent in ``drs`` (see the module docstring).

    ``drs.validate()`` is called first (a pronoun's antecedent search is only meaningful
    over an already-accessibility-valid tree). ``pronouns``, if given, restricts
    resolution to those referent names (each MUST carry a ``Pred(PRONOUN, (ref,))``
    marker somewhere in ``drs``, else :class:`ValueError`); ``None`` (the default)
    resolves every marker found, in the order :func:`~unicode_fol_kit.drt.nodes.walk_boxes`
    discovers them (pre-order, deterministic).

    Raises:
        ValueError: a named pronoun has no marker; a pronoun has zero accessible
            candidates; or (with ``strict=True``, the default) a pronoun has two or more
            accessible candidates (message lists them, most recent first).
    """
    drs.validate()
    boxes = list(walk_boxes(drs))

    marker_boxes: Dict[str, tuple] = {}
    for box, layers in boxes:
        for cond in box.conditions:
            if isinstance(cond, Pred) and cond.name == PRONOUN:
                if len(cond.args) != 1:
                    raise ValueError(
                        f"resolve_anaphora: a {PRONOUN} marker must have exactly one "
                        f"argument, got {cond.args!r}")
                ref = cond.args[0]
                if ref in marker_boxes:
                    raise ValueError(
                        f"resolve_anaphora: referent {ref!r} has more than one "
                        f"{PRONOUN} marker")
                marker_boxes[ref] = (box, layers)

    if pronouns is None:
        targets = list(marker_boxes)
    else:
        targets = list(pronouns)
        for p in targets:
            if p not in marker_boxes:
                raise ValueError(
                    f"resolve_anaphora: no {PRONOUN} marker found for referent {p!r}")

    resolutions = []
    replacements: Dict[str, Eq] = {}
    for p in targets:
        box, layers = marker_boxes[p]
        candidates = _recency_sorted_candidates(layers, p)
        if not candidates:
            raise ValueError(
                f"resolve_anaphora: pronoun {p!r} has no accessible referent to bind to.")
        ambiguous = len(candidates) > 1
        if ambiguous and strict:
            raise ValueError(
                f"resolve_anaphora: pronoun {p!r} has {len(candidates)} accessible "
                f"candidates {candidates} (most recent first) — ambiguous under "
                f"strict=True. Pass strict=False to accept the most-recent heuristic, "
                f"or disambiguate by hand.")
        antecedent = candidates[0]
        resolutions.append(Resolution(p, antecedent, candidates, ambiguous))
        replacements[p] = Eq(p, antecedent)

    return ResolutionReport(_replace_markers(drs, replacements), tuple(resolutions))
