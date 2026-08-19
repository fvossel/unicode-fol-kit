"""The ``drt`` subpackage — Discourse Representation Theory (Kamp & Reyle).

Single-sentence FOL cannot express **cross-sentence anaphora** ("A farmer owns a donkey.
He beats it.") or **donkey sentences** ("Every farmer who owns a donkey beats it.") — the
pronoun's antecedent lives in a different sentence/clause than the pronoun, and the donkey
sentence's indefinite ("a donkey") gets a UNIVERSAL reading once it sits in a conditional's
antecedent. Discourse Representation Theory (Kamp & Reyle, *From Discourse to Logic*, 1993)
is the classical fix: represent a discourse as a **box** of referents + conditions, with a
structural ACCESSIBILITY relation deciding which referents a pronoun (or a later sentence)
can see, then give the whole box a first-order **standard translation** that gets the
donkey reading right for free.

This subpackage implements exactly that core, and nothing beyond it — see "Scope" below.

Modules
---------
* :mod:`unicode_fol_kit.drt.nodes` — the ``DRS`` data model (``referents``, ``conditions``)
  and its condition variants — the five classical ones (``Pred``, ``Eq``, ``Neg``, ``Impl``, ``Or``) plus the 0.24.0 plural-DRT pair (``Card``, ``Part``) —
  plus the accessibility checker :meth:`~unicode_fol_kit.drt.nodes.DRS.validate`.
* :mod:`unicode_fol_kit.drt.parser` — :func:`~unicode_fol_kit.drt.parser.parse_drs` for a
  compact hand-written box notation, and
  :func:`~unicode_fol_kit.drt.parser.parse_sbn` for a precisely documented SUBSET of the
  Parallel Meaning Bank's Sequence Box Notation (SBN) — PMB is the natural "found data"
  source of real DRSs, so SBN is this subpackage's interchange FROM format.
* :mod:`unicode_fol_kit.drt.resolve` — :func:`~unicode_fol_kit.drt.resolve.resolve_anaphora`,
  accessibility-respecting pronoun resolution (right-to-left / most-recent preference; not
  an NLP guesser — see that module's docstring).
* :mod:`unicode_fol_kit.drt.export` — :func:`~unicode_fol_kit.drt.export.drs_to_fol`, the
  standard translation into the kit's own FOL AST
  (:mod:`unicode_fol_kit.fol.nodes`), ready for ``unicode_fol_kit.api.prove`` /
  ``unicode_fol_kit.api.check``.

Quick usage — the classic donkey sentence, entailed from its premises via Z3::

    from unicode_fol_kit import drt, api

    rule = drt.parse_drs(
        "[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]")
    facts = drt.parse_drs("[ | Farmer(john), Donkey(daisy), Owns(john, daisy)]")
    goal = drt.parse_drs("[ | Beats(john, daisy)]")

    v = api.prove(drt.drs_to_fol(goal),
                  [drt.drs_to_fol(rule), drt.drs_to_fol(facts)])
    assert v.status == "proved"

Scope (deliberately tight — this is a single kit subpackage, not a discourse-parsing system)
------------------------------------------------------------------------------------------------
IN scope: the classical propositional DRS core (five condition variants), box-notation and
SBN-subset parsing, accessibility-respecting explicit-marker pronoun resolution, and the
standard translation to FOL.

OUT of scope, refused loudly rather than silently approximated:

* multi-paragraph discourse machinery (discourse segmentation, rhetorical relations,
  coreference chains spanning many sentences) — this subpackage parses and represents ONE
  assembled DRS (one sentence, or a small hand-built discourse) per call;
* event semantics beyond plain predicates (no Davidsonian event variables are threaded
  through automatically, no thematic-role ontology beyond "whatever role name the input
  uses") — a ``Pred``'s arguments are exactly what the box notation or SBN input says;
* presupposition projection (definites, factives, "again", ...) — DRT's presupposition
  extensions (van der Sandt's binding theory and successors) are a substantial theory of
  their own and are not implemented here; a presupposition trigger in an SBN/box-notation
  input is just an ordinary predicate as far as this subpackage is concerned, with no
  special accommodation/binding behaviour.

See each module's docstring for the precise grammar/semantics decisions and their sources.
"""

from .nodes import (
    DRS, Card, CARD_OPS, Condition, Pred, Eq, Neg, Impl, Or, Part,
    is_referent, is_predicate_name, is_constant_name, walk_boxes,
)
from .parser import (
    parse_drs, DRSSyntaxError,
    parse_sbn, SBNSyntaxError, SBNMapping,
)
from .resolve import resolve_anaphora, Resolution, ResolutionReport, PRONOUN
from .export import drs_to_fol

__all__ = [
    "DRS", "Condition", "Pred", "Eq", "Neg", "Impl", "Or", "Card", "Part",
    "CARD_OPS",
    "is_referent", "is_predicate_name", "is_constant_name", "walk_boxes",
    "parse_drs", "DRSSyntaxError",
    "parse_sbn", "SBNSyntaxError", "SBNMapping",
    "resolve_anaphora", "Resolution", "ResolutionReport", "PRONOUN",
    "drs_to_fol",
]
