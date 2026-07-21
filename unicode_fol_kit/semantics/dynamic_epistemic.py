"""Public announcement logic (PAL) — dynamic epistemic model update.

Static epistemic logic (``Knows`` over a Kripke model) describes *what agents know*;
**public announcement logic** adds the dynamics: a truthful public announcement of
``φ`` removes every world where ``φ`` is false, so the agents' knowledge changes. The
announcement operator ``[φ!]ψ`` ("after announcing φ, ψ holds") has the truth
condition::

    M, w ⊨ [φ!] ψ   iff   M, w ⊨ φ  implies  M|φ, w ⊨ ψ

where ``M|φ`` is :func:`announce` — ``M`` restricted to its ``φ``-worlds (relations and
valuation cut down to the survivors). The dual ``⟨φ!⟩ψ`` ("φ is true and after
announcing it ψ holds") is ``φ ∧ M|φ,w ⊨ ψ``. Announcements compose, so iterated
updates and the Moore-sentence phenomenon (announcing ``p ∧ ¬K_a p`` makes it false)
fall straight out.

Built on :func:`unicode_fol_kit.semantics.kripke.satisfies_modal`; the announced and
post formulas are ordinary (propositional, epistemic, …) modal formulas.

``[φ!]ψ`` / ``⟨φ!⟩ψ`` ALSO exist as first-class AST nodes —
:class:`~unicode_fol_kit.fol._modal_nodes.Announce` /
:class:`~unicode_fol_kit.fol._modal_nodes.AnnounceDiamond` (parsed by
``MSFLParser(modal=True)`` from exactly this surface syntax). Two independent, and
independently useful, routes evaluate them:

* :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal` interprets an
  ``Announce``/``AnnounceDiamond`` node DIRECTLY, by calling :func:`announce` (this
  module) internally to build ``M|φ`` — i.e. this module is satisfies_modal's own
  implementation of the PAL case, not a separate parallel semantics.
* :func:`unicode_fol_kit.fol.pal.reduce_announcements` ELIMINATES an
  ``Announce``/``AnnounceDiamond`` node SYNTACTICALLY, rewriting it to an
  announcement-free modal formula via the standard PAL reduction axioms — the
  route into every other reasoning tool in the kit (:mod:`unicode_fol_kit.atp.modal_tableau`,
  the Isabelle/THF embeddings, …), none of which know about Announce/AnnounceDiamond
  directly. ``satisfies_modal`` (hence this module's :func:`announce` /
  :func:`box_announce` / :func:`diamond_announce`) is the ORACLE
  ``fol.pal.reduce_announcements`` is differentially tested against — see that
  module's docstring for the correctness argument connecting the two.

:func:`box_announce` / :func:`diamond_announce` remain useful on their own for
MODEL-level (rather than AST-level) PAL reasoning — e.g. stepping an existing
:class:`~unicode_fol_kit.semantics.kripke.KripkeModel` through a sequence of
announcements programmatically, with no ``Announce`` node ever constructed.

Public API: :func:`announce`, :func:`box_announce`, :func:`diamond_announce`.
"""

from typing import Any

from ..fol.nodes import Node
from .kripke import KripkeModel, satisfies_modal


def announce(model: KripkeModel, formula: Node) -> KripkeModel:
    """Return ``model`` updated by a truthful public announcement of ``formula``.

    The result keeps exactly the worlds where ``formula`` is true (under
    :func:`satisfies_modal`); every relation is restricted to those survivors and the
    valuation (and per-world object domains, if any) likewise. Inputs are not mutated.
    """
    survivors = frozenset(w for w in model.worlds if satisfies_modal(formula, model, w))
    relations = {
        name: {(a, b) for (a, b) in edges if a in survivors and b in survivors}
        for name, edges in model.relations.items()
    }
    valuation = {w: set(model.atoms_true_at(w)) for w in survivors}
    domains = None
    if model.domains is not None:
        domains = {w: set(model.domains.get(w, frozenset())) for w in survivors}
    return KripkeModel(survivors, relations, valuation, domains=domains)


def box_announce(model: KripkeModel, world: Any, announcement: Node, post: Node) -> bool:
    """Return whether ``model, world ⊨ [announcement!] post`` (PAL box).

    Vacuously true when the announcement is false at ``world`` (an untruthful
    announcement is not made); otherwise ``post`` must hold at ``world`` in the
    updated model :func:`announce`.
    """
    if not satisfies_modal(announcement, model, world):
        return True
    updated = announce(model, announcement)
    return satisfies_modal(post, updated, world)


def diamond_announce(model: KripkeModel, world: Any, announcement: Node, post: Node) -> bool:
    """Return whether ``model, world ⊨ ⟨announcement!⟩ post`` (PAL diamond).

    True iff the announcement is truthful at ``world`` **and** ``post`` then holds at
    ``world`` in the updated model — the dual of :func:`box_announce`.
    """
    if not satisfies_modal(announcement, model, world):
        return False
    updated = announce(model, announcement)
    return satisfies_modal(post, updated, world)
