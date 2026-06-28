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
