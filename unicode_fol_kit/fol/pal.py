"""Public Announcement Logic (PAL): syntactic reduction of announcements.

Public announcement logic extends static modal logic with an update operator: a
truthful public announcement of ``φ`` deletes every world where ``φ`` is false, and
``[φ!]ψ`` / ``⟨φ!⟩ψ`` (see :mod:`unicode_fol_kit.fol._modal_nodes`, classes
:class:`~unicode_fol_kit.fol._modal_nodes.Announce` /
:class:`~unicode_fol_kit.fol._modal_nodes.AnnounceDiamond`) say what holds *after*
that update. :func:`reduce_announcements` implements the standard PAL result that
every announcement is ELIMINABLE: PAL over the propositional-modal fragment
interpreted here is exactly as expressive as the announcement-free base logic, via
the reduction axioms below.

Public API: :func:`reduce_announcements`.

CORRECTNESS ARGUMENT
=====================

The whole reduction rests on one invariant, proved by induction on ψ:

    (INV)   M, w ⊨ ψ^φ   IFF   M|φ, w ⊨ ψ        (for every w with M, w ⊨ φ)

— "ψ RELATIVIZED to φ, evaluated in the ORIGINAL model M, agrees with ψ evaluated
in the φ-RESTRICTED model M|φ" (:func:`unicode_fol_kit.semantics.dynamic_epistemic.announce`
builds M|φ: the submodel on the worlds satisfying φ, with every relation and the
valuation cut down to survivors). Given (INV), the announcement operators reduce
immediately from their own truth conditions
(:func:`unicode_fol_kit.semantics.kripke.satisfies_modal`'s Announce/AnnounceDiamond
cases, restated in :mod:`unicode_fol_kit.semantics.dynamic_epistemic`'s module
docstring)::

    M, w ⊨ [φ!]ψ   iff   M,w⊨φ implies M|φ,w⊨ψ   iff (INV)   M,w⊨φ implies M,w⊨ψ^φ
                   iff   M, w ⊨ (φ → ψ^φ)

    M, w ⊨ ⟨φ!⟩ψ   iff   M,w⊨φ and M|φ,w⊨ψ       iff (INV)   M,w⊨φ and M,w⊨ψ^φ
                   iff   M, w ⊨ (φ ∧ ψ^φ)

which are exactly the two clauses :func:`reduce_announcements` applies to a
top-level Announce/AnnounceDiamond node (with the inner announcement-free ψ, φ
already produced by pre-reducing everything below them — "innermost first").

Proof of (INV), by structural induction on ψ (each case implements the matching
standard PAL reduction axiom):

* ``ψ = p`` (atom): p^φ = p. p's truth value only depends on the valuation at w,
  which M|φ COPIES verbatim from M for every survivor w — so M,w⊨p iff M|φ,w⊨p.
* ``ψ = ¬χ``, ``χ₁∘χ₂`` (∘ ∈ {∧,∨,→,↔,⊕}): the classical connectives commute with
  restriction (M|φ's valuation at w is M's, unchanged) and with the induction
  hypothesis applied to χ / χ₁ / χ₂ at the SAME world w, which — because w ⊨ φ
  throughout this induction — is still a world of M|φ. So the classical clauses
  relativize by simply relativizing their immediate subformulas: (¬χ)^φ=¬χ^φ,
  (χ₁∘χ₂)^φ = χ₁^φ ∘ χ₂^φ.
* ``ψ = K_a χ`` (and identically B_a / Say_a / Want_a / □ / Ⓞ, every UNIVERSAL —
  "box" — modality): M|φ,w ⊨ K_a χ iff χ holds at every "K:a"-successor of w that
  SURVIVED the restriction (M|φ only keeps edges between survivors) — i.e. at
  every successor v of w in M with v⊨φ. By the induction hypothesis (applicable
  at each such v, since v⊨φ), that is M,v⊨χ^φ. So the whole condition is: for
  every M-successor v of w, v⊨φ implies M,v⊨χ^φ — i.e. M,w ⊨ K_a(φ → χ^φ). Hence
  (K_aχ)^φ = K_a(φ → χ^φ) (identically for B_a, Say_a, Want_a, □, Ⓞ, each over its
  own relation).
* ``ψ = ◇χ`` (and identically Ⓟ, every EXISTENTIAL — "diamond" — modality): dual
  reasoning — M|φ,w ⊨ ◇χ iff SOME surviving successor v (so v⊨φ) has M|φ,v⊨χ, iff
  (by the induction hypothesis) M,v⊨χ^φ — i.e. some M-successor v has v⊨φ AND
  M,v⊨χ^φ, i.e. M,w ⊨ ◇(φ ∧ χ^φ). Hence (◇χ)^φ = ◇(φ ∧ χ^φ) (identically Ⓟ).
* ``ψ = [χ!]ω`` (a NESTED announcement): reduced FIRST, entirely on its own —
  ``([χ!]ω)^φ`` is defined as ``ρ^φ`` where ``ρ = reduce_announcements([χ!]ω)`` is
  the (announcement-free) result of reducing the inner announcement by itself.
  This is sound because reduce_announcements is truth-preserving in M (it is
  exactly this same theorem, applied one level down: M,v⊨[χ!]ω iff M,v⊨ρ, at
  every world v, by structural induction on the announcement itself) — so
  substituting ρ for [χ!]ω anywhere and THEN relativizing by φ computes the same
  (INV) as relativizing [χ!]ω directly would, if the latter were defined. This
  is the "innermost-first" rule: :func:`reduce_announcements` eliminates deeper
  announcements before an enclosing one is relativized, so RELATIVIZE (the
  induction above) is only ever asked to handle an announcement-free ψ.

Where the induction BREAKS — REJECTED, not silently mishandled:

* Temporal closure / one-step operators (Ⓖ Ⓕ Ⓝ Ⓤ ⒣ ⒫ ⒴ ⒮): the induction step for
  a box/diamond modality above crucially used that M|φ's accessibility relation is
  M's relation RESTRICTED to survivors — a ONE-STEP fact. Always/Eventually/Until
  (and their past duals) quantify over the REFLEXIVE-TRANSITIVE CLOSURE of the
  one-step relation; the closure of the RESTRICTED relation is in general a
  STRICT SUBSET of the RESTRICTION of the closure (a path through M can visit a
  ¬φ-world and come back to φ-worlds; M|φ has no such path, since it never
  contains the ¬φ-world at all, but M's closure "sees past" it) — "restriction of
  a closure relation is not the closure of the restriction". So no box/diamond-style
  axiom is sound for these operators under an announcement, including the
  one-step Next: this module rejects it too, deliberately more conservative than
  a operator-by-operator soundness argument might require, rather than risk
  publishing an axiom that has not been verified.
* Would / Might (Lewis counterfactuals): interpreted over a similarity ordering
  of worlds (Lewis spheres), not an accessibility relation — restriction has no
  defined action on a sphere system in this codebase, so relativizing them is
  undefined, not merely unproven.
* Nominal / At (hybrid H(@)): a nominal names EXACTLY ONE world; announcement
  restriction can delete that very world (if it fails φ), after which the
  nominal names nothing — undefined, not merely unproven.
* Quantifier / SortedQuantifier (first-order): :func:`satisfies_modal` interprets
  these ACTUALISTICALLY over a per-world domain ``D_w``; :func:`announce`'s model
  restriction never updates ``domains``, so relativizing a quantifier would be
  reasoning about domains the restriction does not touch — out of scope here
  (the propositional/ground modal fragment this reduction targets never needs
  one anyway).

Any of the above found ANYWHERE inside the ψ (or φ) being relativized — however
deeply buried — raises :class:`NotImplementedError` identifying which family and
pointing at :func:`unicode_fol_kit.semantics.dynamic_epistemic.announce` /
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal` for direct, MODEL-level
(rather than syntactic) evaluation, which handles Announce/AnnounceDiamond
directly and has no such restriction.

EXPORTS: :func:`reduce_announcements` is the sanctioned route from a PAL formula to
every classical modal back-end. Since Announce/AnnounceDiamond nodes themselves
reject to_z3/to_prover9/to_tptp (and the Isabelle/THF/Isabelle-Isabelle embeddings
in :mod:`unicode_fol_kit.hol.isabelle_modal` / :mod:`unicode_fol_kit.hol.thf_modal`
have no case for them either, so they raise the same generic "unsupported node
type" error every other out-of-scope construct does), a PAL formula bound for any
of those back-ends — or for :mod:`unicode_fol_kit.atp.modal_tableau` (which applies
this reduction itself, as a pre-pass, on every public entry point) — MUST be
reduced first: ``to_isabelle_modal(reduce_announcements(formula))``, etc.
"""

from .nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Would, Might,
    Nominal, At,
    Quantifier, SortedQuantifier,
)
from ._modal_nodes import Announce, AnnounceDiamond

__all__ = ["reduce_announcements"]


# Node types with no sound relativization rule (see the module docstring's
# "Where the induction BREAKS" section) — grouped by WHY, so the raised message
# names the exact reason rather than a generic "unsupported".
_TEMPORAL_UNDER_ANNOUNCEMENT = (Always, Eventually, Next, Until,
                                Historically, Once, Previous, Since)
_TEMPORAL_MSG = (
    "pal.reduce_announcements: {name} (a temporal operator) cannot be "
    "relativized under an announcement: Always/Eventually/Until (and their past "
    "duals Historically/Once/Since, and the one-step Next) quantify over the "
    "REFLEXIVE-TRANSITIVE CLOSURE of the one-step temporal relation, and "
    "restriction of a CLOSURE relation is not the closure of the restriction — "
    "the box/diamond reduction axiom this module uses for K_a/B_a/□/Ⓞ/◇/Ⓟ is "
    "UNSOUND here. Evaluate the announcement directly instead: "
    "unicode_fol_kit.semantics.kripke.satisfies_modal (which interprets "
    "Announce/AnnounceDiamond via the restricted-model semantics of "
    "unicode_fol_kit.semantics.dynamic_epistemic.announce) has no such "
    "restriction."
)
_COUNTERFACTUAL_MSG = (
    "pal.reduce_announcements: {name} (a Lewis counterfactual, □→/◇→) cannot be "
    "relativized under an announcement: it is evaluated over a similarity "
    "ordering of worlds (Lewis spheres), not an accessibility relation, and "
    "announcement restriction has no defined action on a sphere system in this "
    "codebase. Evaluate the announcement directly with "
    "unicode_fol_kit.semantics.kripke.satisfies_modal instead."
)
_HYBRID_MSG = (
    "pal.reduce_announcements: {name} (a hybrid-logic construct, a nominal or "
    "@) cannot be relativized under an announcement: a nominal names EXACTLY "
    "ONE world, and announcement restriction can delete that very world (if it "
    "fails the announcement), after which the nominal would name nothing. "
    "Evaluate the announcement directly with "
    "unicode_fol_kit.semantics.kripke.satisfies_modal instead."
)
_QUANTIFIER_MSG = (
    "pal.reduce_announcements: {name} (a first-order quantifier) cannot be "
    "relativized under an announcement: satisfies_modal interprets object "
    "quantifiers actualistically over a per-world domain D_w, and "
    "dynamic_epistemic.announce's model restriction never updates the domains "
    "map, so there is no sound reduction axiom for a quantifier here. Evaluate "
    "the announcement directly with unicode_fol_kit.semantics.kripke.satisfies_modal "
    "instead (with domains= set on the KripkeModel)."
)


def _relativize(psi: Node, phi: Node) -> Node:
    """Compute ψ^φ (ψ relativized to the announced φ) — see the module docstring's
    CORRECTNESS ARGUMENT for the invariant this implements and its proof.

    Precondition: ψ is already announcement-free (the caller pre-reduces every
    nested Announce/AnnounceDiamond bottom-up before relativizing), and φ is
    likewise announcement-free.
    """
    if isinstance(psi, Atom):
        return psi
    if isinstance(psi, Not):
        return Not(_relativize(psi.formula, phi))
    if isinstance(psi, And):
        return And(_relativize(psi.left, phi), _relativize(psi.right, phi))
    if isinstance(psi, Or):
        return Or(_relativize(psi.left, phi), _relativize(psi.right, phi))
    if isinstance(psi, Xor):
        return Xor(_relativize(psi.left, phi), _relativize(psi.right, phi))
    if isinstance(psi, Implies):
        return Implies(_relativize(psi.left, phi), _relativize(psi.right, phi))
    if isinstance(psi, Iff):
        return Iff(_relativize(psi.left, phi), _relativize(psi.right, phi))

    # --- box-wise (universal) modalities: (Xψ)^φ = X(φ → ψ^φ) ---
    if isinstance(psi, Knows):
        return Knows(psi.agent, Implies(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Believes):
        return Believes(psi.agent, Implies(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Says):
        return Says(psi.agent, Implies(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Wants):
        return Wants(psi.agent, Implies(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Box):
        return Box(Implies(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Obligatory):
        return Obligatory(Implies(phi, _relativize(psi.formula, phi)))

    # --- diamond-wise (existential) modalities: (Xψ)^φ = X(φ ∧ ψ^φ) ---
    if isinstance(psi, Diamond):
        return Diamond(And(phi, _relativize(psi.formula, phi)))
    if isinstance(psi, Permitted):
        return Permitted(And(phi, _relativize(psi.formula, phi)))

    # --- nested announcement: eliminate it FIRST (on its own), THEN relativize
    # the announcement-free result — "innermost first" (module docstring). Only
    # reachable if a caller invokes _relativize directly on un-pre-reduced input;
    # reduce_announcements itself always pre-reduces, so this never fires there.
    if isinstance(psi, (Announce, AnnounceDiamond)):
        return _relativize(reduce_announcements(psi), phi)

    # --- no sound rule: reject with a precise, family-specific explanation ---
    if isinstance(psi, _TEMPORAL_UNDER_ANNOUNCEMENT):
        raise NotImplementedError(_TEMPORAL_MSG.format(name=type(psi).__name__))
    if isinstance(psi, (Would, Might)):
        raise NotImplementedError(_COUNTERFACTUAL_MSG.format(name=type(psi).__name__))
    if isinstance(psi, (Nominal, At)):
        raise NotImplementedError(_HYBRID_MSG.format(name=type(psi).__name__))
    if isinstance(psi, (Quantifier, SortedQuantifier)):
        raise NotImplementedError(_QUANTIFIER_MSG.format(name=type(psi).__name__))

    raise NotImplementedError(
        f"pal.reduce_announcements: no relativization rule for "
        f"{type(psi).__name__} under an announcement.")


def _reduce(node: Node) -> Node:
    """Bottom-up worker for :func:`reduce_announcements`: reduce every child
    first (innermost first), then eliminate a top-level Announce/AnnounceDiamond.
    """
    if isinstance(node, (Announce, AnnounceDiamond)):
        phi = _reduce(node.announcement)
        psi = _reduce(node.formula)
        relativized = _relativize(psi, phi)
        if isinstance(node, Announce):
            return Implies(phi, relativized)
        return And(phi, relativized)
    # Not an announcement: recurse structurally into every Node-valued field
    # (Node.map_children — the generic engine every other structural pass in
    # this codebase uses), so an announcement buried under ANY other
    # construct (∧, K_a, Ⓖ, ∀x, …) is still found and eliminated, as long as
    # it does not itself end up inside a relativization that rejects it.
    return node.map_children(_reduce)


def reduce_announcements(formula: Node) -> Node:
    """Eliminate every :class:`Announce` / :class:`AnnounceDiamond` in ``formula``,
    returning an equivalent announcement-free modal formula.

    Applies the standard PAL reduction axioms — ``[φ!]ψ ≡ φ → ψ^φ`` and
    ``⟨φ!⟩ψ ≡ φ ∧ ψ^φ`` — bottom-up, so a NESTED announcement (whether inside the
    announcement or the post-condition of an outer one) is reduced before the
    outer one is relativized. See the module docstring for the full correctness
    argument (the relativization invariant ``M,w⊨ψ^φ iff M|φ,w⊨ψ`` and its proof)
    and for exactly which constructs raise :class:`NotImplementedError` when they
    occur under an announcement's scope (temporal closure/one-step operators,
    Lewis counterfactuals, hybrid nominals/@, and first-order quantifiers) —
    always because the reduction is UNSOUND or UNDEFINED there, never silently
    approximated.

    A formula with no announcement anywhere is returned as a structurally equal
    (but freshly rebuilt) copy — a safe no-op pass. Idempotent: reducing an
    already announcement-free formula returns an equal formula unchanged.
    """
    return _reduce(formula)
