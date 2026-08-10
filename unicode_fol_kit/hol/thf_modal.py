"""Full-family modal THF export — a Benzmüller-style higher-order shallow embedding.

This module extends :func:`unicode_fol_kit.fol.qml.to_thf_modal` (which only handles
the *alethic* ``□`` / ``◇`` fragment plus object quantifiers and **raises** on the
other modalities) to the **full modal family** the toolkit's AST can express:

- alethic        ``□φ`` / ``◇φ``                         over relation ``r``;
- epistemic      ``K_a φ``  (``Knows(agent, φ)``)        over an AGENT-INDEXED ``rk``;
- doxastic       ``B_a φ``  (``Believes(agent, φ)``)     over an AGENT-INDEXED ``rb``;
- assertive      ``Say_a φ`` (``Says(agent, φ)``)        over an AGENT-INDEXED ``rs``;
- bouletic       ``Want_a φ`` (``Wants(agent, φ)``)      over an AGENT-INDEXED ``rw``;
- deontic        ``Oφ`` / ``Pφ``                         over a SERIAL relation ``d``;
- temporal       ``Gφ`` / ``Fφ`` / ``Xφ``               over ``t`` / ``tnext``, with the
  past mirrors ``⒣`` / ``⒫`` / ``⒴`` over the CONVERSE relations and strong
  ``Ⓤ`` / ``⒮`` as impredicative least fixpoints (``muntil`` / ``msince``);
- hybrid         nominals ``i`` and ``@i φ``             as ``mu`` world constants.

It is a genuine higher-order shallow embedding (SSE): a modal proposition is a
function ``mu > $o`` (world → bool), the modalities are λ-lifted quantifiers over the
relevant accessibility relation, and object quantifiers are ``existsAt``-guarded
(actualist). The emitted THF problem is **complete and self-contained** — type
declarations, every lifted operator, frame axioms (per relation where relevant),
domain axioms, and the conjecture ``mvalid @ ⟨formula⟩`` — ready for a higher-order
ATP (Leo-III, Satallax). As elsewhere in the toolkit, this module only *emits* the
problem; it does **not** run any prover.

Faithfulness to :func:`unicode_fol_kit.semantics.kripke.satisfies_modal`:

- epistemic/doxastic accessibility is **agent-indexed**. The agent of ``Knows`` /
  ``Believes`` is a first-class TERM (Variable or Constant). In THF it becomes a real
  ``$i`` argument of the relation: ``rk : $i > mu > mu > $o`` and
  ``mknows = ^[A:$i, Phi:mu>$o, W:mu] : ![V:mu] : (rk @ A @ W @ V) => Phi @ V``. A bound
  object variable in agent position (``∀x (Student(x) → K_x φ)``) is bound by the
  embedding's ``mforall`` (which binds an ``$i`` variable), so it correctly quantifies
  over agents — exactly mirroring ``satisfies_modal``'s per-agent ``"K:"+agent`` /
  ``"B:"+agent`` relations. Named agents become ordinary ``$i`` constants (the same
  individual sort as object-quantifier variables), so an agent can also be an object.
- deontic ``O`` / ``P`` are a box / diamond over a **serial** relation ``d`` (Standard
  Deontic Logic, KD), matching the evaluator's serial ``"deontic"`` relation; the
  serial axiom is always emitted for ``d``.
- temporal ``G`` / ``F`` / ``X`` are box / diamond / box over ``t`` / ``tnext`` — but
  **note** the one-step-vs-closure caveat below.
- equality ``=`` / ``≠`` is an **uninterpreted, world-relativized** predicate (rendered
  via the ``feq`` / ``fneq`` aliases), NOT primitive HOL identity — identical to
  ``to_thf_modal`` and to ``satisfies_modal``.

CAVEAT — temporal closure. ``satisfies_modal`` reads ``G``/``F`` over the
*reflexive-transitive closure* of the temporal relation, and ``X`` over the immediate
successors. A first-order / higher-order shallow embedding cannot express transitive
closure (it is not first-order definable). This module therefore embeds:

- ``Xφ`` as a box over the **one-step** relation ``tnext`` — faithful to
  ``satisfies_modal`` on the *universal* "all next states" reading of ``Next``;
- ``Gφ`` / ``Fφ`` as box / diamond over ``t`` **made reflexive and transitive** by the
  emitted ``t_refl`` / ``t_trans`` frame axioms. On a frame whose ``t`` is already its
  own reflexive-transitive closure the embedding coincides with the evaluator; in
  general the embedding's ``G``/``F`` quantify over the *transitive closure of the
  emitted ``t``*, which is the standard SSE rendering of LTL ``G``/``F`` but is only an
  **approximation** of ``satisfies_modal``'s closure over the caller's raw temporal
  edges. ``Until`` / ``Since`` **are supported**: TH0 quantifies over predicates, so
  strong Until/Since embed directly as the impredicative Knaster–Tarski least
  fixpoints ``muntil`` / ``msince`` over the one-step ``tnext`` — the same least
  fixpoint Isabelle's ``inductive muntil`` compiles to.

  The two temporal relations are **linked** by the emitted ``tnext_in_t`` inclusion
  axiom ``![W,V]: (tnext @ W @ V) => (t @ W @ V)``. In ``satisfies_modal`` ``X`` reads
  the immediate successors of the *single* ``"temporal"`` relation while ``G``/``F``
  read its reflexive-transitive closure, so every one-step ``X``-successor is reachable
  by ``G``/``F``; the inclusion axiom reproduces exactly that containment in the
  embedding. Without it ``Gφ→Xφ`` — valid for the evaluator — was a non-theorem of the
  emitted problem (``t`` and ``tnext`` were unconstrained relative to each other); with
  it ``Gφ→Xφ`` (and ``Xφ→Fφ`` wherever the evaluator agrees) is now a theorem of the
  embedding.

Cross-family bridges (``bridges=``). ``frame=`` and ``systems=`` each constrain ONE
relation; a *bridge* relates two relations of different families and is therefore a
separate, opt-in option — ``knowledge_implies_belief`` (``K_a φ → B_a φ``, condition
``rb ⊆ rk``, axiom ``rb_in_rk``), ``sincerity`` (``Say_a φ → B_a φ``, ``rb ⊆ rs``,
``rb_in_rs``) and ``ought_implies_can`` (``Oφ → ◇φ``, ``∀W ∃V. d W V ∧ r W V``,
``d_meets_r``). The names, the required families and the axiom names are
single-sourced from :mod:`unicode_fol_kit.hol.isabelle_modal`, so the two HOL routes
cannot drift apart. Each condition is the *exact* correspondent of its schema,
measured against :func:`satisfies_modal` over every frame on ≤ 2 worlds — in
particular ``ought_implies_can`` is deliberately NOT the folklore inclusion
``d ⊆ r``, which on its own does not validate ``Oφ → ◇φ`` at all and which, with
seriality, additionally validates the strictly stronger ``□φ → Oφ``. Requesting a
bridge whose partner family does not occur in the formula raises ``ValueError``
here too — see :func:`_thf_bridge_axioms` for why this route refuses even though
its relations are all declared unconditionally.

UNDECIDABILITY / honesty. First-order modal logic is **undecidable** — though the
standard systems emitted here (K/T/S4/S5, deontic KD) are still *semi-decidable*:
validity is recursively enumerable. (Higher-order modal logic and full second-order
logic are *not even semi-decidable*.) "Emit a problem a prover may discharge" is the
honest claim — never "decide every instance". The propositional
fragments (modal K/T/S4/S5, deontic KD) are decidable, but this export targets the
quantified family, so a ``Theorem`` verdict depends on an external HOL ATP and is not
guaranteed to terminate.

Public API: :func:`to_thf_modal_full`, plus the introspection helpers
:func:`thf_full_definitions` and :func:`thf_full_frame_axioms`.
"""

from typing import Dict, List, Optional, Sequence

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Contrast,
    Box, Diamond, Knows, Believes, Says, Wants,
    Obligatory, Permitted, Always, Eventually, Next, Until, Since,
    Historically, Once, Previous, Nominal, At,
    SortedQuantifier,
)

# Re-use qml.py's THF helpers verbatim so the two exports stay byte-compatible on the
# overlapping (alethic + object-quantifier + equality) fragment.
from ..fol.qml import (
    _FRAMES, _CONSTANT_MODES, _ACTUALIST_MODES,
    _THF_FRAME, _THF_DOMAIN, _THF_PRED_ALIAS, _THF_RESERVED,
    _thf_name, _thf_term, _thf_signature, _ThfNames,
    _FORALL,
)
from ..fol._symbol_names import dedupe

# The cross-family bridge REGISTRY is single-sourced from the Isabelle route: the
# names, the families each bridge needs, and the fact names are shared, so the two
# HOL routes cannot answer differently on the same input (the divergence this
# option exists to remove). Only the axiom TEXT is route-local (_THF_BRIDGE_LINES).
from .isabelle_modal import (
    BRIDGES, _BRIDGES as _BRIDGE_SPEC, _validate_bridges,
)

__all__ = ["to_thf_modal_full", "thf_full_definitions", "thf_full_frame_axioms",
           "BRIDGES"]


# Accessibility-relation THF functors, one per modal family. Alethic ``r`` keeps the
# qml.py name so the alethic fragment is identical across both exports.
_R_ALETHIC = "r"        # mu > mu > $o
_R_KNOWS = "rk"         # $i > mu > mu > $o   (AGENT-indexed)
_R_BELIEVES = "rb"      # $i > mu > mu > $o   (AGENT-indexed)
_R_DEONTIC = "d"        # mu > mu > $o        (serial)
_R_TEMPORAL = "t"       # mu > mu > $o        (G/F)
_R_NEXT = "tnext"       # mu > mu > $o        (X, one-step)
_R_SAYS = "rs"          # $i > mu > mu > $o   (AGENT-indexed, Says, plain K)
_R_WANTS = "rw"         # $i > mu > mu > $o   (AGENT-indexed, Wants, plain K)

# Every fixed functor of the FULL export (qml's core set plus the extra relations
# and lifted operators of this module). A user symbol sanitising onto one of
# these is pushed to a suffixed variant by the resolver — a predicate literally
# named "t" or "muntil" must not silently re-declare a built-in at another type.
_THF_RESERVED_FULL = _THF_RESERVED | frozenset({
    _R_KNOWS, _R_BELIEVES, _R_DEONTIC, _R_TEMPORAL, _R_NEXT, _R_SAYS, _R_WANTS,
    "mknows", "mbelieves", "mobl", "mperm", "malways", "meventually", "mnext",
    "msays", "mwants", "mhistorically", "monce", "mprevious", "muntil", "msince",
})


# ---------------------------------------------------------------------------
# Lifted operators (the SSE macro definitions).
# ---------------------------------------------------------------------------
#
# The classical / alethic / object-quantifier / mvalid macros are copied from
# qml.py's _THF_DEFS (kept inline rather than imported so the emitted block is a
# single self-contained string and so adding the extra families does not depend on
# qml.py's private layout). The new macros are:
#
#   mknows / mbelieves : agent-indexed box, AGENT is a real $i argument so a bound
#                        object variable in agent position quantifies over agents.
#   mobl / mperm       : deontic box / diamond over the serial relation d.
#   malways / meventually : temporal box / diamond over t (refl-trans).
#   mnext              : temporal box over the one-step relation tnext.
_THF_DEFS_FULL = """\
thf(mnot, definition, ( mnot = ( ^ [Phi: mu>$o, W: mu] : ~ ( Phi @ W ) ) )).
thf(mand, definition, ( mand = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) & ( Psi @ W ) ) ) )).
thf(mor, definition, ( mor = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) | ( Psi @ W ) ) ) )).
thf(mimplies, definition, ( mimplies = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) => ( Psi @ W ) ) ) )).
thf(mequiv, definition, ( mequiv = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) <=> ( Psi @ W ) ) ) )).
thf(mbox, definition, ( mbox = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( r @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mdia, definition, ( mdia = ( ^ [Phi: mu>$o, W: mu] : ? [V: mu] : ( ( r @ W @ V ) & ( Phi @ V ) ) ) )).
thf(mknows, definition, ( mknows = ( ^ [A: $i, Phi: mu>$o, W: mu] : ! [V: mu] : ( ( rk @ A @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mbelieves, definition, ( mbelieves = ( ^ [A: $i, Phi: mu>$o, W: mu] : ! [V: mu] : ( ( rb @ A @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mobl, definition, ( mobl = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( d @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mperm, definition, ( mperm = ( ^ [Phi: mu>$o, W: mu] : ? [V: mu] : ( ( d @ W @ V ) & ( Phi @ V ) ) ) )).
thf(malways, definition, ( malways = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( t @ W @ V ) => ( Phi @ V ) ) ) )).
thf(meventually, definition, ( meventually = ( ^ [Phi: mu>$o, W: mu] : ? [V: mu] : ( ( t @ W @ V ) & ( Phi @ V ) ) ) )).
thf(mnext, definition, ( mnext = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( tnext @ W @ V ) => ( Phi @ V ) ) ) )).
thf(msays, definition, ( msays = ( ^ [A: $i, Phi: mu>$o, W: mu] : ! [V: mu] : ( ( rs @ A @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mwants, definition, ( mwants = ( ^ [A: $i, Phi: mu>$o, W: mu] : ! [V: mu] : ( ( rw @ A @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mhistorically, definition, ( mhistorically = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( t @ V @ W ) => ( Phi @ V ) ) ) )).
thf(monce, definition, ( monce = ( ^ [Phi: mu>$o, W: mu] : ? [V: mu] : ( ( t @ V @ W ) & ( Phi @ V ) ) ) )).
thf(mprevious, definition, ( mprevious = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( tnext @ V @ W ) => ( Phi @ V ) ) ) )).
thf(muntil, definition, ( muntil = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ! [S: mu>$o] : ( ( ( ! [V: mu] : ( ( Psi @ V ) => ( S @ V ) ) ) & ( ! [V: mu, U: mu] : ( ( ( Phi @ V ) & ( tnext @ V @ U ) & ( S @ U ) ) => ( S @ V ) ) ) ) => ( S @ W ) ) ) )).
thf(msince, definition, ( msince = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ! [S: mu>$o] : ( ( ( ! [V: mu] : ( ( Psi @ V ) => ( S @ V ) ) ) & ( ! [V: mu, U: mu] : ( ( ( Phi @ V ) & ( tnext @ U @ V ) & ( S @ U ) ) => ( S @ V ) ) ) ) => ( S @ W ) ) ) )).
thf(mforall, definition, ( mforall = ( ^ [Phi: $i>(mu>$o), W: mu] : ! [X: $i] : ( ( existsAt @ X @ W ) => ( Phi @ X @ W ) ) ) )).
thf(mexists, definition, ( mexists = ( ^ [Phi: $i>(mu>$o), W: mu] : ? [X: $i] : ( ( existsAt @ X @ W ) & ( Phi @ X @ W ) ) ) )).
thf(mvalid, definition, ( mvalid = ( ^ [Phi: mu>$o] : ! [W: mu] : ( Phi @ W ) ) )).\
"""


# Frame axioms for the *temporal* relation t. G/F are read over a reflexive-transitive
# t (see the module-level caveat), so t carries refl+trans; X uses a separate one-step
# relation tnext. The `tnext ⊆ t` inclusion links the two relations: every one-step
# successor (over which X quantifies) is reachable by the henceforth relation t (over
# which G/F quantify). Without it Gφ→Xφ — VALID for satisfies_modal, where X's
# immediate "temporal" successors are a subset of G's reflexive-transitive closure of
# the *same* "temporal" relation — would be a non-theorem of the embedding (t and tnext
# would be unconstrained relative to each other). With it Gφ→Xφ (and Xφ→Fφ wherever the
# oracle agrees) becomes a theorem, aligning the embedding with the evaluator.
_THF_TEMPORAL_AXIOMS = [
    "thf(t_refl, axiom, ( ! [W: mu] : ( t @ W @ W ) )).",
    "thf(t_trans, axiom, ( ! [W: mu, V: mu, U: mu] : "
    "( ( ( t @ W @ V ) & ( t @ V @ U ) ) => ( t @ W @ U ) ) )).",
    "thf(tnext_in_t, axiom, ( ! [W: mu, V: mu] : "
    "( ( tnext @ W @ V ) => ( t @ W @ V ) ) )).",
]

# Deontic d is serial (Standard Deontic Logic / KD): every world has a d-successor.
_THF_DEONTIC_AXIOM = "thf(d_serial, axiom, ( ! [W: mu] : ? [V: mu] : ( d @ W @ V ) ))."


# Optional per-system frame axioms for the AGENT-INDEXED epistemic/doxastic relations.
# Each is universally quantified over the agent A as well as the worlds, so the
# property holds per agent — matching the per-agent relations of satisfies_modal.
# "S5" (refl+trans+sym) is the usual logic of knowledge; "KD45" (serial+trans+eucl)
# the usual logic of belief.
def _agent_frame_axioms(rel: str, conds: Sequence[str], tag: str) -> List[str]:
    """THF frame axioms for an agent-indexed relation ``rel`` (each ∀ over the agent A).

    Raises on a condition with no per-agent schema (Löb / directed / connected):
    silently dropping one would emit a WEAKER logic than the caller requested.
    """
    unsupported = [c for c in conds
                   if c not in ("refl", "trans", "sym", "serial", "eucl")]
    if unsupported:
        raise NotImplementedError(
            f"to_thf_modal_full: the requested agent-indexed system needs the frame "
            f"condition(s) {unsupported}, which have no per-agent axiom schema here; "
            "use frame= on the alethic relation for those systems.")
    out: List[str] = []
    if "refl" in conds:
        out.append(f"thf({tag}_refl, axiom, ( ! [A: $i, W: mu] : ( {rel} @ A @ W @ W ) )).")
    if "trans" in conds:
        out.append(
            f"thf({tag}_trans, axiom, ( ! [A: $i, W: mu, V: mu, U: mu] : "
            f"( ( ( {rel} @ A @ W @ V ) & ( {rel} @ A @ V @ U ) ) "
            f"=> ( {rel} @ A @ W @ U ) ) )).")
    if "sym" in conds:
        out.append(
            f"thf({tag}_sym, axiom, ( ! [A: $i, W: mu, V: mu] : "
            f"( ( {rel} @ A @ W @ V ) => ( {rel} @ A @ V @ W ) ) )).")
    if "serial" in conds:
        out.append(
            f"thf({tag}_serial, axiom, ( ! [A: $i, W: mu] : ? [V: mu] : "
            f"( {rel} @ A @ W @ V ) )).")
    if "eucl" in conds:
        out.append(
            f"thf({tag}_eucl, axiom, ( ! [A: $i, W: mu, V: mu, U: mu] : "
            f"( ( ( {rel} @ A @ W @ V ) & ( {rel} @ A @ W @ U ) ) "
            f"=> ( {rel} @ A @ V @ U ) ) )).")
    return out


# ---------------------------------------------------------------------------
# Cross-family bridge axioms (opt-in, ``bridges=``).
# ---------------------------------------------------------------------------
#
# Only the axiom TEXT lives here; the bridge names and the families each one needs
# come from hol.isabelle_modal's registry, so `grep rb_in_rk` finds both routes and
# neither can gain a bridge the other lacks. The TPTP formula names are the SAME
# identifiers as the Isabelle fact names (rb_in_rk / rb_in_rs / d_meets_r) and
# cannot collide with the signature declarations, which all carry a `_decl` suffix.
#
# Types check out unconditionally: rk / rb / rs are `$i > mu > mu > $o` and d / r
# are `mu > mu > $o`, and this route declares every relation whether or not its
# operators occur (see the comment at the declaration block), so a bridge axiom is
# always WELL-FORMED here. That is exactly why the refusal below is a policy
# decision rather than a syntactic necessity.
_THF_BRIDGE_LINES = {
    "knowledge_implies_belief": [
        "thf(rb_in_rk, axiom, ( ! [A: $i, W: mu, V: mu] : "
        "( ( rb @ A @ W @ V ) => ( rk @ A @ W @ V ) ) ))."],
    "sincerity": [
        "thf(rb_in_rs, axiom, ( ! [A: $i, W: mu, V: mu] : "
        "( ( rb @ A @ W @ V ) => ( rs @ A @ W @ V ) ) ))."],
    "ought_implies_can": [
        "thf(d_meets_r, axiom, ( ! [W: mu] : ? [V: mu] : "
        "( ( d @ W @ V ) & ( r @ W @ V ) ) ))."],
}


def _thf_bridge_axioms(used: Dict[str, bool], bridges) -> List[str]:
    """THF axioms for the requested cross-family bridges, in registry order.

    Each is the exact frame correspondent of the schema its option is named after
    (``rb ⊆ rk``, ``rb ⊆ rs``, ``∀W ∃V. d W V ∧ r W V``), measured — not the
    folklore ``d ⊆ r``, which fails to validate ``Oφ → ◇φ`` alone and, with
    seriality, over-validates ``□φ → Oφ``. Emission order follows the shared
    registry, not the caller's set-iteration order, so the output is deterministic.

    Honest contract — why this route REFUSES a bridge whose partner family does not
    occur in the formula, even though it could emit it. Unlike the Isabelle route,
    every relation here is declared unconditionally (the ``_THF_DEFS_FULL`` macro
    block references them all), so ``d_meets_r`` for a ``□``-only formula would be
    perfectly well-formed THF. Emitting it anyway would nonetheless be wrong twice
    over: it would make this route DISAGREE with
    :func:`~unicode_fol_kit.hol.isabelle_modal.to_isabelle_modal` on the same input
    — the exact divergence class the ``bridges=`` option exists to remove — and it
    is not conservative, since ``d_meets_r`` entails seriality of the alethic ``r``
    and so silently turns ``□P → ◇P`` from a non-theorem into a theorem under
    ``frame='K'``. Silently skipping it would be worse still (a weaker logic than
    requested, with no signal). So: ``ValueError``, same wording as the Isabelle
    route modulo the function name.
    """
    requested = _validate_bridges(bridges, "to_thf_modal_full")
    if not requested:
        return []
    out: List[str] = []
    for name, spec in _BRIDGE_SPEC.items():
        if name not in requested:
            continue
        missing = [op for fam, op in spec["needs"] if not used[fam]]
        if missing:
            raise ValueError(
                f"to_thf_modal_full: the bridge {name!r} relates {spec['rels']}, "
                f"but the formula contains no {' / '.join(missing)} operator. This "
                "route declares every relation unconditionally, so the axiom would "
                "be well-formed here — but emitting it would make this route "
                "disagree with hol.isabelle_modal on the same input (the exact "
                "divergence this option exists to remove), and it is not "
                "conservative either (d_meets_r entails seriality of the alethic "
                "r, which would silently make []P -> <>P valid under frame='K'); "
                "while skipping it would emit a weaker logic than requested. Drop "
                "the bridge, or state the formula in both families.")
        out += _THF_BRIDGE_LINES[name]
    return out


# ---------------------------------------------------------------------------
# Lifting the formula to a THF term of type mu > $o.
# ---------------------------------------------------------------------------
def _lift(node: Node, names: "_ThfNames") -> str:
    """Render a full-family modal formula as a THF term of type ``mu > $o``.

    Classical connectives, alethic □/◇, object quantifiers and atoms are handled
    exactly as in :func:`unicode_fol_kit.fol.qml._thf_lift`; the additional families
    are lifted through the macros defined in :data:`_THF_DEFS_FULL`. ``names`` is the
    per-formula de-colliding functor resolver (so distinct symbols never collapse).
    """
    if isinstance(node, Atom):
        # `=` / `≠` stay uninterpreted world-relativized predicates (feq / fneq).
        head = names.atom(node)
        if not node.args:
            return head
        return "( " + " @ ".join([head] + [_thf_term(a, names) for a in node.args]) + " )"
    if isinstance(node, Not):
        return f"( mnot @ {_lift(node.formula, names)} )"
    if isinstance(node, And):
        return f"( mand @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"
    if isinstance(node, Or):
        return f"( mor @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"
    if isinstance(node, Xor):
        # Xor is ¬(φ ⇔ ψ): no dedicated macro, build it from mnot/mequiv.
        return f"( mnot @ ( mequiv @ {_lift(node.left, names)} @ {_lift(node.right, names)} ) )"
    if isinstance(node, Implies):
        return f"( mimplies @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"
    if isinstance(node, Iff):
        return f"( mequiv @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"

    if isinstance(node, Box):
        return f"( mbox @ {_lift(node.formula, names)} )"
    if isinstance(node, Diamond):
        return f"( mdia @ {_lift(node.formula, names)} )"

    if isinstance(node, Contrast):
        # Truth-functionally conjunction (Contrast's own contract).
        return f"( mand @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"

    # Agent-indexed epistemic / doxastic / assertive / bouletic: the agent is a
    # real $i argument.
    if isinstance(node, Knows):
        return f"( mknows @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"
    if isinstance(node, Believes):
        return f"( mbelieves @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"
    if isinstance(node, Says):
        return f"( msays @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"
    if isinstance(node, Wants):
        return f"( mwants @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"

    if isinstance(node, Obligatory):
        return f"( mobl @ {_lift(node.formula, names)} )"
    if isinstance(node, Permitted):
        return f"( mperm @ {_lift(node.formula, names)} )"

    if isinstance(node, Always):
        return f"( malways @ {_lift(node.formula, names)} )"
    if isinstance(node, Eventually):
        return f"( meventually @ {_lift(node.formula, names)} )"
    if isinstance(node, Next):
        return f"( mnext @ {_lift(node.formula, names)} )"

    if isinstance(node, Quantifier):
        x = node.variable.name.upper()
        binder = "mforall" if node.type in (_FORALL, "forall") else "mexists"
        return f"( {binder} @ ( ^ [{x}: $i] : {_lift(node.formula, names)} ) )"

    if isinstance(node, Historically):
        # Box over the CONVERSE of t (faithful to satisfies_modal's past reading).
        return f"( mhistorically @ {_lift(node.formula, names)} )"
    if isinstance(node, Once):
        return f"( monce @ {_lift(node.formula, names)} )"
    if isinstance(node, Previous):
        return f"( mprevious @ {_lift(node.formula, names)} )"

    if isinstance(node, Until):
        # Strong Until as the impredicative Knaster–Tarski least fixpoint over
        # the one-step tnext — TH0 quantifies over predicates, so the same least
        # fixpoint Isabelle's `inductive muntil` compiles to is directly shallow-
        # embeddable (the earlier claim that it is not was simply wrong).
        return f"( muntil @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"
    if isinstance(node, Since):
        # The converse-relation mirror of muntil (backward one-step paths).
        return f"( msince @ {_lift(node.left, names)} @ {_lift(node.right, names)} )"

    if isinstance(node, Nominal):
        # True at exactly the named world: the reserved nom_ world constant, the
        # same convention as standard_translation and isabelle_modal. The functor
        # comes from the resolver's per-formula nominal map, so two DISTINCT
        # nominals whose names sanitise alike ('A' / 'a') stay distinct worlds.
        return f"( ^ [W: mu] : ( W = {names.nominal[node.name]} ) )"
    if isinstance(node, At):
        return (f"( ^ [W: mu] : ( {_lift(node.formula, names)} "
                f"@ {names.nominal[node.nominal.name]} ) )")

    if isinstance(node, SortedQuantifier):
        raise NotImplementedError(
            "to_thf_modal_full: SortedQuantifier is not supported; use a plain ∀x/∃x.")
    if type(node).__name__ in ("Would", "Might"):
        raise NotImplementedError(
            "to_thf_modal_full: the counterfactuals □→/◇→ read a similarity "
            "ordering (Lewis spheres), not an accessibility relation — use "
            "hol.isabelle_conditional / isabelle_decide_counterfactual.")
    raise NotImplementedError(
        f"to_thf_modal_full: unsupported node type {type(node).__name__}.")


def _nominal_names(formula: Node):
    """All nominal names occurring in ``formula`` (Nominal and At sites), sorted."""
    return sorted({n.name for n in formula.walk() if isinstance(n, Nominal)})


def _resolve_names(formula: Node) -> "_ThfNames":
    """Build the per-formula functor resolver, including a de-colliding nominal map.

    User symbols are resolved against the full export's reserved functor set;
    then each nominal name gets a ``nom_``-prefixed ``mu`` constant deduped
    against BOTH the user functors and the other nominals. Without this, two
    distinct nominals sanitising alike (``'A'`` / ``'a'``) would silently
    collapse to the SAME world constant — the emitted problem would load but no
    longer mean what the source formula meant (and a user constant literally
    named ``nom_a`` would conflate with the nominal ``a``'s world).
    """
    names = _ThfNames(formula, reserved=_THF_RESERVED_FULL)
    taken = (set(_THF_RESERVED_FULL)
             | set(names.pred.values()) | set(names.const.values())
             | set(names.func.values()))
    names.nominal = {}
    for raw in _nominal_names(formula):
        names.nominal[raw] = dedupe("nom_" + _thf_name(raw), taken)
    return names


# ---------------------------------------------------------------------------
# Which families occur — so we only declare/axiomatise the relations we use.
# ---------------------------------------------------------------------------
def _families_used(formula: Node) -> Dict[str, bool]:
    """Scan ``formula`` for which modal families occur (controls what gets emitted)."""
    used = {"alethic": False, "epistemic": False, "doxastic": False,
            "assertive": False, "bouletic": False,
            "deontic": False, "temporal": False, "tnext": False}
    for n in formula.walk():
        if isinstance(n, (Box, Diamond)):
            used["alethic"] = True
        elif isinstance(n, Knows):
            used["epistemic"] = True
        elif isinstance(n, Believes):
            used["doxastic"] = True
        elif isinstance(n, Says):
            used["assertive"] = True
        elif isinstance(n, Wants):
            used["bouletic"] = True
        elif isinstance(n, (Obligatory, Permitted)):
            used["deontic"] = True
        elif isinstance(n, (Always, Eventually, Historically, Once)):
            # ⒣/⒫ read the CONVERSE of the same henceforth t, whose refl/trans
            # axioms constrain the past readings equally.
            used["temporal"] = True
        elif isinstance(n, (Next, Previous, Until, Since)):
            # ⒴ reads the converse of tnext; the muntil/msince fixpoints step
            # over tnext — all need the one-step relation's link into t.
            used["tnext"] = True
    return used


def thf_full_definitions() -> str:
    """Return the block of lifted-operator THF definitions used by the full export."""
    return _THF_DEFS_FULL


# Agent-indexed families that systems= may constrain, with their relation + tag.
_AGENT_SYSTEM_FAMILIES = (
    ("epistemic", _R_KNOWS, "rk"),
    ("doxastic", _R_BELIEVES, "rb"),
    ("assertive", _R_SAYS, "rs"),
    ("bouletic", _R_WANTS, "rw"),
)


def thf_full_frame_axioms(frame: str = "K",
                          systems: Optional[Dict[str, str]] = None,
                          temporal_closure: bool = True,
                          bridges: Optional[Sequence[str]] = None) -> List[str]:
    """Return the frame axioms the full export would emit (for inspection / testing).

    ``frame`` constrains the alethic relation ``r`` (K/T/S4/S5/KD/KD45); ``systems`` is
    an optional mapping that constrains the agent-indexed epistemic / doxastic /
    assertive / bouletic relations, e.g. ``{"epistemic": "S5", "doxastic": "KD45"}``.
    The deontic relation ``d`` is always serial; the temporal relation ``t`` is
    reflexive-transitive unless ``temporal_closure=False`` (which keeps only the
    ``tnext ⊆ t`` inclusion, leaving ``t`` an arbitrary relation — mirroring
    ``isabelle_modal_theory``'s parameter of the same name). ``bridges`` appends the
    cross-family bridge axioms (see :func:`_thf_bridge_axioms`).

    ASYMMETRY, stated so this helper does not look like it contradicts the emitter:
    it takes no formula, so it cannot know which families occur and emits every
    requested axiom UNCONDITIONALLY — exactly as it already emits the ``systems=``
    axioms and ``d_serial`` unconditionally while :func:`to_thf_modal_full` gates
    them on the families actually used. Unknown bridge names are still rejected
    here, so a typo is caught in the inspection path too; the "family absent"
    refusal can only be made by the real emitter.
    """
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal_full: unknown frame {frame!r}.")
    systems = systems or {}
    axioms: List[str] = [_THF_FRAME[c] for c in _FRAMES[frame]]
    for fam, rel, tag in _AGENT_SYSTEM_FAMILIES:
        sys = systems.get(fam)
        if sys is not None:
            if sys not in _FRAMES:
                raise ValueError(
                    f"to_thf_modal_full: unknown system {sys!r} for {fam} "
                    f"(use one of {sorted(_FRAMES)}).")
            axioms += _agent_frame_axioms(rel, _FRAMES[sys], tag)
    axioms.append(_THF_DEONTIC_AXIOM)
    axioms += _THF_TEMPORAL_AXIOMS if temporal_closure else _THF_TEMPORAL_AXIOMS[-1:]
    requested = _validate_bridges(bridges, "to_thf_modal_full")
    for name in _BRIDGE_SPEC:      # registry order, not the caller's set order
        if name in requested:
            axioms += _THF_BRIDGE_LINES[name]
    return axioms


def to_thf_modal_full(formula: Node, mode: str = "constant", frame: str = "K",
                      systems: Optional[Dict[str, str]] = None,
                      temporal_closure: bool = True,
                      bridges: Optional[Sequence[str]] = None) -> str:
    """Emit a complete Benzmüller-style **THF** shallow embedding of a full-family modal formula.

    Unlike :func:`unicode_fol_kit.fol.qml.to_thf_modal` (alethic-only), this covers the
    whole modal family the AST expresses: alethic ``□``/``◇``, agent-indexed epistemic
    ``K_a`` and doxastic ``B_a``, deontic ``O``/``P`` (serial / KD), and temporal
    ``G``/``F``/``X``. It produces a self-contained THF problem — type declarations,
    every lifted operator, the relevant frame axioms, the ``existsAt`` domain axioms for
    ``mode``, and the conjecture ``mvalid @ ⟨formula⟩`` — ready for a higher-order ATP
    (Leo-III / Satallax). The toolkit only emits the problem; it does not run a prover.

    Parameters:
        formula: the modal formula to embed.
        mode: object-quantifier domain regime — ``"constant"`` / ``"possibilist"``
            (unrelativised) or ``"varying"`` / ``"increasing"`` / ``"cumulative"`` /
            ``"decreasing"`` (actualist, ``existsAt``-guarded).
        frame: constrains the ALETHIC relation ``r`` (K/T/S4/S5/KD/KD45).
        systems: optional per-family system selection for the AGENT-INDEXED epistemic /
            doxastic / assertive / bouletic relations, e.g. ``{"epistemic": "S5",
            "doxastic": "KD45"}``. Each value is a frame name from
            ``{K,T,S4,S5,KD,KD45}``; the property is asserted ``∀A`` over the agent, so
            it holds per agent.
        temporal_closure: emit the ``t_refl`` / ``t_trans`` axioms making ``t``
            reflexive-transitive (default). ``False`` keeps only the ``tnext ⊆ t``
            inclusion, so ``t`` denotes an arbitrary relation — mirroring
            ``isabelle_modal_theory``'s parameter of the same name.
        bridges: optional collection of CROSS-family bridge names (:data:`BRIDGES`,
            shared verbatim with ``hol.isabelle_modal``), **off by default**:
            ``"knowledge_implies_belief"`` (``K_a φ → B_a φ``, axiom ``rb_in_rk``,
            condition ``rb ⊆ rk``), ``"sincerity"`` (``Say_a φ → B_a φ``,
            ``rb_in_rs``, ``rb ⊆ rs``) and ``"ought_implies_can"`` (``Oφ → ◇φ``,
            ``d_meets_r``, ``∀W ∃V. d W V ∧ r W V`` — NOT the folklore ``d ⊆ r``).
            Each condition is the exact correspondent of its schema, so a bridge
            adds that principle and nothing stronger. Requesting a bridge whose
            partner family does not occur in the formula raises ``ValueError``,
            matching ``to_isabelle_modal`` even though the axiom would be
            well-formed here — see :func:`_thf_bridge_axioms`.

    Agent-indexedness (faithful to ``satisfies_modal``): the agent of ``Knows`` /
    ``Believes`` / ``Says`` / ``Wants`` is a first-class TERM and is carried into
    ``rk`` / ``rb`` / ``rs`` / ``rw`` as a real ``$i`` argument, so a bound object
    variable in agent position quantifies over agents
    (``∀x (Student(x) → K_x φ)``). A named agent becomes an ordinary ``$i`` constant.

    Caveats: ``Until`` / ``Since`` ARE supported — as the impredicative
    Knaster–Tarski least-fixpoint macros ``muntil`` / ``msince`` over the one-step
    ``tnext`` (TH0 quantifies over predicates, so the least fixpoint is directly
    expressible). Temporal ``G``/``F`` are read over a reflexive-transitive ``t`` and
    only approximate ``satisfies_modal``'s closure over the caller's raw temporal
    edges (see the module docstring). Equality ``=`` / ``≠`` is an uninterpreted
    world-relativized predicate (``feq`` / ``fneq``), not primitive HOL identity.
    First-order/higher-order modal logic is undecidable, so a ``Theorem`` verdict
    requires an external HOL ATP and is not guaranteed to terminate.
    """
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal_full: unknown frame {frame!r}.")
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"to_thf_modal_full: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    # Reject a bare string / an unknown bridge name before any emission work.
    _validate_bridges(bridges, "to_thf_modal_full")

    used = _families_used(formula)
    systems = systems or {}

    lines: List[str] = [
        f"% Full-family shallow embedding of a quantified modal formula "
        f"(mode={mode}, frame={frame}).",
        "% Families: alethic r, epistemic rk(agent), doxastic rb(agent), "
        "deontic d(serial), temporal t.",
        "% Conjecture is 'Theorem' iff the formula is valid under this regime "
        "(external HOL ATP required).",
        "thf(mu_type, type, ( mu : $tType )).",
    ]

    # --- relation type declarations ---
    # The lifted-operator definitions block (_THF_DEFS_FULL) is emitted WHOLE and its
    # macros (mbox/mdia, mknows/mbelieves, mobl/mperm, mnext) reference every relation
    # r/rk/rb/d/tnext. So all of them must be declared unconditionally — otherwise a
    # Box-only formula would still emit mknows etc. referencing an undeclared rk, and a
    # strict THF parser (Leo-III/Satallax) would reject the problem. Unused declared
    # symbols are harmless.
    lines.append("thf(r_decl, type, ( r : ( mu > mu > $o ) )).")
    lines.append("thf(rk_decl, type, ( rk : ( $i > mu > mu > $o ) )).")
    lines.append("thf(rb_decl, type, ( rb : ( $i > mu > mu > $o ) )).")
    lines.append("thf(d_decl, type, ( d : ( mu > mu > $o ) )).")
    lines.append("thf(t_decl, type, ( t : ( mu > mu > $o ) )).")
    lines.append("thf(tnext_decl, type, ( tnext : ( mu > mu > $o ) )).")
    lines.append("thf(rs_decl, type, ( rs : ( $i > mu > mu > $o ) )).")
    lines.append("thf(rw_decl, type, ( rw : ( $i > mu > mu > $o ) )).")
    lines.append("thf(existsAt_decl, type, ( existsAt : ( $i > mu > $o ) )).")

    # --- signature of the object-level predicates / constants / functions ---
    # (named agents fall out here as ordinary $i constants, matching rk/rb's $i slot).
    # The de-colliding resolver guarantees distinct source symbols never share a functor
    # (e.g. Ab / ab) and never shadow a built-in (a predicate named "r"/"mbox" is pushed
    # to r_2/mbox_2), so a non-valid formula can neither collapse to a tautology nor
    # re-declare an export-internal relation at a conflicting type.
    names = _resolve_names(formula)
    # One mu constant per nominal (reserved nom_ prefix; true at exactly the
    # world it names — matching standard_translation / isabelle_modal). The map
    # is deduped, so nominals 'A'/'a' get distinct constants (nom_a / nom_a_2).
    for raw in _nominal_names(formula):
        f = names.nominal[raw]
        lines.append(f"thf({f}_decl, type, ( {f} : mu )).")
    lines += _thf_signature(formula, names)

    # --- the lifted-operator definitions (one self-contained block) ---
    lines.append(_THF_DEFS_FULL)

    # --- standing axiom: every world has an existing individual ---
    lines.append(
        "thf(nonempty_dom, axiom, ( ! [W: mu] : ? [X: $i] : ( existsAt @ X @ W ) )).")

    # --- alethic frame axioms (frame) ---
    for cond in _FRAMES[frame]:
        lines.append(_THF_FRAME[cond])

    # --- agent-indexed epistemic/doxastic/assertive/bouletic system axioms ---
    for fam, rel, tag in _AGENT_SYSTEM_FAMILIES:
        if not used[fam]:
            continue
        sys = systems.get(fam)
        if sys is None:
            continue
        if sys not in _FRAMES:
            raise ValueError(
                f"to_thf_modal_full: unknown system {sys!r} for {fam} "
                f"(use one of {sorted(_FRAMES)}).")
        for ax in _agent_frame_axioms(rel, _FRAMES[sys], tag):
            lines.append(ax)

    # --- deontic seriality (Standard Deontic Logic, KD) ---
    if used["deontic"]:
        lines.append(_THF_DEONTIC_AXIOM)

    # --- temporal frame axioms: refl/trans for G/F (see caveat) plus the tnext ⊆ t
    # inclusion linking X's one-step relation to G/F's henceforth relation. Emitted
    # whenever EITHER the temporal (G/F) or next (X) family occurs, since the linking
    # axiom is exactly what makes a mixed formula such as Gφ→Xφ — valid for
    # satisfies_modal — a theorem of the embedding. (t and tnext are declared
    # unconditionally, so the axiom is always well-formed.)
    if used["temporal"] or used["tnext"]:
        lines += _THF_TEMPORAL_AXIOMS if temporal_closure else _THF_TEMPORAL_AXIOMS[-1:]

    # --- opt-in cross-family bridge axioms (raises when a partner family is absent) ---
    lines += _thf_bridge_axioms(used, bridges)

    # --- object-quantifier domain regime ---
    if mode in _THF_DOMAIN:
        lines.append(_THF_DOMAIN[mode])
    elif mode not in ("varying",) and mode not in _CONSTANT_MODES:
        raise ValueError(f"to_thf_modal_full: unknown mode {mode!r}.")

    # --- the conjecture ---
    lines.append(f"thf(goal, conjecture, ( mvalid @ {_lift(formula, names)} )).")
    return "\n".join(lines) + "\n"
