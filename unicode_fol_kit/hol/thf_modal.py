"""Full-family modal THF export — a Benzmüller-style higher-order shallow embedding.

This module extends :func:`unicode_fol_kit.fol.qml.to_thf_modal` (which only handles
the *alethic* ``□`` / ``◇`` fragment plus object quantifiers and **raises** on the
other modalities) to the **full modal family** the toolkit's AST can express:

- alethic        ``□φ`` / ``◇φ``                         over relation ``r``;
- epistemic      ``K_a φ``  (``Knows(agent, φ)``)        over an AGENT-INDEXED ``rk``;
- doxastic       ``B_a φ``  (``Believes(agent, φ)``)     over an AGENT-INDEXED ``rb``;
- deontic        ``Oφ`` / ``Pφ``                         over a SERIAL relation ``d``;
- temporal       ``Gφ`` / ``Fφ`` / ``Xφ``               over a relation ``t``.

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
  edges. ``Until`` is **omitted** (raises): strong Until needs the transitive closure
  and is not (higher-order) shallow-embeddable here — evaluate it with
  ``satisfies_modal`` instead.

  The two temporal relations are **linked** by the emitted ``tnext_in_t`` inclusion
  axiom ``![W,V]: (tnext @ W @ V) => (t @ W @ V)``. In ``satisfies_modal`` ``X`` reads
  the immediate successors of the *single* ``"temporal"`` relation while ``G``/``F``
  read its reflexive-transitive closure, so every one-step ``X``-successor is reachable
  by ``G``/``F``; the inclusion axiom reproduces exactly that containment in the
  embedding. Without it ``Gφ→Xφ`` — valid for the evaluator — was a non-theorem of the
  emitted problem (``t`` and ``tnext`` were unconstrained relative to each other); with
  it ``Gφ→Xφ`` (and ``Xφ→Fφ`` wherever the evaluator agrees) is now a theorem of the
  embedding.

UNDECIDABILITY / honesty. First-order (and higher-order) modal logic is **undecidable
and not even semi-decidable** in general; SOL likewise. "Emit a problem a prover may
discharge" is the honest claim — never "decide every instance". The propositional
fragments (modal K/T/S4/S5, deontic KD) are decidable, but this export targets the
quantified family, so a ``Theorem`` verdict depends on an external HOL ATP and is not
guaranteed to terminate.

Public API: :func:`to_thf_modal_full`, plus the introspection helpers
:func:`thf_full_definitions` and :func:`thf_full_frame_axioms`.
"""

from typing import Dict, List, Optional, Sequence

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes,
    Obligatory, Permitted, Always, Eventually, Next, Until,
    SortedQuantifier,
)

# Re-use qml.py's THF helpers verbatim so the two exports stay byte-compatible on the
# overlapping (alethic + object-quantifier + equality) fragment.
from ..fol.qml import (
    _FRAMES, _CONSTANT_MODES, _ACTUALIST_MODES,
    _THF_FRAME, _THF_DOMAIN, _THF_PRED_ALIAS,
    _thf_name, _thf_term, _thf_signature, _ThfNames,
    _FORALL,
)

__all__ = ["to_thf_modal_full", "thf_full_definitions", "thf_full_frame_axioms"]


# Accessibility-relation THF functors, one per modal family. Alethic ``r`` keeps the
# qml.py name so the alethic fragment is identical across both exports.
_R_ALETHIC = "r"        # mu > mu > $o
_R_KNOWS = "rk"         # $i > mu > mu > $o   (AGENT-indexed)
_R_BELIEVES = "rb"      # $i > mu > mu > $o   (AGENT-indexed)
_R_DEONTIC = "d"        # mu > mu > $o        (serial)
_R_TEMPORAL = "t"       # mu > mu > $o        (G/F)
_R_NEXT = "tnext"       # mu > mu > $o        (X, one-step)


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
    """THF frame axioms for an agent-indexed relation ``rel`` (each ∀ over the agent A)."""
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

    # Agent-indexed epistemic / doxastic: the agent is a real $i argument.
    if isinstance(node, Knows):
        return f"( mknows @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"
    if isinstance(node, Believes):
        return f"( mbelieves @ {_thf_term(node.agent, names)} @ {_lift(node.formula, names)} )"

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

    if isinstance(node, Until):
        raise NotImplementedError(
            "to_thf_modal_full: Until is not (higher-order) shallow-embeddable "
            "(strong Until needs the transitive closure of the temporal relation); "
            "evaluate it with satisfies_modal instead."
        )
    if isinstance(node, SortedQuantifier):
        raise NotImplementedError(
            "to_thf_modal_full: SortedQuantifier is not supported; use a plain ∀x/∃x.")
    raise NotImplementedError(
        f"to_thf_modal_full: unsupported node type {type(node).__name__}.")


# ---------------------------------------------------------------------------
# Which families occur — so we only declare/axiomatise the relations we use.
# ---------------------------------------------------------------------------
def _families_used(formula: Node) -> Dict[str, bool]:
    """Scan ``formula`` for which modal families occur (controls what gets emitted)."""
    used = {"alethic": False, "epistemic": False, "doxastic": False,
            "deontic": False, "temporal": False, "tnext": False}
    for n in formula.walk():
        if isinstance(n, (Box, Diamond)):
            used["alethic"] = True
        elif isinstance(n, Knows):
            used["epistemic"] = True
        elif isinstance(n, Believes):
            used["doxastic"] = True
        elif isinstance(n, (Obligatory, Permitted)):
            used["deontic"] = True
        elif isinstance(n, (Always, Eventually)):
            used["temporal"] = True
        elif isinstance(n, Next):
            used["tnext"] = True
    return used


def thf_full_definitions() -> str:
    """Return the block of lifted-operator THF definitions used by the full export."""
    return _THF_DEFS_FULL


def thf_full_frame_axioms(frame: str = "K",
                          systems: Optional[Dict[str, str]] = None) -> List[str]:
    """Return the frame axioms the full export would emit (for inspection / testing).

    ``frame`` constrains the alethic relation ``r`` (K/T/S4/S5/KD/KD45); ``systems`` is
    an optional mapping that constrains the agent-indexed epistemic/doxastic relations,
    e.g. ``{"epistemic": "S5", "doxastic": "KD45"}``. The deontic relation ``d`` is
    always serial; the temporal relation ``t`` is always reflexive-transitive.
    """
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal_full: unknown frame {frame!r}.")
    systems = systems or {}
    axioms: List[str] = [_THF_FRAME[c] for c in _FRAMES[frame]]
    for fam, rel, tag in (("epistemic", _R_KNOWS, "rk"), ("doxastic", _R_BELIEVES, "rb")):
        sys = systems.get(fam)
        if sys is not None:
            if sys not in _FRAMES:
                raise ValueError(
                    f"to_thf_modal_full: unknown system {sys!r} for {fam} "
                    f"(use one of {sorted(_FRAMES)}).")
            axioms += _agent_frame_axioms(rel, _FRAMES[sys], tag)
    axioms.append(_THF_DEONTIC_AXIOM)
    axioms += _THF_TEMPORAL_AXIOMS
    return axioms


def to_thf_modal_full(formula: Node, mode: str = "constant", frame: str = "K",
                      systems: Optional[Dict[str, str]] = None) -> str:
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
            doxastic relations, e.g. ``{"epistemic": "S5", "doxastic": "KD45"}``. Each
            value is a frame name from ``{K,T,S4,S5,KD,KD45}``; the property is asserted
            ``∀A`` over the agent, so it holds per agent.

    Agent-indexedness (faithful to ``satisfies_modal``): the agent of ``Knows`` /
    ``Believes`` is a first-class TERM and is carried into ``rk`` / ``rb`` as a real
    ``$i`` argument, so a bound object variable in agent position quantifies over agents
    (``∀x (Student(x) → K_x φ)``). A named agent becomes an ordinary ``$i`` constant.

    Caveats: ``Until`` raises (needs transitive closure); temporal ``G``/``F`` are read
    over a reflexive-transitive ``t`` and only approximate ``satisfies_modal``'s closure
    over the caller's raw temporal edges (see the module docstring). Equality ``=`` /
    ``≠`` is an uninterpreted world-relativized predicate (``feq`` / ``fneq``), not
    primitive HOL identity. First-order/higher-order modal logic is undecidable, so a
    ``Theorem`` verdict requires an external HOL ATP and is not guaranteed to terminate.
    """
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal_full: unknown frame {frame!r}.")
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"to_thf_modal_full: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")

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
    lines.append("thf(existsAt_decl, type, ( existsAt : ( $i > mu > $o ) )).")

    # --- signature of the object-level predicates / constants / functions ---
    # (named agents fall out here as ordinary $i constants, matching rk/rb's $i slot).
    # The de-colliding resolver guarantees distinct source symbols never share a functor
    # (e.g. Ab / ab), so a non-valid formula like □Ab→□ab cannot collapse to a tautology.
    names = _ThfNames(formula)
    lines += _thf_signature(formula, names)

    # --- the lifted-operator definitions (one self-contained block) ---
    lines.append(_THF_DEFS_FULL)

    # --- standing axiom: every world has an existing individual ---
    lines.append(
        "thf(nonempty_dom, axiom, ( ! [W: mu] : ? [X: $i] : ( existsAt @ X @ W ) )).")

    # --- alethic frame axioms (frame) ---
    for cond in _FRAMES[frame]:
        lines.append(_THF_FRAME[cond])

    # --- agent-indexed epistemic / doxastic system axioms (systems=...) ---
    for fam, rel, tag in (("epistemic", _R_KNOWS, "rk"),
                          ("doxastic", _R_BELIEVES, "rb")):
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
        lines += _THF_TEMPORAL_AXIOMS

    # --- object-quantifier domain regime ---
    if mode in _THF_DOMAIN:
        lines.append(_THF_DOMAIN[mode])
    elif mode not in ("varying",) and mode not in _CONSTANT_MODES:
        raise ValueError(f"to_thf_modal_full: unknown mode {mode!r}.")

    # --- the conjecture ---
    lines.append(f"thf(goal, conjecture, ( mvalid @ {_lift(formula, names)} )).")
    return "\n".join(lines) + "\n"
