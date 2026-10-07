"""Labelled analytic tableaux for the propositional modal family.

The classical :mod:`unicode_logic_kit.atp.tableau` engine has no rule for a modal
operator — a ``Box`` / ``Knows`` / ``Obligatory`` node makes it raise. This module
fills that gap with a **labelled** (world-prefixed) tableau: a branch is a set of
*labelled* formulas ``w: φ`` (worlds are integers) together with the accessibility
edges generated along the way. The propositional / connective rules act at a fixed
world; the modal rules move between worlds:

- ``w: □φ`` (a *box* over its relation) asserts ``v: φ`` at every successor ``v`` of
  ``w`` — and is re-applied whenever a new successor appears;
- ``w: ◇φ`` (a *diamond*) creates a **fresh** successor ``v`` with ``v: φ``;
- a negated box becomes a diamond of the negation and vice versa (``¬□φ ≡ ◇¬φ``).

The box/diamond family handled here is exactly the one with a single accessibility
relation: alethic ``□``/``◇``, epistemic ``K_a``, doxastic ``B_a``, deontic
``O``/``P``, and the one-step temporal ``X`` (``Next``). Two of the three
GROUP-epistemic operators join that family too: ``EverybodyKnows`` (E_G, alpha-
reduced into one ``Knows`` box per agent) and ``DistributedKnowledge`` (D_G, a box
over the intersection of the group's per-agent relations, POSITIVE occurrences
only — see the comment above ``_distributed_relname``). ``CommonKnowledge`` (C_G)
needs the reflexive-transitive closure of a union relation, the same
least/greatest-fixpoint machinery ``Always``/``Eventually``/``Until`` need, so it
is rejected the same way they are (below). The relation names match the
:class:`~unicode_logic_kit.semantics.kripke.KripkeModel` convention
(``"alethic"`` / ``"K:"+a`` / ``"B:"+a`` / ``"deontic"`` / ``"temporal"``), so an open
branch is read off directly as a Kripke counter-model. The temporal *closure*
operators ``Always`` (G), ``Eventually`` (F) and ``Until`` need least/greatest-fixpoint
(eventuality) machinery beyond a basic labelled tableau and are rejected with a pointer
to :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal` /
:func:`~unicode_logic_kit.hol.isabelle_runner.isabelle_decide_modal`. Hybrid constructs
(``Nominal`` / ``At``) are likewise rejected — a nominal's name-exactly-one-world
constraint has no rule here; use ``hybrid_is_valid`` (the standard translation + Z3)
or evaluate in a ``KripkeModel`` with a ``nominals=`` assignment.

**Public announcement logic (PAL)** — the ``Announce``/``AnnounceDiamond`` nodes
(``[φ!]ψ`` / ``⟨φ!⟩ψ``, :mod:`unicode_logic_kit.fol._modal_nodes`) — is decided too,
via a PRE-PASS: every public entry point below runs its formula(s) through
:func:`unicode_logic_kit.fol.pal.reduce_announcements` first (see :func:`_run`),
which eliminates every announcement using the standard PAL reduction axioms
before this tableau ever sees the formula. So ``modal_decide``/``modal_prove``/
``is_modal_valid``/``modal_countermodel`` all decide genuine PAL formulas — e.g.
the reduction axiom ``[φ!]K_aψ ↔ (φ → K_a[φ!]ψ)`` is K-valid, while the famous
NON-theorem ``[φ!]K_aψ → K_a[φ!]ψ`` is not (see ``tests/test_pal.py``) — with no
PAL-specific rule in this module at all.

**Sorted constants.** ``c:S`` denotes an element of ``S`` at every world (a constant is a
rigid designator; ``semantics.kripke``'s module docstring). The annotation does not make a
second symbol, so ``Mortal(c:S)`` and ``Mortal(c)`` are one letter, and the guard atom
``S(c)`` is a letter that is true at EVERY world: a world holding ``¬S(c)`` closes its
branch, and a model read off an open branch makes ``S(c)`` true everywhere. Without that a
valid formula such as ``S(c:S)`` had an open branch whose model left ``c`` out of ``S``, and
:func:`modal_decide` called it invalid. A sorted QUANTIFIER stays an opaque literal.

**Frame conditions** are realised as structural rules over the edge set: reflexivity
adds ``w → w`` for every world, symmetry mirrors each edge, transitivity takes the
closure, the euclidean rule closes ``w→v, w→u ⊢ v→u``, and seriality manufactures a
successor for a world that has a box obligation and lacks one. The named systems are K, T,
D/KD, B/KB, K4, K45, S4, S5, KD45.

**The model is a model of the frame.** The branch the search leaves open is not yet a
structure of the frame class that was asked for: a world that has no box obligation needs no
successor for the formula, but a serial relation gives it one. The model that is read off
therefore lets every such dead end of a serial relation see itself. A self-loop at a world
without a successor adds no obligation (the world has no box of that relation to satisfy) and
keeps a transitive, symmetric or euclidean relation closed. A relation the formula reads
but the branch never used (its operator sits in a disjunct the branch does not take) has no
edge on the branch, and a relation the model does not list is the empty relation, which is
neither reflexive nor serial: it is given the loops its system asks for as well, so every
relation the formula reads is a relation of the frame class. A relation the formula does not
read is not made up: nothing the formula says could tell the difference. The loops can change
the value of one construct: a distributed-knowledge box ``D_G`` reads the intersection of
several relations, and a world that is a dead end in each of them then gains an edge in the
intersection. A model is therefore handed out only when it falsifies the formula
(:func:`satisfies_modal`, which evaluates the relations as they are and does not know the
frame) AND every relation of it, and every relation the formula reads, satisfies the frame
conditions of its system; if either check fails, no model is handed out and the answer is
``"unknown"``. The first check is made at each open branch already, so a branch whose model
does not falsify the formula (it holds a construct this tableau has no rule for, such as a
negated ``D_G``) does not end the search while another branch is left.

**Equality is NOT interpreted here.** ``a = b`` / ``a ≠ b`` need a semantics of TERMS —
what ``a`` and ``b`` denote, so that the atom can be decided as identity of those
denotations — and this tableau has none: an atom is a propositional letter, a branch
closes on a syntactic complement, and an open branch is read off as a valuation of
rendered atom keys. Run on ``a = a`` it would leave the branch for ``¬(a = a)`` open
(``is_modal_valid`` False, ``modal_decide`` "unknown") although identity is reflexive,
and on ``a = b → □(a = b)`` it would build a counter-model in which identity varies
from world to world — both against :func:`unicode_logic_kit.fol.qml.qml_is_valid`, where
``=`` is RIGID identity over the object domain. Reading identity as an uninterpreted
relation is an approximation this kit refuses, so every public entry point raises
``NotImplementedError`` naming the atom (the shared
:func:`~unicode_logic_kit.semantics._modal_reject.reject_equality`, the same refusal
:func:`~unicode_logic_kit.semantics.kripke.satisfies_modal` gives). The refusal is a
whole-formula scan at entry (:func:`_run`), BEFORE any search, and never left to the
search reaching an ``Atom``: a branch that closes on an unrelated contradiction, a
vacuous ``□`` at a dead end, or a tautologous disjunct would
otherwise return a verdict that never looked at the atom. Decide identity with
``fol.qml.qml_is_valid`` or another first-order route.

**Cross-family bridges are NOT supported here.** A frame condition relating two
DIFFERENT relations — ``rb ⊆ rk`` (``K_a φ → B_a φ``), ``rb ⊆ rs``
(``Say_a φ → B_a φ``), ``∀w ∃v. d w v ∧ r w v`` (``Oφ → ◇φ``) — would need edge
rules that copy or jointly witness across relations, and this tableau has none:
every structural rule above acts within a single relation. Rather than accept a
``bridges=`` request and quietly decide a *different* (weaker) logic, every public
entry point takes ``bridges=None`` and **raises** ``NotImplementedError`` naming the
routes that do implement the option — ``fol.qml.qml_is_valid`` /
``fol.qml.qml_axioms`` and ``hol.isabelle_modal.to_isabelle_modal`` /
``hol.thf_modal.to_thf_modal_full``. Without the guard a caller that threaded
``bridges=`` through the toolkit would get ``invalid`` here and ``valid`` there for
the same formula, which is precisely the cross-route disagreement the option was
introduced to remove.

**Soundness vs. completeness.** Every rule preserves satisfiability over its frame
class, so a *closed* tableau is a real proof — ``is_modal_valid`` only returns ``True``
when the tableau closes. Termination on the transitive logics relies on subset
*blocking*, and the whole search is bounded (``max_worlds`` / ``max_steps`` and an optional
wall-clock ``timeout`` in milliseconds, which every public entry point takes and the search
checks at every step; a bound hit is ``"unknown"``, never an exception); to keep
the *invalid* verdict trustworthy regardless of any blocking/bound effect, an open
branch's model is **verified** with :func:`satisfies_modal` before it is reported, and
a model that fails to falsify the formula downgrades the answer to ``"unknown"`` rather
than risk a wrong ``"invalid"``. The result is the same valid / invalid / unknown
contract as the local-Isabelle runner, but in-process and install-free.

Public API: :func:`modal_tableau_closed`, :func:`is_modal_valid`, :func:`modal_prove`,
:func:`modal_decide`, :func:`modal_countermodel`.
"""

import time
from typing import List, Optional, Tuple

from .._deadline import DeadlineReached
from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Contrast,
    Box, Diamond, Knows, Believes, Says, Wants, Obligatory, Permitted,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    Next, Always, Eventually, Until,
    Historically, Once, Previous, Since,
    Nominal, At, Would, Might,
    Quantifier, SortedQuantifier, Count, SortedCount,
    Cardinality, SortedCardinality, SecondOrderQuantifier,
)
from ..fol._modal_nodes import Announce, AnnounceDiamond
# Down (the ↓ binder, N1) is not yet re-exported through fol.nodes / fol's
# public __init__ / the top-level unicode_logic_kit package (that three-file
# edit is outside this change's file ownership — see the change's own
# report); imported directly from its defining module in the meantime, the
# same class object either import path would give.
from ..fol._hybrid_nodes import Down
from ..fol.pal import reduce_announcements
from ..semantics.kripke import KripkeModel, satisfies_modal
from ..semantics._modal_reject import reject_equality_in
from ..fol.frames import (
    FRAME_CONDITIONS, FRAMES as _SHARED_FRAMES,
    UnsupportedFrameCondition, resolve_frame, require_supported,
)
from ..fol._atom_keys import refuse_alike_agents
from ..fol._truth_constants import is_true_constant, is_truth_constant
from .fitch import is_falsum
from .lj import _forget_constant_sorts


# Relation names — the contract with semantics.kripke.KripkeModel.
_ALETHIC = "alethic"
_DEONTIC = "deontic"
_TEMPORAL = "temporal"
_KNOWS = "K:"
_BELIEVES = "B:"
_SAYS = "Say:"
_WANTS = "Want:"

#: The named modal systems, shared with every other route
#: (:mod:`unicode_logic_kit.fol.frames`). This tableau implements the rules for
#: five of the conditions in that registry — reflexivity, transitivity,
#: symmetry, seriality, euclideanness — and REFUSES the rest by name
#: (:data:`_TABLEAU_CONDITIONS` / :func:`_check_frame`): a labelled tableau
#: for density or partial functionality needs rules this module does not
#: have, and quietly dropping the condition would answer about a larger
#: frame class than the caller asked for.
_FRAMES = _SHARED_FRAMES

#: The frame conditions this tableau has sound rules for.
_TABLEAU_CONDITIONS = frozenset({"refl", "trans", "sym", "serial", "eucl"})

# Operators needing least/greatest-fixpoint (eventuality) or converse-relation
# machinery beyond this labelled tableau — routed to satisfies_modal / Isabelle.
_TEMPORAL_CLOSURE = (Always, Eventually, Until, Historically, Once, Previous, Since)


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic agent term (its name)."""
    return getattr(agent, "name", None) or agent.to_unicode_str()


# ---------------------------------------------------------------------------
# Distributed knowledge (D_G): a box over the INTERSECTION of the group's
# per-agent "K:"+agent relations.
# ---------------------------------------------------------------------------
#
# Every OTHER box/diamond rule here acts on ONE named relation (`_apply_boxes`
# just pushes a box's body to `b.rels[relname]`'s successors; `_frame_close`
# closes ONE relation's edges under its own frame conditions). Distributed
# knowledge needs a box over several relations' INTERSECTION at once, which
# is not a relation _frame_close (or anything else here) already builds. The
# fix is additive rather than new machinery in the search loop itself: a D_G
# box is filed under a SYNTHETIC relation name that encodes its own
# constituent "K:"+agent names (`_distributed_relname`), and `_close_distributed`
# — run to fixpoint alongside `_frame_close`/`_apply_boxes` in `_solve` — keeps
# that synthetic relation's edge set equal to the intersection of its
# constituents' CURRENT edges every round (constituents only ever GROW during
# search — frame closure, or a nested diamond inside one of them — so this
# recompute is monotonic and terminates for exactly the reason `_frame_close`'s
# own transitive closure does). satisfies_modal itself never reads a "D∩:…"
# key — semantics.action_models.distributed_knowledge_holds recomputes the
# SAME intersection directly from "K:"+agent — so the synthetic name is purely
# an internal tableau bookkeeping device; `_build_model` happening to carry it
# along into the returned KripkeModel is harmless (an extra relation entry
# nothing downstream queries).
#
# A constituent "K:"+agent relation must also be FRAME-CLOSED under the
# caller's requested epistemic system (S5 reflexivity, etc.) even when the
# agent is mentioned nowhere else in the formula — otherwise D_G's box would
# quantify over an intersection of relations the search never applied the
# requested frame conditions to, which is unsound the moment any of those
# conditions matters (e.g. S5 factivity: D_a P → P needs "K:a" reflexive).
# `_frame_close` only ever looks at `_relnames(b)` (`b.rels`'s keys plus box
# relation names), so `_close_distributed` REGISTERS each constituent in
# `b.rels` (even with no edges yet) the first time it sees a synthetic D∩ key
# — this alone makes the constituent "live" for the next `_frame_close` pass,
# which is why the registration also reports `changed`: the `_solve` fixpoint
# loop (`_frame_close` / `_close_distributed` / `_apply_boxes`) must run one
# more round for that newly-live relation to actually pick up its reflexive/
# transitive/etc. edges before the intersection is (re)computed from them.
#
# Only the POSITIVE (box) occurrence of D_G is given a rule: the negated form
# ¬D_G φ (a diamond over the intersection) would need a fresh witness world
# added to EVERY constituent relation at once — the generic diamond rule in
# `_solve` adds an edge to exactly ONE named relation, and adding it only to
# the synthetic key would just be erased by the next `_close_distributed`
# pass (it is not yet in every constituent). Rather than special-case the
# generic diamond-witness step for one synthetic relation family, ¬D_G is left
# `"unsupported"` (inert, sound, see `_expand_simple`) — this still decides
# every validity of the shape `D_G φ → …` (the useful direction: D_G occurs
# POSITIVELY once its negation-as-premise is pushed through), which is what
# the box rule below is for.
_DISTRIBUTED_PREFIX = "D∩:"
_DISTRIBUTED_SEP = "|"


def _distributed_relname(agent_keys) -> str:
    """Synthetic relation name for a D_G box: encodes its own "K:"+agent
    constituents (sorted, so the same group always yields the same key)."""
    names = sorted(_KNOWS + a for a in agent_keys)
    return _DISTRIBUTED_PREFIX + _DISTRIBUTED_SEP.join(names)


def _distributed_constituents(relname: str):
    """Return the constituent relation names a synthetic D∩ key encodes, or
    None if ``relname`` is not one (an ordinary relation name never starts
    with "D∩:", since that prefix is not producible by any agent name — agent
    names lex as VARIABLE/NAME, which cannot contain "∩")."""
    if not relname.startswith(_DISTRIBUTED_PREFIX):
        return None
    return relname[len(_DISTRIBUTED_PREFIX):].split(_DISTRIBUTED_SEP)


def _close_distributed(b: "_Branch") -> bool:
    """Recompute every synthetic D∩ relation as the intersection of its
    constituents' CURRENT edges; return True iff any edge set changed.

    Also REGISTERS every constituent "K:"+agent relation in ``b.rels`` (with
    no edges, if it has none yet) the first time it is seen — this makes it
    'live' for `_frame_close` (see the module comment above), which is what
    lets an agent whose only mention is inside this D_G box still receive the
    caller's requested epistemic frame conditions (S5 reflexivity and so on).
    Registering a previously-absent constituent counts as a change so the
    `_solve` fixpoint loop runs `_frame_close` again before the intersection
    below is treated as final.
    """
    changed = False
    for relname in list(_relnames(b)):
        constituents = _distributed_constituents(relname)
        if constituents is None:
            continue
        for name in constituents:
            if name not in b.rels:
                b.rels[name] = set()
                changed = True
        inter = None
        for name in constituents:
            edges = b.rels.get(name, set())
            inter = set(edges) if inter is None else (inter & edges)
        inter = inter if inter is not None else set()
        if b.rels.get(relname) != inter:
            b.rels[relname] = inter
            changed = True
    return changed


def _neg(f: Node) -> Node:
    """Return the complementary formula of ``f`` (``¬φ`` ↔ ``φ``)."""
    return f.formula if isinstance(f, Not) else Not(f)


def has_modal(node: Node) -> bool:
    """True iff ``node`` contains any modal/temporal/epistemic/deontic/hybrid
    operator — or a counterfactual — or a public-announcement operator.

    Hybrid constructs (Nominal / At), the Lewis counterfactuals (Would / Might),
    and the PAL announcement operators (Announce / AnnounceDiamond) count as
    modal so the classical tableau routes them here, where each gets its clean,
    specific rejection (or, for Announce/AnnounceDiamond, its pal.reduce_announcements
    pre-pass — see :func:`_run`) instead of a generic no-rule error.
    """
    modal = (Box, Diamond, Knows, Believes, Says, Wants, Obligatory, Permitted,
             EverybodyKnows, DistributedKnowledge, CommonKnowledge,
             Next, Always, Eventually, Until,
             Historically, Once, Previous, Since,
             Nominal, At, Down, Would, Might, Announce, AnnounceDiamond)
    return any(isinstance(n, modal) for n in node.walk())


def _contains_hybrid(node: Node) -> bool:
    """True iff ``node`` contains a hybrid construct (a Nominal or an At)."""
    return any(isinstance(n, (Nominal, At)) for n in node.walk())


def _contains_down(node: Node) -> bool:
    """True iff ``node`` contains the ↓ binder (N1).

    ``Down.variable`` is itself a :class:`Nominal` (see fol._hybrid_nodes'
    module docstring), which means ``_contains_hybrid`` above already
    detects every ``Down``-containing formula with ZERO extra code (the
    generic ``Node._child_nodes``/``walk`` traversal is field-VALUE-typed,
    not field-NAME-typed, so it walks straight into ``Down.variable`` too).
    This function exists ONLY so ``_run`` can raise a ↓-SPECIFIC,
    undecidability-naming message ahead of that generic one — Down must
    never fall through to a generic branch (or even a correct-but-vaguer
    one) unnoticed.
    """
    return any(isinstance(n, Down) for n in node.walk())


def _contains_counterfactual(node: Node) -> bool:
    """True iff ``node`` contains a Lewis counterfactual (Would / Might)."""
    return any(isinstance(n, (Would, Might)) for n in node.walk())


#: Constructs that bind an object/predicate variable. The modal tableau is a
#: ground (propositional-modal) engine with no quantifier rules, so these are
#: treated as OPAQUE literals: a branch may still close on a syntactic
#: complement (sound — φ and ¬φ at one world are contradictory whatever φ
#: means), while an open branch's model must pass satisfies_modal verification
#: before any caller sees it, so no wrong verdict can arise from the opacity.
_QUANTIFIED = (Quantifier, SortedQuantifier, Count, SortedCount,
               Cardinality, SortedCardinality, SecondOrderQuantifier)


def _decompose(f: Node):
    """Classify a formula for the tableau.

    Returns one of:
      ``("lit",)``                         — atom / negated atom / ⊥ (closure only);
      ``("true",)``                        — ¬⊥ (always true, discard);
      ``("alpha", [comp, …])``             — assert all components at the same world;
      ``("beta", [[…], […]])``             — branch (each list one branch's components);
      ``("box", relname, body)``           — universal modality over ``relname``;
      ``("dia", relname, body)``           — existential modality over ``relname``;
      ``("unsupported", node)``            — a temporal-closure operator (G / F / U).
    """
    if is_falsum(f):
        return ("lit",)
    if is_true_constant(f):
        return ("true",)        # `$true` holds at every world: discard
    if isinstance(f, Atom):
        return ("lit",)
    if isinstance(f, _QUANTIFIED):
        # Opaque literal: no quantifier rules here, but syntactic-complement
        # closure stays sound and open models are verified before release.
        return ("lit",)

    # --- positive modal operators ---
    if isinstance(f, Box):
        return ("box", _ALETHIC, f.formula)
    if isinstance(f, Diamond):
        return ("dia", _ALETHIC, f.formula)
    if isinstance(f, Knows):
        return ("box", _KNOWS + _agent_key(f.agent), f.formula)
    if isinstance(f, Believes):
        return ("box", _BELIEVES + _agent_key(f.agent), f.formula)
    if isinstance(f, Says):
        return ("box", _SAYS + _agent_key(f.agent), f.formula)
    if isinstance(f, Wants):
        return ("box", _WANTS + _agent_key(f.agent), f.formula)
    if isinstance(f, EverybodyKnows):
        # E_G φ ≡ ⋀_{a∈G} K_a φ: an ALPHA reduction into one Knows(a, φ) per
        # agent, each of which the loop re-decomposes into its own box rule
        # on the NEXT pass — no new relation-key machinery needed (see the
        # module-level comment above _distributed_relname for why D_G, unlike
        # E_G, does need one). An empty group alpha-reduces to [] (no
        # components), which the caller treats as "nothing new asserted" —
        # correctly vacuous, matching everybody_knows's own convention.
        return ("alpha", [Knows(a, f.formula) for a in f.group])
    if isinstance(f, DistributedKnowledge):
        # D_G φ: a genuine box, over the SYNTHETIC intersection relation
        # _close_distributed keeps in sync (see the module-level comment).
        agents = tuple(_agent_key(a) for a in f.group)
        return ("box", _distributed_relname(agents), f.formula)
    if isinstance(f, CommonKnowledge):
        # C_G needs the reflexive-transitive closure of a union relation —
        # an induction/fixpoint rule this labelled tableau does not have, the
        # same G/F/U precedent below. Inert, never a wrong verdict (see
        # _expand_simple's "unsupported" branch).
        return ("unsupported", f)
    if isinstance(f, Obligatory):
        return ("box", _DEONTIC, f.formula)
    if isinstance(f, Permitted):
        return ("dia", _DEONTIC, f.formula)
    if isinstance(f, Next):
        return ("box", _TEMPORAL, f.formula)
    if isinstance(f, _TEMPORAL_CLOSURE):
        return ("unsupported", f)

    # --- positive connectives ---
    if isinstance(f, And):
        return ("alpha", [f.left, f.right])
    if isinstance(f, Contrast):
        # Concession is truth-functionally conjunction (Contrast's own contract).
        return ("alpha", [f.left, f.right])
    if isinstance(f, Or):
        return ("beta", [[f.left], [f.right]])
    if isinstance(f, Implies):
        return ("beta", [[Not(f.left)], [f.right]])
    if isinstance(f, Iff):
        return ("beta", [[f.left, f.right], [Not(f.left), Not(f.right)]])
    if isinstance(f, Xor):
        return ("beta", [[f.left, Not(f.right)], [Not(f.left), f.right]])

    # --- negations: push through ---
    if isinstance(f, Not):
        g = f.formula
        if is_falsum(g):
            return ("true",)
        if isinstance(g, Atom):
            return ("lit",)
        if isinstance(g, _QUANTIFIED):
            return ("lit",)
        if isinstance(g, Not):
            return ("alpha", [g.formula])
        if isinstance(g, And):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Contrast):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Or):
            return ("alpha", [Not(g.left), Not(g.right)])
        if isinstance(g, Implies):
            return ("alpha", [g.left, Not(g.right)])
        if isinstance(g, Iff):
            return ("beta", [[g.left, Not(g.right)], [Not(g.left), g.right]])
        if isinstance(g, Xor):
            return ("beta", [[g.left, g.right], [Not(g.left), Not(g.right)]])
        if isinstance(g, Box):
            return ("dia", _ALETHIC, Not(g.formula))
        if isinstance(g, Diamond):
            return ("box", _ALETHIC, Not(g.formula))
        if isinstance(g, Knows):
            return ("dia", _KNOWS + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, Believes):
            return ("dia", _BELIEVES + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, Says):
            return ("dia", _SAYS + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, Wants):
            return ("dia", _WANTS + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, EverybodyKnows):
            # ¬E_G φ ≡ ⋁_{a∈G} ¬K_a φ: a BETA branch, one option per agent,
            # each a single Not(Knows(a,φ)) component — which this SAME
            # negation section already turns into a diamond rule on its own
            # next pass (the `if isinstance(g, Knows)` case just above,
            # reached because `_decompose` is called again on each freshly
            # asserted Not(Knows(...))). An empty group beta-branches into
            # ZERO options, which `_solve`'s beta handling immediately reports
            # "closed" (no branch to keep the tableau open) — the correct
            # verdict, since ¬E_∅ φ negates an always-vacuously-true E_∅ φ and
            # so is itself unsatisfiable.
            return ("beta", [[Not(Knows(a, g.formula))] for a in g.group])
        if isinstance(g, DistributedKnowledge):
            # ¬D_G φ (a diamond over the intersection relation) has no rule
            # here — see the module-level comment above _distributed_relname
            # for why. Inert, sound.
            return ("unsupported", f)
        if isinstance(g, CommonKnowledge):
            return ("unsupported", f)
        if isinstance(g, Obligatory):
            return ("dia", _DEONTIC, Not(g.formula))
        if isinstance(g, Permitted):
            return ("box", _DEONTIC, Not(g.formula))
        if isinstance(g, Next):
            return ("dia", _TEMPORAL, Not(g.formula))
        if isinstance(g, _TEMPORAL_CLOSURE):
            return ("unsupported", f)

    raise NotImplementedError(
        f"modal_tableau: no rule for {type(f).__name__} {f.to_unicode_str()}")


class _OrderedSet(dict):
    """A set that iterates in the order its members were first added.

    The branch keeps each world's formulas and its box obligations in one. The search takes
    "the first" unexpanded branching formula, diamond or box obligation it meets, and which
    one it takes decides the numbering of the worlds it creates and therefore the model it
    reads off an open branch. A ``set`` of formulas (which hash their names) or of tuples
    holding a relation name iterates in an order that follows ``PYTHONHASHSEED``, so the
    same input gave a different countermodel from one process to the next; here the order is
    a function of the sequence of insertions alone, and every insertion is itself made by an
    ordered traversal, so the model is a function of the input. The rules and the bounds are
    those of a plain ``set``: only the order in which they are tried is fixed.

    A ``dict`` subclass, so membership, iteration and ``len`` keep the speed of the built-in
    container; only the set operations the search uses are spelled out.
    """

    __slots__ = ()

    def add(self, member) -> None:
        self[member] = None

    def copy(self) -> "_OrderedSet":
        duplicate = _OrderedSet()
        dict.update(duplicate, self)
        return duplicate

    def __le__(self, other) -> bool:
        """Subset test, as for a ``set`` (``other`` may be any set-like)."""
        return self.keys() <= (other.keys() if isinstance(other, dict) else other)

    def __repr__(self) -> str:
        return f"_OrderedSet({list(self)!r})"


class _Branch:
    """A single open tableau branch: labelled formulas, edges, box obligations."""

    __slots__ = ("tv", "rels", "boxes", "wcount", "expanded", "facts")

    def __init__(self):
        self.tv = {0: _OrderedSet()}         # world -> the labelled formulas, in insertion order
        self.rels = {}                       # relname -> set of (w, v) edges
        self.boxes = _OrderedSet()           # (world, relname, body) obligations, in insertion order
        self.wcount = 1                      # next fresh world id
        self.expanded = set()                # (world, formula) already consumed
        self.facts = frozenset()             # atoms true at EVERY world (sorted constants' membership)

    def copy(self) -> "_Branch":
        b = _Branch.__new__(_Branch)
        b.tv = {w: s.copy() for w, s in self.tv.items()}
        b.rels = {r: set(e) for r, e in self.rels.items()}
        b.boxes = self.boxes.copy()
        b.wcount = self.wcount
        b.expanded = set(self.expanded)
        b.facts = self.facts
        return b


class _Ctx:
    """Search budget and frame configuration shared across the branch tree."""

    def __init__(self, frame: str, systems, max_worlds: int, max_steps: int,
                 timeout: Optional[int] = None, mentioned: Tuple[str, ...] = (),
                 roots: Tuple[Node, ...] = ()):
        self.frame = frame
        self.systems = systems or {}
        # every relation name the formulas read, whether or not the search used it: the model
        # that is read off has to give each one the shape its system asks for
        self.mentioned = tuple(mentioned)
        # the formulas asserted at the root world: a model read off an open branch has to make
        # them true there, or the branch (which holds a construct it has no rule for) is no help
        self.roots = tuple(roots)
        self.max_worlds = max_worlds
        self.steps = max_steps
        self.exhausted = False
        # ``timeout`` is in milliseconds, counted from the moment the search starts.
        self.deadline = None if timeout is None else time.perf_counter() + timeout / 1000.0

    def tick(self) -> bool:
        """Charge one step; False once the step budget is gone or the deadline has passed."""
        self.steps -= 1
        if self.steps <= 0 or (self.deadline is not None and time.perf_counter() > self.deadline):
            self.exhausted = True
            self.steps = 0
            return False
        return True

    def poll(self) -> None:
        """Raise :class:`~unicode_logic_kit._deadline.DeadlineReached` once the deadline has passed.

        For the loops that run between two :meth:`tick` calls (the frame closure, the box
        rule): they read the clock themselves, so one step of the search cannot outlast the
        deadline however many worlds it has to close. No charge is made against the budget.
        :func:`_run` catches the exception and gives up the whole search.
        """
        if self.deadline is not None and time.perf_counter() > self.deadline:
            self.exhausted = True
            self.steps = 0
            raise DeadlineReached

    def conds(self, relname: str) -> Tuple[str, ...]:
        """Frame conditions for a relation name, per the configured systems."""
        if relname == _ALETHIC:
            return _FRAMES[self.frame]
        if relname == _DEONTIC:
            return _FRAMES[self.systems.get("deontic", "KD")]
        if relname == _TEMPORAL:
            return _FRAMES[self.systems.get("temporal", "K")]
        if relname.startswith(_KNOWS):
            return _FRAMES[self.systems.get("epistemic", "K")]
        if relname.startswith(_BELIEVES):
            return _FRAMES[self.systems.get("doxastic", "K")]
        return ()


def _assert(b: _Branch, w: int, f: Node) -> bool:
    """Assert ``w: f``; return True iff it was new."""
    s = b.tv.setdefault(w, _OrderedSet())
    if f in s:
        return False
    s.add(f)
    return True


def _closes(b: _Branch) -> bool:
    """True iff some world holds a formula and its negation (or ⊥).

    An atom of ``b.facts`` is true at EVERY world, so a world that holds its
    negation is contradictory too, whatever else it holds.
    """
    for s in b.tv.values():
        for f in s:
            if is_falsum(f):
                return True
            if isinstance(f, Not) and is_true_constant(f.formula):
                return True         # ¬$true is false at every world, like ⊥ and $false
            if _neg(f) in s:
                return True
            if b.facts and isinstance(f, Not) and f.formula in b.facts:
                return True
    return False


def _relations_read_by(node: Node) -> Tuple[str, ...]:
    """The relation names a modal operator reads: ``node`` itself, never its operands.

    The same names :func:`_decompose` files its box and diamond rules under (the group
    operators read the relation of each agent of the group), and the ones
    :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal` reads in the model. Every other
    node reads none.
    """
    if isinstance(node, (Box, Diamond)):
        return (_ALETHIC,)
    if isinstance(node, (Obligatory, Permitted)):
        return (_DEONTIC,)
    if isinstance(node, (Next,) + _TEMPORAL_CLOSURE):
        return (_TEMPORAL,)
    if isinstance(node, Knows):
        return (_KNOWS + _agent_key(node.agent),)
    if isinstance(node, Believes):
        return (_BELIEVES + _agent_key(node.agent),)
    if isinstance(node, Says):
        return (_SAYS + _agent_key(node.agent),)
    if isinstance(node, Wants):
        return (_WANTS + _agent_key(node.agent),)
    if isinstance(node, (EverybodyKnows, DistributedKnowledge, CommonKnowledge)):
        return tuple(_KNOWS + _agent_key(a) for a in node.group)
    return ()


def _mentioned_relations(formulas) -> Tuple[str, ...]:
    """Every relation name any of ``formulas`` reads, in the order they first occur.

    A relation is mentioned when an operator that reads it occurs ANYWHERE in a formula,
    also in a disjunct the open branch of the search does not take: the model that is read
    off an open branch has to give that relation the shape its system asks for, though the
    branch has no edge of it.
    """
    names = _OrderedSet()
    for f in formulas:
        for node in f.walk():
            for rel in _relations_read_by(node):
                names.add(rel)
    return tuple(names)


def _relnames(b: _Branch):
    """Relation names that are 'live' on this branch (have edges or box obligations),
    in the order they first appeared (a ``set`` of names would follow the hash seed)."""
    names = _OrderedSet()
    for rel in b.rels:
        names.add(rel)
    for (_w, rel, _body) in b.boxes:
        names.add(rel)
    return names


def _frame_close(b: _Branch, ctx: _Ctx) -> bool:
    """Apply reflexive/symmetric/transitive/euclidean edge rules; return True if changed.

    The closure of a large edge set takes many times the work of one search step, so it
    reads the clock itself (:meth:`_Ctx.poll`) once per edge it takes up and gives the
    whole search up at the deadline.
    """
    changed = False
    worlds = list(b.tv)
    for rel in list(_relnames(b)):
        conds = ctx.conds(rel)
        if not conds:
            continue
        edges = b.rels.setdefault(rel, set())
        if "refl" in conds:
            for w in worlds:
                ctx.poll()
                if (w, w) not in edges:
                    edges.add((w, w))
                    changed = True
        if "sym" in conds:
            for (w, v) in list(edges):
                ctx.poll()
                if (v, w) not in edges:
                    edges.add((v, w))
                    changed = True
        if "eucl" in conds:
            out = {}
            for (w, v) in edges:
                out.setdefault(w, []).append(v)
            for w, succs in out.items():
                for v in succs:
                    ctx.poll()
                    for u in succs:
                        if (v, u) not in edges:
                            edges.add((v, u))
                            changed = True
        if "trans" in conds:
            added = True
            while added:
                added = False
                for (w, v) in list(edges):
                    ctx.poll()
                    for (v2, u) in list(edges):
                        if v == v2 and (w, u) not in edges:
                            edges.add((w, u))
                            added = True
                            changed = True
    return changed


def _apply_boxes(b: _Branch, ctx: Optional[_Ctx] = None) -> bool:
    """Push every box obligation to its successors; return True if anything was new.

    With a ``ctx`` the clock is read once per obligation (see :meth:`_Ctx.poll`).
    """
    changed = False
    for (w, rel, body) in list(b.boxes):
        if ctx is not None:
            ctx.poll()
        for (a, v) in b.rels.get(rel, ()):
            if a == w and _assert(b, v, body):
                changed = True
    return changed


def _expand_simple(b: _Branch) -> bool:
    """Apply double-negation / α / box-record rules; return True if anything changed.

    A temporal-closure operator is marked inert (see the ``unsupported`` branch)
    rather than raising, keeping every verdict sound and every crash impossible.
    """
    changed = False
    for w in list(b.tv):
        for f in list(b.tv[w]):
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            tag = kind[0]
            if tag in ("lit", "true"):
                b.expanded.add((w, f))
            elif tag == "alpha":
                for comp in kind[1]:
                    if _assert(b, w, comp):
                        changed = True
                b.expanded.add((w, f))
                changed = True
            elif tag == "box":
                _, rel, body = kind
                if (w, rel, body) not in b.boxes:
                    b.boxes.add((w, rel, body))
                    changed = True
                b.expanded.add((w, f))
            elif tag == "unsupported":
                # A temporal-closure operator (G/F/U/H/P/Y/S over the closure of
                # the temporal relation) has no rule here. Leave it INERT rather
                # than raising: closure of a branch is monotone (a contradiction
                # among the expanded formulas makes the full set unsatisfiable
                # regardless of the inert ones), so "closed" verdicts stay sound;
                # and an open branch's model only ever reaches a caller after
                # satisfies_modal — which evaluates these operators exactly —
                # verifies it, so no spurious countermodel can leak. The price is
                # honest incompleteness: a branch kept open only by an inert
                # formula yields "unknown", never a wrong verdict.
                b.expanded.add((w, f))
            # beta / dia handled by the search loop
    return changed


def _find_beta(b: _Branch):
    """Return ``(w, f, options)`` for an unexpanded branching formula, or None."""
    for w in b.tv:
        for f in b.tv[w]:
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            if kind[0] == "beta":
                return (w, f, kind[1])
    return None


def _find_diamond(b: _Branch):
    """Return ``(w, f, relname, body)`` for an unexpanded diamond, or None."""
    for w in b.tv:
        for f in b.tv[w]:
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            if kind[0] == "dia":
                return (w, f, kind[1], kind[2])
    return None


def _blocked(b: _Branch, w: int, relname: str, ctx: _Ctx) -> bool:
    """Subset-blocking for transitive relations: an earlier world subsumes ``w``.

    Only applied when the relation is transitive (where unbounded regress is
    otherwise possible); sound for the K4 family and, with the counter-model
    verification downstream, safe for S5/B too.
    """
    if "trans" not in ctx.conds(relname):
        return False
    sw = b.tv.get(w, _OrderedSet())
    for u in b.tv:
        if u < w and sw <= b.tv[u]:
            return True
    return False


def _find_seriality(b: _Branch, ctx: _Ctx):
    """A serial relation with a box obligation at a world that has no successor."""
    for (w, rel, _body) in b.boxes:
        if "serial" not in ctx.conds(rel):
            continue
        if not any(a == w for (a, _v) in b.rels.get(rel, ())):
            return (w, rel)
    return None


def _build_model(b: _Branch, ctx: _Ctx) -> KripkeModel:
    """Read an open saturated branch off as a Kripke model of the frame class of ``ctx``.

    The valuation is the atoms of each world. A serial relation also needs a successor for a
    world that has none, and the search only gave one to a world with a box obligation, so
    every other dead end of such a relation sees itself here: the self-loop adds no obligation
    (the world has no box of that relation to satisfy) and keeps a transitive, symmetric or
    euclidean relation closed (a world with no successor has no path through it, and a
    euclidean relation with an edge into the world has the loop already).

    A relation the formulas read but the branch never used (its operator sits in a disjunct
    the branch does not take) has no edge on the branch, and an absent relation is the empty
    relation, which is neither reflexive nor serial. It is completed the same way: when its
    system asks for reflexivity or seriality every world sees itself. Nothing the branch
    asserts reads that relation (an assertion of one of its operators would have made it
    live), so the loops cannot change what the branch makes true; a transitive, symmetric
    or euclidean relation that has only loops is still all three. A relation whose system
    asks for none of reflexivity and seriality stays empty, which is all of them vacuously.

    The caller checks the result against the formula and the frame (see :func:`_fits_frame`
    and :func:`modal_countermodel`), which is what keeps the one construct a loop can change
    (a distributed-knowledge box over relations that are all dead ends at the world) honest.
    """
    valuation = {}
    always = {fact.to_unicode_str() for fact in b.facts}
    for w, s in b.tv.items():
        valuation[w] = {f.to_unicode_str() for f in s
                        if isinstance(f, Atom) and not is_truth_constant(f)} | always
    relations = {r: set(e) for r, e in b.rels.items()}
    worlds = set(b.tv) | {0}
    completed = _OrderedSet()
    for rel in _relnames(b):
        completed.add(rel)
    for rel in ctx.mentioned:
        completed.add(rel)
    for rel in completed:
        conds = ctx.conds(rel)
        if "refl" in conds or "serial" in conds:
            edges = relations.setdefault(rel, set())
            if "refl" in conds:
                edges.update((w, w) for w in worlds)
            seeing = {a for (a, _v) in edges}
            edges.update((w, w) for w in worlds if w not in seeing)
    return KripkeModel(worlds, relations, valuation)


def _frame_condition_holds(condition: str, edges, worlds) -> bool:
    """Whether the finite frame ``(worlds, edges)`` satisfies one of the conditions this tableau has rules for.

    The five conditions of :data:`_TABLEAU_CONDITIONS`, read straight off their definitions in
    :data:`~unicode_logic_kit.fol.frames.FRAME_CONDITIONS` in time linear in the edges and their
    out-degrees. (:func:`~unicode_logic_kit.fol.frames.holds_on_finite_frame` answers the same
    question for every condition of the registry, but its cost grows with about the fourth power
    of the number of worlds: 26 ms for a transitive chain of 40 worlds against under 1 ms here,
    and a tableau may return a model of several hundred worlds. The tests hold this check to
    the registry's on every frame of up to three worlds.)
    """
    successors: dict = {}
    for (a, v) in edges:
        successors.setdefault(a, set()).add(v)
    if condition == "refl":
        return all(w in successors.get(w, ()) for w in worlds)
    if condition == "serial":
        return all(w in successors for w in worlds)
    if condition == "sym":
        return all(a in successors.get(v, ()) for (a, v) in edges)
    if condition == "trans":
        return all(u in successors[a] for (a, v) in edges for u in successors.get(v, ()))
    if condition == "eucl":
        return all(u in successors.get(v, ()) for succs in successors.values()
                   for v in succs for u in succs)
    raise ValueError(f"modal_tableau: no check for the frame condition {condition!r}")


def _fits_frame(model: KripkeModel, ctx: _Ctx) -> bool:
    """True iff every relation of ``model`` and every relation the formulas read satisfies
    the frame conditions of its system.

    A relation the formulas read that the model does not list is the empty relation (the
    model's own reading of a missing name), and it is checked as such: a check over the
    listed relations alone passes a model with no entry for a reflexive or serial relation.
    """
    names = list(model.relations)
    names.extend(rel for rel in ctx.mentioned if rel not in model.relations)
    for rel in names:
        edges = model.relations.get(rel, ())
        for condition in ctx.conds(rel):
            if not _frame_condition_holds(condition, edges, model.worlds):
                return False
    return True


def _makes_roots_true(model: KripkeModel, ctx: _Ctx) -> bool:
    """False iff ``model``, read as it is, makes one of the root formulas false at world 0.

    A branch can be open with a formula on it that this tableau has no rule for (a negated
    distributed-knowledge formula, a temporal closure operator): the formula stays on the
    branch and the model read off it need not make it true. Whether it does is not something
    the branch can tell, so the evaluator of the kit is asked. A formula the evaluator cannot
    read in this model is left to the caller, which makes the same check and says so.
    """
    for f in ctx.roots:
        try:
            if not satisfies_modal(f, model, 0):
                return False
        except (NotImplementedError, ValueError, TypeError, KeyError, RecursionError):
            return True
    return True


def _solve(b: _Branch, ctx: _Ctx):
    """Depth-first saturation of one branch.

    Returns ``("closed", None)``, ``("open", model)``, or ``("unknown", None)``.
    """
    while True:
        if not ctx.tick():
            return ("unknown", None)
        if _closes(b):
            return ("closed", None)

        # 1) propositional + box + frame saturation to fixpoint
        progressed = True
        while progressed:
            if not ctx.tick():
                return ("unknown", None)
            progressed = False
            if _expand_simple(b):
                progressed = True
            if _frame_close(b, ctx):
                progressed = True
            if _close_distributed(b):
                progressed = True
            if _apply_boxes(b, ctx):
                progressed = True
            if _closes(b):
                return ("closed", None)

        # 2) a branching formula?
        beta = _find_beta(b)
        if beta is not None:
            w, f, options = beta
            all_closed = True
            for opt in options:
                child = b.copy()
                child.expanded.add((w, f))
                for comp in opt:
                    _assert(child, w, comp)
                res, model = _solve(child, ctx)
                if res == "open":
                    return ("open", model)
                if res != "closed":
                    all_closed = False
            return ("closed", None) if all_closed else ("unknown", None)

        # 3) an unfulfilled diamond?
        dia = _find_diamond(b)
        if dia is not None:
            w, f, relname, body = dia
            b.expanded.add((w, f))
            if _blocked(b, w, relname, ctx):
                continue
            if b.wcount >= ctx.max_worlds:
                return ("unknown", None)
            v = b.wcount
            b.wcount += 1
            b.tv.setdefault(v, _OrderedSet())
            b.rels.setdefault(relname, set()).add((w, v))
            _assert(b, v, body)
            continue

        # 4) seriality witness for a box-bearing world with no successor
        ser = _find_seriality(b, ctx)
        if ser is not None:
            w, relname = ser
            if b.wcount >= ctx.max_worlds:
                return ("unknown", None)
            v = b.wcount
            b.wcount += 1
            b.tv.setdefault(v, _OrderedSet())
            b.rels.setdefault(relname, set()).add((w, v))
            continue

        # 5) saturated and open: the model that is read off must be one of the frame class and
        # must make the root formulas true. A branch whose model is not is "unknown" and the
        # search goes on with the branches that are left, as it does for any other bound.
        model = _build_model(b, ctx)
        if _fits_frame(model, ctx) and _makes_roots_true(model, ctx):
            return ("open", model)
        return ("unknown", None)


#: How this route reads an atom — the clause :func:`_reject_equality` hands the shared
#: refusal so the message says why identity cannot be read here.
_EQUALITY_ROUTE = "the propositional modal tableau"
_EQUALITY_ATOM_READING = ("an atom is a propositional letter: a branch closes on a "
                          "syntactic complement and an open branch is read off as "
                          "a valuation of rendered atom keys")


def _reject_equality(formulas) -> None:
    """Refuse an equality / disequality atom ANYWHERE in ``formulas``, by name.

    A whole-tree scan of every formula, run by :func:`_run` before anything else
    touches them (see the module docstring's "Equality is NOT interpreted here").
    It walks the formulas exactly as the caller wrote them — announcement operators
    and all, ahead of :func:`~unicode_logic_kit.fol.pal.reduce_announcements` — so an
    atom inside an announcement or inside a quantifier this tableau would treat as an
    opaque literal is refused too, not only one in the propositional skeleton.
    """
    for f in formulas:
        reject_equality_in(f, "modal_tableau", _EQUALITY_ROUTE,
                           atom_reading=_EQUALITY_ATOM_READING)


#: The cross-family bridge names the HOL / qml routes accept. Listed here only so
#: the refusal below can name them; this module implements NONE of them.
_KNOWN_BRIDGES = ("knowledge_implies_belief", "sincerity", "ought_implies_can")


def _check_bridges(bridges) -> None:
    """Refuse any ``bridges=`` request, naming the routes that can honour it.

    A bridge is a frame condition on TWO relations at once; this tableau's
    structural rules (``_frame_close`` / ``_find_seriality``) each work inside a
    single relation, so there is no rule to apply and no sound way to approximate
    one. Accepting the argument and ignoring it would decide a strictly WEAKER
    logic than the caller asked for and would make this module disagree with the
    HOL routes on the same formula — so it raises instead, in the same style as the
    GL guard below: name the boundary, name what does express it.
    """
    if not bridges:
        return
    if isinstance(bridges, str):
        bridges = [bridges]
    raise NotImplementedError(
        f"modal_tableau: cross-family bridges {sorted(set(bridges))!r} are not "
        "supported by this tableau — a bridge constrains two DIFFERENT "
        "accessibility relations at once (e.g. rb ⊆ rk for K_aφ → "
        "B_aφ), and every structural rule here acts inside a single relation. "
        "Use a route that emits the bridge as an axiom: fol.qml.qml_is_valid / "
        "qml_axioms, or hol.isabelle_modal.to_isabelle_modal (with "
        "hol.isabelle_runner.isabelle_decide_modal) / "
        f"hol.thf_modal.to_thf_modal_full. Known bridges: {list(_KNOWN_BRIDGES)}.")


def _check_frame(frame: str, systems) -> None:
    _check_one_frame(frame)
    for fam, sys in (systems or {}).items():
        if fam not in ("epistemic", "doxastic", "deontic", "temporal"):
            raise ValueError(
                f"modal_tableau: unknown system family {fam!r} (use epistemic / "
                "doxastic / deontic / temporal).")
        _check_one_frame(sys, what=f"system {sys!r} for {fam}")


def _check_one_frame(frame: str, what: str = "") -> None:
    """Resolve a frame name and refuse every condition this tableau has no
    rule for — by name, with the route that does carry it named too."""
    try:
        conds = resolve_frame(frame)
    except ValueError as exc:
        raise ValueError(f"modal_tableau: {exc}") from None
    require_supported(
        f"modal_tableau ({what})" if what else "modal_tableau",
        conds, _TABLEAU_CONDITIONS,
        hint="This labelled tableau has rules for reflexivity, transitivity, "
             "symmetry, seriality and euclideanness only. Use the "
             "first-order route fol.qml (Z3) for the other first-order "
             "conditions, or the higher-order embeddings — "
             "hol.isabelle_modal.to_isabelle_modal / isabelle_decide_modal "
             "and hol.thf_modal.to_thf_modal_full — for the ones that are "
             "not first-order definable at all (GL, S4.1, Grz); for a "
             "bounded REFUTATION (not a proof) of those three, "
             "atp.kripke_enum.modal_enum_search decides them directly via "
             "their finite frame characterisation.")


def _refuse_unsupported_constructs(formulas) -> None:
    """Refuse, by name, a ↓ binder, a nominal / ``@`` or a counterfactual anywhere in ``formulas``."""
    for f in formulas:
        if _contains_down(f):
            # Checked BEFORE the general hybrid-constructs guard below so a
            # ↓-formula gets its own clear, undecidability-naming message
            # (N1) rather than being lumped under the general nominals/@
            # rejection — even though _contains_hybrid would ALSO already
            # catch it for free (Down.variable is a Nominal, walked
            # automatically — see _contains_down's own docstring).
            raise NotImplementedError(
                "modal_tableau: the ↓ binder is not supported by this labelled "
                "tableau — H(@,↓) validity is undecidable, and this tableau's "
                "rule set (like hybrid_is_valid's Z3 route) only ever "
                "soundly-and-completely covers DECIDABLE fragments. Use "
                "fol.modal_translation.down_is_valid (Z3, PROVED-only) or "
                "atp.kripke_enum.KripkeEnumBackend / modal_enum_search "
                "(bounded search, REFUTED-only), or evaluate directly with "
                "semantics.kripke.satisfies_modal.")
        if _contains_hybrid(f):
            raise NotImplementedError(
                "modal_tableau: hybrid constructs (nominals/@) are not supported "
                "by the modal tableau; use hybrid_is_valid or a KripkeModel.")
        if _contains_counterfactual(f):
            raise NotImplementedError(
                "modal_tableau: the counterfactuals □→/◇→ are evaluated over a "
                "similarity ordering (Lewis spheres), not an accessibility "
                "relation, so this tableau cannot decide them. Use cf_valid / "
                "cf_countermodel (bounded sphere-model search), cf_satisfies "
                "over a CounterfactualModel, or isabelle_decide_counterfactual.")


def _run(formulas, frame: str, systems, max_worlds: int, max_steps: int,
         bridges=None, timeout: Optional[int] = None, causes: Optional[List[str]] = None):
    """Build the root branch from ``formulas`` at world 0 and search it.

    ``timeout`` (milliseconds, default none) is one more bound next to ``max_worlds`` and
    ``max_steps``, checked at every step of the search and inside the frame closure and the
    box rule, which can outlast a step on a large edge set; so is Python's recursion limit
    (the search recurses once per branching formula along a branch, and every walk over a
    formula, before and during the search, once per level of its nesting). Past either bound
    the answer is ``("unknown", None)``, never an exception: also for a formula nested too
    deeply for those walks, whose guards below then cannot be run to their end.

    ``formulas`` is first run through :func:`~unicode_logic_kit.fol.pal.reduce_announcements`
    (a no-op on a formula with no Announce/AnnounceDiamond node), so every public
    entry point of this module DECIDES public-announcement formulas — no
    modal-tableau rule for Announce/AnnounceDiamond exists or is needed, since the
    reduction eliminates them into the ordinary modal fragment this tableau
    already handles, BEFORE tableau search ever begins. A temporal operator (or
    Would/Might/Nominal/At/a quantifier) found INSIDE an announcement's scope
    still raises — that is pal.reduce_announcements's own clean, precise
    NotImplementedError (unsound/undefined relativization, not this module's
    concern), propagated unchanged; see that module's docstring for why each
    case is rejected.

    Hybrid constructs are rejected up front — a nominal names ONE world, a
    constraint this labelled tableau has no rule for, and treating it as an
    ordinary atom would produce wrong verdicts (e.g. it would refute ``@i i``).
    A ``bridges=`` request is rejected here for the same reason (see
    :func:`_check_bridges`), and so is an equality / disequality atom anywhere in
    ``formulas`` (see :func:`_reject_equality` — scanned FIRST, over the formulas as
    given, so no later guard or search can answer before it has looked). Every
    public entry point funnels through here, so all three guards cover them all.
    """
    formulas = list(formulas)
    # Every walk below is recursive, so a formula nested deeper than the interpreter's stack
    # allows ends one of them in a ``RecursionError``: the answer is then "unknown" (the
    # formula was not read to its end, so nothing may be said about it). The arguments that
    # do not depend on the formulas are still checked first, so a wrong ``frame`` is refused
    # whatever the depth.
    too_deep = False
    try:
        _reject_equality(formulas)
        formulas = [reduce_announcements(f) for f in formulas]
    except RecursionError:
        too_deep = True
    _check_frame(frame, systems)
    _check_bridges(bridges)
    if too_deep:
        if causes is not None:
            causes.append("nesting")
        return ("unknown", None)
    try:
        _refuse_unsupported_constructs(formulas)
        # The operators of an agent are filed under the relation named after the agent: two
        # different agent terms of one name (the numeral 1 and the constant '1') would be one
        # agent, and a branch could close for a formula about two.
        refuse_alike_agents(formulas, "modal_tableau")
        # A sorted constant ``c:S`` is the constant ``c`` and is an element of ``S`` at every
        # world (``semantics.kripke``'s module docstring): ``Mortal(c:S)`` and ``Mortal(c)``
        # are ONE letter, and ``S(c)`` is a letter true everywhere -- a branch with its
        # negation at any world is closed, and a model read off an open branch makes it
        # true at every world, so the countermodel is one the many-sorted reading allows.
        membership: List[Node] = []
        formulas = [_forget_constant_sorts(f, membership) for f in formulas]
        ctx = _Ctx(frame, systems, max_worlds, max_steps, timeout,
                   mentioned=_mentioned_relations(formulas), roots=formulas)
        root = _Branch()
        root.facts = frozenset(membership)
        for f in formulas:
            _assert(root, 0, f)
        return _solve(root, ctx)
    except RecursionError:
        if causes is not None:
            causes.append("nesting")
        return ("unknown", None)
    except DeadlineReached:
        return ("unknown", None)


def modal_tableau_closed(formulas, frame: str = "K", systems=None,
                         max_worlds: int = 400, max_steps: int = 200000,
                         bridges=None, timeout: Optional[int] = None) -> bool:
    """Return True iff ``formulas`` are jointly unsatisfiable at a world (the tableau closes).

    Interprets the list as a set of formulas true at the same (root) world under the
    chosen ``frame`` (alethic system) and ``systems`` (per-family systems for
    epistemic / doxastic / deontic / temporal relations). Sound: a True is a real
    closed tableau. A False means "no closed tableau within the bound", never a
    positive satisfiability claim — use :func:`modal_countermodel` for that.

    ``bridges`` exists only to be REFUSED: any non-empty request raises
    ``NotImplementedError`` pointing at the routes that implement cross-family
    bridges (see :func:`_check_bridges`). An ``=`` / ``≠`` atom anywhere in the formula raises ``NotImplementedError`` (see the
    module docstring's "Equality is NOT interpreted here").
    """
    res, _ = _run(formulas, frame, systems, max_worlds, max_steps, bridges, timeout)
    return res == "closed"


def is_modal_valid(formula: Node, frame: str = "K", systems=None,
                   max_worlds: int = 400, max_steps: int = 200000,
                   bridges=None, timeout: Optional[int] = None) -> bool:
    """Return True iff ``formula`` is modally valid over ``frame`` — ``¬formula`` closes.

    Sound: only the closed tableau yields True. An open or bound-exhausted search
    yields False (the formula is then invalid-or-unknown; :func:`modal_decide`
    distinguishes the two with a verified counter-model). A non-empty ``bridges``
    raises ``NotImplementedError`` (see :func:`_check_bridges`). An ``=`` / ``≠`` atom anywhere in the formula raises ``NotImplementedError`` (see the
    module docstring's "Equality is NOT interpreted here").
    """
    res, _ = _run([Not(formula)], frame, systems, max_worlds, max_steps, bridges, timeout)
    return res == "closed"


def modal_prove(premises, conclusion: Node, frame: str = "K", systems=None,
                max_worlds: int = 400, max_steps: int = 200000,
                bridges=None, timeout: Optional[int] = None) -> bool:
    """Return True iff ``premises`` locally entail ``conclusion`` over ``frame``.

    Local consequence: the tableau for ``premises ∪ {¬conclusion}`` at one world
    closes. Sound (a True is a closed tableau); incomplete only up to the bound.
    A non-empty ``bridges`` raises ``NotImplementedError``
    (see :func:`_check_bridges`). An ``=`` / ``≠`` atom anywhere in the formula raises ``NotImplementedError`` (see the
    module docstring's "Equality is NOT interpreted here").
    """
    res, _ = _run(list(premises) + [Not(conclusion)], frame, systems,
                  max_worlds, max_steps, bridges, timeout)
    return res == "closed"


def modal_countermodel(formula: Node, frame: str = "K", systems=None,
                       max_worlds: int = 400, max_steps: int = 200000,
                       bridges=None, timeout: Optional[int] = None):
    """Return a Kripke model falsifying ``formula`` over ``frame``, or None.

    None means the formula is valid (the tableau closed) **or** the search was
    inconclusive within the bound. The returned model is *verified* twice: it is only
    handed back when :func:`satisfies_modal` confirms the formula is false at its
    root world, and when every relation of it and every relation the formula reads satisfies
    the frame conditions of its system (a serial relation gives each of its dead ends a
    successor, itself, and a relation the formula reads that the search never used gets the
    loops its system asks for; see the module docstring), so a counter-model is never
    spurious and never a structure of another frame class. A relation the formula does not
    read is not part of the model. A non-empty ``bridges``
    raises ``NotImplementedError`` (see :func:`_check_bridges`). An ``=`` / ``≠`` atom anywhere in the formula raises ``NotImplementedError`` (see the
    module docstring's "Equality is NOT interpreted here").
    """
    res, model = _run([Not(formula)], frame, systems, max_worlds, max_steps, bridges, timeout)
    if res != "open" or model is None:
        return None
    try:
        refuted = not satisfies_modal(formula, model, 0)
    except (NotImplementedError, ValueError, TypeError, KeyError, RecursionError):
        # The verifier cannot evaluate the formula in this model (e.g. an opaque
        # quantified construct with no domain information, or a formula nested deeper
        # than the evaluator can walk) — the candidate is unverifiable, so it must not
        # be handed back as a counter-model.
        refuted = False
    return model if refuted else None


def modal_decide(formula: Node, frame: str = "K", systems=None,
                 max_worlds: int = 400, max_steps: int = 200000,
                 bridges=None, timeout: Optional[int] = None) -> str:
    """Decide ``formula`` over ``frame``: ``"valid"`` / ``"invalid"`` / ``"unknown"``.

    * ``"valid"``   — the tableau for ``¬formula`` closed (a sound proof).
    * ``"invalid"`` — an open branch yielded a counter-model **verified** by
      :func:`satisfies_modal` and a model of the frame (see :func:`modal_countermodel`).
    * ``"unknown"`` — the search hit the world/step bound or the deadline, the formula
      is nested too deeply for the recursive walks, or an open branch's
      model failed verification (so neither verdict is safe to assert).

    Mirrors the valid / invalid / unknown contract of the local-Isabelle runner
    (:func:`~unicode_logic_kit.hol.isabelle_runner.isabelle_decide_modal`), but runs
    fully in-process with no external prover. A non-empty ``bridges`` raises
    ``NotImplementedError`` rather than silently deciding the bridge-free logic
    (see :func:`_check_bridges`). An ``=`` / ``≠`` atom anywhere in the formula raises ``NotImplementedError`` (see the
    module docstring's "Equality is NOT interpreted here").
    """
    return _decide_explained(formula, frame, systems, max_worlds, max_steps, bridges, timeout)[0]


def _decide_explained(formula: Node, frame: str = "K", systems=None,
                      max_worlds: int = 400, max_steps: int = 200000,
                      bridges=None, timeout: Optional[int] = None) -> Tuple[str, bool]:
    """:func:`modal_decide`'s answer, and whether the recursion limit ended one of its walks.

    The second component is true only next to ``"unknown"``: the formula was not read to its
    end (or its candidate countermodel could not be checked to its end) because a walk over
    it recursed deeper than the interpreter allows. A caller that reports the answer can then
    name the bound that was hit instead of guessing between it and the search budget.
    """
    causes: List[str] = []
    res, model = _run([Not(formula)], frame, systems, max_worlds, max_steps, bridges, timeout,
                      causes=causes)
    if res == "closed":
        return "valid", False
    if res == "open" and model is not None:
        try:
            if not satisfies_modal(formula, model, 0):
                return "invalid", False
        except RecursionError:
            causes.append("nesting")  # unverifiable candidate → honest "unknown"
        except (NotImplementedError, ValueError, TypeError, KeyError):
            pass                      # unverifiable candidate → honest "unknown"
    return "unknown", bool(causes)
