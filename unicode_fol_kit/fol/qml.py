"""Quantified modal logic via a first-order shallow embedding (Benzmüller-style, FO).

This is the *first-order fragment* of the shallow semantical embedding (SSE): a modal
formula over an explicit "current world" is translated into classical first-order
logic, so the existing back-ends (Z3, the resolution prover) can decide its validity
or the equivalence of two modal formulas. Unlike the propositional
:func:`unicode_fol_kit.fol.modal_translation.standard_translation`, this embedding
handles **object quantifiers** (`∀x` / `∃x`) under a chosen *domain regime*, so the
**Barcan** formula and its converse come out valid or invalid exactly as the regime
dictates.

Single-sorted embedding with guard predicates (worlds and individuals share one FO
sort): ``World(t)`` / ``Object(t)`` carve the two kinds apart; accessibility ``R`` is
typed World×World; existence ``E(x, w)`` ("object ``x`` exists at world ``w``") is
typed Object×World. The translation:

- ``P(t̄)`` → ``P(t̄, w)`` (the world is appended as the last argument);
- ``□φ`` → ``∀v (World(v) ∧ R(w,v) → ST(φ,v))``; ``◇φ`` → ``∃v (World(v) ∧ R(w,v) ∧ ST(φ,v))``;
- **actualist** ``∀x φ`` → ``∀x (Object(x) ∧ E(x,w) → ST(φ,w))`` and dually ``∃x``;
- **constant / possibilist** ``∀x φ`` → ``∀x (Object(x) → ST(φ,w))`` (``E`` unused).

Domain regimes (the existence-axiom correspondence, verified against the Kripke
evaluator): **decreasing** ``∀x∀w∀v(E(x,v)∧R(w,v)→E(x,w))`` validates BF; **increasing**
(cumulative) ``∀x∀w∀v(E(x,w)∧R(w,v)→E(x,v))`` validates CBF; **constant** validates both;
**varying** neither.

**One relation per modal family.** ``R`` is alethic (``□`` / ``◇``, configured by
``frame=``), ``T`` is the temporal *henceforth* relation (``Always`` / ``Eventually``
read it forward, ``Historically`` / ``Once`` read its converse), ``N`` is the *one-step
successor* (``Next``, and ``Previous`` over its converse) and ``D`` is deontic
(``Obligatory`` / ``Permitted``); the agent-indexed families use the ternary ``Rk`` /
``Rb`` / ``Rs`` / ``Rw`` (configured by ``systems=``). :func:`qml_axioms` types every
relation the formula actually uses and, for ``T`` / ``N`` / ``D``, asserts these
**default-on** frame conditions — chosen so this route agrees with
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal` and with the HOL routes, whose
``t_refl`` / ``t_trans`` / ``n_in_t`` / ``d_serial`` are the same conditions
(:mod:`unicode_fol_kit.hol.isabelle_modal`, :mod:`unicode_fol_kit.hol.thf_modal`):

- ``T`` reflexive + transitive, ``N ⊆ T``, and — when both relations occur — the
  ``first_step`` axiom below, the first-order shadow of the HOL routes' ``t_in_nstar``.
  So ``Gφ → φ``, ``Gφ → GGφ``, ``Gφ → Fφ``, ``Gφ → Xφ``, ``φ → Fφ``, the fixpoint
  unfolding ``(φ ∧ XGφ) → Gφ`` and the past mirrors ``Hφ → φ``, ``Hφ → HHφ``,
  ``Hφ → Yφ``, ``φ → Once φ`` are valid, while ``Xφ → φ``, ``φ → Gφ``, ``Fφ → Gφ``,
  ``Gφ → Hφ`` and ``Xφ → Fφ`` correctly stay invalid.
- ``D`` serial (Standard Deontic Logic, KD), the reading the ``Obligatory`` / ``Permitted``
  node docstrings already declare. ``Oφ → Pφ`` and ``Oφ → ¬O¬φ`` become valid; ``Oφ → φ``
  stays invalid. Honest contract: a ``True`` verdict for a deontic formula therefore means
  "valid over every **serial-deontic** model". ``satisfies_modal`` enforces no seriality of
  its own, so a hand-built dead-end deontic model still refutes ``Oφ → Pφ`` *there*.

**The transitive-closure limit — what stays out of reach.** ``satisfies_modal`` evaluates
``Always`` / ``Eventually`` over the reflexive-transitive CLOSURE ``N*`` of the one-step
relation, i.e. the *intended* constraint is ``T = N*``. Reflexivity, transitivity and
``N ⊆ T`` axiomatise the half ``T ⊇ N*`` (``N*`` is by definition the least refl-trans
relation containing ``N``), which is what makes the list above sound. The converse half
``T ⊆ N*`` is **not** first-order definable — the same obstacle this module already
reports for ``Until`` / ``Since`` — because it demands that the witnessing path be
*finite*. A first-order CONSEQUENCE of it is definable, however, and this route asserts it
whenever ``T`` and ``N`` both occur (``first_step``, see
:func:`_temporal_first_step_axiom`)::

    ∀w ∀v (World(w) ∧ World(v) ∧ T(w,v) → w = v ∨ ∃u (World(u) ∧ N(w,u) ∧ T(u,v)))

— "a henceforth-step is either standing still or one step followed by a henceforth-step".
Every ``T = N*`` model satisfies it, so it over-validates nothing, and with it the ``←``
direction of the fixpoint unfolding ``(φ ∧ XGφ) → Gφ`` becomes provable here (the ``→``
direction needs only ``T ⊇ N*``). Temporal induction ``(φ ∧ G(φ → Xφ)) → Gφ`` genuinely
does stay out of reach — measured: ``first_step`` does not close it — because reaching an
arbitrary ``T``-successor from the first step needs induction over the closure, which no
first-order theory states. For that one use the higher-order routes
:func:`unicode_fol_kit.hol.isabelle_modal.to_isabelle_modal` /
:func:`unicode_fol_kit.hol.isabelle_runner.isabelle_decide_modal`, whose ``t_in_nstar``
axiom pins ``t`` to ``rtranclp n``. The honest summary of this route's temporal strength
is therefore "refl + trans + ``N ⊆ T`` + ``first_step``" — a chosen axiom set, not "the
limit of first-order logic".

**Cross-family bridges** relate two families' relations and are **opt-in**: none is
emitted by default, because none of them is forced by ``satisfies_modal``. Pass
``bridges=["knowledge_implies_belief", ...]``; the table is :data:`QML_BRIDGES`, an
unknown name raises ``ValueError`` listing the known ones, and so does a bridge whose
partner family the formula never mentions. Each condition is the exact frame correspondent
of its schema and is **the same condition the HOL routes emit under the same name** —
inclusions ``Rb ⊆ Rk`` / ``Rb ⊆ Rs`` for the two agent-indexed bridges, and the meet
condition ``∀w ∃v (D(w,v) ∧ R(w,v))`` (``d_meets_r``) for ``ought_implies_can``, which is
deliberately NOT the folklore ``D ⊆ R``: see :func:`_bridge_axiom` for the measured
witnesses showing that the inclusion validates the unrequested ``□φ → Oφ`` and
``Pφ → ◇φ`` while the meet condition validates ``Oφ → ◇φ`` and neither artefact.

Validity is ``AX → ∀w (World(w) → ST(φ, w))``, checked with Z3. First-order modal logic
is undecidable, so this is **sound but bounded-incomplete** (Z3 may not close every
valid instance) — the model-theoretic partner is
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal` with per-world ``domains``.

Public API: :func:`qml_translate`, :func:`qml_axioms`, :func:`qml_is_valid`,
:func:`qml_equivalent`, and the constants :data:`BARCAN`, :data:`CONVERSE_BARCAN`,
:data:`QML_BRIDGES`.
"""

from functools import reduce
from typing import Dict, List, Optional

from .nodes import (
    Node, Variable, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted, SortedQuantifier,
)
from ._fol_nodes import constant_name_to_ascii
from ._symbol_names import SymbolNames, dedupe

# Guard / typing predicate names (the contract with the axiom set).
_WORLD = "World"
_OBJECT = "Object"
_E = "E"          # existence: E(x, w)  ≙  x ∈ D_w

# Accessibility-relation names per modality (all typed World×World).
_R_ALETHIC = "R"
_R_TEMPORAL = "T"
_R_NEXT = "N"
_R_DEONTIC = "D"
# Epistemic / doxastic / assertive / bouletic accessibility relations are
# AGENT-INDEXED ternary predicates Rk(agent, w, v) / Rb(agent, w, v) /
# Rs(agent, w, v) / Rw(agent, w, v), so the agent can be a quantified object
# variable (``∀x (Student(x) → K_x φ)``) rather than baked into the relation name.
_R_KNOWS = "Rk"
_R_BELIEVES = "Rb"
_R_SAYS = "Rs"
_R_WANTS = "Rw"

_FORALL = "∀"
_EXISTS = "∃"
_ACTUALIST_MODES = frozenset({"varying", "increasing", "cumulative", "decreasing"})
_CONSTANT_MODES = frozenset({"constant", "possibilist"})
_FRAMES = {
    "K": (), "T": ("refl",), "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"), "KD": ("serial",),
    "KD45": ("serial", "trans", "eucl"),
    "B": ("refl", "sym"),                          # Brouwer
    "S4.2": ("refl", "trans", "directed"),         # convergent (.2)
    "S4.3": ("refl", "trans", "connected"),        # no-branching / linear (.3)
    # GL (Gödel–Löb provability) is transitive + Löb. It is NOT first-order
    # definable, so qml_axioms rejects it (see the GL guard there); it is listed
    # here only so the HIGHER-ORDER THF / Isabelle exporters, which share this
    # table, accept frame="GL" and emit the Löb schema.
    "GL": ("trans", "loeb"),
}


class _Fresh:
    """Fresh world-variable generator that avoids a reserved set of names."""

    def __init__(self, reserved):
        self._n = 0
        self._reserved = set(reserved)

    def next(self) -> Variable:
        while True:
            name = f"_w{self._n}"
            self._n += 1
            if name not in self._reserved:
                return Variable(name)


def _object_var_names(node: Node) -> set:
    """All Variable names occurring in ``node`` (object variables, pre-translation)."""
    names = set()
    for n in node.walk():
        if isinstance(n, Variable):
            names.add(n.name)
    return names


def _pick_world_name(formula: Node, preferred: str) -> str:
    """Return a world-variable name not clashing with any object variable in ``formula``.

    The translation appends the current-world variable as the last argument of every
    atom (``A(x)`` → ``A(x, w)``); if the caller's world name coincides with an object
    variable the formula already binds (e.g. ``∃w A(w)`` with the default world ``w``),
    that object quantifier would *capture* the world parameter and corrupt the
    translation. Keep the preferred name when it is free, otherwise pick a fresh one.
    """
    reserved = _object_var_names(formula)
    if preferred not in reserved:
        return preferred
    n = 0
    while f"_world{n}" in reserved:
        n += 1
    return f"_world{n}"


def _box(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    v = fresh.next()
    guard = And(Atom(_WORLD, [v]), Atom(rel, [w, v]))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


def _diamond(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    v = fresh.next()
    guard = And(Atom(_WORLD, [v]), Atom(rel, [w, v]))
    return Quantifier(_EXISTS, v, And(guard, _st(body, v, fresh, mode)))


def _box_conv(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """``∀v (World(v) ∧ rel(v, w) → ST(body, v))`` — a box over the CONVERSE relation."""
    v = fresh.next()
    guard = And(Atom(_WORLD, [v]), Atom(rel, [v, w]))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


def _diamond_conv(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """``∃v (World(v) ∧ rel(v, w) ∧ ST(body, v))`` — a diamond over the CONVERSE relation."""
    v = fresh.next()
    guard = And(Atom(_WORLD, [v]), Atom(rel, [v, w]))
    return Quantifier(_EXISTS, v, And(guard, _st(body, v, fresh, mode)))


def _box_agent(rel: str, agent: Node, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """Agent-indexed □: ``∀v (World(v) ∧ rel(agent, w, v) → ST(body, v))``.

    ``agent`` is carried into the relation as a real term argument, so a bound object
    variable in agent position quantifies over agents.
    """
    v = fresh.next()
    guard = And(Atom(_WORLD, [v]), Atom(rel, [agent, w, v]))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


def _st(formula: Node, w: Variable, fresh: _Fresh, mode: str) -> Node:
    """The shallow-embedding translation ST(formula, w)."""
    if isinstance(formula, Atom):
        return Atom(formula.predicate, list(formula.args) + [w])
    if isinstance(formula, Not):
        return Not(_st(formula.formula, w, fresh, mode))
    if isinstance(formula, And):
        return And(_st(formula.left, w, fresh, mode), _st(formula.right, w, fresh, mode))
    if isinstance(formula, Or):
        return Or(_st(formula.left, w, fresh, mode), _st(formula.right, w, fresh, mode))
    if isinstance(formula, Xor):
        return Xor(_st(formula.left, w, fresh, mode), _st(formula.right, w, fresh, mode))
    if isinstance(formula, Implies):
        return Implies(_st(formula.left, w, fresh, mode), _st(formula.right, w, fresh, mode))
    if isinstance(formula, Iff):
        return Iff(_st(formula.left, w, fresh, mode), _st(formula.right, w, fresh, mode))

    if isinstance(formula, Box):
        return _box(_R_ALETHIC, w, formula.formula, fresh, mode)
    if isinstance(formula, Diamond):
        return _diamond(_R_ALETHIC, w, formula.formula, fresh, mode)
    if isinstance(formula, Knows):
        return _box_agent(_R_KNOWS, formula.agent, w, formula.formula, fresh, mode)
    if isinstance(formula, Believes):
        return _box_agent(_R_BELIEVES, formula.agent, w, formula.formula, fresh, mode)
    if isinstance(formula, Says):
        return _box_agent(_R_SAYS, formula.agent, w, formula.formula, fresh, mode)
    if isinstance(formula, Wants):
        return _box_agent(_R_WANTS, formula.agent, w, formula.formula, fresh, mode)
    if isinstance(formula, Obligatory):
        return _box(_R_DEONTIC, w, formula.formula, fresh, mode)
    if isinstance(formula, Permitted):
        return _diamond(_R_DEONTIC, w, formula.formula, fresh, mode)
    if isinstance(formula, Always):
        return _box(_R_TEMPORAL, w, formula.formula, fresh, mode)
    if isinstance(formula, Eventually):
        return _diamond(_R_TEMPORAL, w, formula.formula, fresh, mode)
    if isinstance(formula, Next):
        return _box(_R_NEXT, w, formula.formula, fresh, mode)
    if isinstance(formula, Historically):
        return _box_conv(_R_TEMPORAL, w, formula.formula, fresh, mode)
    if isinstance(formula, Once):
        return _diamond_conv(_R_TEMPORAL, w, formula.formula, fresh, mode)
    if isinstance(formula, Previous):
        return _box_conv(_R_NEXT, w, formula.formula, fresh, mode)

    if isinstance(formula, Quantifier):
        x = formula.variable
        body = _st(formula.formula, w, fresh, mode)
        obj = Atom(_OBJECT, [x])
        if mode in _ACTUALIST_MODES:
            guard = And(obj, Atom(_E, [x, w]))     # actualist: x exists at w
        else:
            guard = obj                            # constant / possibilist
        if formula.type in (_FORALL, "forall"):
            return Quantifier(_FORALL, x, Implies(guard, body))
        if formula.type in (_EXISTS, "exists"):
            return Quantifier(_EXISTS, x, And(guard, body))
        raise ValueError(f"qml: unknown quantifier type {formula.type!r}")

    if isinstance(formula, Until):
        raise NotImplementedError(
            "qml: Until is not first-order definable (needs transitive closure); "
            "evaluate it with satisfies_modal, or emit the HOL embedding with "
            "to_isabelle_modal (inductive least-fixpoint muntil)."
        )
    if isinstance(formula, Since):
        raise NotImplementedError(
            "qml: Since is not first-order definable (the backward mirror of "
            "Until — it needs a transitive-closure fixpoint); evaluate it with "
            "satisfies_modal, or emit the HOL embedding with to_isabelle_modal "
            "(inductive least-fixpoint msince) / to_thf_modal_full."
        )
    if isinstance(formula, SortedQuantifier):
        raise NotImplementedError("qml: SortedQuantifier is not supported; use a plain ∀x/∃x.")
    raise NotImplementedError(f"qml: unsupported node type {type(formula).__name__}.")


def qml_translate(formula: Node, mode: str = "constant", world: str = "w") -> Node:
    """Return the shallow-embedding translation ``ST(formula, world)`` (a classical FO Node).

    ``mode`` selects the domain regime for object quantifiers — ``"constant"`` /
    ``"possibilist"`` (unrelativised) or ``"varying"`` / ``"increasing"`` /
    ``"decreasing"`` (actualist, guarded by the existence predicate ``E``).

    If ``world`` clashes with an object variable the formula binds, a fresh world name
    is substituted to prevent that quantifier from capturing the world parameter.
    """
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"qml: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    world = _pick_world_name(formula, world)
    fresh = _Fresh(_object_var_names(formula) | {world})
    return _st(formula, Variable(world), fresh, mode)


def _v(*names):
    return [Variable(n) for n in names]


_AGENT_FAMILIES = {"epistemic": _R_KNOWS, "doxastic": _R_BELIEVES,
                   "assertive": _R_SAYS, "bouletic": _R_WANTS}


def _agent_frame_axioms(rel_name: str, conds) -> List[Node]:
    """Frame axioms for an AGENT-INDEXED relation ``Rel(a, w, v)`` (per agent ``a``).

    Mirrors the alethic frame conditions but quantifies the agent too, so a chosen
    epistemic/doxastic system (e.g. S5 for knowledge, KD45 for belief) constrains every
    agent's accessibility — making e.g. factivity ``K_a φ → φ`` valid under a reflexive
    (T/S4/S5) epistemic system.
    """
    a, w, v, u = _v("a", "w", "v", "u")
    W = lambda z: Atom(_WORLD, [z])
    O = lambda z: Atom(_OBJECT, [z])
    Rel = lambda *args: Atom(rel_name, list(args))
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    fa4 = lambda body: fa(a, fa(w, fa(v, fa(u, body))))
    out: List[Node] = [
        # typing: Rel(a, w, v) → Object(a) ∧ World(w) ∧ World(v).
        fa(a, fa(w, fa(v, Implies(Rel(a, w, v), And(O(a), And(W(w), W(v))))))),
    ]
    if "refl" in conds:
        out.append(fa(a, fa(w, Implies(And(O(a), W(w)), Rel(a, w, w)))))
    if "trans" in conds:
        out.append(fa4(Implies(
            And(And(O(a), W(w)), And(And(W(v), W(u)), And(Rel(a, w, v), Rel(a, v, u)))),
            Rel(a, w, u))))
    if "sym" in conds:
        out.append(fa(a, fa(w, fa(v, Implies(
            And(And(O(a), W(w)), And(W(v), Rel(a, w, v))), Rel(a, v, w))))))
    if "eucl" in conds:
        out.append(fa4(Implies(
            And(And(O(a), W(w)), And(And(W(v), W(u)), And(Rel(a, w, v), Rel(a, w, u)))),
            Rel(a, v, u))))
    if "serial" in conds:
        out.append(fa(a, fa(w, Implies(And(O(a), W(w)),
                   Quantifier(_EXISTS, v, And(W(v), Rel(a, w, v)))))))
    if "directed" in conds:
        out.append(fa(a, fa(w, fa(v, fa(u, Implies(
            And(And(O(a), W(w)), And(And(W(v), W(u)), And(Rel(a, w, v), Rel(a, w, u)))),
            Quantifier(_EXISTS, Variable("z"), And(W(Variable("z")),
                       And(Rel(a, v, Variable("z")), Rel(a, u, Variable("z")))))))))))
    if "connected" in conds:
        out.append(fa(a, fa(w, fa(v, fa(u, Implies(
            And(And(O(a), W(w)), And(And(W(v), W(u)), And(Rel(a, w, v), Rel(a, w, u)))),
            Or(Rel(a, v, u), Rel(a, u, v))))))))
    return out


# Every accessibility relation this embedding can introduce. ``qml_axioms`` called
# WITHOUT a formula ("give me the background theory") emits axioms for all of them.
QML_RELATIONS = (_R_ALETHIC, _R_TEMPORAL, _R_NEXT, _R_DEONTIC,
                 _R_KNOWS, _R_BELIEVES, _R_SAYS, _R_WANTS)

# Which relation each modal node reads. ``Until`` / ``Since`` are deliberately ABSENT:
# ``_st`` rejects them outright (not first-order definable), so they can never reach a
# validity query, and listing them here would suggest this route handles them.
_REL_OF_NODE = (
    ((Box, Diamond), _R_ALETHIC),
    ((Obligatory, Permitted), _R_DEONTIC),
    ((Always, Eventually, Historically, Once), _R_TEMPORAL),
    ((Next, Previous), _R_NEXT),
    ((Knows,), _R_KNOWS),
    ((Believes,), _R_BELIEVES),
    ((Says,), _R_SAYS),
    ((Wants,), _R_WANTS),
)


def _relations_used(formula: Node) -> set:
    """The accessibility relations ``formula`` actually mentions.

    Gating the frame axioms on this is **not** cosmetic. The deontic seriality axiom is
    the only ∃-quantified frame condition in the set, and Z3's model finder chokes on it:
    measured, asserting ``d_serial`` unconditionally turned ``∃x □A(x) → □∃x A(x)`` under
    varying domains — a formula with no deontic operator at all — from a 0.017 s
    countermodel into a 10 s timeout, i.e. flipped a *reported* verdict. The temporal
    axioms are near-free by comparison, but the rule is uniform: a relation that does not
    occur contributes nothing, so for a formula that uses none of ``T`` / ``N`` / ``D``
    (and no configured ``systems=`` family) :func:`qml_axioms` returns the exact same
    list — same members, same order — as it did before those axioms existed. That
    identity is load-bearing: several suite queries sit on a Z3 knife edge under a short
    timeout, where *any* perturbation of the axiom list can flip a verdict.
    """
    used = set()
    for n in formula.walk():
        for classes, rel in _REL_OF_NODE:
            if isinstance(n, classes):
                used.add(rel)
                break
    return used


def _relation_typing(rel: str) -> Node:
    """``∀w ∀v (rel(w,v) → World(w) ∧ World(v))`` — a binary relation is World×World.

    Mirrors the ``R`` typing axiom exactly. Without it a model could relate an *object*
    to a world and the guard predicates would no longer carve the universe in two.
    """
    w, v = _v("w", "v")
    return Quantifier(_FORALL, w, Quantifier(_FORALL, v, Implies(
        Atom(rel, [w, v]), And(Atom(_WORLD, [w]), Atom(_WORLD, [v])))))


def _temporal_frame_axioms() -> List[Node]:
    """``T`` is reflexive and transitive — the *henceforth* relation.

    :func:`unicode_fol_kit.semantics.kripke.satisfies_modal` evaluates ``Always`` /
    ``Eventually`` over the reflexive-transitive CLOSURE of the one-step ``"temporal"``
    edges (and ``Historically`` / ``Once`` over the closure of the reversed edges), so
    the current world is always in view and reachability composes. Asserting exactly that
    makes ``Gφ → φ``, ``Gφ → GGφ``, ``Gφ → Fφ``, ``φ → Fφ`` and the past mirrors valid
    here, matching the oracle and the Isabelle route's ``t_refl`` / ``t_trans``.

    These two axioms plus ``n_in_t`` say ``T ⊇ N*`` and no more. The converse ``T ⊆ N*``
    is not first-order definable, but a first-order CONSEQUENCE of it is, and
    :func:`_temporal_first_step_axiom` asserts it; temporal induction stays out of reach
    even so — see the module docstring and use ``isabelle_decide_modal`` for that one.
    """
    w, v, u = _v("w", "v", "u")
    W = lambda a: Atom(_WORLD, [a])
    T = lambda a, b: Atom(_R_TEMPORAL, [a, b])
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    return [
        fa(w, Implies(W(w), T(w, w))),
        fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(T(w, v), T(v, u)))), T(w, u))))),
    ]


def _next_in_temporal_axiom() -> Node:
    """``∀w ∀v (World(w) ∧ World(v) ∧ N(w,v) → T(w,v))`` — one step is a step.

    ``_st`` splits the oracle's single ``"temporal"`` relation into two symbols: ``N``
    carries the raw one-step edges that ``Next`` / ``Previous`` read, ``T`` carries the
    closure that ``Always`` / ``Eventually`` read. Decoupled, the embedding would refute
    ``Gφ → Xφ``, which the oracle validates. This inclusion restores it, and is the FO
    counterpart of ``isabelle_modal``'s ``n_in_t``.
    """
    w, v = _v("w", "v")
    return Quantifier(_FORALL, w, Quantifier(_FORALL, v, Implies(
        And(And(Atom(_WORLD, [w]), Atom(_WORLD, [v])), Atom(_R_NEXT, [w, v])),
        Atom(_R_TEMPORAL, [w, v]))))


def _temporal_first_step_axiom() -> Node:
    """``∀w ∀v (World(w) ∧ World(v) ∧ T(w,v) → w = v ∨ ∃u (World(u) ∧ N(w,u) ∧ T(u,v)))``.

    "A henceforth-step is either standing still or one step followed by a henceforth-step"
    — the FIRST STEP of the path that witnesses ``T``, made explicit. This is the
    first-order half of ``T ⊆ N*`` that *is* expressible: ``T ⊆ N*`` itself demands the
    witnessing path be finite and so is not first-order definable, but every model with
    ``T = N*`` satisfies the implication above, which is what makes asserting it sound.
    ``t_refl`` / ``t_trans`` / ``n_in_t`` alone do not entail it — they hold of any
    refl-trans superset of ``N``, including one with edges no ``N``-path underwrites.

    What it buys, measured: the ``←`` direction of the fixpoint unfolding
    ``(φ ∧ XGφ) → Gφ`` becomes provable (Z3 closes it in well under a second), where the
    shipped axioms alone left it underivable. What it does NOT buy: temporal induction
    ``(φ ∧ G(φ → Xφ)) → Gφ`` stays underivable, because unrolling the first step finitely
    many times never reaches an arbitrary ``T``-successor — that needs induction over the
    closure, which no first-order theory states. So the honest summary of this route's
    temporal strength is "refl + trans + ``N ⊆ T`` + ``first_step``", not "everything
    first-order logic can reach" and not "everything the oracle validates".

    The ``w = v`` disjunct is genuine identity: at this level ``Atom("=", [w, v])``
    lowers to Z3's own equality (``Node.to_z3`` maps binary ``=`` natively). That is a
    different symbol from an object-language ``=`` inside a modal formula, which ``_st``
    world-relativises into a ternary uninterpreted predicate — the two cannot collide.

    Emitted only when ``T`` and ``N`` BOTH occur and ``temporal_closure`` is on, mirroring
    ``isabelle_modal``'s ``t_in_nstar`` (which pins ``t = rtranclp n`` outright, HOL being
    able to say what first-order logic cannot) and for the same reason: the axiom relates
    the two relations, so it is vacuous — and misleading — unless both are in play.
    """
    w, v, u = _v("w", "v", "u")
    W = lambda a: Atom(_WORLD, [a])
    T = lambda a, b: Atom(_R_TEMPORAL, [a, b])
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    return fa(w, fa(v, Implies(
        And(And(W(w), W(v)), T(w, v)),
        Or(Atom("=", [w, v]),
           Quantifier(_EXISTS, u, And(And(W(u), Atom(_R_NEXT, [w, u])), T(u, v)))))))


def _deontic_frame_axioms() -> List[Node]:
    """``∀w (World(w) → ∃v (World(v) ∧ D(w,v)))`` — the deontic relation is serial (KD).

    Standard Deontic Logic is exactly this condition, and it is the reading the
    ``Obligatory`` / ``Permitted`` node docstrings and the :mod:`kripke` module docstring
    already declare; both HOL routes commit to it unconditionally
    (``isabelle_modal._deontic_axioms``, ``thf_modal._THF_DEONTIC_AXIOM``). It validates
    ``Oφ → Pφ`` and ``Oφ → ¬O¬φ`` and leaves ``Oφ → φ`` invalid.

    Consequence for the contract: ``True`` for a deontic formula means "valid over every
    SERIAL-deontic model". ``satisfies_modal`` itself enforces nothing, so a hand-built
    dead-end deontic model refutes ``Oφ → Pφ`` there — that is the honest reading of the
    disagreement, not a bug on either side.
    """
    w, v = _v("w", "v")
    return [Quantifier(_FORALL, w, Implies(
        Atom(_WORLD, [w]),
        Quantifier(_EXISTS, v, And(Atom(_WORLD, [v]), Atom(_R_DEONTIC, [w, v])))))]


# Cross-family bridges. Each entry names the two relations the bridge relates (with the
# operator label to quote in an error message), the schema it is named after, and the
# frame condition emitted for it.
#
# EVERY CONDITION IS THE EXACT FRAME CORRESPONDENT OF ITS SCHEMA — necessary as well as
# sufficient — and is the SAME condition ``hol.isabelle_modal`` / ``hol.thf_modal`` emit
# under the same option name, down to the fact name in ``"fact"``. One option name must
# denote one logic on every route that offers it; a route-vs-route split is exactly the
# disagreement ``bridges=`` was introduced to remove (``atp.modal_tableau`` refuses the
# option outright for the same reason).
#
# For the two agent-indexed bridges the correspondent is a relation INCLUSION: a box over
# the super-relation entails the box over the sub-relation, so the relation of the ENTAILED
# modality is the subset, and the reversed inclusion does not validate the principle.
#
# THE ``D ⊆ R`` TRAP — do NOT "simplify" ought_implies_can into an inclusion. Measured
# (:func:`_bridge_axiom` documents the witnesses): ``D ⊆ R`` on its own does not validate
# ``Oφ → ◇φ`` at all — a world with no deontic successor makes ``Oφ`` vacuously true while
# ``◇φ`` is false — and ``D ⊆ R`` TOGETHER WITH the default-on ``d_serial`` validates the
# strictly stronger ``□φ → Oφ`` ("whatever is necessary is obligatory") plus ``Pφ → ◇φ``,
# neither of which the caller asked for. The existential "meet" condition below is exactly
# right: it subsumes deontic seriality and validates the schema and nothing else.
#: The cross-family bridge schemas :func:`qml_is_valid` accepts in
#: ``bridges=[...]``, keyed by name. Each entry names the accessibility
#: relations it needs, the schema it validates, the frame condition that does
#: so, and the fact name the exporters emit. The same three names are accepted
#: by the HOL routes via :data:`unicode_fol_kit.hol.BRIDGES`.
QML_BRIDGES = {
    "knowledge_implies_belief": {
        "needs": ((_R_KNOWS, "Knows"), (_R_BELIEVES, "Believes")),
        "schema": "K_a φ → B_a φ",
        "condition": "Rb ⊆ Rk",
        "fact": "rb_in_rk",
    },
    "sincerity": {
        "needs": ((_R_SAYS, "Says"), (_R_BELIEVES, "Believes")),
        "schema": "Say_a φ → B_a φ",
        "condition": "Rb ⊆ Rs",
        "fact": "rb_in_rs",
    },
    "ought_implies_can": {
        "needs": ((_R_DEONTIC, "Obligatory/Permitted"), (_R_ALETHIC, "□/◇")),
        "schema": "Oφ → ◇φ",
        "condition": "∀w (World(w) → ∃v (World(v) ∧ D(w,v) ∧ R(w,v)))",
        "fact": "d_meets_r",
    },
}

# The two agent-indexed bridges are inclusions between ternary relations; the deontic one
# is the binary "meet" condition. Kept next to the table so the shape of each axiom is
# read off one place.
_BRIDGE_INCLUSIONS = {
    "knowledge_implies_belief": (_R_BELIEVES, _R_KNOWS),       # Rb ⊆ Rk
    "sincerity": (_R_BELIEVES, _R_SAYS),                       # Rb ⊆ Rs
}


def _bridge_axiom(name: str) -> Node:
    """The frame condition realising the cross-family bridge ``name``.

    The two INCLUSION bridges are emitted **unguarded** — ``∀a ∀w ∀v (Rb(a,w,v) →
    Rk(a,w,v))``, not the ``Object(a) ∧ World(w) ∧ …`` guarded form. That is deliberate
    and load-bearing: the axiom constrains only the relations, every *use* site is already
    ``World``-guarded by ``_box`` / ``_diamond`` / ``_box_agent``, and a guarded version
    would silently fail to fire for a FREE agent variable, since nothing types a free
    variable as an ``Object`` — so ``∀x (K_x φ → B_x φ)`` would come out invalid.
    Soundness is untouched: any oracle model in which the inclusion holds between world
    pairs expands to a first-order model of the unguarded axiom.

    ``ought_implies_can`` is the ∃-quantified MEET condition ``∀w (World(w) → ∃v (World(v)
    ∧ D(w,v) ∧ R(w,v)))`` — every world has an alternative that is *both* deontically
    ideal and alethically possible — which is the exact correspondent of ``Oφ → ◇φ`` and
    the same condition the HOL routes emit as ``d_meets_r``. Two details:

    * Unlike the inclusions this one **must** be ``World``-guarded. Unguarded it would
      demand a ``D``-successor for every element of the universe, including objects; with
      the ``D`` typing axiom that forces every object to be a world, contradicting the
      sort-disjointness axiom — an inconsistent hypothesis, under which *everything*
      comes out valid. The guard costs nothing, since ``_box`` / ``_diamond`` only ever
      instantiate the axiom at worlds.
    * It does **not** validate the ``D ⊆ R`` artefacts ``□φ → Oφ`` and ``Pφ → ◇φ``, and
      that is a measured difference rather than a stylistic one. The frame
      ``W = {0,1,2}``, ``D = {(0,1),(0,2),(1,1),(2,2)}``, ``R = {(0,1),(1,1),(2,2)}``
      satisfies the meet condition at every world, yet refutes ``□P → OP`` at 0 (with
      ``P`` true only at 1) and ``PP → ◇P`` at 0 (with ``P`` true only at 2), while
      ``OP → ◇P`` holds — checked against ``semantics.kripke.satisfies_modal``.
    """
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    if name in _BRIDGE_INCLUSIONS:
        sub, sup = _BRIDGE_INCLUSIONS[name]
        a, w, v = _v("a", "w", "v")
        return fa(a, fa(w, fa(v, Implies(Atom(sub, [a, w, v]), Atom(sup, [a, w, v])))))
    if name != "ought_implies_can":
        raise ValueError(f"qml: no axiom shape for bridge {name!r}.")
    w, v = _v("w", "v")
    return fa(w, Implies(
        Atom(_WORLD, [w]),
        Quantifier(_EXISTS, v, And(Atom(_WORLD, [v]),
                                   And(Atom(_R_DEONTIC, [w, v]), Atom(_R_ALETHIC, [w, v]))))))


def _validate_bridges(bridges) -> List[str]:
    """Normalise and check ``bridges=``; an unknown name must never be silently ignored."""
    if not bridges:
        return []
    if isinstance(bridges, str):
        bridges = [bridges]
    names = list(bridges)
    for name in names:
        if name not in QML_BRIDGES:
            raise ValueError(
                f"qml: unknown bridge {name!r} (use one of {sorted(QML_BRIDGES)}).")
    return names


def _check_bridge_families(names: List[str], used: set) -> None:
    """Reject a bridge whose partner family does not occur in the formula.

    A bridge is a claim about how two relations sit relative to each other, so asking for
    one while the formula mentions only one of the two families is asking for something
    the query cannot express. The same three policies the HOL routes weigh apply here, and
    the same one wins (see ``hol.isabelle_modal._bridge_axioms``):

    - *skip it silently*: the caller asked for a logic and would get a strictly weaker one
      with no signal — the "silently weakened logic" failure this package refuses;
    - *emit it anyway*: not conservative. ``d_meets_r`` entails ``∃v R(w,v)``, i.e.
      seriality of the ALETHIC relation, so emitting ``ought_implies_can`` for a ``□``-only
      formula would turn ``□P → ◇P`` from invalid into valid under ``frame="K"`` — a
      silent change to the alethic logic the caller *did* select;
    - *raise*: one uniform rule for every bridge, present and future, and the same rule the
      HOL routes apply, so a ``bridges=`` call means the same thing on every route.

    ``ValueError`` — not ``NotImplementedError`` — because the route *can* express the
    bridge; the caller's formula simply does not mention one of the families.
    ``qml_axioms`` called **without** a formula asks for the whole background theory, in
    which every relation is in scope, so nothing is rejected there.
    """
    for name in names:
        spec = QML_BRIDGES[name]
        missing = [op for rel, op in spec["needs"] if rel not in used]
        if missing:
            raise ValueError(
                f"qml: the bridge {name!r} relates two modal families "
                f"({spec['condition']}), but the formula contains no "
                f"{' / '.join(missing)} operator, so that relation is unconstrained by "
                "the query. Emitting the condition anyway is not conservative — "
                "d_meets_r entails seriality of the alethic R, which would silently make "
                "□P → ◇P valid under frame='K' — and skipping it would answer for a "
                "weaker logic than requested. Drop the bridge, state the formula in both "
                "families, or call qml_axioms() without formula= for the whole "
                "background theory. (Same rule as to_isabelle_modal / to_thf_modal_full.)")


def qml_axioms(mode: str = "constant", frame: str = "K", systems=None,
               formula: Optional[Node] = None, bridges=None,
               temporal_closure: bool = True) -> List[Node]:
    """Return the background axioms (sort typing, frame conditions, domain regime).

    The conjunction of these is the hypothesis under which a translated formula's
    validity is checked. ``frame`` ∈ {K, T, S4, S5, KD, KD45} sets the ALETHIC system;
    ``mode`` selects the domain regime (see the module docstring for the existence-axiom
    correspondence). ``systems`` optionally sets the frame system for the AGENT-INDEXED
    epistemic / doxastic relations, e.g. ``systems={"epistemic": "S5", "doxastic": "KD45"}``
    — so knowledge can be made factive (T/S4/S5) and belief consistent (KD45), symmetric
    to the THF exporter.

    The temporal (``T`` reflexive + transitive, ``N ⊆ T``) and deontic (``D`` serial)
    conditions are **on by default**, which is what brings this route into agreement with
    ``satisfies_modal`` and with the Isabelle / THF exporters; see the module docstring
    for the resulting validities and for the transitive-closure limit that keeps temporal
    induction out of reach.

    ``formula`` gates the output: only the relations occurring in it are typed and
    constrained (see :func:`_relations_used` for why that matters — it is a real
    performance and *verdict* concern, not tidiness). Called **without** a formula this
    stays the "give me the whole background theory" call and emits axioms for every
    relation in :data:`QML_RELATIONS`.

    ``bridges`` is an opt-in list of cross-family frame conditions from
    :data:`QML_BRIDGES`; an unknown name raises ``ValueError`` listing the known ones, and
    so does a bridge whose partner family the ``formula`` never mentions (see
    :func:`_check_bridge_families` — the same rule the HOL routes apply, so one option
    name means one thing on every route). A requested bridge is never gated away by
    :func:`_relations_used`, but it also does not drag its relations' default frame blocks
    into scope.

    ``temporal_closure=False`` drops ``T``'s reflexivity and transitivity and the
    ``first_step`` axiom, keeping only ``N ⊆ T``, for parity with
    ``isabelle_modal_theory`` / ``to_thf_modal_full``. Be aware
    of what that means on a *decision* route: the answers are then those of a strictly
    weaker temporal logic than the one ``satisfies_modal`` implements (``Gφ → φ`` and
    ``Gφ → Fφ`` become underivable), so a ``False`` under it is not evidence about the
    oracle's temporal logic.
    """
    if frame == "GL":
        raise NotImplementedError(
            "qml: the GL (Gödel–Löb provability) frame is transitive + converse-"
            "well-founded, which is NOT first-order definable, so the Z3 embedding "
            "cannot express it. Use the higher-order embeddings to_thf_modal / "
            "to_isabelle_modal with frame='GL' (they assert the Löb schema in HOL).")
    if frame not in _FRAMES:
        raise ValueError(f"qml: unknown frame {frame!r} (use one of {sorted(_FRAMES)}).")
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"qml: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    bridge_names = _validate_bridges(bridges)
    used = set(QML_RELATIONS) if formula is None else _relations_used(formula)
    _check_bridge_families(bridge_names, used)
    x, w, v, u = _v("x", "w", "v", "u")
    t = Variable("t")
    W = lambda a: Atom(_WORLD, [a])
    O = lambda a: Atom(_OBJECT, [a])
    R = lambda a, b: Atom(_R_ALETHIC, [a, b])
    E = lambda a, b: Atom(_E, [a, b])
    fa = lambda var, body: Quantifier(_FORALL, var, body)

    axioms: List[Node] = [
        # sort discipline: worlds and objects are disjoint; both kinds are non-empty.
        fa(t, Not(And(W(t), O(t)))),
        Quantifier(_EXISTS, w, W(w)),
        Quantifier(_EXISTS, x, O(x)),
        # typing of the relations.
        fa(w, fa(v, Implies(R(w, v), And(W(w), W(v))))),
        fa(x, fa(w, Implies(E(x, w), And(O(x), W(w))))),
    ]
    # typing for the other world×world relations, only where they occur (see
    # _relations_used). The agent-indexed ones are typed by _agent_frame_axioms.
    axioms += [_relation_typing(rel)
               for rel in (_R_TEMPORAL, _R_NEXT, _R_DEONTIC) if rel in used]

    conds = _FRAMES[frame]
    if "refl" in conds:
        axioms.append(fa(w, Implies(W(w), R(w, w))))
    if "trans" in conds:
        axioms.append(fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(R(w, v), R(v, u)))), R(w, u))))))
    if "sym" in conds:
        axioms.append(fa(w, fa(v, Implies(And(And(W(w), W(v)), R(w, v)), R(v, w)))))
    if "eucl" in conds:
        axioms.append(fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(R(w, v), R(w, u)))), R(v, u))))))
    if "serial" in conds:
        axioms.append(fa(w, Implies(W(w), Quantifier(_EXISTS, v, And(W(v), R(w, v))))))
    if "directed" in conds:
        # .2 convergence: ∀w,v,u (Rwv ∧ Rwu → ∃z (Rvz ∧ Ruz)).
        axioms.append(fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(R(w, v), R(w, u)))),
            Quantifier(_EXISTS, t, And(W(t), And(R(v, t), R(u, t)))))))))
    if "connected" in conds:
        # .3 no-branching: ∀w,v,u (Rwv ∧ Rwu → Rvu ∨ Ruv). With reflexivity the
        # v=u case is covered (Rvv), so no world-equality is needed.
        axioms.append(fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(R(w, v), R(w, u)))),
            Or(R(v, u), R(u, v)))))))

    # inter-modality frame conditions (default-on; see the module docstring). Each block
    # fires only when its relation occurs, so a formula in the alethic fragment gets the
    # exact axiom list it got before these existed.
    if _R_TEMPORAL in used and temporal_closure:
        axioms += _temporal_frame_axioms()
    if _R_TEMPORAL in used and _R_NEXT in used:
        # the link is vacuous — and misleading — unless BOTH relations occur.
        axioms.append(_next_in_temporal_axiom())
        if temporal_closure:
            # ... and, when T is meant to be the closure, say that each T-step starts
            # with an N-step. Mirrors isabelle_modal's t_in_nstar, which pins t = n**.
            axioms.append(_temporal_first_step_axiom())
    if _R_DEONTIC in used:
        axioms += _deontic_frame_axioms()

    # non-empty local domains (standard classical QML: every world has an existing
    # individual). The Barcan counter-models all use non-empty domains, so this does
    # not affect BF/CBF; it makes ∀x φ → ∃x φ valid, and keeps (A) and the THF export
    # (B), which carries the same nonempty_dom axiom, in agreement.
    if mode in _ACTUALIST_MODES:
        axioms.append(fa(w, Implies(W(w), Quantifier(_EXISTS, x, And(O(x), E(x, w))))))

    # domain-regime existence axioms.
    typed = lambda body: And(And(O(x), W(w)), And(W(v), body))
    if mode in ("increasing", "cumulative", "constant"):
        axioms.append(fa(x, fa(w, fa(v, Implies(typed(And(E(x, w), R(w, v))), E(x, v))))))
    if mode in ("decreasing", "constant"):
        axioms.append(fa(x, fa(w, fa(v, Implies(typed(And(E(x, v), R(w, v))), E(x, w))))))

    # agent-indexed epistemic / doxastic frame systems (optional).
    if systems:
        for fam, sys in systems.items():
            if fam not in _AGENT_FAMILIES:
                raise ValueError(
                    f"qml: unknown modal family {fam!r} for systems= "
                    f"(use one of {sorted(_AGENT_FAMILIES)}).")
            if sys not in _FRAMES:
                raise ValueError(
                    f"qml: unknown system {sys!r} for {fam} (use one of {sorted(_FRAMES)}).")
            # both validators stay UNCONDITIONAL — a typo in systems= must be reported
            # even when the configured family does not occur in the formula.
            if _AGENT_FAMILIES[fam] in used:
                axioms += _agent_frame_axioms(_AGENT_FAMILIES[fam], _FRAMES[sys])

    # explicitly requested bridges are never gated away, but they also do not pull their
    # relations' default frame blocks into scope (see the qml_axioms docstring).
    axioms += [_bridge_axiom(name) for name in bridge_names]
    return axioms


def _signature_typing_facts(formula: Node) -> List[Node]:
    """Object-typing facts for the constants and functions of ``formula``.

    The guarded embedding sorts the universe into Worlds and Objects. A bare
    constant is otherwise UNTYPED: no model is forced to put it in Object, so
    an Object-guarded quantifier could never instantiate it — ``∀x P(x) →
    P(c)`` came out spuriously invalid, and an Object-guarded agent frame
    axiom (``systems=``) never fired for a NAMED agent. Constants (including
    numbers and agent names) denote objects rigidly, matching
    ``satisfies_modal``; a function maps objects to objects.
    """
    from .nodes import Constant as _C, Number as _N, Function as _F
    consts, funcs = {}, {}
    for n in formula.walk():
        if isinstance(n, (_C, _N)):
            consts[n.to_unicode_str()] = n
        elif isinstance(n, _F):
            funcs[(n.name, len(n.args))] = n
    facts: List[Node] = [Atom(_OBJECT, [t])
                         for _, t in sorted(consts.items())]
    for (name, arity), fn in sorted(funcs.items()):
        xs = [Variable(f"_a{i}") for i in range(arity)]
        guard = reduce(And, [Atom(_OBJECT, [x]) for x in xs])
        body = Implies(guard, Atom(_OBJECT, [type(fn)(name, xs)]))
        for x in reversed(xs):
            body = Quantifier(_FORALL, x, body)
        facts.append(body)
    return facts


def _validity_formula(formula: Node, mode: str, frame: str, systems=None,
                      bridges=None, temporal_closure: bool = True) -> Node:
    """Build ``⋀axioms ∧ ⋀typing-facts → ∀w (World(w) → ST(formula, w))``.

    The axioms are gated on ``formula``'s signature, so a query only carries the frame
    conditions of the relations it actually mentions. New parameters are APPENDED, so the
    positional call in :mod:`unicode_fol_kit.atp.resolution` keeps working unchanged and
    inherits the gating.
    """
    axioms = qml_axioms(mode, frame, systems, formula=formula, bridges=bridges,
                        temporal_closure=temporal_closure) + _signature_typing_facts(formula)
    w = _pick_world_name(formula, "w")
    body = Implies(Atom(_WORLD, [Variable(w)]), qml_translate(formula, mode, world=w))
    closed = Quantifier(_FORALL, Variable(w), body)
    hyp = reduce(And, axioms)
    return Implies(hyp, closed)


def qml_is_valid(formula: Node, mode: str = "constant", frame: str = "K",
                 systems=None, timeout: int = 10000, bridges=None,
                 temporal_closure: bool = True) -> bool:
    """Return True iff ``formula`` is QML-valid under ``mode`` / ``frame`` (via Z3).

    ``systems`` optionally sets the agent-indexed epistemic / doxastic frame systems,
    e.g. ``systems={"epistemic": "S5"}`` makes knowledge factive so ``∀x (K_x φ → φ)``
    comes out valid. ``bridges`` opts into the cross-family relation inclusions of
    :data:`QML_BRIDGES` (none by default).

    Sound but bounded-incomplete: ``True`` means Z3 proved validity; ``False`` means it
    did not (a genuine countermodel, or — since first-order modal logic is undecidable
    — an instance Z3 could not close). For a definite countermodel use
    :func:`unicode_fol_kit.semantics.kripke.satisfies_modal` over an explicit model.

    Two contract details worth knowing before reading a verdict:

    - a temporal or deontic formula is judged under the default-on frame conditions, so
      ``True`` for a deontic formula means "valid over every SERIAL-deontic model", and
      temporal induction ``(φ ∧ G(φ → Xφ)) → Gφ`` comes back ``False`` here despite
      holding in every intended model — decide that one with
      :func:`unicode_fol_kit.hol.isabelle_runner.isabelle_decide_modal`;
    - a deontic ``False`` is typically Z3 returning *unknown* rather than a countermodel:
      the ∃-quantified seriality axiom defeats its model finder, measured identical at
      1 s / 2 s / 10 s budgets (the same behaviour ``frame="KD"`` has always had). A short
      ``timeout`` therefore costs no reliability on deontic non-theorems.
    """
    from ..atp.z3_models import is_valid
    return is_valid(_validity_formula(formula, mode, frame, systems, bridges=bridges,
                                      temporal_closure=temporal_closure), timeout=timeout)


def qml_equivalent(left: Node, right: Node, mode: str = "constant", frame: str = "K",
                   systems=None, timeout: int = 10000, bridges=None,
                   temporal_closure: bool = True) -> bool:
    """Return True iff two modal formulas are QML-equivalent under ``mode`` / ``frame``."""
    return qml_is_valid(Iff(left, right), mode=mode, frame=frame, systems=systems,
                        timeout=timeout, bridges=bridges,
                        temporal_closure=temporal_closure)


# The Barcan formula and its converse, over a unary predicate A — the standard
# litmus tests for the domain regime.
def _barcan_pair():
    x = Variable("x")
    A = lambda t: Atom("A", [t])
    bf = Implies(Diamond(Quantifier(_EXISTS, x, A(x))),
                 Quantifier(_EXISTS, x, Diamond(A(x))))
    cbf = Implies(Quantifier(_EXISTS, x, Diamond(A(x))),
                  Diamond(Quantifier(_EXISTS, x, A(x))))
    return bf, cbf


BARCAN, CONVERSE_BARCAN = _barcan_pair()


# ===========================================================================
# (B) Higher-order shallow embedding — TPTP THF export (Benzmüller-style)
# ===========================================================================
#
# A genuine higher-order shallow embedding: modal propositions are functions
# ``mu > $o`` (world → bool), the modalities are λ-lifted quantifiers over the
# accessibility relation ``r``, and object quantifiers are ``existsAt``-guarded
# (actualist). The emitted THF problem is decidable by a higher-order ATP
# (Leo-III, Satallax) — the toolkit emits it the way it emits TPTP/Prover9, it
# does not run it. Covers the alethic □/◇ fragment.

_THF_DEFS = """\
thf(mnot, definition, ( mnot = ( ^ [Phi: mu>$o, W: mu] : ~ ( Phi @ W ) ) )).
thf(mand, definition, ( mand = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) & ( Psi @ W ) ) ) )).
thf(mor, definition, ( mor = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) | ( Psi @ W ) ) ) )).
thf(mimplies, definition, ( mimplies = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) => ( Psi @ W ) ) ) )).
thf(mequiv, definition, ( mequiv = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : ( ( Phi @ W ) <=> ( Psi @ W ) ) ) )).
thf(mbox, definition, ( mbox = ( ^ [Phi: mu>$o, W: mu] : ! [V: mu] : ( ( r @ W @ V ) => ( Phi @ V ) ) ) )).
thf(mdia, definition, ( mdia = ( ^ [Phi: mu>$o, W: mu] : ? [V: mu] : ( ( r @ W @ V ) & ( Phi @ V ) ) ) )).
thf(mforall, definition, ( mforall = ( ^ [Phi: $i>(mu>$o), W: mu] : ! [X: $i] : ( ( existsAt @ X @ W ) => ( Phi @ X @ W ) ) ) )).
thf(mexists, definition, ( mexists = ( ^ [Phi: $i>(mu>$o), W: mu] : ? [X: $i] : ( ( existsAt @ X @ W ) & ( Phi @ X @ W ) ) ) )).
thf(mvalid, definition, ( mvalid = ( ^ [Phi: mu>$o] : ! [W: mu] : ( Phi @ W ) ) )).\
"""

_THF_FRAME = {
    "refl": "thf(refl, axiom, ( ! [W: mu] : ( r @ W @ W ) )).",
    "trans": "thf(trans, axiom, ( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ V @ U ) ) => ( r @ W @ U ) ) )).",
    "sym": "thf(symm, axiom, ( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ W ) ) )).",
    "serial": "thf(serial, axiom, ( ! [W: mu] : ? [V: mu] : ( r @ W @ V ) )).",
    "eucl": "thf(euclid, axiom, ( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) => ( r @ V @ U ) ) )).",
    # .2 convergence: any two successors of a world have a common successor.
    "directed": "thf(directed, axiom, ( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) => ? [Z: mu] : ( ( r @ V @ Z ) & ( r @ U @ Z ) ) ) )).",
    # .3 no-branching: the successors of a world are linearly r-ordered.
    "connected": "thf(connected, axiom, ( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) => ( ( r @ V @ U ) | ( r @ U @ V ) ) ) )).",
    # GL: the Löb schema □(□Φ → Φ) → □Φ, quantified over propositions Φ (HOL only).
    "loeb": "thf(loeb, axiom, ( ! [Phi: mu > $o, W: mu] : ( ( mbox @ ( mimplies @ ( mbox @ Phi ) @ Phi ) @ W ) => ( mbox @ Phi @ W ) ) )).",
}

_THF_DOMAIN = {
    "constant": "thf(const_dom, axiom, ( ! [X: $i, W: mu] : ( existsAt @ X @ W ) )).",
    "increasing": "thf(cumulative_dom, axiom, ( ! [X: $i, W: mu, V: mu] : ( ( ( existsAt @ X @ W ) & ( r @ W @ V ) ) => ( existsAt @ X @ V ) ) )).",
    "decreasing": "thf(decreasing_dom, axiom, ( ! [X: $i, W: mu, V: mu] : ( ( ( existsAt @ X @ V ) & ( r @ W @ V ) ) => ( existsAt @ X @ W ) ) )).",
}
_THF_DOMAIN["cumulative"] = _THF_DOMAIN["increasing"]
# possibilist ≡ constant domain (every individual exists at every world): the FO
# embedding treats them identically, so the THF export must emit const_dom too —
# otherwise its actualist mforall/mexists macros would model a varying domain.
_THF_DOMAIN["possibilist"] = _THF_DOMAIN["constant"]


# Equality / inequality are NOT primitive HOL identity here: the toolkit's modal layer
# (satisfies_modal and the first-order embedding) treats `=` / `≠` as ordinary
# uninterpreted, world-relativized predicates. The THF export matches that, so all three
# embeddings agree; these aliases give them valid, distinct THF functors.
_THF_PRED_ALIAS = {"=": "feq", "≠": "fneq", "⊥": "bottom", "⊤": "top"}

# The THF export's own fixed functors. A user symbol that sanitises onto one of
# these (a predicate literally named ``r`` or ``mbox``) must NOT claim it — it
# would re-declare a built-in at a conflicting type, so the emitted problem would
# be rejected by a strict THF parser (or, worse, silently change meaning).
# :class:`_ThfNames` pre-claims them, pushing such symbols to ``r_2`` etc.
_THF_RESERVED = frozenset({
    "mu", "r", "existsAt",
    "mnot", "mand", "mor", "mimplies", "mequiv", "mbox", "mdia",
    "mforall", "mexists", "mvalid",
})


def _thf_name(name: str) -> str:
    """Lower-case ASCII predicate/constant/function stem for a THF functor (NOT injective).

    Non-ASCII characters are transliterated FIRST via
    :func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii` (ASCII passthrough;
    Greek -> conventional name; anything else -> a reversible ``uXXXX`` escape) — THF
    functors are ASCII-only (TPTP ``lower_word``), so a raw Unicode letter reaching this
    far would be silent corruption, not sanitisation. A leading digit (which can also
    now arise from a transliterated escape, though those always start with the ASCII
    letter ``u``) is prefixed with ``p`` so the result is a legal lower identifier — TPTP
    functors can never start with a digit, and unlike the predicate/constant/function
    case this class had no digit guard before, since a THF functor name in this exporter
    is always built from a Constant/Function/Atom name, and only Constant names (via the
    kit's NAME terminal) can be digit-leading in the first place.

    Use :class:`_ThfNames` to get a per-formula *unique* functor — ``_thf_name`` alone
    can map distinct symbols (``Ab`` / ``ab``, or ``theta`` / the Greek ``θ``) to the
    same functor.
    """
    if name in _THF_PRED_ALIAS:
        return _THF_PRED_ALIAS[name]
    safe = "".join(c if (c.isalnum() or c == "_") else "_"
                   for c in constant_name_to_ascii(name))
    if not safe:
        return "p"
    if safe[0].isdigit():
        safe = "p" + safe
    return safe[:1].lower() + safe[1:]


class _ThfNames(SymbolNames):
    """Per-formula THF functor resolver (the shared :class:`SymbolNames` over
    ``_thf_name`` + the equality/inequality aliases), so distinct source symbols that
    sanitise alike — ``Ab`` / ``ab`` — or a predicate used at two arities get DISTINCT
    functors. Without it ``□Ab → □ab`` could collapse to the tautology ``□ab → □ab``.
    The export's own built-in functors (``reserved``, default :data:`_THF_RESERVED`)
    are pre-claimed so no user symbol can shadow them.
    """

    def __init__(self, formula: Node, reserved=_THF_RESERVED):
        super().__init__(formula, _thf_name, _THF_PRED_ALIAS, reserved=reserved)
        self._var_map: Dict[str, str] = {}
        self._var_used: set = set()

    def variable(self, name: str) -> str:
        """Unique upper-case THF variable token for object-variable ``name``.

        THF variable tokens are the whole (transliterated) name upper-cased — the
        pre-existing convention this method preserves, including its one known
        simplification: two source names differing only by case (``x``/``X``) still
        fold onto the same token, since THF variables have no separate case-preserving
        slot the way predicate/function/constant identifiers do. What this method adds
        is (a) ASCII purity — a raw non-ASCII variable name would otherwise reach the
        THF text verbatim (just upper-cased), which is exactly the same "isalnum() lets
        Unicode letters through" gap :func:`_thf_name` had — and (b) de-collision via
        :func:`~unicode_fol_kit.fol._symbol_names.dedupe`, so two DISTINCT source names
        that only coincide AFTER transliteration (not the pre-existing case-fold above,
        which is unaffected by this fix) do not collapse into one bound variable.
        """
        if name in self._var_map:
            return self._var_map[name]
        cand = dedupe(_thf_name(name).upper(), self._var_used)
        self._var_map[name] = cand
        return cand


def _thf_term(node: Node, names: "_ThfNames") -> str:
    """Render an individual term in THF (Variable → unique upper-case token, else a
    unique functor)."""
    if isinstance(node, Variable):
        return names.variable(node.name)
    from .nodes import Constant, Number, Function
    if isinstance(node, Constant):
        return names.constant(node.name)
    if isinstance(node, Number):
        return names.constant("n" + str(node.value))
    if isinstance(node, Function):
        head = names.function(node)
        return "( " + " @ ".join([head] + [_thf_term(a, names) for a in node.args]) + " )"
    raise NotImplementedError(f"to_thf_modal: unsupported term {type(node).__name__}.")


def _thf_lift(node: Node, names: "_ThfNames") -> str:
    """Render a modal formula as a THF term of type ``mu > $o``."""
    if isinstance(node, Atom):
        # `=` / `≠` are uninterpreted world-relativized predicates (like any other),
        # NOT primitive HOL identity — so the THF meaning matches satisfies_modal.
        head = names.atom(node)
        if not node.args:
            return head
        return "( " + " @ ".join([head] + [_thf_term(a, names) for a in node.args]) + " )"
    if isinstance(node, Not):
        return f"( mnot @ {_thf_lift(node.formula, names)} )"
    if isinstance(node, And):
        return f"( mand @ {_thf_lift(node.left, names)} @ {_thf_lift(node.right, names)} )"
    if isinstance(node, Or):
        return f"( mor @ {_thf_lift(node.left, names)} @ {_thf_lift(node.right, names)} )"
    if isinstance(node, Implies):
        return f"( mimplies @ {_thf_lift(node.left, names)} @ {_thf_lift(node.right, names)} )"
    if isinstance(node, Iff):
        return f"( mequiv @ {_thf_lift(node.left, names)} @ {_thf_lift(node.right, names)} )"
    if isinstance(node, Box):
        return f"( mbox @ {_thf_lift(node.formula, names)} )"
    if isinstance(node, Diamond):
        return f"( mdia @ {_thf_lift(node.formula, names)} )"
    if isinstance(node, Quantifier):
        x = names.variable(node.variable.name)
        binder = "mforall" if node.type in (_FORALL, "forall") else "mexists"
        return f"( {binder} @ ( ^ [{x}: $i] : {_thf_lift(node.formula, names)} ) )"
    raise NotImplementedError(
        f"to_thf_modal: {type(node).__name__} is outside the alethic □/◇ fragment "
        "supported by this THF export — use "
        "unicode_fol_kit.hol.thf_modal.to_thf_modal_full, which covers the full "
        "modal family (epistemic/doxastic/assertive/bouletic/deontic/temporal "
        "incl. Until/Since, and hybrid nominals/@).")


def _thf_signature(formula: Node, names: "_ThfNames" = None) -> List[str]:
    """Type declarations for every predicate / constant / function in ``formula``.

    Uses the de-colliding :class:`_ThfNames` resolver (built from ``formula`` if not
    supplied) so each distinct symbol gets a unique functor and a unique declaration.
    """
    if names is None:
        names = _ThfNames(formula)
    decls = []
    for (name, arity), functor in sorted(names.pred.items(), key=lambda kv: kv[1]):
        typ = " > ".join(["$i"] * arity + ["mu > $o"]) if arity else "mu > $o"
        decls.append(f"thf({functor}_decl, type, ( {functor} : ( {typ} ) )).")
    for name, functor in sorted(names.const.items(), key=lambda kv: kv[1]):
        decls.append(f"thf({functor}_decl, type, ( {functor} : $i )).")
    for (name, arity), functor in sorted(names.func.items(), key=lambda kv: kv[1]):
        typ = " > ".join(["$i"] * (arity + 1))
        decls.append(f"thf({functor}_decl, type, ( {functor} : ( {typ} ) )).")
    return decls


def to_thf_modal(formula: Node, mode: str = "constant", frame: str = "K") -> str:
    """Emit a Benzmüller-style TPTP **THF** shallow embedding of ``formula``.

    Produces a complete, self-contained THF problem — type declarations, the lifted
    modal operators, the frame axioms for ``frame`` (K/T/S4/S5/KD/KD45), the
    ``existsAt`` domain axioms for ``mode`` (constant / increasing / decreasing /
    varying), and the conjecture ``mvalid @ ⟨formula⟩`` — ready for a higher-order
    ATP (Leo-III, Satallax). Covers the alethic □/◇ fragment.

    Equality ``=`` / ``≠`` is emitted as an ordinary uninterpreted (world-relativized)
    predicate, **not** primitive HOL identity, to stay faithful to ``satisfies_modal``
    and the first-order embedding; for rigid identity, add your own axioms to the output.
    """
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal: unknown frame {frame!r}.")
    lines = [
        f"% Shallow embedding of a quantified modal formula (mode={mode}, frame={frame}).",
        "% Conjecture is 'Theorem' iff the formula is QML-valid under this regime.",
        "thf(mu_type, type, ( mu : $tType )).",
        "thf(r_decl, type, ( r : ( mu > mu > $o ) )).",
        "thf(existsAt_decl, type, ( existsAt : ( $i > mu > $o ) )).",
    ]
    names = _ThfNames(formula)
    lines += _thf_signature(formula, names)
    lines.append(_THF_DEFS)
    lines.append("thf(nonempty_dom, axiom, ( ! [W: mu] : ? [X: $i] : ( existsAt @ X @ W ) )).")
    for cond in _FRAMES[frame]:
        lines.append(_THF_FRAME[cond])
    if mode in _THF_DOMAIN:
        lines.append(_THF_DOMAIN[mode])
    elif mode not in ("varying",) and mode not in _CONSTANT_MODES:
        raise ValueError(f"to_thf_modal: unknown mode {mode!r}.")
    lines.append(f"thf(goal, conjecture, ( mvalid @ {_thf_lift(formula, names)} )).")
    return "\n".join(lines) + "\n"


def to_isabelle_modal(formula: Node, mode: str = "constant", frame: str = "K") -> str:
    """Emit a complete, loadable Isabelle/HOL theory shallow-embedding ``formula``.

    This delegates to :func:`unicode_fol_kit.hol.isabelle_modal.to_isabelle_modal` — the
    real, full-modal-family exporter that emits a loadable ``theory … begin … end`` with
    every lifted operator defined and a genuine ``lemma`` (it replaced the earlier
    alethic-only skeleton). Use that module directly for the additional options
    (epistemic/doxastic/deontic/temporal coverage, the proof ``tactic``,
    ``temporal_closure``).
    """
    from ..hol.isabelle_modal import to_isabelle_modal as _real
    return _real(formula, mode=mode, frame=frame)
