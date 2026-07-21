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

Validity is ``AX → ∀w (World(w) → ST(φ, w))``, checked with Z3. First-order modal logic
is undecidable, so this is **sound but bounded-incomplete** (Z3 may not close every
valid instance) — the model-theoretic partner is
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal` with per-world ``domains``.

Public API: :func:`qml_translate`, :func:`qml_axioms`, :func:`qml_is_valid`,
:func:`qml_equivalent`, and the constants :data:`BARCAN`, :data:`CONVERSE_BARCAN`.
"""

from functools import reduce
from typing import List, Optional

from .nodes import (
    Node, Variable, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted, SortedQuantifier,
)
from ._symbol_names import SymbolNames

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


def qml_axioms(mode: str = "constant", frame: str = "K", systems=None) -> List[Node]:
    """Return the background axioms (sort typing, frame conditions, domain regime).

    The conjunction of these is the hypothesis under which a translated formula's
    validity is checked. ``frame`` ∈ {K, T, S4, S5, KD, KD45} sets the ALETHIC system;
    ``mode`` selects the domain regime (see the module docstring for the existence-axiom
    correspondence). ``systems`` optionally sets the frame system for the AGENT-INDEXED
    epistemic / doxastic relations, e.g. ``systems={"epistemic": "S5", "doxastic": "KD45"}``
    — so knowledge can be made factive (T/S4/S5) and belief consistent (KD45), symmetric
    to the THF exporter.
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
            axioms += _agent_frame_axioms(_AGENT_FAMILIES[fam], _FRAMES[sys])
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


def _validity_formula(formula: Node, mode: str, frame: str, systems=None) -> Node:
    """Build ``⋀axioms ∧ ⋀typing-facts → ∀w (World(w) → ST(formula, w))``."""
    axioms = qml_axioms(mode, frame, systems) + _signature_typing_facts(formula)
    w = _pick_world_name(formula, "w")
    body = Implies(Atom(_WORLD, [Variable(w)]), qml_translate(formula, mode, world=w))
    closed = Quantifier(_FORALL, Variable(w), body)
    hyp = reduce(And, axioms)
    return Implies(hyp, closed)


def qml_is_valid(formula: Node, mode: str = "constant", frame: str = "K",
                 systems=None, timeout: int = 10000) -> bool:
    """Return True iff ``formula`` is QML-valid under ``mode`` / ``frame`` (via Z3).

    ``systems`` optionally sets the agent-indexed epistemic / doxastic frame systems,
    e.g. ``systems={"epistemic": "S5"}`` makes knowledge factive so ``∀x (K_x φ → φ)``
    comes out valid.

    Sound but bounded-incomplete: ``True`` means Z3 proved validity; ``False`` means it
    did not (a genuine countermodel, or — since first-order modal logic is undecidable
    — an instance Z3 could not close). For a definite countermodel use
    :func:`unicode_fol_kit.semantics.kripke.satisfies_modal` over an explicit model.
    """
    from ..atp.z3_models import is_valid
    return is_valid(_validity_formula(formula, mode, frame, systems), timeout=timeout)


def qml_equivalent(left: Node, right: Node, mode: str = "constant", frame: str = "K",
                   systems=None, timeout: int = 10000) -> bool:
    """Return True iff two modal formulas are QML-equivalent under ``mode`` / ``frame``."""
    return qml_is_valid(Iff(left, right), mode=mode, frame=frame, systems=systems,
                        timeout=timeout)


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
    """Lower-case a predicate/constant/function name for a THF functor (NOT injective).

    Use :class:`_ThfNames` to get a per-formula *unique* functor — ``_thf_name`` alone
    can map distinct symbols (``Ab`` / ``ab``) to the same functor.
    """
    if name in _THF_PRED_ALIAS:
        return _THF_PRED_ALIAS[name]
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in name)
    return (safe[:1].lower() + safe[1:]) if safe else "p"


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


def _thf_term(node: Node, names: "_ThfNames") -> str:
    """Render an individual term in THF (Variable → uppercase, else a unique functor)."""
    if isinstance(node, Variable):
        return node.name.upper()
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
        x = node.variable.name.upper()
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
