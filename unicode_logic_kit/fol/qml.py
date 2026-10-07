"""Quantified modal logic via a first-order shallow embedding (Benzmüller-style, FO).

This is the *first-order fragment* of the shallow semantical embedding (SSE): a modal
formula over an explicit "current world" is translated into classical first-order
logic, so the existing back-ends (Z3, the resolution prover) can decide its validity
or the equivalence of two modal formulas. Unlike the propositional
:func:`unicode_logic_kit.fol.modal_translation.standard_translation`, this embedding
handles **object quantifiers** (`∀x` / `∃x`) under a chosen *domain regime*, so the
**Barcan** formula and its converse come out valid or invalid exactly as the regime
dictates.

Single-sorted embedding with guard predicates (worlds and individuals share one FO
sort): ``World(t)`` / ``Object(t)`` carve the two kinds apart; accessibility ``R`` is
typed World×World; existence ``E(x, w)`` ("object ``x`` exists at world ``w``") is
typed Object×World. The translation:

- ``P(t̄)`` → ``P(t̄, w)`` (the world is appended as the last argument) — for every
  predicate EXCEPT identity: ``t₁ = t₂`` → ``t₁ = t₂`` and ``t₁ ≠ t₂`` → ``¬(t₁ = t₂)``,
  with no world argument (see "Equality is rigid" below);
- ``□φ`` → ``∀v (World(v) ∧ R(w,v) → ST(φ,v))``; ``◇φ`` → ``∃v (World(v) ∧ R(w,v) ∧ ST(φ,v))``;
- **actualist** ``∀x φ`` → ``∀x (Object(x) ∧ E(x,w) → ST(φ,w))`` and dually ``∃x``;
- **constant / possibilist** ``∀x φ`` → ``∀x (Object(x) → ST(φ,w))`` (``E`` unused).

Domain regimes (the existence-axiom correspondence, verified against the Kripke
evaluator): **decreasing** ``∀x∀w∀v(E(x,v)∧R(w,v)→E(x,w))`` validates BF; **increasing**
(cumulative) ``∀x∀w∀v(E(x,w)∧R(w,v)→E(x,v))`` validates CBF; **constant** validates both;
**varying** neither.

**Equality is rigid.** An identity atom (``Atom("=", (t₁, t₂))``, what ``a = b`` parses
to; ``≠`` is its negation) is translated to the SAME binary identity over the object
terms, inside the relativised formula, with **no world argument**. So identity does not
vary by world: the necessity of identity ``a = b → □(a = b)`` and of distinctness
``a ≠ b → □(a ≠ b)`` are valid in every frame and under every domain regime, as is
``◇(a = b) → a = b``; constants and function symbols were already rigid here (``ST``
leaves terms alone), and now so is the relation between them. It is Z3's own binary
identity, so reflexivity, symmetry, transitivity and congruence (hence Leibniz's law,
``a = b → (P(a) ↔ P(b))`` and ``a = b → (□P(a) ↔ □P(b))``) come from the solver, not from
an axiom: :func:`qml_axioms` has none for equality — checked, not assumed (see
``tests/test_qml.py``). Two consequences worth stating, because they are easy to misread:

- ``□(a = b) → a = b`` is **not** valid in K — a dead-end world makes the box vacuously
  true while ``a`` and ``b`` differ — and is valid in every frame that guarantees a
  successor-or-self (T, S4, S5, KD, KD45 …). Rigidity makes the converse direction
  ``a = b → □(a = b)`` free; the direction back needs the frame.
- ``a = b`` and ``¬(a = b)`` are not valid: two terms may denote the same object or two.

*Varying domains — the choice made here.* Identity ranges over the whole **object
domain** (everything typed ``Object``), not over the local domain ``D_w`` of the
world ``ST`` is at; an equality is **not** existence-guarded. So ``a = a``,
``a = b → b = a`` and ``a = b → □(a = b)`` are valid under every mode, *including* at a
world where ``a`` does not exist (a constant outside ``D_w`` still denotes, and is
still itself). That is the reading the rest of this embedding already has for atoms on
a non-existent constant — ``P(c, w)`` is left open, neither forced true (positive free
logic) nor forced false (negative free logic) — and the rigid-designator reading of
constants (``_signature_typing_facts`` types a constant ``Object``, never ``E(c, w)``).
Existence is therefore *expressed*, not presupposed, by ``∃x (x = c)``: valid under
``constant`` / ``possibilist`` (every object exists everywhere), **not** valid under
``varying`` (nor ``increasing`` / ``decreasing``), where the constant may lie outside
``D_w`` — and ``∃x (x = c) → □∃x (x = c)`` is valid exactly under the cumulative regime
(``increasing``) and ``constant``. (Here ``c`` is a CONSTANT, a multi-letter name such as
``alice`` in the kit's syntax; a single letter is a variable, and a free variable is a
parameter, which exists at the world of evaluation: see "A free variable is a
parameter" below.) The quantifier clauses, the domain axioms and the
modes themselves are unchanged. A free-logic variant in which ``c = c`` fails for a
non-existent ``c`` would be a different (negative) logic and is deliberately not
offered; guard explicitly with ``∃x (x = c) → …`` where that reading is wanted.
The propositional evaluator :mod:`unicode_logic_kit.semantics.kripke` has no term
semantics and refuses ``=`` / ``≠`` by name instead, as do the propositional modal
tableau (:mod:`unicode_logic_kit.atp.modal_tableau`), the propositional standard
translation (:mod:`unicode_logic_kit.fol.modal_translation`) and the intuitionistic
GMT embedding (:mod:`unicode_logic_kit.hol.intuitionistic`) — one shared refusal, in
:func:`unicode_logic_kit.semantics._modal_reject.reject_equality`. The modal HOL
exports AGREE with this route: :func:`to_thf_modal`,
:mod:`unicode_logic_kit.hol.thf_modal` and :mod:`unicode_logic_kit.hol.isabelle_modal`
emit identity as the host logic's own ``=`` over the individual sort with no world
argument. So on equality a formula has exactly two fates in this kit: rigid
identity, or a refusal that names the atom.

**A free variable is a parameter.** A variable that is free in a formula names ONE unknown
individual of the object domain, the same everywhere in the formula (the assignment-wise
consequence relation of the textbooks), and it is rigid, like a constant: the same
individual at every world. Which individuals it may be depends on the domain regime. Under
``constant`` / ``possibilist`` every individual exists at every world, so the parameter is
typed ``Object(y)`` like a constant and ``∀x P(x) → P(y)`` and ``P(y) → ∃x P(x)`` are
valid. Under ``varying`` / ``increasing`` / ``decreasing`` the parameter exists at the world
of evaluation, which the validity query states as ``E(y, w)`` (the existence guard the
free-logic route gives its parameters), and nowhere else is it required to exist. So
``∀x P(x) → P(y)``, ``P(y) → ∃x P(x)`` and ``∃x (x = y)`` are valid in every regime, while
``□∀x P(x) → □P(y)`` and ``□∃x (x = y)`` are valid under ``constant`` / ``possibilist`` and
``increasing`` only: the individual may be missing from a later world of a ``varying`` or a
``decreasing`` model, and then the later world's quantifier does not reach it. A CONSTANT
is different (see "Equality is rigid"): it may lie outside the domain of the world it is
read at, so ``∃x (x = alice)`` is valid only under ``constant`` / ``possibilist``. Use a
constant for that reading, or state the existence of the individual in the formula. For a
formula with no premise the parameter reading is the universal closure of the formula
(under a varying regime: of the formula guarded by the existence of its parameters).
``P(y) → P(alice)`` and ``(P(y) ∧ Q(z)) → ∀x (P(x) ∧ Q(x))`` are not valid in any regime.
:func:`qml_translate` leaves a free variable alone; the typing and the guard are part of
the validity query (:func:`qml_validity_formula`), which :func:`qml_is_valid` and
:func:`qml_equivalent` decide.

**One relation per modal family.** ``R`` is alethic (``□`` / ``◇``, configured by
``frame=``), ``T`` is the temporal *henceforth* relation (``Always`` / ``Eventually``
read it forward, ``Historically`` / ``Once`` read its converse), ``N`` is the *one-step
successor* (``Next``, and ``Previous`` over its converse) and ``D`` is deontic
(``Obligatory`` / ``Permitted``); the agent-indexed families use the ternary ``Rk`` /
``Rb`` / ``Rs`` / ``Rw`` (configured by ``systems=``). :func:`qml_axioms` types every
relation the formula actually uses and, for ``T`` / ``N`` / ``D``, asserts these
**default-on** frame conditions — chosen so this route agrees with
:func:`unicode_logic_kit.semantics.kripke.satisfies_modal` and with the HOL routes, whose
``t_refl`` / ``t_trans`` / ``n_in_t`` / ``d_serial`` are the same conditions
(:mod:`unicode_logic_kit.hol.isabelle_modal`, :mod:`unicode_logic_kit.hol.thf_modal`):

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
:func:`unicode_logic_kit.hol.isabelle_modal.to_isabelle_modal` /
:func:`unicode_logic_kit.hol.isabelle_runner.isabelle_decide_modal`, whose ``t_in_nstar``
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
:func:`unicode_logic_kit.semantics.kripke.satisfies_modal` with per-world ``domains``.

**Many-sorted formulas** (``SortedQuantifier``, ``∀x:S φ`` / ``∃x:S φ``) are handled by
relativizing the WHOLE input formula once, at :func:`qml_translate`'s entry, into the
guarded plain FOL ``fol.to_fol`` also builds (``∀x:S φ`` → ``∀x (S(x) → φ)``, ``∃x:S φ``
→ ``∃x (S(x) ∧ φ)``) — before anything scans or translates it, so a ``SortedConstant``
anywhere in the formula (not only directly under a ``SortedQuantifier``) is relativized
too, and :func:`_signature_typing_facts` sees the resulting plain ``Constant`` like any
other. ``ST``'s existing ``P(t̄) → P(t̄, w)`` rule then appends the world argument to the
sort guard exactly as it does to every other atom — so a sort's guard predicate
``S(x, w)`` comes out WORLD-RELATIVE (not rigid): an object can be ``S`` at one world and
not at another, the same "actualist" reading the ``E``xistence guard already gives the
object domain. :func:`qml_axioms` additionally emits, per sort the formula uses, the same
"every sort is non-empty" assumption the classical routes make
(:func:`~unicode_logic_kit.fol._msfl_nodes.nonempty_sort_axioms`) — extended PER WORLD here
(``∀w (World(w) → ∃x (Object(x) [∧ E(x,w)] ∧ S(x,w)))``) to match the world-relative guard,
mirroring the existing ``nonempty_dom`` axiom's shape — so e.g. ``∀x:S P(x) → ∃x:S P(x)``
agrees with the classical Z3 verdict at every world, not just incidentally at one.

A SORTED CONSTANT ``c:S`` denotes an element of ``S``, so :func:`qml_axioms` also emits
``∀w (World(w) → S(c, w))`` for it (read from the formula as given, where the
annotation is still there; :func:`~unicode_logic_kit.fol._msfl_nodes.sort_membership_axioms`
names the constants). A constant is a rigid designator, so the fact holds at EVERY
world, and it is not guarded by ``E(c, w)``: ``c`` may lie outside the domain of a
world, which is the reading of constants this module already has. With it
``∀x:S P(x) → P(c:S)`` is valid exactly where ``∀x P(x) → P(c)`` is (every constant
domain; no actualist mode, where ``c`` may be outside ``D_w`` and the instance is not
available), and it stays invalid with a plain ``c``, which no formula places in ``S``.

Public API: :func:`qml_translate`, :func:`qml_axioms`, :func:`qml_is_valid`,
:func:`qml_equivalent`, :func:`qml_validity_formula` (the closed classical-FOL
validity query itself, e.g. for :func:`unicode_logic_kit.hets.dol.to_dol_library_from_modal`
to hand to the CASL/DOL/Hets route), and the constants :data:`BARCAN`,
:data:`CONVERSE_BARCAN`, :data:`QML_BRIDGES`.
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
from ._hybrid_nodes import Down
from ._fol_nodes import constant_name_to_ascii
from ._free_parameters import free_parameter_names
from ._identifiers import fresh_variables
from ._msfl_nodes import key_text, nonempty_sort_axioms, sort_membership_axioms
from ._truth_constants import truth_value
from .frames import (
    FRAME_CONDITIONS, FRAMES as _SHARED_FRAMES, UnsupportedFrameCondition,
    resolve_frame, parse_geach,
)
from ._numeral_symbols import numerals_as_constants, prefixed_numeral_name
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

# Every predicate name the translation itself emits. A USER predicate (or sort
# guard) with one of these names used to be read as the translation's own
# predicate once ST appended its world argument: a unary user ``R`` became
# ``R(x, w)`` — the alethic accessibility relation — so ``R(alice) →
# ◇R(alice)`` came out VALID in K, and a binary ``R`` crashed Z3 on the arity
# clash. :func:`_user_predicate` keeps the two namespaces apart.
_RESERVED_PREDICATES = frozenset({
    _WORLD, _OBJECT, _E,
    _R_ALETHIC, _R_TEMPORAL, _R_NEXT, _R_DEONTIC,
    _R_KNOWS, _R_BELIEVES, _R_SAYS, _R_WANTS,
})
# U+00B7 MIDDLE DOT: punctuation, never part of an identifier the parsers
# produce, and no reserved name ends in it.
_USER_MARK = "·"


def _user_predicate(name: str) -> str:
    """The name a USER predicate (or sort guard) gets in the translation.

    Unchanged unless the name, with any trailing ``·`` stripped, is one of
    :data:`_RESERVED_PREDICATES`; then one ``·`` is appended. The map is
    injective (a changed name ends in ``·`` and strips to a reserved name,
    which no unchanged name does) and never yields a reserved name, so a user
    predicate can no longer be confused with ``World``/``Object``/``E`` or an
    accessibility relation — and every formula that does not use those names
    translates byte-for-byte as before.
    """
    if name.rstrip(_USER_MARK) in _RESERVED_PREDICATES:
        return name + _USER_MARK
    return name


_FORALL = "∀"
_EXISTS = "∃"
_ACTUALIST_MODES = frozenset({"varying", "increasing", "cumulative", "decreasing"})
_CONSTANT_MODES = frozenset({"constant", "possibilist"})
#: The named modal systems, shared with every other route (see
#: :mod:`unicode_logic_kit.fol.frames`). A ``G(m,n,r,s)`` Scott–Lemmon spec is
#: accepted as a frame name too; ``resolve_frame`` resolves both.
_FRAMES = _SHARED_FRAMES


def _resolve_frame(frame: str, *, route: str = "qml") -> tuple:
    """The conditions of ``frame``, refusing what a FIRST-ORDER route cannot
    express: the three non-first-order conditions (Löb, McKinsey, Grz) are
    named as the scope boundary they are, with the higher-order routes that
    DO carry them pointed at — never silently dropped, which would answer
    about a larger frame class than the caller asked for."""
    try:
        conds = resolve_frame(frame)
    except ValueError as exc:
        raise ValueError(f"{route}: {exc}") from None
    for cond in conds:
        entry = FRAME_CONDITIONS.get(cond)
        if entry is not None and not entry.first_order:
            raise NotImplementedError(
                f"{route}: the frame {frame!r} needs the condition {cond!r} "
                f"({entry.description}), which the first-order embedding "
                "cannot express. Use the higher-order embeddings "
                "hol.thf_modal.to_thf_modal_full / "
                "hol.isabelle_modal.to_isabelle_modal with the same frame — "
                "they assert the schema itself.")
    return conds


def _geach_axiom(spec, W, R):
    """The Scott–Lemmon condition of ``G(m,n,r,s)`` as a closed FO axiom::

        ∀w,u,v (R^m(w,u) ∧ R^r(w,v) → ∃t (R^n(u,t) ∧ R^s(v,t)))

    ``R^0(a,b)`` is ``a = b`` and ``R^k`` for ``k > 1`` chains ``k-1``
    existentially bound intermediate worlds, each World-guarded like every
    other world variable here. The axiom is closed over its own variables,
    so it cannot capture anything in a translated formula.

    Those variables are minted by
    :func:`~unicode_logic_kit.fol._identifiers.fresh_variables` (``v0``, ``v1``,
    …). Until 0.30.0 they were ``_gw`` / ``_gu`` / ``_gv`` / ``_gt`` /
    ``_gz0``, which the kit's own VARIABLE terminal rejects — one letter plus
    digits, no underscore — so an axiom this function built could be printed
    but not read back by :func:`unicode_logic_kit.api.parse_any`.
    """
    mint = _world_minter()

    def path(a, b, k):
        if k == 0:
            return Atom("=", (a, b))
        previous, mids, conj = a, [], None
        for _ in range(k - 1):
            z = mint()
            mids.append(z)
            step = And(W(z), R(previous, z))
            conj = step if conj is None else And(conj, step)
            previous = z
        body = R(previous, b)
        if conj is not None:
            body = And(conj, body)
        for z in reversed(mids):
            body = Quantifier(_EXISTS, z, body)
        return body

    w, u, v, s = mint(), mint(), mint(), mint()
    antecedent = And(And(W(w), And(W(u), W(v))),
                     And(path(w, u, spec.m), path(w, v, spec.r)))
    consequent = Quantifier(_EXISTS, s, And(
        W(s), And(path(u, s, spec.n), path(v, s, spec.s))))
    body = Implies(antecedent, consequent)
    for var in (v, u, w):
        body = Quantifier(_FORALL, var, body)
    return body


#: The letter every world variable this module mints is built from (plus
#: digits: ``w0``, ``w1``, …). It matches the propositional standard
#: translation's own world names, so the two routes' images read alike.
_WORLD_LETTER = "w"

#: The letter the Geach axiom's own bound worlds are built from. A separate
#: letter only for readability — the axiom is closed, so it cannot capture.
_GEACH_LETTER = "v"


def _world_minter(reserved=(), letter: str = _GEACH_LETTER):
    """Return a callable minting never-repeating world Variables.

    The names are :func:`~unicode_logic_kit.fol._identifiers.fresh_variables`'
    — ``letter`` plus digits — because the translation's output has to be text
    this kit's own parser reads back. Until 0.30.0 the shapes were ``_w0`` and
    ``_gz0``, both of which :func:`unicode_logic_kit.api.parse_any` rejects.
    """
    used = set(reserved)

    def mint() -> Variable:
        name = fresh_variables(1, letter=letter, avoid=used)[0]
        used.add(name)
        return Variable(name)

    return mint


class _Fresh:
    """Fresh world-variable generator that avoids a reserved set of names.

    ``reserved`` is the object-variable names of the formula being translated
    (plus the current-world name): a world variable that reused one of them
    would be captured by the object quantifier that binds it. The names are
    ``w0``, ``w1``, … — see :func:`_world_minter`.
    """

    def __init__(self, reserved):
        self._mint = _world_minter(reserved, _WORLD_LETTER)

    def next(self) -> Variable:
        return self._mint()


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
    # The fallback is a minted name, not ``_world0``: an identifier starting
    # with an underscore is not a VARIABLE the kit's own parser accepts.
    return fresh_variables(1, letter=_WORLD_LETTER, avoid=reserved)[0]


def _box(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    v = fresh.next()
    guard = And(Atom(_WORLD, (v,)), Atom(rel, (w, v)))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


def _diamond(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    v = fresh.next()
    guard = And(Atom(_WORLD, (v,)), Atom(rel, (w, v)))
    return Quantifier(_EXISTS, v, And(guard, _st(body, v, fresh, mode)))


def _box_conv(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """``∀v (World(v) ∧ rel(v, w) → ST(body, v))`` — a box over the CONVERSE relation."""
    v = fresh.next()
    guard = And(Atom(_WORLD, (v,)), Atom(rel, (v, w)))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


def _diamond_conv(rel: str, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """``∃v (World(v) ∧ rel(v, w) ∧ ST(body, v))`` — a diamond over the CONVERSE relation."""
    v = fresh.next()
    guard = And(Atom(_WORLD, (v,)), Atom(rel, (v, w)))
    return Quantifier(_EXISTS, v, And(guard, _st(body, v, fresh, mode)))


def _box_agent(rel: str, agent: Node, w: Variable, body: Node, fresh: _Fresh, mode: str) -> Node:
    """Agent-indexed □: ``∀v (World(v) ∧ rel(agent, w, v) → ST(body, v))``.

    ``agent`` is carried into the relation as a real term argument, so a bound object
    variable in agent position quantifies over agents.
    """
    v = fresh.next()
    guard = And(Atom(_WORLD, (v,)), Atom(rel, (agent, w, v)))
    return Quantifier(_FORALL, v, Implies(guard, _st(body, v, fresh, mode)))


_EQUALITY = "="
_DISEQUALITY = "≠"
#: The two spellings the kit gives identity atoms (``a = b`` parses to
#: ``Atom("=", (a, b))``, ``a ≠ b`` to ``Atom("≠", (a, b))``). Neither may ever
#: reach the generic ``P(t̄) → P(t̄, w)`` rule: see :func:`_st_equality`.
_EQUALITY_PREDICATES = frozenset({_EQUALITY, _DISEQUALITY})


def _st_equality(atom: Atom) -> Node:
    """ST of an identity atom: the SAME binary identity, with NO world argument.

    ``t₁ = t₂`` stays ``t₁ = t₂`` and ``t₁ ≠ t₂`` becomes ``¬(t₁ = t₂)``, whatever
    world ``ST`` is currently at. That is what makes identity **rigid** (the module
    docstring's "Equality is rigid" section states the contract and the choice made
    for varying domains): the translated atom does not mention the world, so it
    cannot vary with it. It is Z3's own binary identity, so reflexivity, symmetry,
    transitivity and congruence over function symbols and predicates (Leibniz's law)
    come from the solver, not from any axiom of ours — :func:`qml_axioms` adds none.

    ``≠`` is lowered to ``¬(=)`` rather than kept as a binary ``≠`` atom because the
    two are the same relation by definition and ``¬(=)`` is the form the downstream
    consumers already read (CASL has no disequality connective at all, see
    :mod:`unicode_logic_kit.hets.dol`).

    The previous behaviour appended the world like for any other atom, turning
    ``a = b`` into a TERNARY uninterpreted predicate ``=(a, b, w)`` — so ``a = a`` was
    not valid and ``□(a = b) → a = b`` was "valid" only by reflexivity of the frame,
    never by equality. A silently re-interpreted connective is the approximation this
    package refuses; the arity check below is the same rule for a malformed atom.
    """
    if len(atom.args) != 2:
        raise ValueError(
            f"qml: equality atom {atom.predicate!r} needs exactly two terms, got "
            f"{len(atom.args)} ({atom.to_unicode_str()}). '=' / '≠' are reserved for "
            "identity and are never read as a world-relative predicate here; rename "
            "the predicate if a different relation was meant.")
    if atom.predicate == _DISEQUALITY:
        return Not(Atom(_EQUALITY, tuple(atom.args)))
    return atom


def _st(formula: Node, w: Variable, fresh: _Fresh, mode: str) -> Node:
    """The shallow-embedding translation ST(formula, w)."""
    if isinstance(formula, Down):
        # N1: this route already has no rule for plain hybrid nominals/@
        # (they fall through to the generic "unsupported node type" below,
        # naming themselves that way) — ↓ gets its OWN, named check ahead of
        # that generic one because it additionally makes validity
        # undecidable, which is worth saying explicitly rather than leaving
        # a reader to infer it from "unsupported node type Down".
        raise NotImplementedError(
            "qml: the ↓ binder is outside this first-order-modal shallow "
            "embedding (which does not cover hybrid logic at all — no "
            "nominals/@ either — and, separately, ↓ makes validity "
            "undecidable). Use "
            "unicode_logic_kit.fol.modal_translation.down_is_valid "
            "(propositional H(@,↓), Z3, PROVED-only) or "
            "unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend / "
            "modal_enum_search (bounded search, REFUTED-only), or evaluate "
            "directly with unicode_logic_kit.semantics.kripke.satisfies_modal.")
    if isinstance(formula, Atom):
        if truth_value(formula) is not None:
            return formula      # `$true` / `$false`: the same at every world, no world argument
        if formula.predicate in _EQUALITY_PREDICATES:
            return _st_equality(formula)
        return Atom(_user_predicate(formula.predicate), (*formula.args, w))
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
        obj = Atom(_OBJECT, (x,))
        guard: Node
        if mode in _ACTUALIST_MODES:
            guard = And(obj, Atom(_E, (x, w)))     # actualist: x exists at w
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
        # Delegate to the guarded plain Quantifier _relativize builds, then
        # translate THAT: _st's own Quantifier case adds the usual
        # Object/E guard, and its Atom case appends the world argument to
        # the sort guard atom exactly as it does to every other atom, so the
        # two guards compose correctly with no special-casing here (see the
        # module docstring's "Many-sorted formulas" section). Normally
        # unreachable through the public entry points, which already
        # relativize the WHOLE formula once up front (qml_translate) — kept
        # as a defensive fallback for a direct/recursive _st call on an
        # unrelativized sub-formula.
        return _st(formula._relativize([]), w, fresh, mode)
    raise NotImplementedError(f"qml: unsupported node type {type(formula).__name__}.")


def qml_translate(formula: Node, mode: str = "constant", world: str = "w") -> Node:
    """Return the shallow-embedding translation ``ST(formula, world)`` (a classical FO Node).

    ``mode`` selects the domain regime for object quantifiers — ``"constant"`` /
    ``"possibilist"`` (unrelativised) or ``"varying"`` / ``"increasing"`` /
    ``"decreasing"`` (actualist, guarded by the existence predicate ``E``).

    If ``world`` clashes with an object variable the formula binds, a fresh world name
    is substituted to prevent that quantifier from capturing the world parameter.

    A variable that is free in ``formula`` stays free in the image, as the parameter it
    is. What the translation does not state is its typing (an element of the object
    domain) or, under a varying regime, its existence at ``world``: those are facts of the
    validity query, :func:`qml_validity_formula`. See the module docstring's "A free
    variable is a parameter".

    An identity atom is the one atom that does NOT get the world appended: ``t₁ = t₂``
    stays ``t₁ = t₂`` and ``t₁ ≠ t₂`` becomes ``¬(t₁ = t₂)``, so identity is rigid (see
    the module docstring's "Equality is rigid", which also states the varying-domain
    choice). A non-binary ``=`` / ``≠`` atom raises ``ValueError`` rather than being
    read as a world-relative predicate.

    A many-sorted ``formula`` (``SortedQuantifier`` / ``SortedConstant``) is relativized
    ONCE, here, before anything else runs — see the module docstring's "Many-sorted
    formulas" section for what that does and does not assume. The relativisation forgets
    which constants were annotated, so the membership of a sorted constant in its sort is
    NOT part of this translation: it is an axiom, which :func:`qml_axioms` emits from the
    formula as given.
    """
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"qml: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    formula = formula._relativize([])
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
    W = lambda z: Atom(_WORLD, (z,))
    O = lambda z: Atom(_OBJECT, (z,))
    Rel = lambda *args: Atom(rel_name, tuple(args))
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
        Atom(rel, (w, v)), And(Atom(_WORLD, (w,)), Atom(_WORLD, (v,))))))


def _temporal_frame_axioms() -> List[Node]:
    """``T`` is reflexive and transitive — the *henceforth* relation.

    :func:`unicode_logic_kit.semantics.kripke.satisfies_modal` evaluates ``Always`` /
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
    W = lambda a: Atom(_WORLD, (a,))
    T = lambda a, b: Atom(_R_TEMPORAL, (a, b))
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
        And(And(Atom(_WORLD, (w,)), Atom(_WORLD, (v,))), Atom(_R_NEXT, (w, v))),
        Atom(_R_TEMPORAL, (w, v)))))


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
    lowers to Z3's own equality (``Node.to_z3`` maps binary ``=`` natively). An
    object-language ``=`` inside a modal formula is translated to that SAME binary
    identity (rigid, no world argument — see the module docstring), so the two share
    a symbol and differ in what they relate: this axiom's operands are
    ``World``-guarded worlds, a user equality's are objects, and ``World`` / ``Object``
    are disjoint, so neither equates operands of the other kind.

    Emitted only when ``T`` and ``N`` BOTH occur and ``temporal_closure`` is on, mirroring
    ``isabelle_modal``'s ``t_in_nstar`` (which pins ``t = rtranclp n`` outright, HOL being
    able to say what first-order logic cannot) and for the same reason: the axiom relates
    the two relations, so it is vacuous — and misleading — unless both are in play.
    """
    w, v, u = _v("w", "v", "u")
    W = lambda a: Atom(_WORLD, (a,))
    T = lambda a, b: Atom(_R_TEMPORAL, (a, b))
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    return fa(w, fa(v, Implies(
        And(And(W(w), W(v)), T(w, v)),
        Or(Atom("=", (w, v)),
           Quantifier(_EXISTS, u, And(And(W(u), Atom(_R_NEXT, (w, u))), T(u, v)))))))


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
        Atom(_WORLD, (w,)),
        Quantifier(_EXISTS, v, And(Atom(_WORLD, (v,)), Atom(_R_DEONTIC, (w, v))))))]


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
#: by the HOL routes via :data:`unicode_logic_kit.hol.BRIDGES`.
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
        return fa(a, fa(w, fa(v, Implies(Atom(sub, (a, w, v)), Atom(sup, (a, w, v))))))
    if name != "ought_implies_can":
        raise ValueError(f"qml: no axiom shape for bridge {name!r}.")
    w, v = _v("w", "v")
    return fa(w, Implies(
        Atom(_WORLD, (w,)),
        Quantifier(_EXISTS, v, And(Atom(_WORLD, (v,)),
                                   And(Atom(_R_DEONTIC, (w, v)), Atom(_R_ALETHIC, (w, v)))))))


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
    relation in :data:`QML_RELATIONS`. The same ``formula`` gates the many-sorted
    facts: per sort it uses, that the sort is non-empty at every world, and per sorted
    constant ``c:S``, that ``c`` is in ``S`` at every world (give the formula AS WRITTEN,
    not :func:`qml_translate`'s relativised form, which has forgotten the annotations).

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
    conds = _resolve_frame(frame)
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"qml: unknown mode {mode!r} (use one of "
            f"{sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    bridge_names = _validate_bridges(bridges)
    used = set(QML_RELATIONS) if formula is None else _relations_used(formula)
    _check_bridge_families(bridge_names, used)
    x, w, v, u = _v("x", "w", "v", "u")
    t = Variable("t")
    W = lambda a: Atom(_WORLD, (a,))
    O = lambda a: Atom(_OBJECT, (a,))
    R = lambda a, b: Atom(_R_ALETHIC, (a, b))
    E = lambda a, b: Atom(_E, (a, b))
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
    if "functional" in conds:
        # CD: at most one successor. ∀w,v,u (Rwv ∧ Rwu → v = u).
        axioms.append(fa(w, fa(v, fa(u, Implies(
            And(And(W(w), W(v)), And(W(u), And(R(w, v), R(w, u)))),
            Atom("=", (v, u)))))))
    if "dense" in conds:
        # C4: ∀w,v (Rwv → ∃u (Rwu ∧ Ruv)).
        axioms.append(fa(w, fa(v, Implies(
            And(And(W(w), W(v)), R(w, v)),
            Quantifier(_EXISTS, u, And(W(u), And(R(w, u), R(u, v))))))))
    if "shift_refl" in conds:
        # Ṁ: ∀w,v (Rwv → Rvv) — every accessible world is reflexive.
        axioms.append(fa(w, fa(v, Implies(
            And(And(W(w), W(v)), R(w, v)), R(v, v)))))
    if "empty" in conds:
        # Ver: no accessible worlds at all, so □φ holds vacuously everywhere.
        axioms.append(fa(w, fa(v, Not(R(w, v)))))
    for cond in conds:
        spec = parse_geach(cond)
        if spec is not None:
            axioms.append(_geach_axiom(spec, W, R))

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

    # non-empty SORTS (many-sorted formulas only): the same MSFOL convention
    # fol._msfl_nodes.nonempty_sort_axioms enforces for the classical routes
    # (every sort is non-empty), extended PER WORLD here because a sort guard
    # is an ordinary, WORLD-RELATIVE atom once qml_translate's up-front
    # relativisation feeds it through ST (see the module docstring's
    # "Many-sorted formulas" section) — so ``∀x:S P(x) → ∃x:S P(x)`` agrees
    # with the classical Z3-via-api.prove verdict at every world, not just
    # incidentally at one. Gated on ``formula`` the same way
    # _signature_typing_facts is: there is nothing to scan for sorts without one.
    if formula is not None:
        for name in _sort_names_used(formula):
            s_guard = Atom(_user_predicate(name), (x, w))
            witness = And(O(x), s_guard)
            if mode in _ACTUALIST_MODES:
                witness = And(And(O(x), E(x, w)), s_guard)
            axioms.append(fa(w, Implies(W(w), Quantifier(_EXISTS, x, witness))))
        # membership of a SORTED CONSTANT: ``c:S`` denotes an element of ``S``. A
        # constant is a rigid designator, so the fact is rigid too -- ``S(c, w)`` at
        # EVERY world -- and it is NOT guarded by ``E(c, w)``: the guarded form makes
        # no query's verdict differ, because in the constant-domain modes ``E`` is
        # not forced and in the actualist modes a constant may lie outside ``D_w``
        # (see the module docstring), so the guard would never fire. Read from the
        # ORIGINAL formula: the relativised one has already forgotten which
        # constants were annotated. The atoms ``sort_membership_axioms`` returns
        # carry no world, so each is lifted here, through the same predicate naming
        # the guard of a sorted quantifier gets.
        for member in sort_membership_axioms(formula):
            assert isinstance(member, Atom)     # sort_membership_axioms yields atoms ``S(c)`` only
            axioms.append(fa(w, Implies(
                W(w), Atom(_user_predicate(member.predicate),
                           (member.args[0], w)))))

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


def _sort_names_used(formula: Node) -> List[str]:
    """Distinct sort names ``formula`` mentions, in first-occurrence order.

    Reuses :func:`~unicode_logic_kit.fol._msfl_nodes.nonempty_sort_axioms`'s own
    scan (each of its returned ``∃x (S(x))`` sentences names its sort as the
    predicate of its body atom) rather than re-implementing "which of the four
    many-sorted node types occur" here — so this route and the classical one
    can never disagree about which sorts a formula uses.
    """
    sorts: List[str] = []
    for axiom in nonempty_sort_axioms(formula):
        assert isinstance(axiom, Quantifier) and isinstance(axiom.formula, Atom)   # ∃x S(x)
        sorts.append(axiom.formula.predicate)
    return sorts


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
            # keyed (and so ordered) by the bare name, as ever: the key is not shown anywhere
            consts[key_text(n)] = n
        elif isinstance(n, _F):
            funcs[(n.name, len(n.args))] = n
    facts: List[Node] = [Atom(_OBJECT, (t,))
                         for _, t in sorted(consts.items())]
    for (name, arity), fn in sorted(funcs.items()):
        xs = [Variable(f"_a{i}") for i in range(arity)]
        guards: List[Node] = [Atom(_OBJECT, (x,)) for x in xs]
        guard = reduce(And, guards)
        body: Node = Implies(guard, Atom(_OBJECT, (type(fn)(name, tuple(xs)),)))
        for x in reversed(xs):
            body = Quantifier(_FORALL, x, body)
        facts.append(body)
    return facts


def _validity_formula(formula: Node, mode: str, frame: str, systems=None,
                      bridges=None, temporal_closure: bool = True) -> Node:
    """Build ``⋀axioms ∧ ⋀typing-facts → ∀w (World(w) → ST(formula, w))``.

    The axioms are gated on ``formula``'s signature, so a query only carries the frame
    conditions of the relations it actually mentions. New parameters are APPENDED, so the
    positional call in :mod:`unicode_logic_kit.atp.resolution` keeps working unchanged and
    inherits the gating.

    A free variable of ``formula`` is a parameter (the module docstring's "A free variable
    is a parameter"), and it stays free in the query: it is one unknown individual, so a
    solver that reads it as an uninterpreted constant and one that closes the whole
    query universally decide the same validity. Under ``constant`` / ``possibilist`` the
    individual is typed ``Object(y)``, among the typing facts, as every constant is. Under
    an actualist regime it is guarded where the formula is evaluated: the consequent is
    ``∀w (World(w) ∧ E(y, w) → ST(formula, w))``.
    """
    # The sort-name / relation-usage scan in qml_axioms needs the ORIGINAL,
    # un-relativized ``formula`` (a SortedQuantifier/SortedConstant is what it
    # looks for) — so that scan runs on ``formula`` itself, while everything
    # downstream of it (typing facts, translation) runs on ONE relativized
    # copy, so a SortedConstant gets typed as an Object exactly like a plain
    # Constant would (see qml_translate's own up-front relativisation, which
    # this pre-empts so _signature_typing_facts sees the same plain
    # Constant qml_translate's translation will).
    axioms = qml_axioms(mode, frame, systems, formula=formula, bridges=bridges,
                        temporal_closure=temporal_closure)
    relativized = formula._relativize([])
    axioms += _signature_typing_facts(relativized)
    parameters = [Variable(name) for name in free_parameter_names([relativized])]
    if mode in _CONSTANT_MODES:
        axioms += [Atom(_OBJECT, (parameter,)) for parameter in parameters]
    w = _pick_world_name(relativized, "w")
    where: Node = Atom(_WORLD, (Variable(w),))
    if mode in _ACTUALIST_MODES:
        for parameter in parameters:
            where = And(where, Atom(_E, (parameter, Variable(w))))
    body = Implies(where, qml_translate(relativized, mode, world=w))
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
    :func:`unicode_logic_kit.semantics.kripke.satisfies_modal` over an explicit model.

    Two contract details worth knowing before reading a verdict:

    - a temporal or deontic formula is judged under the default-on frame conditions, so
      ``True`` for a deontic formula means "valid over every SERIAL-deontic model", and
      temporal induction ``(φ ∧ G(φ → Xφ)) → Gφ`` comes back ``False`` here despite
      holding in every intended model — decide that one with
      :func:`unicode_logic_kit.hol.isabelle_runner.isabelle_decide_modal`;
    - an identity atom ``=`` / ``≠`` is rigid (no world argument) and existence-
      independent under every ``mode``; see the module docstring's "Equality is rigid"
      for the varying-domain choice and for why ``□(a = b) → a = b`` needs a frame
      with a successor-or-self (T, S4, S5, KD …) while ``a = b → □(a = b)`` holds in K;
    - a variable that is free in ``formula`` is a PARAMETER: one unknown individual, the
      same everywhere in the formula. Under ``mode='constant'`` / ``'possibilist'`` it is an
      element of the object domain, so ``∀x P(x) → P(y)`` and ``P(y) → ∃x P(x)`` are valid;
      under a varying regime it exists at the world of evaluation (and need not exist at any
      other), so those two are valid there too while ``□∀x P(x) → □P(y)`` is valid under
      ``'constant'`` / ``'possibilist'`` / ``'increasing'`` only. A constant is not read
      that way (it may lie outside the world's domain); see the module docstring's "A free
      variable is a parameter";
    - a deontic ``False`` is typically Z3 returning *unknown* rather than a countermodel:
      the ∃-quantified seriality axiom defeats its model finder, measured identical at
      1 s / 2 s / 10 s budgets (the same behaviour ``frame="KD"`` has always had). A short
      ``timeout`` therefore costs no reliability on deontic non-theorems.
    """
    from ..atp.z3_models import is_valid
    return is_valid(_validity_formula(formula, mode, frame, systems, bridges=bridges,
                                      temporal_closure=temporal_closure), timeout=timeout)


def qml_validity_formula(formula: Node, mode: str = "constant", frame: str = "K",
                         systems=None, bridges=None,
                         temporal_closure: bool = True) -> Node:
    """Return the classical-FOL validity query :func:`qml_is_valid` decides,
    as a :class:`Node` — closed unless ``formula`` has a free variable, which stays
    free in it as the parameter it is (closing the query universally gives the same
    validity) — the documented, public counterpart of the private
    :func:`_validity_formula` this function simply delegates to (kept private and
    unchanged, including its positional-argument shape, since
    :mod:`unicode_logic_kit.atp.resolution` already calls it positionally).

    ``⋀axioms ∧ ⋀typing-facts → ∀w (World(w) → ST(formula, w))`` — see
    :func:`_validity_formula`'s own docstring for exactly what ``axioms`` and
    ``typing-facts`` contain. The Node this returns is built ONLY from
    :class:`Atom`/:class:`Not`/:class:`And`/:class:`Or`/:class:`Xor`/
    :class:`Implies`/:class:`Iff`/:class:`Quantifier` and the term classes
    :class:`Variable`/:class:`Constant`/:class:`Function` — i.e. exactly the
    classical FOL fragment :mod:`unicode_logic_kit.fol.casl_export` accepts — so it
    is ready to hand to :func:`~unicode_logic_kit.fol.casl_export.to_casl_spec`
    directly. The fresh world / Geach variables this route mints are ``w0`` / ``v0``
    style names (:func:`unicode_logic_kit.fol._identifiers.fresh_variables`), which are
    legal CASL identifiers as well as legal names for this kit's own parser — before
    0.30.0 they were ``_w0`` / ``_gz0``, and :mod:`unicode_logic_kit.hets.dol` had to
    rename every one. An object-language ``=`` needs no handling either: it is
    translated to the SAME binary, rigid identity (no world argument — see the module
    docstring's "Equality is rigid"), which is exactly CASL's own fixed built-in
    ``=``, and ``≠`` to ``¬(=)``, which ``casl_export`` renders as it renders any
    negation. What ``hets.dol`` still has to rename is the ``·`` mark this module
    appends to a user predicate named like one of its own relations (``R`` → ``R·``):
    U+00B7 is punctuation no CASL identifier may contain. Use
    :func:`unicode_logic_kit.hets.dol.to_dol_library_from_modal` — it calls this
    function, sanitises the names injectively, and renders the result as a complete
    DOL library over :func:`~unicode_logic_kit.fol.casl_export.to_casl_spec` (see that
    module's own docstring for the sanitisation contract) — rather than feeding this
    function's raw output to ``to_casl_spec`` yourself.
    """
    return _validity_formula(formula, mode, frame, systems, bridges=bridges,
                             temporal_closure=temporal_closure)


def qml_equivalent(left: Node, right: Node, mode: str = "constant", frame: str = "K",
                   systems=None, timeout: int = 10000, bridges=None,
                   temporal_closure: bool = True) -> bool:
    """Return True iff two modal formulas are QML-equivalent under ``mode`` / ``frame``.

    A variable free in either formula is one parameter shared by both (see
    :func:`qml_is_valid`): the formulas are equivalent when ``left ↔ right`` is valid for
    every individual it may denote.
    """
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
    # CD: at most one successor.
    "functional": "thf(functional, axiom, ( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) => ( V = U ) ) )).",
    # C4: dense.
    "dense": "thf(dense, axiom, ( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ? [U: mu] : ( ( r @ W @ U ) & ( r @ U @ V ) ) ) )).",
    # Ṁ: every accessible world is reflexive.
    "shift_refl": "thf(shift_refl, axiom, ( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ V ) ) )).",
    # Ver: no accessible worlds at all.
    "empty": "thf(empty_r, axiom, ( ! [W: mu, V: mu] : ~ ( r @ W @ V ) )).",
    # The three schemas with NO first-order frame condition are asserted as
    # schemas, quantified over propositions — which is exactly what the
    # higher-order route can do and every first-order route cannot.
    "loeb": "thf(loeb, axiom, ( ! [Phi: mu > $o, W: mu] : ( ( mbox @ ( mimplies @ ( mbox @ Phi ) @ Phi ) @ W ) => ( mbox @ Phi @ W ) ) )).",
    "mckinsey": "thf(mckinsey, axiom, ( ! [Phi: mu > $o, W: mu] : ( ( mbox @ ( mdia @ Phi ) @ W ) => ( mdia @ ( mbox @ Phi ) @ W ) ) )).",
    "grz": "thf(grz, axiom, ( ! [Phi: mu > $o, W: mu] : ( ( mbox @ ( mimplies @ ( mbox @ ( mimplies @ Phi @ ( mbox @ Phi ) ) ) @ Phi ) @ W ) => ( Phi @ W ) ) )).",
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


# `feq` / `fneq` are the functors equality USED to get in the THF / Isabelle exports of
# the modal layer, where it was an ordinary uninterpreted, world-relativized predicate
# and so answered a different question than qml_is_valid. It is now rigid identity on
# every one of those routes (`_RigidNames` in hol.thf_modal overrides the two entries,
# and `_lower_identity` rewrites `≠` to `¬(=)` before any name is looked up), so the two
# equality entries below are unreachable from to_thf_modal / to_isabelle_modal /
# hol.thf_modal / hol.isabelle_modal. They are kept because this table also names `⊥`
# and `⊤` and is shared with routes that do not lower identity; a route that reads one
# of the two gets a valid, distinct functor rather than a crash — never a SILENT
# uninterpreted reading, because reaching them at all now takes a caller that opted out
# of `_RigidNames`.
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
    :func:`~unicode_logic_kit.fol._fol_nodes.constant_name_to_ascii` (ASCII passthrough;
    Greek -> conventional name; anything else -> a reversible ``uXXXX`` escape) — THF
    functors are ASCII-only (TPTP ``lower_word``), so a raw Unicode letter reaching this
    far would be silent corruption, not sanitisation. A leading digit (which can also
    now arise from a transliterated escape, though those always start with the ASCII
    letter ``u``) is prefixed with ``p`` so the result is a legal lower identifier — TPTP
    functors can never start with a digit, and unlike the predicate/constant/function
    case this class had no digit guard before, since a THF functor name in this exporter
    is always built from a Constant/Function/Atom name, and only Constant names (via the
    kit's NAME terminal) can be digit-leading in the first place. A leading underscore
    gets the same ``p``: the constant ``'_sk0'``, the constant ``'-3'`` and the function
    ``+`` would otherwise be written ``_sk0``, ``_3`` and ``_``, none of which is a lower
    word (nor, upper-cased for a variable, an upper word).

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
    if safe[0].isdigit() or safe[0] == "_":
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
        :func:`~unicode_logic_kit.fol._symbol_names.dedupe`, so two DISTINCT source names
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
        return names.constant(prefixed_numeral_name(node.value))
    if isinstance(node, Function):
        head = names.function(node)
        return "( " + " @ ".join([head] + [_thf_term(a, names) for a in node.args]) + " )"
    raise NotImplementedError(f"to_thf_modal: unsupported term {type(node).__name__}.")


def _thf_lift(node: Node, names: "_ThfNames") -> str:
    """Render a modal formula as a THF term of type ``mu > $o``."""
    if isinstance(node, Down):
        # See the identical, more fully-explained guard in _st above — this
        # basic THF export never covered hybrid logic either; hol.thf_modal
        # (the full shallow embedding) gets its OWN ↓ guard, see that module.
        raise NotImplementedError(
            "to_thf_modal: the ↓ binder is outside the alethic □/◇ fragment "
            "supported by this THF export (which does not cover hybrid logic "
            "at all — no nominals/@ either); use "
            "unicode_logic_kit.fol.modal_translation.down_is_valid or "
            "unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend instead.")
    if isinstance(node, Atom):
        # An identity atom never reaches here with its own predicate name: the
        # callers lower `≠` to `¬(=)` and hand `names` a `_RigidNames`, whose
        # `atom` maps `=` onto the `meq` macro — THF's own `=` over `$i` with the
        # world dropped, the reading qml_is_valid has ("Equality is rigid").
        constant = truth_value(node)
        if constant is not None:
            # `$true` / `$false`: the proposition true (false) at every world.
            return "( ^ [W: mu] : $true )" if constant else "( ^ [W: mu] : $false )"
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
        "unicode_logic_kit.hol.thf_modal.to_thf_modal_full, which covers the full "
        "modal family (epistemic/doxastic/assertive/bouletic/deontic/temporal "
        "incl. Until/Since, and hybrid nominals/@).")


def _thf_signature(formula: Node, names: Optional["_ThfNames"] = None) -> List[str]:
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

    Equality ``=`` / ``≠`` is **rigid identity**, the reading of :func:`qml_is_valid` /
    :func:`qml_translate` (module docstring, "Equality is rigid"): THF's own ``=`` over
    the individual sort ``$i`` with no world argument, through one extra macro
    ``meq = ^ [A: $i, B: $i, W: mu] : ( A = B )`` that is emitted only when the formula
    contains identity (so an equality-free problem is unchanged). ``t₁ ≠ t₂`` is lowered
    to ``¬(t₁ = t₂)`` as ``qml_translate`` does, a non-binary ``=`` / ``≠`` atom raises
    ``ValueError`` as there, and no ``feq`` / ``fneq`` functor is declared. So a prover
    on this problem answers the question :func:`qml_is_valid` answers: ``∀x (x = x)``,
    ``a = b → □(a = b)`` and ``◇(a = b) → a = b`` are theorems under ``frame='K'``,
    ``□(a = b) → a = b`` only under a reflexive / serial frame. Identity is not
    existence-guarded (the module docstring's varying-domain choice). The macro and the
    lowering live in :mod:`unicode_logic_kit.hol.thf_modal`, which emits the same line.

    THF has no free variable, so a variable that is free in ``formula`` (a parameter, see
    the module docstring's "A free variable is a parameter") is bound in the conjecture:
    ``! [Y: $i] : mvalid @ …``, and under a varying regime ``existsAt @ Y`` guards the
    formula (``! [Y: $i] : mvalid @ (mimplies @ (existsAt @ Y) @ …)``), which is the
    reading :func:`qml_is_valid` has. For a single formula with no premise this binding
    is the parameter reading itself.
    """
    # Lazy: hol.thf_modal imports this module, so the shared rigid-identity helpers
    # are reached from inside the function (as to_isabelle_modal below reaches hol).
    from ..hol.thf_modal import (
        _RigidNames, _THF_RIGID_EQ_DEF, _has_identity, _lower_identity,
    )
    if frame not in _FRAMES:
        raise ValueError(f"to_thf_modal: unknown frame {frame!r}.")
    # A numeral is a constant identified by its value (1 and 1.0 are one), named ``n1``:
    # a user constant spelled like it is refused, not merged with it.
    [formula], _ = numerals_as_constants([formula], where="to_thf_modal",
                                         spell=prefixed_numeral_name)
    formula = _lower_identity(formula, "to_thf_modal")
    lines = [
        f"% Shallow embedding of a quantified modal formula (mode={mode}, frame={frame}).",
        "% Conjecture is 'Theorem' iff the formula is QML-valid under this regime.",
        "thf(mu_type, type, ( mu : $tType )).",
        "thf(r_decl, type, ( r : ( mu > mu > $o ) )).",
        "thf(existsAt_decl, type, ( existsAt : ( $i > mu > $o ) )).",
    ]
    names = _RigidNames(formula)
    lines += _thf_signature(formula, names)
    lines.append(_THF_DEFS)
    if _has_identity(formula):
        lines.append(_THF_RIGID_EQ_DEF)
    lines.append("thf(nonempty_dom, axiom, ( ! [W: mu] : ? [X: $i] : ( existsAt @ X @ W ) )).")
    for cond in _FRAMES[frame]:
        lines.append(_THF_FRAME[cond])
    if mode in _THF_DOMAIN:
        lines.append(_THF_DOMAIN[mode])
    elif mode not in ("varying",) and mode not in _CONSTANT_MODES:
        raise ValueError(f"to_thf_modal: unknown mode {mode!r}.")
    goal = _thf_lift(formula, names)
    parameters = free_parameter_names([formula])
    if mode in _ACTUALIST_MODES:
        for name in reversed(parameters):
            goal = f"( mimplies @ ( existsAt @ {names.variable(name)} ) @ {goal} )"
    conjecture = f"mvalid @ {goal}"
    for name in reversed(parameters):
        conjecture = f"! [{names.variable(name)}: $i] : ( {conjecture} )"
    lines.append(f"thf(goal, conjecture, ( {conjecture} )).")
    return "\n".join(lines) + "\n"


def to_isabelle_modal(formula: Node, mode: str = "constant", frame: str = "K") -> str:
    """Emit a complete, loadable Isabelle/HOL theory shallow-embedding ``formula``.

    This delegates to :func:`unicode_logic_kit.hol.isabelle_modal.to_isabelle_modal` — the
    real, full-modal-family exporter that emits a loadable ``theory … begin … end`` with
    every lifted operator defined and a genuine ``lemma`` (it replaced the earlier
    alethic-only skeleton). Use that module directly for the additional options
    (epistemic/doxastic/deontic/temporal coverage, the proof ``tactic``,
    ``temporal_closure``).

    A variable that is free in ``formula`` stays a free variable of the lemma, which then
    holds for EVERY individual of the type ``i``. Under ``constant`` / ``possibilist`` that
    is the parameter reading of :func:`qml_is_valid` (one formula, no premise). Under a
    varying regime it is stronger than that reading, which asks the individual to exist
    at the world of evaluation only: a proof of the lemma proves the parameter instance,
    and a counterexample to the lemma in which the individual does not exist at the world
    of evaluation does not refute it. Use :func:`qml_is_valid` for the verdict under such
    a regime.
    """
    from ..hol.isabelle_modal import to_isabelle_modal as _real
    return _real(formula, mode=mode, frame=frame)
