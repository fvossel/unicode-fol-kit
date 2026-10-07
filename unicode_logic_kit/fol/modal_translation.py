"""Standard (relational) translation of propositional modal logic into FOL.

The *standard translation* ST embeds the propositional modal fragment into
classical first-order logic over an explicit "current world" term, so that the
existing FOL back-ends (Z3, Prover9, TPTP, the resolution engine, the Tarski
evaluator) can reason about modal formulas. A modal formula is true at a world
*w* in a Kripke model exactly when its translation ``ST(φ, w)`` is true in the
corresponding first-order structure (worlds as the domain, accessibility
relations and atom-predicates as the relations) — this correspondence is what
``tests/test_modal_translation.py`` cross-checks against
:func:`unicode_logic_kit.semantics.kripke.satisfies_modal`.

Translation scheme, with ``w`` the current-world variable and ``w'`` a FRESH
world variable (names ``w0, w1, …`` are generated so nested modalities never
capture each other; the free current-world name and every variable name of
the formula are skipped, so even a caller who passes ``world="w0"`` keeps a
distinct, uncaptured free variable, and an atom ``P(w0)`` keeps its own ``w0``):

- ``Atom A`` (propositional / ground) → ``A(w)``: the atom's predicate is
  applied to the current world. A nullary atom ``P`` becomes ``P(w)``; an atom
  ``Likes(a, b)`` becomes ``Likes(a, b, w)`` (the world is appended as the last
  argument, so ground arguments are preserved).
- ``Not / And / Or / Xor / Implies / Iff`` — map through structurally at the
  same world.
- ``Box φ``      → ``∀w' (R(w, w') → ST(φ, w'))``.
- ``Diamond φ``  → ``∃w' (R(w, w') ∧ ST(φ, w'))``.
- ``Knows(a, φ)``    → ``∀w' (Rk_a(w, w') → ST(φ, w'))``.
- ``Believes(a, φ)`` → ``∀w' (Rb_a(w, w') → ST(φ, w'))``.
- ``EverybodyKnows(G, φ)`` (E_G, "everyone in G knows φ") →
  ``⋀_{a∈G} ∀w' (Rk_a(w, w') → ST(φ, w'))`` — a per-agent :class:`Knows`
  translation for every member of ``G``, ANDed together (one-step; union of
  relations ≡ conjunction of boxes). Empty ``G`` is rejected (see Scope below).
- ``DistributedKnowledge(G, φ)`` (D_G, "φ is distributed knowledge in G") →
  ``∀w' ((⋀_{a∈G} Rk_a(w, w')) → ST(φ, w'))`` — ONE box over the
  INTERSECTION of the group's relations (every ``Rk_a(w,w')`` conjunct must
  hold of the SAME ``w'``), not a per-agent conjunction of separate boxes.
- ``Says(a, φ)``     → ``∀w' (Rs_a(w, w') → ST(φ, w'))`` (assertive: box over
  a per-agent "compatible with what a says" relation).
- ``Wants(a, φ)``    → ``∀w' (Rw_a(w, w') → ST(φ, w'))`` (bouletic: box over
  a per-agent desire relation).
- ``Always φ``     → ``∀w' (T(w, w') → ST(φ, w'))`` (box over a temporal
  accessibility predicate ``T``).
- ``Eventually φ`` → ``∃w' (T(w, w') ∧ ST(φ, w'))`` (diamond over ``T``).
- ``Next φ``       → ``∀w' (N(w, w') → ST(φ, w'))`` (box over a one-step
  predicate ``N``).
- ``Obligatory φ`` → ``∀w' (D(w, w') → ST(φ, w'))`` (box over a deontic
  accessibility predicate ``D``).
- ``Permitted φ``  → ``∃w' (D(w, w') ∧ ST(φ, w'))`` (diamond over ``D``).
- ``Nominal i``  → ``w = nom_i``: a nominal is a world-equality against a
  dedicated world CONSTANT. The ``"nom_"`` prefix keeps these constants out of
  the user's constant namespace, so an atom mentioning a ground constant ``i``
  can never collide with the nominal ``i``. UNLESS ``i`` is currently BOUND by
  an enclosing ``↓i`` (see ``Down`` below), in which case the translation uses
  the bound world TERM instead — the ``bindings`` mechanism, not the ``nom_``
  constant, decides which.
- ``At(i, φ)``   → ``ST(φ, nom_i)``: the satisfaction operator ``@i φ``
  re-anchors the translation at the constant world term ``nom_i`` (the current
  world term is simply replaced — no quantifier is introduced) — again unless
  ``i`` is ``↓``-bound, in which case the bound term replaces ``nom_i``.
- ``Down(x, φ)`` (``↓x.φ``, N1) → ``ST(φ, world)`` with ``x`` now BOUND, for
  the rest of ``φ``'s translation, to the CURRENT WORLD TERM ``world`` — no
  fresh quantifier is introduced (this is the bounded-fragment translation:
  ``↓`` rebinds a name to the current world, it does not existentially
  quantify over worlds). Concretely: every ``Nominal(x)`` / ``At(x, …)`` in
  ``φ`` — down to, but not inside, a nested ``Down(x, …)`` that shadows it —
  translates to ``world`` (or re-anchors at it) instead of to a fresh
  ``nom_x`` constant. This is threaded through ``_translate`` as one extra
  parameter, ``bindings: Dict[str, Node]`` (name → the world TERM it is
  currently bound to), consulted by the ``Nominal``/``At`` cases FIRST,
  falling back to the ``nom_`` scheme only when the name is unbound — so
  ``bindings={}`` (every call site outside ``Down``'s own recursion)
  reproduces the pre-``Down`` translation byte-for-byte. Because ``↓`` makes
  H(@,↓) UNDECIDABLE (unlike plain H(@)), no bare-bool validity check treats
  a ``Down``-containing formula: ``hybrid_is_valid`` refuses it by name;
  :func:`down_is_valid` (below) is the PROVED-only replacement.

Scope / caveats (v1):

- ``Always`` and ``Eventually`` are translated as a **box / diamond over an
  assumed temporal accessibility predicate** ``T``. To make ``Always`` a genuine
  "henceforth" (reflexive-transitive reachability) one would need extra frame
  axioms forcing ``T`` to be reflexive and transitive — that is not pure
  first-order logic (transitive closure is not first-order definable), so it is
  out of scope here. The cross-check in the tests therefore drives the Tarski
  structure with ``T`` interpreted as the SAME one-step ``"temporal"`` relation
  used by the Kripke model, NOT its closure.
- ``Until`` is rejected: strong Until needs the transitive closure of the
  temporal relation, which is not first-order definable.
- ``CommonKnowledge`` (C_G) is rejected for the exact same reason: it needs the
  reflexive-transitive closure of the group's union relation.
- ``EverybodyKnows`` over an EMPTY group is rejected too: ``E_∅ φ`` is
  vacuously true by definition (the union over zero relations is empty, so
  "holds at every successor" holds vacuously), but this grammar has no
  first-order truth constant to render that without borrowing an unrelated
  atom from the caller's own vocabulary. ``DistributedKnowledge`` never
  raises this way — its own constructor already refuses an empty group (see
  ``fol._modal_nodes.DistributedKnowledge``'s docstring).
- ``Quantifier`` / ``SortedQuantifier`` are rejected: first-order (quantified)
  modal logic with object domains is out of scope for v1. So are Łukasiewicz and
  lambda nodes.

The accessibility-predicate names are fixed so the matching Tarski structure can
be built mechanically: ``"R"`` (alethic), ``"Rk_" + agent`` (epistemic),
``"Rb_" + agent`` (doxastic), ``"Rs_" + agent`` (assertive), ``"Rw_" + agent``
(bouletic), ``"T"`` (temporal), ``"N"`` (next), ``"D"`` (deontic).
"""

from typing import TYPE_CHECKING, Dict, FrozenSet, Iterable, List, NoReturn, Optional

if TYPE_CHECKING:
    from ..atp.protocol import Verdict

from ._atom_keys import refuse_alike_agents
from ._identifiers import fresh_variables, symbol_names
from .nodes import (
    Node,
    Variable, Constant, LambdaVar,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Nominal, At,
    sort_membership_axioms, substitute,
)
from ._truth_constants import truth_value
# Down (the ↓ binder, N1) is not yet re-exported through fol.nodes / fol's
# public __init__ / the top-level unicode_logic_kit package — that three-file
# edit is outside this change's file ownership (see the change's own
# report); imported directly from its defining module instead, the same
# class object either import path would give.
from ._hybrid_nodes import Down
from .frames import (
    FRAMES as _SHARED_FRAMES, UnsupportedFrameCondition,
    is_first_order, resolve_frame, unguarded_frame_axiom,
)
from ..semantics._modal_reject import (
    FUZZY_TYPES, LAMBDA_TYPES,
    reject_equality, reject_fuzzy, reject_lambda,
)

# Accessibility predicate names (the contract with the matching Tarski
# structure; keep these stable).
_R_ALETHIC = "R"
_R_KNOWS_PREFIX = "Rk_"
_R_BELIEVES_PREFIX = "Rb_"
_R_SAYS_PREFIX = "Rs_"
_R_WANTS_PREFIX = "Rw_"


def _agent_key(agent: Node) -> str:
    """Agent term's name for the per-agent relation (this propositional translation
    rejects object quantifiers, so the agent is always a ground Constant here)."""
    return getattr(agent, "name", None) or agent.to_unicode_str()
_R_TEMPORAL = "T"
_R_NEXT = "N"
_R_DEONTIC = "D"

# Prefix for the world constant a hybrid nominal translates to ("nom_" + name).
# The prefix keeps the generated constants disjoint from user constants, so a
# formula whose atoms mention a ground constant `i` cannot collide with the
# nominal `i`. This is the contract with any structure built for the image.
_NOM_PREFIX = "nom_"

# Equality is NOT an ordinary atom here. This translation is PROPOSITIONAL: an
# atom is a world-relative proposition, so appending the world to ``=`` would
# make identity a ternary, uninterpreted, world-varying relation — under which
# ``a = a`` comes back "not valid" (measured on 0.28.1) and ``□(a = b) → a = b``
# is "valid" only through reflexivity of R, not through identity. That is a
# silent approximation of a construct this layer has no semantics for (the
# Kripke evaluator reads atoms off a per-world valuation of ground-atom keys
# and interprets no terms either), so it is refused by name. First-order modal
# logic with rigid identity is :mod:`unicode_logic_kit.fol.qml`.
# ``≠`` is the same construct and is refused the same way: the kit prints
# ``a ≠ b`` as ``Atom("≠", (a, b))``, and appending the world there produced
# ``≠(a, b, w)`` — a ternary uninterpreted relation unrelated to the ``=`` one,
# so ``a = b ∨ a ≠ b`` came back "not valid" (measured on 0.28.1). Both
# spellings live in :data:`EQUALITY_PREDICATES`, and :func:`reject_equality`
# (shared with the Kripke evaluator, the modal tableau and the GMT embedding)
# is the single place that says why.
#: The predicate the FOL IMAGE uses for world identity (``@i j`` becomes
#: ``i = j``, and the temporal first-step axiom says ``T(w,v) → w = v ∨ …``).
#: An equality atom in the SOURCE is refused; one in the image is ordinary FOL.
_EQUALITY = "="

_EQUALITY_ROUTE = "the propositional standard translation"
_EQUALITY_ATOM_READING = ("an atom becomes a predicate with the world appended, "
                          "so '=' would become a world-varying uninterpreted "
                          "relation")
_EQUALITY_INSTEAD = ("Use unicode_logic_kit.fol.qml (quantified modal logic, "
                     "where '=' is rigid identity over the object domain) for a "
                     "formula with identity.")


def _reject_equality(formula: Node) -> None:
    """:func:`reject_equality` with this route's wording (check-and-raise)."""
    reject_equality(formula, "standard_translation", _EQUALITY_ROUTE,
                    atom_reading=_EQUALITY_ATOM_READING,
                    instead=_EQUALITY_INSTEAD)

# Universal/existential quantifier-type spellings used by the AST.
_FORALL = "∀"
_EXISTS = "∃"

# A USER predicate named like one of the accessibility relations above used to
# BE that relation once the translation appended its world argument (a
# propositional atom ``R`` became ``R(w)`` next to the binary relation
# ``R(w, v)`` and crashed Z3 on the arity clash). _user_predicate keeps the
# two namespaces apart: U+00B7 MIDDLE DOT is punctuation no parser puts into
# an identifier, so the renamed user name can collide with nothing.
_RESERVED_RELATIONS = frozenset({_R_ALETHIC, _R_TEMPORAL, _R_NEXT, _R_DEONTIC})
_RESERVED_RELATION_PREFIXES = (_R_KNOWS_PREFIX, _R_BELIEVES_PREFIX,
                               _R_SAYS_PREFIX, _R_WANTS_PREFIX)
_USER_MARK = "·"


def _user_predicate(name: str) -> str:
    """The name a USER atom's predicate gets in the image: unchanged unless it
    (with any trailing ``·`` stripped) is a relation name above, then with one
    ``·`` appended — injective, and a formula that avoids those names
    translates byte-for-byte as before (the same scheme as ``fol.qml``)."""
    base = name.rstrip(_USER_MARK)
    if base in _RESERVED_RELATIONS or base.startswith(_RESERVED_RELATION_PREFIXES):
        return name + _USER_MARK
    return name


class _FreshWorlds:
    """A monotonic generator of fresh world-variable names ``w0, w1, …``.

    Threading a single counter through one translation guarantees every modal
    operator introduces a distinct bound world variable, so nested boxes /
    diamonds cannot capture one another's worlds. A world variable never has the
    spelling of a name the translation must leave alone: the free current-world
    name (so a caller who passes ``world="w0"`` keeps a distinct, uncaptured free
    variable), every name of the formula, of any kind (an atom ``P(w0)`` of the
    source keeps its own ``w0`` under a box, which a bound world variable of that
    name would capture) and every name the caller asks to avoid. Names are compared
    exactly and with their case folded, because a target that reads a variable
    ``w0`` and a variable ``W0`` as one word (TPTP, Prover9) would conflate them.

    A variable of the formula that is spelled like the current-world name would be
    read as the world itself, so it is renamed, once for the whole formula, to a name
    of its own (:meth:`term` applies the renaming to a term of an atom).
    """

    def __init__(self, world: str = "", names: Iterable[str] = (),
                 variables: Iterable[str] = (), avoid: Iterable[str] = ()):
        """Start the fresh-name counter at zero and settle the names that are never minted.

        ``world`` is the free current-world name, ``names`` every name of the formula,
        ``variables`` the names of its variables and ``avoid`` further names to keep
        clear of.
        """
        self._n = 0
        reserved = set(names) | set(variables) | set(avoid) | {world}
        taken = reserved | {name.casefold() for name in reserved}
        self._renamed: Dict[str, Variable] = {}
        for name in sorted(set(variables)):
            if name.casefold() == world.casefold():
                new_name = fresh_variables(1, letter="x", avoid=taken)[0]
                taken = taken | {new_name}
                self._renamed[name] = Variable(new_name)
        self._reserved = taken

    def next(self) -> Variable:
        """Return the next fresh world Variable (``w0``, ``w1``, …), skipping ``reserved``."""
        while True:
            name = f"w{self._n}"
            self._n += 1
            if name not in self._reserved:
                return Variable(name)

    def term(self, term: Node) -> Node:
        """``term`` with each variable spelled like the current world renamed (else unchanged)."""
        for old, new in self._renamed.items():
            term = substitute(term, Variable(old), new)
        return term


def _box_like(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds,
             bindings: Dict[str, Node]) -> Node:
    """Build ``∀w' (rel(world, w') → ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, (world, w2))
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh, bindings)))


def _diamond_like(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds,
                  bindings: Dict[str, Node]) -> Node:
    """Build ``∃w' (rel(world, w') ∧ ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, (world, w2))
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh, bindings)))


def _box_intersection(rel_names: List[str], world: Node, body: Node, fresh: _FreshWorlds,
                      bindings: Dict[str, Node]) -> Node:
    """Build ``∀w' ((R1(w,w')∧R2(w,w')∧…) → ST(body,w'))`` — a box over the
    INTERSECTION of several accessibility relations, one atom per relation
    ANDed together into the antecedent, sharing ONE fresh ``w'`` (a single
    successor has to satisfy every relation at once — this is exactly what
    distinguishes :class:`DistributedKnowledge` from
    :func:`_box_like`-per-agent-then-ANDed, which is what
    :class:`EverybodyKnows` uses instead, and which shares no such single
    witness). ``rel_names`` must be non-empty (guaranteed by
    :class:`DistributedKnowledge`'s own constructor refusing an empty group).
    """
    w2 = fresh.next()
    guard: Node = Atom(rel_names[0], (world, w2))
    for name in rel_names[1:]:
        guard = And(guard, Atom(name, (world, w2)))
    return Quantifier(_FORALL, w2, Implies(guard, _translate(body, w2, fresh, bindings)))


def _box_converse(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds,
                  bindings: Dict[str, Node]) -> Node:
    """Build ``∀w' (rel(w', world) → ST(body, w'))`` — a box over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, (w2, world))
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh, bindings)))


def _diamond_converse(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds,
                      bindings: Dict[str, Node]) -> Node:
    """Build ``∃w' (rel(w', world) ∧ ST(body, w'))`` — a diamond over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, (w2, world))
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh, bindings)))


def _translate(formula: Node, world: Node, fresh: _FreshWorlds,
               bindings: Optional[Dict[str, Node]] = None) -> Node:
    """Recursively translate ``formula`` relative to ``world`` (the worker).

    ``world`` is the current-world TERM: the free Variable at the top, a bound
    fresh Variable under a modality, or a ``nom_``-Constant under an ``@``-jump.

    ``bindings`` (name → world TERM) holds the ``↓``-bound nominal names in
    scope (N1); every call site outside :class:`Down`'s own recursion passes
    ``{}`` (the default), which is exactly what makes ``bindings={}``
    reproduce the pre-``Down`` translation byte-for-byte — see the module
    docstring's ``Down`` bullet.
    """
    if bindings is None:
        bindings = {}

    # --- atomic: append the world as the last predicate argument ---
    if isinstance(formula, Atom):
        if truth_value(formula) is not None:
            return formula      # `$true` / `$false` are the same at every world: no world argument
        _reject_equality(formula)
        return Atom(_user_predicate(formula.predicate),
                    (*(fresh.term(arg) for arg in formula.args), world))

    # --- classical connectives: structural at the same world ---
    if isinstance(formula, Not):
        return Not(_translate(formula.formula, world, fresh, bindings))
    if isinstance(formula, And):
        return And(_translate(formula.left, world, fresh, bindings),
                   _translate(formula.right, world, fresh, bindings))
    if isinstance(formula, Or):
        return Or(_translate(formula.left, world, fresh, bindings),
                  _translate(formula.right, world, fresh, bindings))
    if isinstance(formula, Xor):
        return Xor(_translate(formula.left, world, fresh, bindings),
                   _translate(formula.right, world, fresh, bindings))
    if isinstance(formula, Implies):
        return Implies(_translate(formula.left, world, fresh, bindings),
                       _translate(formula.right, world, fresh, bindings))
    if isinstance(formula, Iff):
        return Iff(_translate(formula.left, world, fresh, bindings),
                   _translate(formula.right, world, fresh, bindings))

    # --- alethic ---
    if isinstance(formula, Box):
        return _box_like(_R_ALETHIC, world, formula.formula, fresh, bindings)
    if isinstance(formula, Diamond):
        return _diamond_like(_R_ALETHIC, world, formula.formula, fresh, bindings)

    # --- epistemic / doxastic (both box-like / universal) ---
    if isinstance(formula, Knows):
        return _box_like(_R_KNOWS_PREFIX + _agent_key(formula.agent), world,
                         formula.formula, fresh, bindings)
    if isinstance(formula, Believes):
        return _box_like(_R_BELIEVES_PREFIX + _agent_key(formula.agent), world,
                         formula.formula, fresh, bindings)

    # --- group epistemic: E_G and D_G are one-step (union/intersection of
    # per-agent relations) and ARE first-order definable; C_G needs the
    # reflexive-transitive CLOSURE of the union relation and is NOT (see the
    # rejection below, alongside Until/Since). ---
    if isinstance(formula, EverybodyKnows):
        if not formula.group:
            raise NotImplementedError(
                "standard_translation: E_∅ φ (a group-epistemic operator over "
                "an empty group) is vacuously TRUE at every world by "
                "definition (everybody_knows's own empty-group convention), "
                "but this grammar has no first-order truth constant to render "
                "that without borrowing an unrelated atom. Evaluate it "
                "directly with semantics.kripke.satisfies_modal / "
                "semantics.action_models.everybody_knows instead."
            )
        conj = _box_like(_R_KNOWS_PREFIX + _agent_key(formula.group[0]), world,
                         formula.formula, fresh, bindings)
        for agent in formula.group[1:]:
            conj = And(conj, _box_like(_R_KNOWS_PREFIX + _agent_key(agent), world,
                                       formula.formula, fresh, bindings))
        return conj
    if isinstance(formula, DistributedKnowledge):
        rel_names = [_R_KNOWS_PREFIX + _agent_key(a) for a in formula.group]
        return _box_intersection(rel_names, world, formula.formula, fresh, bindings)
    if isinstance(formula, CommonKnowledge):
        raise NotImplementedError(
            "standard_translation: CommonKnowledge (C_G) is not first-order "
            "definable — common knowledge is the REFLEXIVE-TRANSITIVE CLOSURE "
            "of the group's union relation, and transitive closure has no "
            "first-order rendering (the same obstacle this module already "
            "reports for Until/Since — see the module docstring). Evaluate it "
            "with the Kripke evaluator (semantics.kripke.satisfies_modal) "
            "instead."
        )

    # --- assertive / bouletic (both box-like, per-agent relations) ---
    if isinstance(formula, Says):
        return _box_like(_R_SAYS_PREFIX + _agent_key(formula.agent), world,
                         formula.formula, fresh, bindings)
    if isinstance(formula, Wants):
        return _box_like(_R_WANTS_PREFIX + _agent_key(formula.agent), world,
                         formula.formula, fresh, bindings)

    # --- deontic (box/diamond over a deontic accessibility predicate D) ---
    if isinstance(formula, Obligatory):
        return _box_like(_R_DEONTIC, world, formula.formula, fresh, bindings)
    if isinstance(formula, Permitted):
        return _diamond_like(_R_DEONTIC, world, formula.formula, fresh, bindings)

    # --- temporal (box/diamond over an assumed accessibility predicate) ---
    if isinstance(formula, Always):
        return _box_like(_R_TEMPORAL, world, formula.formula, fresh, bindings)
    if isinstance(formula, Eventually):
        return _diamond_like(_R_TEMPORAL, world, formula.formula, fresh, bindings)
    if isinstance(formula, Next):
        return _box_like(_R_NEXT, world, formula.formula, fresh, bindings)

    # --- past tense (box/diamond over the CONVERSE temporal/next predicate) ---
    if isinstance(formula, Historically):
        return _box_converse(_R_TEMPORAL, world, formula.formula, fresh, bindings)
    if isinstance(formula, Once):
        return _diamond_converse(_R_TEMPORAL, world, formula.formula, fresh, bindings)
    if isinstance(formula, Previous):
        return _box_converse(_R_NEXT, world, formula.formula, fresh, bindings)

    # --- hybrid: a nominal is a world-equality; @ re-anchors the world term.
    # ``bindings`` is consulted FIRST — a ↓-bound name uses its bound TERM
    # directly (no fresh nom_ constant, no equality atom needed for Nominal:
    # "x" bound to term t just means "the current world is t", i.e. w = t —
    # same shape as the nom_ case, just with t instead of a fresh constant). ---
    if isinstance(formula, Nominal):
        bound = bindings.get(formula.name)
        target = bound if bound is not None else Constant(_NOM_PREFIX + formula.name)
        return Atom("=", (world, target))
    if isinstance(formula, At):
        bound = bindings.get(formula.nominal.name)
        target = bound if bound is not None else Constant(_NOM_PREFIX + formula.nominal.name)
        return _translate(formula.formula, target, fresh, bindings)
    if isinstance(formula, Down):
        # ↓x.φ: bind x to the CURRENT world term for the rest of φ's
        # translation — NO fresh quantifier (the bounded-fragment
        # translation; see the module docstring's Down bullet and
        # fol._hybrid_nodes.Down's own docstring for why this is sound: ST
        # stays meaning-preserving for full H(@,↓), this is not an
        # approximation).
        return _translate(formula.formula, world, fresh,
                          {**bindings, formula.variable.name: world})

    # --- rejected ---
    if isinstance(formula, (Until, Since)):
        raise NotImplementedError(
            "standard_translation: Until / Since are not first-order definable — "
            "strong Until/Since need the transitive closure of the temporal "
            "relation, which no pure FOL formula captures. Evaluate them with the "
            "Kripke evaluator (semantics.kripke.satisfies_modal) instead."
        )
    if isinstance(formula, (Quantifier, SortedQuantifier)):
        _reject_quantifier(formula)
    if isinstance(formula, FUZZY_TYPES):
        reject_fuzzy(formula, "standard_translation")
    if isinstance(formula, LAMBDA_TYPES):
        reject_lambda(formula, "standard_translation")

    raise NotImplementedError(
        f"standard_translation: unsupported node type {type(formula).__name__}."
    )


def _reject_quantifier(formula: Node) -> NoReturn:
    """Reject an object-level quantifier: FO-modal domains are out of scope."""
    raise NotImplementedError(
        f"standard_translation: {type(formula).__name__} is not supported — the "
        "standard translation here covers the propositional modal fragment only. "
        "For quantified (first-order) modal logic with object domains use "
        "unicode_logic_kit.fol.qml (qml_translate / qml_is_valid, the FO shallow "
        "embedding with explicit constant/varying/increasing/decreasing domain "
        "regimes)."
    )


def _check_nominal_collision(formula: Node) -> None:
    """Raise if a user symbol's name collides with a nominal world constant.

    Each nominal ``i`` (a ``Nominal`` or the label of an ``At``) translates to the
    reserved world constant ``nom_i``. If the formula independently contains a
    user symbol named ``nom_i`` -- a ``Constant``, a ``SortedConstant``, a
    ``Function``, or any other node that carries a name and is neither a nominal nor
    a variable -- the first-order image would
    conflate the two terms and Z3's equality reasoning could report a genuinely
    invalid formula as valid — a hole in the "``True`` is always a proof"
    guarantee. The parser builds such a name from the text itself (``@i P(nom_i)``),
    and a hand-built or deserialised AST can carry one in any position; the check fails
    fast, exactly like a dangling nominal assignment.
    """
    nominal_names, user_names = set(), set()
    for node in formula.walk():
        if isinstance(node, Nominal):
            nominal_names.add(node.name)
        elif isinstance(node, At):
            nominal_names.add(node.nominal.name)
        elif (not isinstance(node, (Variable, LambdaVar))
              and isinstance(getattr(node, "name", None), str)):
            user_names.add(node.name)
    clash = {_NOM_PREFIX + n for n in nominal_names} & user_names
    if clash:
        colliding = sorted(n for n in nominal_names if _NOM_PREFIX + n in clash)
        raise ValueError(
            f"standard_translation: user symbol(s) {sorted(clash)} collide with the "
            f"reserved world constant(s) for nominal(s) {colliding}; the "
            f"{_NOM_PREFIX!r} prefix is reserved for the hybrid translation — rename "
            "the user constant/function."
        )


def standard_translation(formula: Node, world: str = "w",
                         avoid: Iterable[str] = ()) -> Node:
    """Translate a propositional modal ``formula`` into a classical FOL Node.

    ``world`` names the free current-world variable threaded through the
    translation (default ``"w"``); the result is a plain first-order formula in
    which propositional atoms ``A`` become ``A(world)`` and each modality becomes
    a quantification over a fresh world variable bounded by an accessibility
    predicate (see the module docstring for the exact scheme and the fixed
    predicate names). The returned Node uses only classical FOL constructs, so it
    can be handed to ``to_z3`` / ``to_prover9`` / ``to_tptp`` / the Tarski
    evaluator.

    Hybrid constructs translate too: ``Nominal i`` becomes the world-equality
    ``world = nom_i`` and ``At(i, φ)`` becomes ``ST(φ)`` anchored at the constant
    ``nom_i`` (the ``"nom_"`` prefix keeps nominal constants disjoint from user
    constants — see the module docstring).

    The variables of an atom (``P(w0)``) are the caller's own, and so are the names
    the translation mints. The world variables it binds (``w0``, ``w1``, …) never have
    the spelling of a name of ``formula`` (of any kind: variable, constant, predicate,
    nominal, …), of ``world`` or of a name in ``avoid``, compared exactly and with the
    case folded, so ``□P(w0)`` is ``∀w1 (R(w, w1) → P(w0, w1))`` and not a statement
    about the bound world. A variable of ``formula`` that is spelled like ``world``
    would be read as the current world itself, so it is renamed to a name of its own
    (``x0``, …, clear of every name of ``formula``, of ``world`` and of ``avoid``) in
    the image: it stays one free variable, the same in every atom. To translate several
    formulas of one problem separately and keep that name the same in all of them, pass
    the names of the others as ``avoid``.

    Raises:
        NotImplementedError: on ``Until`` (not first-order definable), any
            object-level quantifier (first-order modal logic is out of scope for
            v1), a Łukasiewicz node, or a lambda node; and on two different agent
            terms that are named alike (the numeral ``1`` and a constant named ``1``):
            the relation of an agent's operator is named after the agent, so the two
            would be ONE relation and the image would say another thing than ``formula``.
    """
    _check_nominal_collision(formula)
    refuse_alike_agents([formula], "standard_translation")
    variables = {node.name for node in formula.walk() if isinstance(node, Variable)}
    fresh = _FreshWorlds(world, symbol_names(formula), variables, avoid)
    return _translate(formula, Variable(world), fresh)


# =========================
# Hybrid validity via the standard translation + the Z3 oracle
# =========================

# Frame classes hybrid_is_valid understands, as conditions on the ALETHIC
# accessibility predicate R (the other modal families keep their minimal K
# reading — no axioms are asserted for Rk_a / Rb_a / T / N / D here). The
# table is the shared registry (unicode_logic_kit.fol.frames), so this route
# understands the same systems as every other one; conditions with no
# first-order form are refused by name.
_HYBRID_FRAMES = _SHARED_FRAMES


# Which accessibility relation each modal family reads, mirroring _st above.
_AGENT_FAMILY_PREFIX: Dict[str, str] = {
    "epistemic": _R_KNOWS_PREFIX,
    "doxastic": _R_BELIEVES_PREFIX,
    "assertive": _R_SAYS_PREFIX,
    "bouletic": _R_WANTS_PREFIX,
}


def relations_used(formula: Node) -> FrozenSet[str]:
    """Every accessibility predicate :func:`standard_translation` emits for
    ``formula`` (``"R"``, ``"T"``, ``"N"``, ``"D"``, ``"Rk_alice"``, …).

    This is what gates :func:`frame_axioms`: a condition on a relation the
    formula never mentions is noise, and — on a route that reports a bare
    "not valid" — noise that can change the answer.
    """
    used: set = set()
    for node in formula.walk():
        if isinstance(node, (Box, Diamond)):
            used.add(_R_ALETHIC)
        elif isinstance(node, Knows):
            used.add(_R_KNOWS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, (EverybodyKnows, DistributedKnowledge)):
            used.update(_R_KNOWS_PREFIX + _agent_key(a) for a in node.group)
        elif isinstance(node, Believes):
            used.add(_R_BELIEVES_PREFIX + _agent_key(node.agent))
        elif isinstance(node, Says):
            used.add(_R_SAYS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, Wants):
            used.add(_R_WANTS_PREFIX + _agent_key(node.agent))
        elif isinstance(node, (Obligatory, Permitted)):
            used.add(_R_DEONTIC)
        elif isinstance(node, (Always, Eventually, Historically, Once)):
            used.add(_R_TEMPORAL)
        elif isinstance(node, (Next, Previous)):
            used.add(_R_NEXT)
    return frozenset(used)


def _link(antecedent_relation: str, consequent_relation: str) -> Node:
    """``∀v0 ∀v1 (A(v0,v1) → B(v0,v1))`` over two relation names."""
    w, v = Variable("v0"), Variable("v1")
    return Quantifier(_FORALL, w, Quantifier(_FORALL, v, Implies(
        Atom(antecedent_relation, (w, v)), Atom(consequent_relation, (w, v)))))


def _temporal_first_step() -> Node:
    """``∀v0 ∀v1 (T(v0,v1) → v0 = v1 ∨ ∃v2 (N(v0,v2) ∧ T(v2,v1)))``.

    The first-order half of ``T ⊆ N*``: the witnessing path of a henceforth-step
    either stands still or starts with one ``N``-step. ``T ⊆ N*`` itself demands
    a FINITE path and is not first-order definable, but every model with
    ``T = N*`` satisfies this, which is what makes asserting it sound. The
    unguarded twin of :func:`unicode_logic_kit.fol.qml._temporal_first_step_axiom`
    — the two routes must agree, so they assert the same thing.
    """
    w, v, u = Variable("v0"), Variable("v1"), Variable("v2")
    return Quantifier(_FORALL, w, Quantifier(_FORALL, v, Implies(
        Atom(_R_TEMPORAL, (w, v)),
        Or(Atom(_EQUALITY, (w, v)),
           Quantifier(_EXISTS, u, And(Atom(_R_NEXT, (w, u)),
                                      Atom(_R_TEMPORAL, (u, v))))))))


def frame_axioms(formula: Node, frame: str = "K", systems=None,
                 temporal_closure: bool = True) -> List[Node]:
    """The first-order frame axioms for EVERY relation ``formula``'s translation
    emits — the side conditions of the standard translation.

    ``frame`` constrains the ALETHIC relation ``R`` and is any system in the
    shared registry (:mod:`unicode_logic_kit.fol.frames`) or a Scott–Lemmon spec
    like ``"G(1,1,1,1)"``; a system whose condition has no first-order form
    (GL, S4.1, Grz) is refused by name, because this route is first-order.

    The other families get the conventions :mod:`unicode_logic_kit.fol.qml` and
    the Isabelle/THF exporters already use, so the routes agree instead of
    contradicting each other:

    - temporal: ``T`` reflexive and transitive (``temporal_closure=True``,
      the default), ``N ⊆ T``, and :func:`_temporal_first_step` when both
      occur — this is what makes ``Ⓖφ → φ``, ``Ⓖφ → Ⓝφ`` and the past mirrors
      come out valid, as the Kripke evaluator reads them (it evaluates
      ``Always``/``Eventually`` over the reflexive-transitive CLOSURE of the
      one-step relation). Until 0.28.1 NOTHING asserted these on this route,
      so ``hybrid_is_valid(Ⓖ P → P, "S5")`` answered False while
      ``qml_is_valid`` on the same formula answered True — a bare "not valid"
      about a formula the kit's own modal semantics validates.
    - deontic: ``D`` serial (Standard Deontic Logic), so ``Ⓞφ → Ⓟφ`` is valid.
    - agent-indexed: nothing unless ``systems`` asks, e.g.
      ``systems={"epistemic": "S5", "doxastic": "KD45"}`` — the families are
      ``epistemic`` / ``doxastic`` / ``assertive`` / ``bouletic`` and an unknown
      one raises. A system for a family the formula never mentions contributes
      nothing (same as ``qml_axioms``).
    - sorted constants: ``c:S`` is an element of ``S`` at EVERY world (a constant is
      a rigid designator), so each distinct ``c:S`` of the formula adds
      ``∀v0 S(c, v0)`` — the sort guard in the translation's own vocabulary (a
      world as last argument), unguarded by any existence predicate, as in
      ``qml_axioms``. Without it ``Human(carl:Human)`` has a countermodel in
      which ``carl`` is no ``Human``, and a route that reads Z3's ``sat`` as
      "refuted" answers wrongly. A sort that occurs only through a constant needs
      no non-emptiness axiom: the constant is its member.

    Every axiom is closed over its own bound variables (``v0``, ``v1``, …), so
    it can never capture anything in the translated formula, and they are
    returned for the caller to pass as SEPARATE premises — never conjoined onto
    the translation itself. The names are deliberately ones the kit's own
    parser reads back: an axiom that prints as ``∀_hw0 R(_hw0, _hw0)`` is text
    :func:`unicode_logic_kit.api.parse_any` rejects.

    Raises:
        ValueError: unknown frame system, or an unknown ``systems`` family.
        UnsupportedFrameCondition: a condition with no first-order frame form.
    """
    used = relations_used(formula)
    axioms: List[Node] = []
    # Resolve the frame FIRST, whatever the formula mentions: a typo in a frame
    # name must fail loudly even for a formula with no alethic operator, or the
    # caller would believe a system was applied that nothing ever looked at.
    try:
        alethic = resolve_frame(frame)
    except ValueError as exc:
        raise ValueError(f"frame_axioms: {exc}") from None
    # ... and refuse a condition with no first-order form here too, rather than
    # only when the formula happens to mention R: asking this route for GL is a
    # request it cannot honour either way.
    for cond in alethic:
        if not is_first_order(cond):
            raise UnsupportedFrameCondition(
                f"frame_axioms: the frame condition {cond!r} has no "
                f"first-order frame condition, so the standard translation "
                f"cannot express {frame!r} (Löb, S4.1 and Grz need the "
                f"higher-order routes: hol.isabelle_modal / hol.thf_modal, or "
                f"the finite-frame enumerator atp.kripke_enum)")
    if _R_ALETHIC in used:
        axioms += [unguarded_frame_axiom(cond, _R_ALETHIC, prefix="v")
                   for cond in alethic]
    if _R_TEMPORAL in used and temporal_closure:
        axioms += [unguarded_frame_axiom("refl", _R_TEMPORAL, prefix="v"),
                   unguarded_frame_axiom("trans", _R_TEMPORAL, prefix="v")]
    if _R_TEMPORAL in used and _R_NEXT in used:
        # Vacuous — and misleading — unless BOTH relations occur.
        axioms.append(_link(_R_NEXT, _R_TEMPORAL))
        if temporal_closure:
            axioms.append(_temporal_first_step())
    if _R_DEONTIC in used:
        axioms.append(unguarded_frame_axiom("serial", _R_DEONTIC, prefix="v"))
    for family, system in dict(systems or {}).items():
        if family not in _AGENT_FAMILY_PREFIX:
            raise ValueError(
                f"frame_axioms: unknown modal family {family!r} in systems "
                f"(known: {sorted(_AGENT_FAMILY_PREFIX)})")
        prefix = _AGENT_FAMILY_PREFIX[family]
        try:
            conds = resolve_frame(system)
        except ValueError as exc:
            raise ValueError(f"frame_axioms: {exc}") from None
        for relation in sorted(r for r in used if r.startswith(prefix)):
            axioms += [unguarded_frame_axiom(cond, relation, prefix="v")
                       for cond in conds]
    for member in sort_membership_axioms(formula):
        assert isinstance(member, Atom)     # sort_membership_axioms yields atoms ``S(c)`` only
        axioms.append(Quantifier(_FORALL, Variable("v0"), Atom(
            _user_predicate(member.predicate), (member.args[0], Variable("v0")))))
    return axioms


def _frame_axioms(frame: str) -> List[Node]:
    """Deprecated alias: :func:`frame_axioms` for an alethic-only formula.

    Kept because the name was imported inside the kit; it cannot see which
    relations a formula uses, so it only ever constrained ``R``.
    """
    return frame_axioms(Box(Atom("P", ())), frame=frame)


def hybrid_is_valid(formula: Node, frame: str = "K", timeout: int = 10000,
                    systems=None, temporal_closure: bool = True) -> bool:
    """Return True iff the hybrid-modal ``formula`` is valid over ``frame`` (via Z3).

    Validity of H(@) over a frame class: true at EVERY world of EVERY Kripke
    model whose alethic relation satisfies the frame conditions, under EVERY
    nominal assignment. The check is the standard translation closed over the
    current world under the frame axioms::

        frame_axioms  →  ∀w ST(formula)(w)

    handed to the Z3 validity oracle. The nominal constants ``nom_i`` are left
    FREE in that implication — first-order validity quantifies free constants
    universally, which is exactly "for every nominal assignment" (each constant
    denotes exactly one domain element = one world, matching a nominal's
    name-exactly-one-world semantics).

    ``frame`` constrains the ALETHIC relation and is any system of the shared
    registry (:mod:`unicode_logic_kit.fol.frames`) or a Scott–Lemmon spec; a
    system with no first-order condition (GL, S4.1, Grz) is refused by name.
    The OTHER relations the translation emits get the conventions
    :func:`frame_axioms` documents — temporal ``T`` reflexive-transitive with
    ``N ⊆ T`` (``temporal_closure=True``) and deontic ``D`` serial, both ON by
    default, so this route agrees with ``fol.qml`` and with the Kripke
    evaluator instead of reporting "not valid" for ``Ⓖφ → φ``; the
    agent-indexed epistemic / doxastic / assertive / bouletic relations stay K
    unless ``systems={"epistemic": "S5", …}`` asks for more.

    Soundness/completeness: first-order validity is only semi-decidable in
    general, so ``is_valid`` may time out (returning False) on hard instances —
    but hybrid logic H(@) over K is DECIDABLE, and the ST images of H(@)
    formulas (two-variable-like, tiny) are well within Z3's reach in practice;
    the frame-axiom variants used here (T/S4/S5) behave the same on these
    inputs. ``True`` is always a real proof; treat ``False`` as
    "not proven valid" (for these small hybrid instances: a genuine
    countermodel).

    Raises:
        NotImplementedError: ``formula`` contains a ``Down`` node (the ↓
            binder, N1). Adding ↓ makes hybrid validity UNDECIDABLE, so this
            function's bare-``bool`` contract — where ``False`` is safe to
            read as "a genuine countermodel" precisely BECAUSE H(@) over K is
            decidable and Z3 reliably closes these small instances — no
            longer holds: a bare ``False`` on a ↓-formula could equally be a
            countermodel or an honest Z3 timeout on an undecidable query, and
            this function has no second field to tell them apart. Use
            :func:`down_is_valid` instead (a :class:`~unicode_logic_kit.atp.protocol.Verdict`,
            PROVED-only — never claims REFUTED) or
            :func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search` /
            :class:`~unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend` for a
            bounded-search REFUTED verdict.
    """
    for n in formula.walk():
        if isinstance(n, Down):
            raise NotImplementedError(
                "hybrid_is_valid: the ↓ binder (Down) makes hybrid validity "
                "undecidable, so this bare-bool, PROVED-and-REFUTED-conflating "
                "check cannot honestly answer for it. Use down_is_valid "
                "(PROVED-only, never REFUTED) or "
                "unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend / "
                "modal_enum_search (bounded search, REFUTED-only) instead."
            )
    from ..atp.z3_models import is_valid  # local import (as in fol.qml): keeps fol importable without z3
    w = Variable("w")
    closed = Quantifier(_FORALL, w, standard_translation(formula, world="w"))
    hyp = None
    for axiom in frame_axioms(formula, frame, systems=systems,
                              temporal_closure=temporal_closure):
        hyp = axiom if hyp is None else And(hyp, axiom)
    goal = closed if hyp is None else Implies(hyp, closed)
    return is_valid(goal, timeout=timeout)


# =========================
# ↓ validity via the standard translation + a direct Z3 solver call (N1)
# =========================
#
# down_is_valid is hybrid_is_valid's PROVED-only sibling for the FULL hybrid
# language H(@,↓). It exists as a SEPARATE function, not a keyword flag on
# hybrid_is_valid, precisely because the two make different promises:
# hybrid_is_valid's bare bool is safe only because H(@) over K is decidable
# (so "not proved" IS "refuted" there); down_is_valid must call the Z3
# Solver() directly — never the bare-bool is_valid() wrapper, which collapses
# Z3's 'sat' (a genuine countermodel) and 'unknown' (timeout / incompleteness
# on an undecidable query) into the same False (unicode_logic_kit.atp.z3_models
# .is_valid, confirmed by direct reading) — so it can tell the two apart and
# report them honestly as UNKNOWN, never smuggling a REFUTED claim out of a
# SAT witness this route never verified against a presentable finite
# KripkeModel (that verification is KripkeEnumBackend's job — see
# fol._hybrid_nodes' module docstring and atp.hybrid_down.down_decide, which
# combines the two into one call).

def down_is_valid(formula: Node, frame: str = "K", timeout: int = 10000,
                  systems=None, temporal_closure: bool = True) -> "Verdict":
    """Return a :class:`~unicode_logic_kit.atp.protocol.Verdict` for the FULL
    hybrid-modal ``formula`` (H(@,↓), including ``Down``/↓) over ``frame``.

    Builds the exact same goal ``hybrid_is_valid`` does — the standard
    translation, closed over the current world, under the frame axioms
    (``standard_translation`` now threads ``Down``'s local rebinding through,
    see the module docstring) — but decides it with a Z3 ``Solver()`` called
    directly, so ``unsat`` (of the negated goal) and ``sat``/``unknown`` are
    told apart instead of collapsed:

    - Z3 ``unsat`` → ``PROVED`` — sound unconditionally: soundness of a
      Z3-``unsat`` verdict depends only on Z3's own soundness, never on
      whether Z3 is a COMPLETE decision procedure for this (undecidable)
      fragment (see ``fol._hybrid_nodes``' module docstring for the
      co-r.e. argument this rests on: ST is meaning-preserving for H(@,↓)
      — Areces/Blackburn/Marx 1999 — so FO-``unsat``-of-the-negation IS
      H(@,↓)-validity, exactly).
    - Z3 ``sat`` (of the negated goal) → ``UNKNOWN`` / ``reason="incomplete"``
      — NEVER ``REFUTED``. A SAT witness here would, ON INSPECTION, also be a
      sound Kripke countermodel in principle (same correspondence as above,
      run in the other direction) — this is a deliberate COMPLETENESS
      sacrifice, not a soundness requirement, made to sidestep turning an
      arbitrary Z3 model back into a presentable, inspectable finite
      :class:`~unicode_logic_kit.semantics.kripke.KripkeModel`. Use
      :func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search` /
      :class:`~unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend` for an
      actual REFUTED verdict, with a countermodel independently
      re-verified by :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal`
      — or :func:`~unicode_logic_kit.atp.hybrid_down.down_decide`, which runs
      both routes and combines them.
    - Z3 times out → ``UNKNOWN`` / ``reason="timeout"``.

    This function decides ANY formula ``standard_translation`` accepts
    (``Down`` or not) — it is not restricted to ↓-containing input; a plain
    H(@) formula is handled identically, just more conservatively than
    ``hybrid_is_valid`` (which, for THAT decidable fragment, is entitled to —
    and does — read Z3 ``sat``/``unknown`` as a genuine countermodel).
    """
    import time
    from ..atp.protocol import PROVED, UNKNOWN, Verdict  # local: keeps fol importable without atp
    from z3 import Not as _ZNot, Solver, sat, unsat

    w = Variable("w")
    closed = Quantifier(_FORALL, w, standard_translation(formula, world="w"))
    hyp = None
    for axiom in frame_axioms(formula, frame, systems=systems,
                              temporal_closure=temporal_closure):
        hyp = axiom if hyp is None else And(hyp, axiom)
    goal = closed if hyp is None else Implies(hyp, closed)

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.add(_ZNot(goal.to_z3()))
    start = time.perf_counter()
    result = solver.check()
    elapsed = time.perf_counter() - start

    if result == unsat:
        return Verdict(PROVED, "down_is_valid", logic="hybrid", wall_time=elapsed)
    if result == sat:
        return Verdict(
            UNKNOWN, "down_is_valid", logic="hybrid", reason="incomplete", wall_time=elapsed,
            detail=("Z3 found a model of the negated goal; down_is_valid never "
                    "reads this as REFUTED (see its own docstring) — use "
                    "atp.kripke_enum.KripkeEnumBackend / modal_enum_search, or "
                    "atp.hybrid_down.down_decide, for a genuine countermodel."))
    why = solver.reason_unknown()
    reason = "timeout" if ("timeout" in why or "cancel" in why) else "incomplete"
    return Verdict(UNKNOWN, "down_is_valid", logic="hybrid", reason=reason,
                   wall_time=elapsed, detail=why)
