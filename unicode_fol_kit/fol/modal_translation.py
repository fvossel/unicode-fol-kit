"""Standard (relational) translation of propositional modal logic into FOL.

The *standard translation* ST embeds the propositional modal fragment into
classical first-order logic over an explicit "current world" term, so that the
existing FOL back-ends (Z3, Prover9, TPTP, the resolution engine, the Tarski
evaluator) can reason about modal formulas. A modal formula is true at a world
*w* in a Kripke model exactly when its translation ``ST(φ, w)`` is true in the
corresponding first-order structure (worlds as the domain, accessibility
relations and atom-predicates as the relations) — this correspondence is what
``tests/test_modal_translation.py`` cross-checks against
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal`.

Translation scheme, with ``w`` the current-world variable and ``w'`` a FRESH
world variable (names ``w0, w1, …`` are generated so nested modalities never
capture each other; the free current-world name is skipped, so even a caller
who passes ``world="w0"`` keeps a distinct, uncaptured free variable):

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
  can never collide with the nominal ``i``.
- ``At(i, φ)``   → ``ST(φ, nom_i)``: the satisfaction operator ``@i φ``
  re-anchors the translation at the constant world term ``nom_i`` (the current
  world term is simply replaced — no quantifier is introduced).

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
- ``Quantifier`` / ``SortedQuantifier`` are rejected: first-order (quantified)
  modal logic with object domains is out of scope for v1. So are Łukasiewicz and
  lambda nodes.

The accessibility-predicate names are fixed so the matching Tarski structure can
be built mechanically: ``"R"`` (alethic), ``"Rk_" + agent`` (epistemic),
``"Rb_" + agent`` (doxastic), ``"Rs_" + agent`` (assertive), ``"Rw_" + agent``
(bouletic), ``"T"`` (temporal), ``"N"`` (next), ``"D"`` (deontic).
"""

from typing import List, NoReturn

from .nodes import (
    Node,
    Variable, Constant, Function,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Nominal, At,
)
from .frames import (
    FRAMES as _SHARED_FRAMES, UnsupportedFrameCondition,
    resolve_frame, unguarded_frame_axiom,
)
from ..semantics._modal_reject import (
    FUZZY_TYPES, LAMBDA_TYPES,
    reject_fuzzy, reject_lambda,
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

# Universal/existential quantifier-type spellings used by the AST.
_FORALL = "∀"
_EXISTS = "∃"


class _FreshWorlds:
    """A monotonic generator of fresh world-variable names ``w0, w1, …``.

    Threading a single counter through one translation guarantees every modal
    operator introduces a distinct bound world variable, so nested boxes /
    diamonds cannot capture one another's worlds. The free current-world name is
    held in ``reserved`` and skipped, so passing a current-world name that lies
    in the ``w0, w1, …`` namespace (e.g. ``world="w0"``) cannot be captured by a
    bound world variable.
    """

    def __init__(self, reserved: str = ""):
        """Start the fresh-name counter at zero, reserving the free-world name."""
        self._n = 0
        self._reserved = reserved

    def next(self) -> Variable:
        """Return the next fresh world Variable (``w0``, ``w1``, …), skipping ``reserved``."""
        name = f"w{self._n}"
        self._n += 1
        if name == self._reserved:
            return self.next()
        return Variable(name)


def _box_like(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∀w' (rel(world, w') → ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, [world, w2])
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh)))


def _diamond_like(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∃w' (rel(world, w') ∧ ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, [world, w2])
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh)))


def _box_converse(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∀w' (rel(w', world) → ST(body, w'))`` — a box over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, [w2, world])
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh)))


def _diamond_converse(rel_name: str, world: Node, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∃w' (rel(w', world) ∧ ST(body, w'))`` — a diamond over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, [w2, world])
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh)))


def _translate(formula: Node, world: Node, fresh: _FreshWorlds) -> Node:
    """Recursively translate ``formula`` relative to ``world`` (the worker).

    ``world`` is the current-world TERM: the free Variable at the top, a bound
    fresh Variable under a modality, or a ``nom_``-Constant under an ``@``-jump.
    """
    # --- atomic: append the world as the last predicate argument ---
    if isinstance(formula, Atom):
        return Atom(formula.predicate, list(formula.args) + [world])

    # --- classical connectives: structural at the same world ---
    if isinstance(formula, Not):
        return Not(_translate(formula.formula, world, fresh))
    if isinstance(formula, And):
        return And(_translate(formula.left, world, fresh),
                   _translate(formula.right, world, fresh))
    if isinstance(formula, Or):
        return Or(_translate(formula.left, world, fresh),
                  _translate(formula.right, world, fresh))
    if isinstance(formula, Xor):
        return Xor(_translate(formula.left, world, fresh),
                   _translate(formula.right, world, fresh))
    if isinstance(formula, Implies):
        return Implies(_translate(formula.left, world, fresh),
                       _translate(formula.right, world, fresh))
    if isinstance(formula, Iff):
        return Iff(_translate(formula.left, world, fresh),
                   _translate(formula.right, world, fresh))

    # --- alethic ---
    if isinstance(formula, Box):
        return _box_like(_R_ALETHIC, world, formula.formula, fresh)
    if isinstance(formula, Diamond):
        return _diamond_like(_R_ALETHIC, world, formula.formula, fresh)

    # --- epistemic / doxastic (both box-like / universal) ---
    if isinstance(formula, Knows):
        return _box_like(_R_KNOWS_PREFIX + _agent_key(formula.agent), world, formula.formula, fresh)
    if isinstance(formula, Believes):
        return _box_like(_R_BELIEVES_PREFIX + _agent_key(formula.agent), world, formula.formula, fresh)

    # --- assertive / bouletic (both box-like, per-agent relations) ---
    if isinstance(formula, Says):
        return _box_like(_R_SAYS_PREFIX + _agent_key(formula.agent), world, formula.formula, fresh)
    if isinstance(formula, Wants):
        return _box_like(_R_WANTS_PREFIX + _agent_key(formula.agent), world, formula.formula, fresh)

    # --- deontic (box/diamond over a deontic accessibility predicate D) ---
    if isinstance(formula, Obligatory):
        return _box_like(_R_DEONTIC, world, formula.formula, fresh)
    if isinstance(formula, Permitted):
        return _diamond_like(_R_DEONTIC, world, formula.formula, fresh)

    # --- temporal (box/diamond over an assumed accessibility predicate) ---
    if isinstance(formula, Always):
        return _box_like(_R_TEMPORAL, world, formula.formula, fresh)
    if isinstance(formula, Eventually):
        return _diamond_like(_R_TEMPORAL, world, formula.formula, fresh)
    if isinstance(formula, Next):
        return _box_like(_R_NEXT, world, formula.formula, fresh)

    # --- past tense (box/diamond over the CONVERSE temporal/next predicate) ---
    if isinstance(formula, Historically):
        return _box_converse(_R_TEMPORAL, world, formula.formula, fresh)
    if isinstance(formula, Once):
        return _diamond_converse(_R_TEMPORAL, world, formula.formula, fresh)
    if isinstance(formula, Previous):
        return _box_converse(_R_NEXT, world, formula.formula, fresh)

    # --- hybrid: a nominal is a world-equality; @ re-anchors the world term ---
    if isinstance(formula, Nominal):
        return Atom("=", [world, Constant(_NOM_PREFIX + formula.name)])
    if isinstance(formula, At):
        return _translate(formula.formula,
                          Constant(_NOM_PREFIX + formula.nominal.name), fresh)

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
        "unicode_fol_kit.fol.qml (qml_translate / qml_is_valid, the FO shallow "
        "embedding with explicit constant/varying/increasing/decreasing domain "
        "regimes)."
    )


def _check_nominal_collision(formula: Node) -> None:
    """Raise if a user constant/function name collides with a nominal world constant.

    Each nominal ``i`` (a ``Nominal`` or the label of an ``At``) translates to the
    reserved world constant ``nom_i``. If the formula independently contains a
    user ``Constant`` or ``Function`` named ``nom_i``, the first-order image would
    conflate the two terms and Z3's equality reasoning could report a genuinely
    invalid formula as valid — a hole in the "``True`` is always a proof"
    guarantee. The parser cannot build such a name (``NAME`` / ``CONSTANT`` tokens
    carry no underscores outside the ``c_`` prefix), so this only guards hand-built
    ASTs; it fails fast, exactly like a dangling nominal assignment.
    """
    nominal_names, user_names = set(), set()
    for node in formula.walk():
        if isinstance(node, Nominal):
            nominal_names.add(node.name)
        elif isinstance(node, At):
            nominal_names.add(node.nominal.name)
        elif isinstance(node, (Constant, Function)):
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


def standard_translation(formula: Node, world: str = "w") -> Node:
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

    Raises:
        NotImplementedError: on ``Until`` (not first-order definable), any
            object-level quantifier (first-order modal logic is out of scope for
            v1), a Łukasiewicz node, or a lambda node.
    """
    _check_nominal_collision(formula)
    return _translate(formula, Variable(world), _FreshWorlds(reserved=world))


# =========================
# Hybrid validity via the standard translation + the Z3 oracle
# =========================

# Frame classes hybrid_is_valid understands, as conditions on the ALETHIC
# accessibility predicate R (the other modal families keep their minimal K
# reading — no axioms are asserted for Rk_a / Rb_a / T / N / D here). The
# table is the shared registry (unicode_fol_kit.fol.frames), so this route
# understands the same systems as every other one; conditions with no
# first-order form are refused by name.
_HYBRID_FRAMES = _SHARED_FRAMES


def _frame_axioms(frame: str) -> List[Node]:
    """Return the first-order frame axioms over ``R`` for a named frame class.

    ``frame`` is any system in the shared registry
    (:mod:`unicode_fol_kit.fol.frames`) or a Scott–Lemmon spec like
    ``"G(1,1,1,1)"``. The axioms are closed formulas over their own bound
    variables, so they cannot capture anything in a translated formula. A
    system needing a condition with no first-order frame condition (GL,
    S4.1, Grz) is refused by name — this route is first-order.
    """
    try:
        conds = resolve_frame(frame)
    except ValueError as exc:
        raise ValueError(f"hybrid_is_valid: {exc}") from None
    return [unguarded_frame_axiom(cond, _R_ALETHIC, prefix="_hw")
            for cond in conds]


def hybrid_is_valid(formula: Node, frame: str = "K", timeout: int = 10000) -> bool:
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
    name-exactly-one-world semantics). ``frame`` is one of ``K`` / ``T`` /
    ``S4`` / ``S5`` and constrains the ALETHIC relation only.

    Soundness/completeness: first-order validity is only semi-decidable in
    general, so ``is_valid`` may time out (returning False) on hard instances —
    but hybrid logic H(@) over K is DECIDABLE, and the ST images of H(@)
    formulas (two-variable-like, tiny) are well within Z3's reach in practice;
    the frame-axiom variants used here (T/S4/S5) behave the same on these
    inputs. ``True`` is always a real proof; treat ``False`` as
    "not proven valid" (for these small hybrid instances: a genuine
    countermodel).

    The ↓ binder (which makes hybrid validity undecidable) has no node type in
    this kit — deliberately out of scope.
    """
    from ..atp.z3_models import is_valid  # local import (as in fol.qml): keeps fol importable without z3
    w = Variable("w")
    closed = Quantifier(_FORALL, w, standard_translation(formula, world="w"))
    hyp = None
    for axiom in _frame_axioms(frame):
        hyp = axiom if hyp is None else And(hyp, axiom)
    goal = closed if hyp is None else Implies(hyp, closed)
    return is_valid(goal, timeout=timeout)
