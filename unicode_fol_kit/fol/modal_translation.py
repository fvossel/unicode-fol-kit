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
- ``Always φ``     → ``∀w' (T(w, w') → ST(φ, w'))`` (box over a temporal
  accessibility predicate ``T``).
- ``Eventually φ`` → ``∃w' (T(w, w') ∧ ST(φ, w'))`` (diamond over ``T``).
- ``Next φ``       → ``∀w' (N(w, w') → ST(φ, w'))`` (box over a one-step
  predicate ``N``).
- ``Obligatory φ`` → ``∀w' (D(w, w') → ST(φ, w'))`` (box over a deontic
  accessibility predicate ``D``).
- ``Permitted φ``  → ``∃w' (D(w, w') ∧ ST(φ, w'))`` (diamond over ``D``).

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
``"Rb_" + agent`` (doxastic), ``"T"`` (temporal), ``"N"`` (next), ``"D"``
(deontic).
"""

from typing import NoReturn

from .nodes import (
    Node,
    Variable,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
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


def _agent_key(agent: Node) -> str:
    """Agent term's name for the per-agent relation (this propositional translation
    rejects object quantifiers, so the agent is always a ground Constant here)."""
    return getattr(agent, "name", None) or agent.to_unicode_str()
_R_TEMPORAL = "T"
_R_NEXT = "N"
_R_DEONTIC = "D"

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


def _box_like(rel_name: str, world: Variable, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∀w' (rel(world, w') → ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, [world, w2])
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh)))


def _diamond_like(rel_name: str, world: Variable, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∃w' (rel(world, w') ∧ ST(body, w'))`` with a fresh ``w'``."""
    w2 = fresh.next()
    access = Atom(rel_name, [world, w2])
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh)))


def _box_converse(rel_name: str, world: Variable, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∀w' (rel(w', world) → ST(body, w'))`` — a box over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, [w2, world])
    return Quantifier(_FORALL, w2, Implies(access, _translate(body, w2, fresh)))


def _diamond_converse(rel_name: str, world: Variable, body: Node, fresh: _FreshWorlds) -> Node:
    """Build ``∃w' (rel(w', world) ∧ ST(body, w'))`` — a diamond over the CONVERSE relation."""
    w2 = fresh.next()
    access = Atom(rel_name, [w2, world])
    return Quantifier(_EXISTS, w2, And(access, _translate(body, w2, fresh)))


def _translate(formula: Node, world: Variable, fresh: _FreshWorlds) -> Node:
    """Recursively translate ``formula`` relative to ``world`` (the worker)."""
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
        "standard translation here covers the propositional modal fragment only; "
        "quantified (first-order) modal logic with object domains is future work."
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

    Raises:
        NotImplementedError: on ``Until`` (not first-order definable), any
            object-level quantifier (first-order modal logic is out of scope for
            v1), a Łukasiewicz node, or a lambda node.
    """
    return _translate(formula, Variable(world), _FreshWorlds(reserved=world))
