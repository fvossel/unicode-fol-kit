"""A persistent, push/pop Z3 session for many goals against one premise set.

Every OTHER Z3 route in this kit (:mod:`unicode_fol_kit.atp.z3_models`,
:class:`unicode_fol_kit.atp.protocol.Z3Backend`) builds a brand-new
``z3.Solver()`` per call: correct, but wasteful when the SAME premise set is
checked against many different goals in a row — the real workload of
``eval.datasets.fracas``/``prontoqa``/``proverqa`` (a paired verdict/negated
``api.prove()`` call per example, same premises each time) and
``eval.datasets.proofwriter``'s ``atom_oracle`` loop (many single-atom goals
against one fixed theory). :class:`IncrementalSession` keeps ONE ``z3.Solver``
alive across those calls and uses Z3's native push/pop scope stack so the
premise set only has to be re-asserted when it actually changes.

**Not a decision route.** This is a standalone utility, deliberately NOT a
:class:`~unicode_fol_kit.atp.protocol.ProverBackend` and NOT registered or
reachable through :func:`~unicode_fol_kit.api.prove`'s backend chain — it
answers a narrower question (repeated queries against a mutable-by-push/pop
premise stack) that the uniform one-shot ``decide(formula, premises)``
contract does not express. Wiring a caller like ``atom_oracle`` to use this
instead of repeated stateless ``api.prove()`` calls is a reasonable follow-up,
kept out of this module on purpose.

**LIFO only.** Z3's ``Solver.push()``/``pop()`` is a stack: you can only
retract the MOST RECENTLY asserted premise, never an arbitrary earlier one
while keeping the rest — see :meth:`IncrementalSession.retract`. Arbitrary
(non-LIFO) premise editing needs Z3's assumption-literal pattern
(``solver.add(Implies(a_i, premise_i)); solver.check(a_1, ..., a_n)``)
instead of push/pop; that is a different API and out of scope here.

**Many-sorted (MSFOL) soundness.** Exactly like :mod:`z3_models` and
:class:`~unicode_fol_kit.atp.protocol.Z3Backend` (see either module's
docstring, and the classical-reasoning guide's many-sorted section):
``Node.to_z3()`` relativises a sorted quantifier/constant/count to plain
classical FOL but never asserts that a sort's universe is non-empty — MSFOL,
by convention, never gives a sort an empty one. :meth:`IncrementalSession.decide`
closes that gap the same way ``Z3Backend.decide`` does: at EVERY call it
recomputes ``nonempty_sort_axioms(goal, *premises)`` over the goal and the
CURRENT premise set (base premises plus whatever :meth:`assert_premise` has
added and :meth:`retract` has not yet undone) and asserts them, unnegated,
inside that same call's own push/pop scope — never folded into ``to_z3()``
itself (polarity-blind, shared with every other caller), and never asserted
on a scope :meth:`retract` could later pop away with an unrelated premise:
each ``decide()`` call adds and removes its own copy, so the axioms are
always exactly the ones the CURRENT premise set and goal need, no more and
no less — the same set :class:`Z3Backend` would compute from scratch for an
equivalent one-shot call, so the two always agree.
"""

import time
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol._msfl_nodes import nonempty_sort_axioms
from ..fol.nodes import Node
from .protocol import PROVED, REFUTED, UNKNOWN, Verdict

__all__ = ["IncrementalSession"]

#: The backend tag on every Verdict this session returns — distinct from the
#: stateless ``"z3"`` backend name (:class:`~unicode_fol_kit.atp.protocol
#: .Z3Backend`) so logs/caches never conflate a stateful-session answer with
#: a fresh-Solver-per-call one, even though both use Z3 underneath.
_BACKEND_NAME = "z3-incremental"


def _model_assignment(model) -> Dict[str, str]:
    """Read a satisfying ``z3.ModelRef`` back into a ``{name: value}`` dict.

    Same shape as :func:`unicode_fol_kit.atp.z3_models.get_model`'s return
    value. Unlike :class:`~unicode_fol_kit.atp.protocol.Z3Backend`'s own
    model reader, no tracking-tag filtering is needed here: this session
    never uses ``assert_and_track`` (see the module docstring — it has no
    unsat-core proof to build), so no ``"goal"``/``"p<i>"`` Bool declaration
    is ever present in ``model.decls()`` to begin with.
    """
    return {str(d.name()): str(model[d]) for d in model.decls()}


class IncrementalSession:
    """One persistent ``z3.Solver`` for many goals against a growing/shrinking
    premise set, using Z3's native push/pop scope stack.

    Construct with the starting ("base") premises, grow the set with
    :meth:`assert_premise`, shrink it with :meth:`retract` (LIFO — see the
    module docstring), and decide any number of goals against whatever the
    current premise set is with :meth:`decide`. The base premises supplied to
    the constructor can never be retracted: they are asserted directly on the
    solver, not on a push scope, so there is nothing for :meth:`retract` to
    pop back to below them — calling it with nothing else on the stack raises
    rather than reaching into the base set.

    Timeout and random seed are set ONCE, at construction, exactly like every
    other Z3 route in this kit (:mod:`unicode_fol_kit.atp.z3_models`,
    :class:`~unicode_fol_kit.atp.protocol.Z3Backend`) — ``random_seed`` makes
    a REFUTED verdict's countermodel reproducible across runs of the same
    session, since Z3's model search is otherwise free to return any
    satisfying structure it finds first.
    """

    def __init__(self, premises: Sequence[Node] = (), *,
                timeout: int = 10000, random_seed: int = 42) -> None:
        from z3 import Solver

        self._solver = Solver()
        self._solver.set("timeout", timeout)
        self._solver.set("random_seed", random_seed)
        self._timeout = timeout

        self._base_premises: Tuple[Node, ...] = tuple(premises)
        # Translate every base premise BEFORE touching the solver, so an
        # unsupported fragment (Node.to_z3 raising NotImplementedError, e.g.
        # a substructural node) is refused loudly with no partial state
        # asserted — never approximated, per the kit's fragment-refusal
        # policy. Each premise gets its OWN solver.add call (never folded
        # into one conjunction), so push/pop granularity in assert_premise
        # can later align 1:1 with individual premises the same way.
        z3_base = [p.to_z3() for p in self._base_premises]
        for z3_p in z3_base:
            self._solver.add(z3_p)

        # LIFO stack of premises asserted via assert_premise, each on its
        # own push scope; retract() pops exactly one. Never includes a base
        # premise (those have no push scope of their own — see the class
        # docstring).
        self._stack: List[Node] = []

    @property
    def premises(self) -> Tuple[Node, ...]:
        """The current premise set, base premises first, in assertion order."""
        return self._base_premises + tuple(self._stack)

    @property
    def scope_depth(self) -> int:
        """The underlying solver's current push/pop scope depth.

        Grows by one per live :meth:`assert_premise` call and shrinks by one
        per :meth:`retract`; :meth:`decide` pushes and pops its own
        transient scope internally and always leaves this unchanged before
        vs. after — see :meth:`decide`'s docstring.
        """
        return self._solver.num_scopes()

    def assert_premise(self, p: Node) -> None:
        """Grow the premise set by ``p``, on its own new push scope.

        Translates ``p`` first and only then pushes/asserts, so a fragment
        ``Node.to_z3`` cannot translate (``NotImplementedError``) is refused
        loudly with the scope stack left exactly as it was — never a
        half-pushed scope.
        """
        z3_p = p.to_z3()
        self._solver.push()
        self._solver.add(z3_p)
        self._stack.append(p)

    def retract(self) -> Node:
        """Undo the most recent :meth:`assert_premise` call (LIFO) and
        return the premise that was removed.

        Z3 scopes are a stack: this can only retract the MOST RECENTLY
        asserted premise, never an arbitrary earlier one while keeping the
        rest — see the module docstring for the assumption-literal pattern
        an arbitrary-retraction API would need instead. Retracting past the
        constructor-supplied base premises raises ``ValueError`` — never a
        silent no-op, and never an under/over ``pop()`` of the solver itself.
        """
        if not self._stack:
            raise ValueError(
                "IncrementalSession.retract: nothing left to retract — the "
                "constructor's base premises are never retractable (LIFO "
                "push/pop only reaches premises added by assert_premise)")
        self._solver.pop()
        return self._stack.pop()

    def decide(self, goal: Node, *, timeout: Optional[int] = None) -> Verdict:
        """Decide ``self.premises ⊨ goal`` against the CURRENT premise set.

        Mirrors :meth:`~unicode_fol_kit.atp.protocol.Z3Backend.decide`'s
        body on the session's persistent solver instead of a fresh one:
        pushes a new scope, asserts ``Not(goal)`` plus the many-sorted
        non-emptiness axioms the current premises/goal need (see the module
        docstring), checks, builds the same three-way PROVED/REFUTED/UNKNOWN
        verdict :class:`~unicode_fol_kit.atp.protocol.Z3Backend` would, then
        pops — leaving :attr:`scope_depth` exactly as it was before this
        call, whichever branch is taken (the push/pop live in a ``finally``).

        ``timeout``, if given, overrides the constructor's timeout for THIS
        call only and is restored immediately after — the constructor's
        original value is otherwise untouched by any number of ``decide()``
        calls in between.

        An unsupported fragment (``goal.to_z3()`` or a current premise's
        ``to_z3()`` raising ``NotImplementedError``) is reported as
        ``UNKNOWN``/``"unsupported"``, exactly like ``Z3Backend.decide`` —
        never guessed at, and never leaves a scope pushed.
        """
        from z3 import Not as _z3_not, sat, unsat

        current_premises = self.premises
        try:
            z3_goal = goal.to_z3()
            axioms = [ax.to_z3() for ax in
                     nonempty_sort_axioms(goal, *current_premises)]
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, _BACKEND_NAME, reason="unsupported", detail=str(exc))

        self._solver.push()
        try:
            if timeout is not None:
                self._solver.set("timeout", timeout)
            self._solver.add(_z3_not(z3_goal))
            for axiom in axioms:
                self._solver.add(axiom)

            start = time.perf_counter()
            res = self._solver.check()
            elapsed = time.perf_counter() - start

            if res == unsat:
                return Verdict(PROVED, _BACKEND_NAME, wall_time=elapsed)
            if res == sat:
                assignment = _model_assignment(self._solver.model())
                return Verdict(REFUTED, _BACKEND_NAME, wall_time=elapsed,
                               countermodel={"kind": "z3_model", "assignment": assignment})
            why = self._solver.reason_unknown()
            reason = "timeout" if ("timeout" in why or "cancel" in why) else "incomplete"
            return Verdict(UNKNOWN, _BACKEND_NAME, reason=reason, wall_time=elapsed, detail=why)
        finally:
            self._solver.pop()
            if timeout is not None:
                self._solver.set("timeout", self._timeout)
