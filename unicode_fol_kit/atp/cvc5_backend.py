"""cvc5 as a second, independent SMT decision procedure for classical FOL.

cvc5 (BSD-3, https://cvc5.github.io) is a full SMT solver with its own
quantifier-instantiation engine (E-matching, enumerative and syntax-guided
instantiation, finite model finding), independent of and often complementary
to Z3's. This module wires it in as a :class:`~unicode_fol_kit.atp.protocol
.ProverBackend` (:class:`Cvc5Backend`, registry name ``"cvc5"``) using
exactly the same classical-FOL fragment Z3 decides in
:class:`unicode_fol_kit.atp.protocol.Z3Backend`: whatever ``Node.to_z3()``
can translate (uninterpreted sort + equality, no arithmetic — see
``fol/_fol_nodes.py``); substructural nodes (linear logic, Lambek calculus)
reject with ``NotImplementedError`` from ``to_z3()`` itself and are reported
UNKNOWN/``"unsupported"`` here, never guessed at.

Translation route — SMT-LIB2 text, not the pythonic term API
--------------------------------------------------------------
cvc5's Python API (1.3.x) builds terms through its own :class:`cvc5.Solver`
/ ``TermManager``, which do not accept Z3 expressions. Re-walking every kit
``Node`` a second time against cvc5's term constructors would duplicate the
entire ``to_z3`` translation and risk it drifting out of sync. Instead this
backend reuses ``to_z3()`` as already trusted by :class:`Z3Backend`, hands
the resulting Z3 expression to a throwaway ``z3.Solver`` for canonical
SMT-LIB2 serialisation (``Solver.to_smt2()`` — sorts, functions and the goal
all print correctly, including quantifiers), and replays that text into
cvc5 via ``cvc5.InputParser``. Each parsed command is invoked on the cvc5
solver immediately (the parser resolves later symbols against earlier
declarations, so streaming invocation is required — buffering all commands
before invoking any breaks the sort/symbol lookups); the ``(check-sat)``
command in the text is skipped and ``Solver.checkSat()`` is called directly
so a genuine :class:`cvc5.Result` (not a string) drives the verdict.

Validity is asked as an UNSAT question, mirroring Z3Backend: ``unsat`` on
``¬((⋀ premises) → φ)`` proves the entailment; ``sat`` produces a genuine
countermodel (a best-effort variable/function assignment read back off the
cvc5 model — one term at a time, so a model cvc5 cannot print for some
symbol does not blank out the whole witness); ``unknown`` is honestly
UNKNOWN, with ``reason="timeout"`` iff cvc5's own explanation says the time
budget (``tlimit``, set from the ``timeout`` argument, milliseconds) was the
cause, else ``"incomplete"`` (quantified UF is undecidable in general; cvc5
gave up without exhausting time or hitting a bound it can name).

Optional dependency: this backend needs ``pip install cvc5`` (extra
``unicode-fol-kit[cvc5]``). :meth:`Cvc5Backend.available` is pure discovery
(``importlib.util.find_spec``, no import) so probing it never pays the
binding's load cost; ``cvc5`` itself is imported lazily inside ``decide()``.
"""

import importlib.util
import time
from typing import Sequence

from ..fol.nodes import Node, And, Implies
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["Cvc5Backend"]


def _implication(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ φ`` into the single formula ``(∧ premises) → φ``.

    Reimplemented locally (rather than imported from
    :mod:`unicode_fol_kit.atp.protocol`) because the helper there is a
    private, unexported symbol — this module only imports protocol's public
    contract (:class:`ProverBackend`, :class:`Verdict`, the status
    constants).
    """
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


def _timed(fn):
    """Run ``fn()`` returning ``(result, seconds)``."""
    start = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - start


class Cvc5Backend(ProverBackend):
    """Classical FOL/MSFOL via cvc5 — tri-state, with a model on refutation.

    Structurally the same contract as ``Z3Backend``: an entailment
    ``premises ⊨ formula`` is decided by asking whether the negated goal is
    UNSAT. ``proved`` and ``refuted`` are both fully trustworthy (cvc5's
    ``unsat``/``sat`` are sound and, on the quantifier-free fragment,
    complete); ``unknown`` only ever means cvc5's own instantiation search
    did not close the goal — never a silent downgrade of a real answer.

    Registered automatically: ``atp/protocol.py`` imports and registers this
    backend at the bottom of its own module, and its ``default_chain("fol")``
    inserts ``"cvc5"`` directly after ``"z3"`` whenever :meth:`available`
    is true — so on a machine with the optional ``cvc5`` extra installed, a
    plain ``prove()`` call runs cvc5 with zero caller action (see
    ``default_chain``'s docstring for why that one member is
    availability-dependent). This module itself never touches the registry.
    """

    name = "cvc5"
    logics = frozenset({"fol"})
    external = False   # pip package (optional extra), not a spawned binary

    def available(self) -> bool:
        """Pure discovery: is the ``cvc5`` package importable? (No import.)"""
        return importlib.util.find_spec("cvc5") is not None

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` and return a :class:`Verdict`.

        Args:
            formula: the goal.
            premises: entailment premises (``⊨ formula`` when empty).
            timeout: milliseconds; forwarded to cvc5's ``tlimit`` option
                (``0``/negative disables the limit, matching cvc5's own
                "unlimited" default).
            **options: ``logic`` overrides the SMT-LIB logic string handed
                to cvc5 (default ``"ALL"`` — safe for any classical FOL/MSFOL
                fragment ``to_z3`` produces, since it is always a single
                uninterpreted sort with equality and uninterpreted
                functions/predicates, never arithmetic); ``random_seed``
                overrides cvc5's search seed (default ``42``, for
                reproducible verdicts across runs).

        Returns:
            A :class:`Verdict` with ``status`` in
            ``{"proved", "refuted", "unknown", "error"}``. Never raises for
            an in-contract ``Node`` — an unsupported fragment (``to_z3``
            raising ``NotImplementedError``, e.g. linear-logic/Lambek nodes)
            comes back UNKNOWN/``"unsupported"``; any failure in the
            SMT-LIB2 round trip through cvc5 itself comes back
            ERROR/``"infra"`` rather than propagating.
        """
        goal = _implication(formula, premises)
        try:
            z3_goal = goal.to_z3()
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))

        logic = options.pop("logic", "ALL")
        random_seed = options.pop("random_seed", 42)

        try:
            (kind, payload), elapsed = _timed(lambda: self._run(z3_goal, timeout, logic, random_seed))
        except Exception as exc:   # noqa: BLE001 - cvc5/z3 raise plain RuntimeError/etc.
            return Verdict(ERROR, self.name, reason="infra",
                           detail=f"{type(exc).__name__}: {exc}")

        if kind == "unsat":
            return Verdict(PROVED, self.name, wall_time=elapsed)
        if kind == "sat":
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "cvc5_model", "assignment": payload})
        # kind == "unknown"
        return Verdict(UNKNOWN, self.name, reason=payload["reason"], wall_time=elapsed,
                       detail=payload["detail"])

    @staticmethod
    def _run(z3_goal, timeout: int, logic: str, random_seed: int):
        """Serialise ``¬z3_goal`` to SMT-LIB2 via Z3 and decide it with cvc5.

        Returns ``("unsat", None)``, ``("sat", assignment_dict)``, or
        ``("unknown", {"reason": ..., "detail": ...})``.
        """
        import cvc5
        from z3 import Solver as Z3Solver, Not as _ZNot

        z3_solver = Z3Solver()
        z3_solver.add(_ZNot(z3_goal))
        smt2_text = z3_solver.to_smt2()

        solver = cvc5.Solver()
        solver.setLogic(logic)
        solver.setOption("produce-models", "true")
        solver.setOption("seed", str(random_seed))
        if timeout and timeout > 0:
            solver.setOption("tlimit", str(timeout))

        parser = cvc5.InputParser(solver)
        symbol_manager = parser.getSymbolManager()
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt2_text, "cvc5_backend")

        while True:
            command = parser.nextCommand()
            if command.isNull():
                break
            # The (check-sat) command in the replayed text is skipped so we
            # get a real cvc5.Result from checkSat() below, not its stringified
            # form from Command.invoke().
            if command.getCommandName() == "check-sat":
                continue
            command.invoke(solver, symbol_manager)

        result = solver.checkSat()

        if result.isUnsat():
            return "unsat", None
        if result.isSat():
            assignment = {}
            for term in symbol_manager.getDeclaredTerms():
                try:
                    assignment[str(term)] = str(solver.getValue(term))
                except Exception:   # noqa: BLE001 - best-effort witness, one symbol must not blank out the rest
                    continue
            return "sat", assignment

        explanation = result.getUnknownExplanation()
        reason = "timeout" if explanation == cvc5.UnknownExplanation.TIMEOUT else "incomplete"
        return "unknown", {"reason": reason, "detail": str(explanation)}
