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

**ASCII/legality sanitisation (problem-level seam) — narrower than TPTP's.**
``Node.to_z3()`` hands a symbol's name to Z3's Python API completely raw —
no transliteration, no fold — and that is FINE for Z3 itself: a Z3 symbol
name is an arbitrary Python string, not text that has to satisfy any
lexical grammar. The gap this module has is specifically in the SMT-LIB2
TEXT round trip described above (``Solver.to_smt2()`` -> ``InputParser``):
Z3's own ``to_smt2()`` already pipe-quotes (``|...|``) any name that is not
already a legal SMT-LIB2 ``simple_symbol`` — verified live, a non-ASCII
name such as ``świątek`` round-trips through it correctly ALREADY, with no
help from this module — except for ONE case it gets wrong: a name that is
pure ASCII, made only of ``simple_symbol``-legal characters, but starts
with a DIGIT (``2008SummerOlympics``). SMT-LIB2's grammar requires a
``simple_symbol`` to start with a non-digit, so that name needed quoting
too, but Z3's serialiser does not add it — the resulting ``.smt2`` text
fails to parse (``z3.parse_smt2_string`` raises; reproduced live, and
feeding one such name to this backend segfaults the whole process before
:meth:`Cvc5Backend.decide` ever gets to return an ERROR ``Verdict``, since a
native crash is not a Python exception ``decide()`` can catch). So, unlike
:mod:`atp._tptp_problem` and :mod:`atp.prover9_entailment` (which must fix
BOTH non-ASCII and digit-leading names — Vampire/E/Prover9 have no
automatic quoting of their own), :func:`_sanitize_for_smtlib` only ever
touches a name that is pure ASCII AND digit-leading; every other name,
including every non-ASCII one, is left completely untouched — touching one
would change the export for a name this backend already handles correctly
today, which R1 forbids. The sanitised goal's ``sat`` countermodel is
translated back via :func:`_reverse_map_assignment` before it reaches the
caller, so a caller always sees the ORIGINAL kit-level symbol name, never
the synthesised digit-safe token.
"""

import importlib.util
import time
from dataclasses import dataclass, field
from typing import Dict, Sequence, Tuple

from ..fol.nodes import Atom, Constant, Function, Node, And, Implies
from ._ascii_names import ascii_safe_base, reserve_rendered
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["Cvc5Backend"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring's sanitisation
# section for why this is narrower than atp._tptp_problem's / atp
# .prover9_entailment's (only digit-leading pure-ASCII names are unsafe here;
# everything else, including every non-ASCII name, already round-trips
# correctly through Z3's own SMT-LIB2 serialisation).
# ---------------------------------------------------------------------------

def _is_smtlib_safe(name: str) -> bool:
    if not name:
        return False
    return not (name.isascii() and name[0].isdigit())


def _unquote_smtlib(s: str) -> str:
    """Strip an SMT-LIB2 ``|...|`` quoted-symbol wrapper, if present.

    A quoted symbol has no escape mechanism (the only characters forbidden
    INSIDE one are ``|`` and ``\\``, per the SMT-LIB2 spec), so stripping the
    outer pair is a lossless, exact inverse of the quoting Z3's ``to_smt2()``
    already applies to any name it did not consider a plain ``simple_symbol``
    (see the module docstring) — no unescaping needed, unlike a string
    literal.
    """
    if len(s) >= 2 and s[0] == "|" and s[-1] == "|":
        return s[1:-1]
    return s


@dataclass
class SmtNameMap:
    """The digit-leading-name renamings :func:`_sanitize_for_smtlib` chose
    for one goal — a single FLAT namespace across predicate/function/constant
    names (Z3/SMT-LIB2's uninterpreted-function declarations share one
    symbol space regardless of return sort), built from the same
    :func:`~atp._ascii_names.ascii_safe_base` / :func:`~atp._ascii_names
    .reserve_rendered` primitives :mod:`atp._tptp_problem` and
    :mod:`atp.prover9_entailment` use, with SMT-LIB2's own (much narrower —
    see the module docstring) legality test and no render/fold step (SMT-LIB2
    text is never case-folded, so the rendered form IS the raw token).
    """

    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: list = field(default_factory=list)

    def collect(self, name: str) -> None:
        """First pass: register `name`; an already-legal name is reserved
        immediately (order-independent — see
        :class:`~atp._tptp_problem._Renamer`'s docstring for why collision
        avoidance for a synthesised name must not depend on processing
        order relative to an unrelated already-legal name)."""
        if name in self.mapping or name in self._pending:
            return
        if _is_smtlib_safe(name):
            self.used.add(name)
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        """Second pass: synthesise a token for every queued digit-leading
        name, now that every already-legal name in the goal is reserved."""
        for name in self._pending:
            base = ascii_safe_base(name, "n")
            token = reserve_rendered(base, self.used)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return self.mapping[name]

    def reverse(self) -> Dict[str, str]:
        return {v: k for k, v in self.mapping.items()}


def _sanitize_node_for_smtlib(node: Node, names: SmtNameMap) -> Node:
    """Rebuild ``node`` with every digit-leading symbol name replaced.

    Mirrors :func:`atp._tptp_problem._sanitize_node_for_tptp`'s structural
    recursion; ``=``/``≠`` are excluded from renaming because
    :meth:`~fol.nodes.Atom.to_z3` maps them to Z3's native equality
    operators rather than an uninterpreted predicate — they are never
    identifiers to begin with.
    """
    if isinstance(node, Atom):
        if node.predicate in ("=", "≠"):
            pred = node.predicate
        else:
            pred = names.get(node.predicate)
        return Atom(pred, [_sanitize_node_for_smtlib(a, names) for a in node.args])
    if isinstance(node, Function):
        return Function(names.get(node.name),
                        [_sanitize_node_for_smtlib(a, names) for a in node.args])
    if isinstance(node, Constant):
        return Constant(names.get(node.name))
    return node.map_children(lambda c: _sanitize_node_for_smtlib(c, names))


def _collect_names_for_smtlib(node: Node, names: SmtNameMap) -> None:
    """First pass (see :meth:`SmtNameMap.collect`): register every
    predicate/function/constant name ``node`` uses, without rewriting
    anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in ("=", "≠"):
                names.collect(n.predicate)
        elif isinstance(n, Function):
            names.collect(n.name)
        elif isinstance(n, Constant):
            names.collect(n.name)


def _sanitize_for_smtlib(node: Node) -> Tuple[Node, SmtNameMap]:
    """Sanitise ``node`` (the already-folded ``(∧ premises) → φ`` goal) for
    the SMT-LIB2 round trip. Returns ``(sanitised_node, mapping)`` — the
    two-pass collect-then-finalize split (see :class:`SmtNameMap`, mirroring
    :class:`atp._tptp_problem._Renamer`) means a synthesised digit-safe
    token can never collide with an already-legal name anywhere in
    ``node``, regardless of which one this walk reaches first.
    """
    names = SmtNameMap()
    _collect_names_for_smtlib(node, names)
    names.finalize()
    return _sanitize_node_for_smtlib(node, names), names


def _reverse_map_assignment(assignment: Dict[str, str], reverse: Dict[str, str]) -> Dict[str, str]:
    """Translate a cvc5 ``sat`` model's ``{declared_term_str: value_str}``
    witness back to original kit-level names.

    Every key AND value is first unquoted (:func:`_unquote_smtlib`) — cvc5's
    ``str(term)``/``str(value)`` reproduce whatever quoting the term's own
    declaration used, so a non-ASCII name that Z3 pipe-quoted on export (see
    the module docstring — already correct, never renamed by
    :func:`_sanitize_for_smtlib`) would otherwise reach the caller as
    ``"|świątek|"`` rather than the true original ``"świątek"``. After
    unquoting, a name found in ``reverse`` (a digit-leading name this module
    DID rename) is translated back to its original; anything else — cvc5's
    own fresh model-value tokens (``"(as @S_0 S)"``, ``"(lambda (...) ...)"``,
    ...) included — passes through the unquoted form unchanged, since
    ``reverse.get(..., default)`` falls back to the unquoted string itself.
    """
    return {
        reverse.get(_unquote_smtlib(k), _unquote_smtlib(k)):
            reverse.get(_unquote_smtlib(v), _unquote_smtlib(v))
        for k, v in assignment.items()
    }


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
            ERROR/``"infra"`` rather than propagating. A REFUTED verdict's
            ``countermodel["assignment"]`` names every symbol by its
            ORIGINAL kit-level name — see :func:`_reverse_map_assignment`
            and the module docstring's sanitisation section — never a
            digit-safe synthesised token, and never SMT-LIB2 ``|...|``
            quoting syntax wrapped around a non-ASCII one.
        """
        goal = _implication(formula, premises)
        sanitised_goal, name_map = _sanitize_for_smtlib(goal)
        try:
            z3_goal = sanitised_goal.to_z3()
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
            assignment = _reverse_map_assignment(payload, name_map.reverse())
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "cvc5_model", "assignment": assignment})
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
