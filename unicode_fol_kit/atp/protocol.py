"""Uniform prover protocol: one Verdict type over every decision route.

The kit decides validity/entailment through many routes — its OWN calculi and
semantic model searches (Z3-free tableau, resolution, finite model finder,
modal labelled tableau, the QML embedding) and EXTERNAL provers (Z3, Isabelle,
Prover9, Vampire). Each grew its own return convention (bare bool,
``"valid"/"invalid"/"unknown"`` strings, ``ModalVerdict``/``FolVerdict``).
This module adds the layer a pipeline needs on top, without touching any
existing signature:

* :class:`Verdict` — the one result type: a semantic ``status`` (proved /
  refuted / unknown / error), a ``reason`` axis that distinguishes budget
  exhaustion from honest incompleteness from timeouts, the SZS status string,
  provenance (which backend, how long), and JSON-able witnesses.
* :class:`ProverBackend` — the adapter contract (``available()`` +
  ``decide()``), with the kit's internal calculi and semantic searches as
  first-class backends alongside the external provers.
* a registry (:func:`register_backend`, :func:`get_backend`,
  :func:`available_backends`, :func:`default_chain`) that the ``prove()``
  facade in :mod:`unicode_fol_kit.api` dispatches over.

Error contract: requesting an UNKNOWN backend name raises ``ValueError``;
requesting a known backend whose prerequisites are missing (no binary, no
install) raises :class:`BackendUnavailable` — never a silent skip, because a
silently skipped backend makes evaluation results irreproducible.

The status/reason split is deliberate: ``status`` answers "what do we know
about the formula" (only four values, easy to branch on), ``reason`` answers
"why do we not know more" (``bound_hit`` ≠ ``timeout`` ≠ ``incomplete`` ≠
``unsupported`` — a benchmark table must not conflate them).
"""

import shutil
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from typing import Dict, Optional, Sequence, Tuple

from ..fol.nodes import Node, And, Implies

__all__ = [
    "PROVED", "REFUTED", "UNKNOWN", "ERROR", "STATUSES",
    "Verdict", "BackendUnavailable", "ProverBackend",
    "register_backend", "get_backend", "available_backends", "default_chain",
    "run_backend",
    "z3_relevant_premises",
]

# ---------------------------------------------------------------------------
# Statuses, reasons, and their SZS image
# ---------------------------------------------------------------------------

PROVED = "proved"      # validity / entailment established
REFUTED = "refuted"    # a genuine countermodel witnesses invalidity
UNKNOWN = "unknown"    # neither, within this backend's budget/strength
ERROR = "error"        # the backend failed for an infrastructure reason
STATUSES = (PROVED, REFUTED, UNKNOWN, ERROR)

# reason values (for UNKNOWN/ERROR): why we do not know more.
#   "timeout"     — a wall-clock budget expired
#   "bound_hit"   — a step/size bound expired (max_steps, max_worlds, …)
#   "incomplete"  — the method is sound but incomplete on this fragment and
#                   gave up honestly (no bound was hit)
#   "unsupported" — the backend has no rule/translation for this fragment
#   "infra"       — subprocess/JVM/syntax failure (ERROR only)

_SZS = {
    (PROVED, None): "Theorem",
    (REFUTED, None): "CounterSatisfiable",
    (UNKNOWN, "timeout"): "Timeout",
    (UNKNOWN, "bound_hit"): "ResourceOut",
    (UNKNOWN, "incomplete"): "GaveUp",
    (UNKNOWN, "unsupported"): "Inappropriate",
    (UNKNOWN, None): "Unknown",
    (ERROR, "infra"): "Error",
    (ERROR, None): "Error",
}


def _szs_for(status: str, reason: Optional[str]) -> str:
    """Return the SZS ontology value for a (status, reason) pair."""
    return _SZS.get((status, reason), _SZS[(status, None)])


# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Verdict:
    """One decision result, whatever route produced it.

    Fields:

    * status: ``"proved"`` / ``"refuted"`` / ``"unknown"`` / ``"error"``.
      Truthiness follows ``status == "proved"``.
    * backend: name of the backend that produced this verdict.
    * logic: the logic the query was decided in (``"fol"``, ``"modal"``, …).
    * reason: the why-not-more axis for UNKNOWN/ERROR (see module docstring);
      ``None`` for definitive verdicts.
    * szs_status: SZS ontology value; derived from (status, reason) unless a
      backend sets it explicitly (e.g. verbatim from a TSTP line).
    * wall_time: seconds spent inside the backend call.
    * countermodel: JSON-able witness for REFUTED (shape is backend-specific
      but always a dict with a ``"kind"`` key), else ``None``.
    * proof: JSON-able proof object where the backend yields one, else None.
      A ``"kind": "z3_unsat_core"`` or ``"kind": "cvc5_alethe"`` proof
      carries an unsat CORE — sound (re-asserting just that subset is still
      unsat) but not necessarily MINIMAL (the underlying solver is free to
      track more than the smallest sufficient subset) — see
      :func:`z3_relevant_premises` for the same caveat on the dedicated
      premise-relevance query.
    * detail: short free-text note (method that closed it, bound that was
      hit, tried-backends summary, …).
    * agreement: backend names that reported the SAME status, filled by the
      portfolio layer; a single-backend verdict lists just its own.
    * relevant_premises: 0-based indices into the caller's ``premises`` that
      a premise-relevance query found necessary for a PROVED verdict (see
      :func:`z3_relevant_premises`, :mod:`atp.tstp`'s ancestor walk, and
      :mod:`atp.eprover_backend`'s ``eprover_relevant_premises``); ``None``
      when nobody computed it (the default) — NOT a claim that every premise
      was needed. Like ``proof``'s unsat core, a reported set is sound but
      not guaranteed minimal.
    * solver_version: the underlying external tool's own version string
      (Vampire's/Prover9's/E's/Zipperposition's ``--version`` banner, the
      reachable HETS server's ``GET /version`` text, the installed ``cvc5``
      package's distribution version), captured once per process per
      backend/binary and reported here unchanged — see
      :meth:`ProverBackend.solver_version` and :func:`_binary_version` for
      the memoization contract. ``None`` for the kit's own internal
      backends (Z3/tableau/resolution/modelfinder/QML/…, which have no
      external tool to version) and for an external backend whose version
      lookup itself failed or found nothing (the tool's PROOF/DISPROOF
      verdict is unaffected either way — a missing version string is never
      grounds to downgrade a sound answer).
    """

    status: str
    backend: str
    logic: str = "fol"
    reason: Optional[str] = None
    szs_status: Optional[str] = None
    wall_time: float = 0.0
    countermodel: Optional[dict] = None
    proof: Optional[dict] = None
    detail: Optional[str] = None
    agreement: Tuple[str, ...] = ()
    relevant_premises: Optional[Tuple[int, ...]] = None
    # New fields go last: positional construction by callers must keep working.
    solver_version: Optional[str] = None

    def __post_init__(self):
        if self.status not in STATUSES:
            raise ValueError(f"Verdict: unknown status {self.status!r} (use one of {STATUSES})")
        if self.szs_status is None:
            object.__setattr__(self, "szs_status", _szs_for(self.status, self.reason))
        if not self.agreement:
            object.__setattr__(self, "agreement", (self.backend,))

    def __bool__(self) -> bool:
        return self.status == PROVED

    @property
    def is_definitive(self) -> bool:
        """True iff the verdict settles the question (proved or refuted)."""
        return self.status in (PROVED, REFUTED)

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (all fields, names as keys)."""
        return {
            "status": self.status,
            "backend": self.backend,
            "logic": self.logic,
            "reason": self.reason,
            "szs_status": self.szs_status,
            "wall_time": self.wall_time,
            "countermodel": self.countermodel,
            "proof": self.proof,
            "detail": self.detail,
            "agreement": list(self.agreement),
            "relevant_premises": (list(self.relevant_premises)
                                  if self.relevant_premises is not None else None),
            "solver_version": self.solver_version,
        }


class BackendUnavailable(RuntimeError):
    """A KNOWN backend was requested but its prerequisites are missing.

    Raised instead of silently skipping, because a pipeline whose backend
    quietly vanished produces irreproducible numbers. The message names the
    backend and what discovery looked for (env var / binary / install).
    """


# ---------------------------------------------------------------------------
# The backend contract
# ---------------------------------------------------------------------------

class ProverBackend(ABC):
    """Adapter contract for one decision route.

    ``name`` is the registry key; ``logics`` the set of logic labels the
    backend accepts (``"fol"``, ``"modal"``). ``available()`` performs
    discovery without side effects. ``decide()`` answers "do ``premises``
    entail ``formula``?" (validity when ``premises`` is empty) and must NEVER
    raise for an in-contract input — undecidable/unsupported fragments come
    back as an UNKNOWN verdict with the honest ``reason``. Extra keyword
    options are forwarded verbatim to the underlying route (``frame=``,
    ``systems=``, ``max_steps=``, …), so the adapters stay thin and nothing
    of the existing signatures is hidden.

    For the modal backends, a non-empty ``premises`` is the LOCAL consequence
    ``⊨ (∧ premises) → φ`` — the standard finite-premise reading; global
    consequence is out of scope here.
    """

    name: str = ""
    logics: frozenset = frozenset({"fol"})
    external: bool = False           # needs a binary/install outside this venv

    @abstractmethod
    def available(self) -> bool:
        """Return whether this backend can run right now (pure discovery)."""

    @abstractmethod
    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` and return a :class:`Verdict`."""

    def solver_version(self) -> Optional[str]:
        """The underlying external tool's own version string, or ``None``.

        Default (this base implementation): always ``None`` — the kit's own
        internal calculi and semantic searches (Z3 aside: its Python BINDING
        version is not "the solver's version" in the sense this method
        means, and :class:`Z3Backend` does not override this) have no
        external tool to version. An external backend overrides this with a
        lookup that is PROCESS-LOCAL MEMOIZED (see :func:`_binary_version`
        for the subprocess-spawning backends, and each override's own
        docstring for the HETS/cvc5 routes) — probed at most once per
        distinct binary/server/package for the life of this process, so
        neither this method nor :meth:`decide` (which populates
        ``Verdict.solver_version`` from it) ever pays a second lookup.
        Never raises and never changes any verdict's status/reason — this
        is provenance only, queried both from ``decide()`` and, independently,
        from :func:`unicode_fol_kit.eval.batch.batch_decide`'s cache key (so
        a solver upgrade invalidates stale cache entries).
        """
        return None


# ---------------------------------------------------------------------------
# Solver-version provenance: a process-local memoized ``--version`` lookup,
# shared by every subprocess-spawning backend below (Vampire, Prover9, and —
# via atp.eprover_backend's own import of this function — E/Zipperposition).
# HETS (an HTTP server, not a spawned binary) and cvc5 (a pip binding, not a
# spawned binary) have their own analogous, separately-memoized routes in
# their own modules (hets_backend.py, cvc5_backend.py) — see
# ProverBackend.solver_version's docstring.
# ---------------------------------------------------------------------------

#: (command, use_wsl) -> the tool's version string, or None on a failed
#: lookup — a MISS is cached too (never retried), matching item 5's "never
#: spawn a subprocess per decide() call after the first" requirement.
#: Deliberately separate from atp.eprover_backend._DISCOVERY_CACHE: discovery
#: (does a binary exist at all?) and version (what does it print?) answer
#: different questions and can fail independently — collapsing them into one
#: cache would make a version-lookup failure look like the binary vanished,
#: or vice versa.
_VERSION_CACHE: Dict[Tuple[str, bool], Optional[str]] = {}


def _binary_version(command: str, use_wsl: bool,
                    args: Tuple[str, ...] = ("--version",)) -> Optional[str]:
    """Process-local memoized ``<command> <args>`` version lookup.

    Spawns the subprocess (through ``wsl.exe`` when ``use_wsl``) at most ONCE
    per ``(command, use_wsl)`` pair for the life of this process; every
    later call for the same pair — including one that failed — returns the
    cached result without spawning again. On a ZERO exit, returns the first
    non-blank line of stdout, falling back to stderr (some tools print
    version banners there), stripped. ``None`` on any failure: binary
    missing, a timeout, WSL unreachable, a non-zero exit — an unrecognized
    flag commonly prints an error/usage line to stdout or stderr on a
    non-zero exit, and accepting that text as a version string would be
    worse than reporting no provenance at all (mirrors the returncode check
    :func:`unicode_fol_kit.atp.eprover_backend._discover` already applies to
    its own subprocess probe) — OR the banner not being valid text under
    ``subprocess.run(..., text=True)``'s decoding (``UnicodeError``, e.g. a
    tool that writes a non-UTF-8 locale-encoded byte in its ``--version``
    output): decoding happens INSIDE ``subprocess.run`` here, so this is
    caught exactly like any other failure to read the banner, never left to
    propagate as a bare ``ValueError`` out of a caller's ``decide()``. This
    is best-effort provenance, so nothing here ever raises or turns into an
    ERROR verdict.
    """
    key = (command, use_wsl)
    if key in _VERSION_CACHE:
        return _VERSION_CACHE[key]

    import subprocess

    result: Optional[str] = None
    try:
        cmd = ["wsl.exe", command, *args] if use_wsl else [command, *args]
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
        if proc.returncode == 0:
            text = (proc.stdout or "").strip() or (proc.stderr or "").strip()
            if text:
                result = text.splitlines()[0].strip()
    except (OSError, subprocess.TimeoutExpired, UnicodeError):
        result = None
    _VERSION_CACHE[key] = result
    return result


def _implication(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ φ`` into the single formula ``(∧ premises) → φ``."""
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


def _z3_nonempty_sort_axioms(formula: Node, premises: Sequence[Node]) -> list:
    """``nonempty_sort_axioms(formula, *premises)``, each translated via ``to_z3()``.

    Shared by :class:`Z3Backend` and :func:`z3_relevant_premises` so both
    decide the exact same many-sorted entailment — see
    :func:`_z3_track_and_check`'s ``z3_nonempty_sort_axioms`` parameter for
    why these are added UNTRACKED rather than as more ``p<i>``-tagged
    premises. Empty for an unsorted query.
    """
    from ..fol._msfl_nodes import nonempty_sort_axioms
    return [axiom.to_z3() for axiom in nonempty_sort_axioms(formula, *premises)]


# ---------------------------------------------------------------------------
# Internal backends: the kit's own calculi and semantic searches
# ---------------------------------------------------------------------------

def _z3_track_and_check(z3_formula, z3_premises: Sequence, timeout: int,
                        z3_nonempty_sort_axioms: Sequence = ()):
    """Run ONE per-call Z3 ``Solver``, tracking every assertion by name.

    Asserts ``Not(z3_formula)`` under the tag ``"goal"`` and each of
    ``z3_premises`` under ``"p<i>"`` (0-based), via ``assert_and_track``,
    with ``unsat_core=True`` set on THIS solver instance only — never
    ``z3.set_param(proof=True)``, which is a process-wide global that would
    change solving behaviour for every other Z3 consumer in the kit
    (semantics evaluators, dl, chem, finite-model, modal/second/third-order
    — anything sharing the module-level ``_SORT``/default context in
    ``fol/_fol_nodes.py``) for the rest of the process.

    ``z3_nonempty_sort_axioms`` (see
    :func:`~unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms`) are added
    with a plain, UNTRACKED ``solver.add`` — they are background MSFOL
    convention (every sort is non-empty), never one of the caller's own
    premises, so they must never gain a ``p<i>`` tag: that would make an
    untranslatable, caller-invisible synthetic sentence show up in
    :class:`Z3Backend`'s ``proof`` unsat core or in
    :func:`z3_relevant_premises`'s reported indices, which are defined purely
    over the CALLER's own ``premises`` list. Empty (the default) for an
    unsorted query, so the solver call is byte-for-byte the same as before
    this parameter existed.

    Built once and shared by :class:`Z3Backend` (C12: a per-verdict
    ``z3_unsat_core`` proof certificate) and :func:`z3_relevant_premises`
    (C11: which premises a PROVED entailment actually needed) so both read
    the exact same assert-and-track call shape rather than drifting apart —
    including, now, the identical non-emptiness axioms, so the two can never
    disagree about whether a many-sorted entailment holds.

    Returns ``(result, solver)`` — ``result`` is Z3's own
    ``sat``/``unsat``/``unknown``; on ``unsat``, ``solver.unsat_core()``
    holds the tracked-name subset Z3 actually used. That subset is SOUND
    (re-asserting just it is still unsat) but not necessarily MINIMAL (Z3's
    core extraction is not obliged to find the smallest one) — callers that
    need "used" language should say "relevant"/"a sufficient subset", never
    "the minimal set".
    """
    from z3 import Solver, Not as _ZNot, Bool

    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    solver.set(unsat_core=True)
    for axiom in z3_nonempty_sort_axioms:
        solver.add(axiom)
    for i, p in enumerate(z3_premises):
        solver.assert_and_track(p, Bool(f"p{i}"))
    solver.assert_and_track(_ZNot(z3_formula), Bool("goal"))
    return solver.check(), solver


def _z3_model_assignment(model, n_premises: int) -> Dict[str, str]:
    """Read a satisfying ``z3.ModelRef`` back into a ``{name: value}`` dict.

    ``assert_and_track``'s own tracking booleans (``"goal"``, ``"p0"``, …
    — see :func:`_z3_track_and_check`) are themselves 0-ary Bool-sorted Z3
    declarations, so they show up in ``model.decls()`` right alongside the
    formula's real symbols and would otherwise leak into a REFUTED verdict's
    witness as spurious extra keys. They are excluded here by declaration
    shape, not by hoping for no name clash: a kit-level PREDICATE can never
    collide (the parser only ever emits an uppercase-initial name for one —
    see ``fol._identifiers``), and a kit-level CONSTANT named ``"goal"`` or
    ``"p0"`` is never Bool-sorted (constants live in the uninterpreted sort
    ``S`` — see ``Z3Env.get_symbol``), so only a genuine tracking tag is ever
    both same-named AND Bool-sorted-arity-0 — the exact combination checked
    below.
    """
    from z3 import BoolSort

    tag_names = {"goal", *(f"p{i}" for i in range(n_premises))}
    assignment = {}
    for d in model.decls():
        name = str(d.name())
        if name in tag_names and d.arity() == 0 and d.range() == BoolSort():
            continue
        assignment[name] = str(model[d])
    return assignment


def z3_relevant_premises(formula: Node, premises: Sequence[Node] = (),
                         timeout: int = 10000) -> Optional[Tuple[int, ...]]:
    """Which of ``premises`` did Z3 actually need to prove ``⊨ formula``?

    Runs the same :func:`_z3_track_and_check` per-``Solver`` assert-and-track
    call :class:`Z3Backend` uses for its own ``proof`` certificate — including
    the same many-sorted non-emptiness axioms when ``formula``/``premises``
    use a sort (:func:`_z3_nonempty_sort_axioms`), so this always agrees with
    :class:`Z3Backend` about whether the entailment holds — but reports only
    the premise side of the core, as 0-based indices into ``premises`` (never
    including the ``"goal"`` tag itself — the negated conclusion is always
    "needed" trivially, so it carries no information about which PREMISES
    were relevant; the non-emptiness axioms are untracked, so they can never
    appear in the core either — see :func:`_z3_track_and_check`).

    Args:
        formula: the goal.
        premises: candidate premises (same fragment ``Z3Backend``/
            ``Node.to_z3`` decides — uninterpreted sort + equality, no
            arithmetic; substructural nodes are outside it).
        timeout: milliseconds, forwarded to the solver exactly as
            ``Z3Backend.decide`` forwards its own ``timeout``.

    Returns:
        A sorted tuple of 0-based premise indices, or ``None`` when there is
        nothing sound to report: the entailment does not hold (Z3 finds it
        SAT or times out UNKNOWN — there is no "used premises" answer for a
        non-theorem), or the fragment is unsupported (``to_z3`` raises
        ``NotImplementedError`` on ``formula`` or any premise). ``None`` is
        the honest "don't know" answer here, never a guessed subset.

        The returned set is SOUND but not necessarily MINIMAL — see
        :func:`_z3_track_and_check`'s docstring; a genuinely redundant
        premise (one that, alone, already suffices) need not appear
        alongside the other route to the same conclusion, but two premises
        that are each independently sufficient are not guaranteed to be
        pruned down to a single one either — only that the returned subset
        itself is enough.
    """
    premises = list(premises)
    try:
        z3_formula = formula.to_z3()
        z3_premises = [p.to_z3() for p in premises]
        z3_nonempty = _z3_nonempty_sort_axioms(formula, premises)
    except NotImplementedError:
        return None

    from z3 import unsat

    res, solver = _z3_track_and_check(z3_formula, z3_premises, timeout, z3_nonempty)
    if res != unsat:
        return None
    core = {str(tag) for tag in solver.unsat_core()}
    indices = sorted(int(tag[1:]) for tag in core
                     if tag != "goal" and tag.startswith("p") and tag[1:].isdigit())
    return tuple(indices)


class Z3Backend(ProverBackend):
    """Classical FOL/MSFOL via Z3 — tri-state, with a model on refutation.

    Many-sorted input: a sort's non-emptiness (the MSFOL convention — see
    the classical-reasoning guide's many-sorted section) is asserted as an
    extra, untracked, UNNEGATED premise alongside ``premises`` — see
    :func:`_z3_nonempty_sort_axioms` and :func:`_z3_track_and_check` — never
    folded inside ``Node.to_z3()`` itself, which stays polarity-blind. This
    is what makes a REFUTED verdict's countermodel always a legal MSFOL
    structure (no sort empty) instead of exploiting an empty-sort loophole
    ``semantics.modelfinder`` never considers.
    """

    name = "z3"
    logics = frozenset({"fol"})
    external = False                 # z3-solver is a hard dependency

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from z3 import sat, unsat

        premises = list(premises)
        try:
            z3_formula = formula.to_z3()
            z3_premises = [p.to_z3() for p in premises]
            z3_nonempty = _z3_nonempty_sort_axioms(formula, premises)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))

        (res, solver), elapsed = _timed(
            lambda: _z3_track_and_check(z3_formula, z3_premises, timeout, z3_nonempty))
        if res == unsat:
            # A tracked-name unsat core, per _z3_track_and_check's docstring:
            # sound (re-asserting just these is still unsat, see the C12
            # soundness self-check test) but not necessarily minimal.
            core = sorted(str(tag) for tag in solver.unsat_core())
            proof = {"kind": "z3_unsat_core", "core": core}
            return Verdict(PROVED, self.name, wall_time=elapsed, proof=proof)
        if res == sat:
            assignment = _z3_model_assignment(solver.model(), len(z3_premises))
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "z3_model", "assignment": assignment})
        why = solver.reason_unknown()
        reason = "timeout" if ("timeout" in why or "cancel" in why) else "incomplete"
        return Verdict(UNKNOWN, self.name, reason=reason, wall_time=elapsed, detail=why)


class TableauBackend(ProverBackend):
    """The kit's own classical analytic tableau (Z3-free).

    Complete and decidable propositionally; on first-order inputs a
    non-closure is only "no closed tableau within the bounds" → bound_hit.
    """

    name = "tableau"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        # The detailed route records a TableauProof alongside the same
        # search (recording never changes the verdict — regression-pinned
        # in test_tableau_check.py), so a PROVED Verdict can carry the
        # independently checkable proof dict.
        from .tableau import prove_tableau_detailed

        try:
            proof, elapsed = _timed(
                lambda: prove_tableau_detailed(list(premises), formula,
                                               **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if proof is not None:
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           proof=proof.to_dict())
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="no closed tableau within max_steps/max_terms")


class ResolutionBackend(ProverBackend):
    """The kit's own resolution prover (given-clause saturation).

    The underlying bool API cannot distinguish saturation from a hit step
    bound, so a False is reported as UNKNOWN/bound_hit — never as REFUTED.
    """

    name = "resolution"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .resolution import prove as resolution_prove

        try:
            proved, elapsed = _timed(
                lambda: resolution_prove(list(premises), formula, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, wall_time=elapsed)
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="not refuted within max_steps (saturation not distinguished)")


class ModelFinderBackend(ProverBackend):
    """The kit's finite model finder — a refutation-only semantic backend.

    Finding a finite structure that satisfies the premises but not the
    conclusion REFUTES the entailment; exhausting the size bound proves
    nothing (FOL has no finite model property) → bound_hit.
    """

    name = "modelfinder"
    logics = frozenset({"fol"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..semantics.modelfinder import find_countermodel

        try:
            structure, elapsed = _timed(
                lambda: find_countermodel(list(premises), formula, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if structure is not None:
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel={"kind": "finite_structure", "repr": repr(structure)})
        return Verdict(UNKNOWN, self.name, reason="bound_hit", wall_time=elapsed,
                       detail="no countermodel up to the size bound")


class ModalTableauBackend(ProverBackend):
    """The kit's labelled modal tableau — tri-state with Kripke witnesses."""

    name = "modal-tableau"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .modal_tableau import modal_decide, modal_countermodel

        goal = _implication(formula, premises)
        try:
            status, elapsed = _timed(lambda: modal_decide(goal, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="modal",
                           reason="unsupported", detail=str(exc))
        if status == "valid":
            return Verdict(PROVED, self.name, logic="modal", wall_time=elapsed)
        if status == "invalid":
            cm = modal_countermodel(goal, **options)
            witness = None
            if cm is not None:
                from .kripke_enum import kripke_model_to_dict
                witness = {"kind": "kripke", "repr": repr(cm),
                           "data": kripke_model_to_dict(cm)}
            return Verdict(REFUTED, self.name, logic="modal", wall_time=elapsed,
                           countermodel=witness)
        # modal_decide answers "unknown" both for an exhausted budget and for
        # the temporal-closure operators it has no rule for (G/F/U/H/O/P/S,
        # classified "unsupported" internally) — tell them apart here so the
        # reason axis stays honest.
        from .modal_tableau import _TEMPORAL_CLOSURE
        if any(isinstance(n, _TEMPORAL_CLOSURE) for n in goal.walk()):
            return Verdict(UNKNOWN, self.name, logic="modal", reason="unsupported",
                           wall_time=elapsed,
                           detail="temporal closure operators (G/F/U/…) have no "
                                  "tableau rule here for the kit's general Kripke "
                                  "frame — for the STANDARD linear-time reading, "
                                  "the 'ltl-tableau' backend (atp.ltl_tableau) is "
                                  "a complete decision procedure and the "
                                  "definitive route; 'qml' and 'isabelle' decide "
                                  "the general (possibly non-linear) frame "
                                  "instead, soundly but not completely")
        return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                       wall_time=elapsed,
                       detail="tableau budget exhausted (max_worlds/max_steps)")


class QmlBackend(ProverBackend):
    """Quantified modal logic via the FO embedding + Z3 — sound, incomplete.

    ``True`` is a proof; ``False`` only means "not proven" (undecidable
    fragment), so it is reported as UNKNOWN/incomplete, never as REFUTED.
    """

    name = "qml"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..fol.qml import qml_is_valid

        goal = _implication(formula, premises)
        try:
            proved, elapsed = _timed(
                lambda: qml_is_valid(goal, timeout=timeout, **options))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="modal",
                           reason="unsupported", detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, logic="modal", wall_time=elapsed)
        return Verdict(UNKNOWN, self.name, logic="modal", reason="incomplete",
                       wall_time=elapsed,
                       detail="Z3 did not close the embedded goal (FO modal logic is undecidable)")


# ---------------------------------------------------------------------------
# External backends
# ---------------------------------------------------------------------------

class IsabelleBackend(ProverBackend):
    """Isabelle/HOL via the kit's runner — the most trusted external route.

    Deliberately NOT in any default chain: one decision spawns a real
    ``isabelle build`` (minutes of wall time), so it runs only when requested
    by name. ``ModalVerdict``/``FolVerdict`` map 1:1 onto :class:`Verdict`
    (their ``infra_error`` becomes reason="infra" detail on UNKNOWN).

    The classical route decides with ``native_equality=True``: ``=`` is HOL
    identity, as in every other backend's semantics. With the embedding's
    uninterpreted ``feq`` a nitpick countermodel is one for FOL *without*
    identity, so ``∀x (x = x)`` came back REFUTED. Passing
    ``native_equality=False`` is refused for that reason. The modal route is
    unaffected: the Kripke evaluator reads ``s = t`` as an ordinary atom.
    """

    name = "isabelle"
    logics = frozenset({"fol", "modal"})
    external = True

    def available(self) -> bool:
        from ..hol.isabelle_runner import isabelle_available
        return isabelle_available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        goal = _implication(formula, premises)
        logic = options.pop("logic", None) or (
            "modal" if _looks_modal(goal) else "fol")

        if logic == "modal":
            from ..hol.isabelle_runner import isabelle_decide_modal
            verdict, elapsed = _timed(lambda: isabelle_decide_modal(goal, **options))
        else:
            from ..hol.isabelle_runner import isabelle_decide_fol
            if not options.pop("native_equality", True):
                raise ValueError(
                    "isabelle backend: native_equality=False would decide FOL without "
                    "identity (uninterpreted feq), so a REFUTED verdict could contradict "
                    "every other backend; call hol.isabelle_runner.isabelle_decide_fol "
                    "directly for that reading.")
            verdict, elapsed = _timed(
                lambda: isabelle_decide_fol(goal, native_equality=True, **options))

        if verdict.status == "valid":
            return Verdict(PROVED, self.name, logic=logic, wall_time=elapsed,
                           detail=verdict.method)
        if verdict.status == "invalid":
            witness = ({"kind": "nitpick" if logic == "fol" else "kripke",
                        "repr": verdict.countermodel}
                       if verdict.countermodel else None)
            return Verdict(REFUTED, self.name, logic=logic, wall_time=elapsed,
                           countermodel=witness)
        reason = "infra" if verdict.infra_error else "incomplete"
        return Verdict(UNKNOWN, self.name, logic=logic, reason=reason,
                       wall_time=elapsed, detail=verdict.infra_error)


class Prover9Backend(ProverBackend):
    """Prover9 via subprocess. Discovery: $UFK_PROVER9, then PATH."""

    name = "prover9"
    logics = frozenset({"fol"})
    external = True

    @staticmethod
    def _binary() -> Optional[str]:
        import os
        return os.environ.get("UFK_PROVER9") or shutil.which("prover9")

    def available(self) -> bool:
        return self._binary() is not None

    def solver_version(self) -> Optional[str]:
        """Prover9's ``--version`` banner (first line), for whichever binary
        discovery (``$UFK_PROVER9``/PATH) resolves to right now — the same
        default :meth:`available` uses. Memoized per binary for the life of
        the process via :func:`_binary_version`. ``None`` when no binary is
        currently discoverable; a per-call ``prover9_path=`` override is
        reflected in THAT call's own ``Verdict.solver_version`` (see
        :meth:`decide`), not here — see :func:`_binary_version`'s
        module-level docstring section for why this method answers for the
        default binary only.
        """
        path = self._binary()
        if path is None:
            return None
        return _binary_version(path, False)

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .prover9_entailment import check_logical_entailment

        path = options.pop("prover9_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "prover9: no binary found (set $UFK_PROVER9 or put 'prover9' on PATH)")
        solver_version = _binary_version(path, False)
        try:
            proved, elapsed = _timed(
                lambda: check_logical_entailment(list(premises), formula, path))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version, detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           solver_version=solver_version)
        return Verdict(UNKNOWN, self.name, reason="incomplete", wall_time=elapsed,
                       solver_version=solver_version,
                       detail="Prover9 found no proof (its exit does not certify invalidity)")


class VampireBackend(ProverBackend):
    """Vampire via subprocess. Discovery: $UFK_VAMPIRE, then PATH.

    Set ``UFK_VAMPIRE_WSL=1`` when the binary is a Linux build reached
    through WSL on a Windows host.

    Decides through the SZS/TSTP route
    (:func:`~unicode_fol_kit.atp.vampire_entailment.check_entailment_vampire_detailed`):
    the verdict's ``szs_status`` is Vampire's own status line verbatim, a
    ``CounterSatisfiable`` answer becomes an honest REFUTED (Vampire's
    saturation certifies invalidity, though it yields no model structure —
    ``countermodel`` stays ``None``), and a PROVED verdict carries the parsed
    TSTP derivation DAG in ``proof``.
    """

    name = "vampire"
    logics = frozenset({"fol"})
    external = True

    @staticmethod
    def _binary() -> Optional[str]:
        import os
        return os.environ.get("UFK_VAMPIRE") or shutil.which("vampire")

    def available(self) -> bool:
        return self._binary() is not None

    def solver_version(self) -> Optional[str]:
        """Vampire's ``--version`` banner (first line), for whichever binary
        discovery (``$UFK_VAMPIRE``/PATH, ``$UFK_VAMPIRE_WSL``) resolves to
        right now — the same default :meth:`available` uses. Memoized per
        ``(binary, use_wsl)`` for the life of the process via
        :func:`_binary_version`. ``None`` when no binary is currently
        discoverable; a per-call ``vampire_path=``/``use_wsl=`` override is
        reflected in THAT call's own ``Verdict.solver_version`` (see
        :meth:`decide`), not here — see :func:`_binary_version`'s
        module-level docstring section for why this method answers for the
        default binary only.
        """
        import os

        path = self._binary()
        if path is None:
            return None
        use_wsl = os.environ.get("UFK_VAMPIRE_WSL") == "1"
        return _binary_version(path, use_wsl)

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        import os
        from .vampire_entailment import check_entailment_vampire_detailed

        path = options.pop("vampire_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "vampire: no binary found (set $UFK_VAMPIRE or put 'vampire' on PATH)")
        use_wsl = options.pop("use_wsl", os.environ.get("UFK_VAMPIRE_WSL") == "1")
        solver_version = _binary_version(path, use_wsl)
        try:
            result, elapsed = _timed(lambda: check_entailment_vampire_detailed(
                list(premises), formula, path,
                timeout=max(1, timeout // 1000), use_wsl=use_wsl))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version, detail=str(exc))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version, detail=str(exc))
        status, reason, szs = result["status"], result["reason"], result["szs_status"]
        detail = (f"SZS status {szs}" if szs is not None
                  else "no SZS status line in Vampire's output")
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed, solver_version=solver_version,
                       proof=result["derivation"] if status == PROVED else None,
                       detail=detail)


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

def _looks_modal(node: Node) -> bool:
    """Route helper: does the formula contain any modal-family operator?"""
    from .modal_tableau import has_modal
    return has_modal(node)


_REGISTRY: Dict[str, ProverBackend] = {}


def register_backend(backend: ProverBackend) -> None:
    """Register (or replace) a backend under ``backend.name``.

    Third-party code can plug in its own :class:`ProverBackend` here and it
    becomes addressable by every ``prove(backends=[...])`` call.
    """
    if not backend.name:
        raise ValueError("register_backend: backend must set a non-empty name")
    _REGISTRY[backend.name] = backend


for _b in (Z3Backend(), TableauBackend(), ResolutionBackend(),
           ModelFinderBackend(), ModalTableauBackend(), QmlBackend(),
           IsabelleBackend(), Prover9Backend(), VampireBackend()):
    register_backend(_b)

# The remaining stock backends live in their own modules (an optional
# dependency, a heavier search, an external prover family) and import THIS
# module's public contract — so they are pulled in here, after that contract
# is fully defined. A deliberate bottom-of-registration import, not an
# accident: keeping the whole stock registry in one place guarantees that
# `default_chain` and `_REGISTRY` can never disagree about what exists,
# whichever submodule a process imports first.
from .clingo_backend import ClingoBackend      # noqa: E402
from .cvc5_backend import Cvc5Backend          # noqa: E402
from .eprover_backend import EProverBackend, ZipperpositionBackend  # noqa: E402
from .hets_backend import HetsBackend          # noqa: E402
from .kripke_enum import KripkeEnumBackend     # noqa: E402
from .leo3_backend import Leo3Backend          # noqa: E402
from .ltl_tableau import LtlTableauBackend     # noqa: E402
from .minizinc_backend import MinizincBackend  # noqa: E402
from .nanocop_backend import NanocopBackend    # noqa: E402
from .twee_backend import TweeBackend          # noqa: E402
# Five individually-reasoned per-logic adapters (C10) — see logic_backends'
# module docstring for why these are NOT a uniform bulk registration.
from .logic_backends import (                  # noqa: E402
    IntBackend, LambekBackend, IllBackend, RelevantBackend, HybridBackend,
)

for _b in (ClingoBackend(), Cvc5Backend(), EProverBackend(), HetsBackend(),
           KripkeEnumBackend(), Leo3Backend(), LtlTableauBackend(), MinizincBackend(),
           NanocopBackend(), TweeBackend(), ZipperpositionBackend(),
           IntBackend(), LambekBackend(), IllBackend(), RelevantBackend(),
           HybridBackend()):
    register_backend(_b)


def get_backend(name: str) -> ProverBackend:
    """Return the backend registered under ``name`` (ValueError if unknown)."""
    if name not in _REGISTRY:
        raise ValueError(
            f"get_backend: unknown backend {name!r} (registered: {sorted(_REGISTRY)})")
    return _REGISTRY[name]


def available_backends(logic: Optional[str] = None) -> Tuple[str, ...]:
    """Names of the currently-available backends, optionally per logic."""
    names = []
    for name, backend in _REGISTRY.items():
        if logic is not None and logic not in backend.logics:
            continue
        if backend.available():
            names.append(name)
    return tuple(sorted(names))


# Default chains: fast, deterministic, and NEVER silently expensive — the
# external minutes-per-call route (isabelle) must be requested by name.
# "kripke-enum" sits between the tableau and qml on purpose: it is the only
# default-chain member that can REFUTE a temporal-closure formula (the
# tableau reports those unsupported, qml is proof-only), and its bounded
# enumeration settles the refutation side before qml's Z3 call can burn its
# full timeout failing to prove an invalid goal.
#
# The five substructural/non-classical entries (C10) are each a SINGLETON
# chain: every one of these logics currently has exactly one decision route
# in the kit, so there is no actual "portfolio race" to order here (unlike
# "fol"/"modal" above) — see logic_backends' module docstring for why these
# five are individually-reasoned adapters, not a uniform bulk registration.
_DEFAULT_CHAINS = {
    "fol": ("z3", "tableau", "resolution", "modelfinder"),
    "modal": ("modal-tableau", "kripke-enum", "qml"),
    "intuitionistic": ("intuitionistic",),
    "lambek": ("lambek",),
    "ill": ("ill",),
    "relevant": ("relevant",),
    "hybrid": ("hybrid",),
}


def default_chain(logic: str) -> Tuple[str, ...]:
    """The default backend order for ``logic`` (ValueError if unknown).

    The chains are static, with ONE documented availability-dependent member:
    when the optional ``cvc5`` extra is installed
    (``pip install unicode-fol-kit[cvc5]``), the FOL chain gains ``"cvc5"``
    directly after ``"z3"`` — a second, fully independent SMT decision
    procedure whose quantifier instantiation (E-matching/enumerative/CEGQI)
    often closes goals Z3's MBQI leaves UNKNOWN, and vice versa. It cannot be
    an unconditional member: a missing backend in the DEFAULT chain would
    make every plain ``prove()`` call raise :class:`BackendUnavailable` on a
    machine without the extra. Every verdict names the backend that actually
    answered (``backend`` / ``agreement``), so provenance stays exact even
    though the chain adapts to the install.
    """
    if logic not in _DEFAULT_CHAINS:
        raise ValueError(
            f"default_chain: unknown logic {logic!r} (use one of {sorted(_DEFAULT_CHAINS)})")
    chain = _DEFAULT_CHAINS[logic]
    if logic == "fol" and _REGISTRY["cvc5"].available():
        chain = chain[:1] + ("cvc5",) + chain[1:]
    return chain


def run_backend(name: str, formula: Node, premises: Sequence[Node] = (),
                timeout: int = 10000, **options) -> Verdict:
    """Run one backend by name, enforcing the availability contract.

    Raises ``ValueError`` for an unknown name and :class:`BackendUnavailable`
    for a known-but-unavailable one. Any unexpected exception inside the
    backend is converted to an ERROR verdict (reason="infra") so a batch run
    over thousands of formulas records the failure instead of dying.
    """
    backend = get_backend(name)
    if not backend.available():
        raise BackendUnavailable(
            f"{name}: backend is not available on this machine "
            f"(external={backend.external}) — install it or drop it from `backends`.")
    try:
        return backend.decide(formula, premises, timeout=timeout, **options)
    except (ValueError, BackendUnavailable):
        raise                                    # caller errors stay loud
    except Exception as exc:                     # infra failure → recorded, not fatal
        return Verdict(ERROR, name, reason="infra",
                       detail=f"{type(exc).__name__}: {exc}")
