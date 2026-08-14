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
    * detail: short free-text note (method that closed it, bound that was
      hit, tried-backends summary, …).
    * agreement: backend names that reported the SAME status, filled by the
      portfolio layer; a single-backend verdict lists just its own.
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


# ---------------------------------------------------------------------------
# Internal backends: the kit's own calculi and semantic searches
# ---------------------------------------------------------------------------

class Z3Backend(ProverBackend):
    """Classical FOL/MSFOL via Z3 — tri-state, with a model on refutation."""

    name = "z3"
    logics = frozenset({"fol"})
    external = False                 # z3-solver is a hard dependency

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from z3 import Solver, Not as _ZNot, sat, unsat

        goal = _implication(formula, premises)
        try:
            z3_goal = goal.to_z3()
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))

        def run():
            solver = Solver()
            solver.set("timeout", timeout)
            solver.set("random_seed", 42)
            solver.add(_ZNot(z3_goal))
            res = solver.check()
            return res, solver

        (res, solver), elapsed = _timed(run)
        if res == unsat:
            return Verdict(PROVED, self.name, wall_time=elapsed)
        if res == sat:
            model = solver.model()
            assignment = {str(d.name()): str(model[d]) for d in model.decls()}
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
                                  "tableau rule — use the qml or isabelle backend")
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
            verdict, elapsed = _timed(lambda: isabelle_decide_fol(goal, **options))

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

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .prover9_entailment import check_logical_entailment

        path = options.pop("prover9_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "prover9: no binary found (set $UFK_PROVER9 or put 'prover9' on PATH)")
        try:
            proved, elapsed = _timed(
                lambda: check_logical_entailment(list(premises), formula, path))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra", detail=str(exc))
        if proved:
            return Verdict(PROVED, self.name, wall_time=elapsed)
        return Verdict(UNKNOWN, self.name, reason="incomplete", wall_time=elapsed,
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

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        import os
        from .vampire_entailment import check_entailment_vampire_detailed

        path = options.pop("vampire_path", None) or self._binary()
        if path is None:
            raise BackendUnavailable(
                "vampire: no binary found (set $UFK_VAMPIRE or put 'vampire' on PATH)")
        use_wsl = options.pop("use_wsl", os.environ.get("UFK_VAMPIRE_WSL") == "1")
        try:
            result, elapsed = _timed(lambda: check_entailment_vampire_detailed(
                list(premises), formula, path,
                timeout=max(1, timeout // 1000), use_wsl=use_wsl))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        except OSError as exc:
            return Verdict(ERROR, self.name, reason="infra", detail=str(exc))
        status, reason, szs = result["status"], result["reason"], result["szs_status"]
        detail = (f"SZS status {szs}" if szs is not None
                  else "no SZS status line in Vampire's output")
        return Verdict(status, self.name, reason=reason, szs_status=szs,
                       wall_time=elapsed,
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
from .cvc5_backend import Cvc5Backend          # noqa: E402
from .eprover_backend import EProverBackend, ZipperpositionBackend  # noqa: E402
from .hets_backend import HetsBackend          # noqa: E402
from .kripke_enum import KripkeEnumBackend     # noqa: E402
from .leo3_backend import Leo3Backend          # noqa: E402
from .nanocop_backend import NanocopBackend    # noqa: E402
from .twee_backend import TweeBackend          # noqa: E402

for _b in (Cvc5Backend(), EProverBackend(), HetsBackend(),
           KripkeEnumBackend(), Leo3Backend(), NanocopBackend(),
           TweeBackend(), ZipperpositionBackend()):
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
_DEFAULT_CHAINS = {
    "fol": ("z3", "tableau", "resolution", "modelfinder"),
    "modal": ("modal-tableau", "kripke-enum", "qml"),
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
