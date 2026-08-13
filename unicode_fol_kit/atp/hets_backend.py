"""HETS (the Heterogeneous Tool Set) as an opt-in prover backend.

:class:`HetsBackend` (registry name ``"hets"``) decides classical FOL and
MSFOL entailment by exporting the problem to CASL
(:mod:`unicode_fol_kit.fol.casl_export` — premises become axioms, the goal a
``%implied`` conjecture), uploading it to a running ``hets-server`` REST
instance (:mod:`unicode_fol_kit.hets`), and mapping the per-goal result back
onto the kit's :class:`~unicode_fol_kit.atp.protocol.Verdict`:

===========  ==========  =====================================================
Hets result  Verdict     Notes
===========  ==========  =====================================================
``Proved``     PROVED    ``detail`` carries reasoner + comorphism provenance
``Disproved``  REFUTED   any reasoner may report it (live-verified: the
                         default SPASS route disproves simple non-theorems
                         too); ``darwin-non-fd`` is the DEDICATED finite
                         model finder for when the others stay Open
``Open``       UNKNOWN   ``reason="incomplete"`` — NEVER mapped to refuted
                         (this image's eprover/Vampire wrappers are broken
                         and always report Open; see ``hets/docker.py``)
===========  ==========  =====================================================

What this buys: the Hets reasoner stable (SPASS, the darwins, MathServe
brokered provers, …) behind one backend, each answer stamped with the
comorphism Hets actually used (e.g. ``CASL2TPTP_FOF`` for SPASS,
``CASL2SoftFOL`` for darwin) — and native many-sorted CASL, so kit MSFOL
problems go through WITHOUT the single-sort collapse every TPTP route needs.

Cost model and chain policy: a Docker container start is minutes-expensive
(image pull even more so), exactly like the Isabelle route — so this backend
is NEVER part of any default chain and ``decide()`` NEVER starts a container
itself. It only talks to an already-running server found by
:func:`unicode_fol_kit.hets.discover_hets_url` (``$UFK_HETS_URL``, then
``localhost:8000``); nothing reachable raises ``BackendUnavailable`` with
the start-it-yourself instructions, never a silent skip. Callers who want
managed lifecycle wrap their session in
:class:`unicode_fol_kit.hets.HetsContainer`.

``decide()`` options (all keyword, via ``**options``): ``reasoner`` (Hets
prover identifier, default ``"SPASS"`` — the one verified reliable in the
official image; ``"darwin-non-fd"`` is the dedicated finite model finder
for disproof when other reasoners stay Open), ``translation`` (a comorphism
name from ``HetsClient.translations``, default: let Hets choose), ``url``
(skip discovery and use this server). CAVEAT on ``url``: the chain
orchestration in :func:`~unicode_fol_kit.atp.protocol.run_backend` gates on
``available()`` BEFORE ``decide()`` ever sees options, and ``available()``
can only probe ``$UFK_HETS_URL``/localhost — so for a server on a
non-default address, set ``$UFK_HETS_URL`` (visible to both) rather than
passing ``url=`` through ``api.prove``; ``url=`` works for DIRECT
``decide()`` calls.

:meth:`HetsBackend.check_consistency` is the extra non-protocol route over
``POST /consistency-check``: it asks whether the PREMISES have a model at
all. It deliberately returns a plain dict (``consistent`` True/False/None +
provenance), not a :class:`Verdict` — Verdict's status axis answers
"entailed?", and overloading PROVED to mean "consistent" would corrupt
every consumer that treats PROVED as "goal follows".
"""

import time
from typing import Sequence

from ..fol.nodes import Node
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["HetsBackend"]

#: The reasoner used when the caller does not choose one. SPASS is the
#: verified-working prover of the official image (translation CASL2TPTP_FOF);
#: eprover and Vampire are broken there (always Open) — see hets/docker.py.
_DEFAULT_REASONER = "SPASS"

_SPEC_NAME = "KitProblem"


def _prover_id(goal: dict):
    """The reasoner identifier out of a normalized goal dict.

    ``used_prover`` arrives as ``{"identifier": …, "name": …}`` from the
    server; fall back to the raw value (or None) if the shape ever changes.
    """
    prover = goal.get("used_prover")
    if isinstance(prover, dict):
        return prover.get("identifier", prover.get("name"))
    return prover


class HetsBackend(ProverBackend):
    """CASL export + hets-server REST prove, results as kit Verdicts."""

    name = "hets"
    logics = frozenset({"fol"})
    external = True                  # needs Docker (or a remote hets-server)

    def available(self) -> bool:
        """True iff a hets-server answers right now (no container start)."""
        from ..hets import hets_available

        return hets_available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..fol.casl_export import to_casl_spec
        from ..hets import HetsClient, discover_hets_url

        reasoner = options.pop("reasoner", _DEFAULT_REASONER)
        translation = options.pop("translation", None)
        url = options.pop("url", None)

        try:
            spec = to_casl_spec(list(premises), conjectures=[formula],
                                spec_name=_SPEC_NAME)
        except (ValueError, NotImplementedError) as exc:
            # Outside the CASL FOL/MSFOL fragment (modal node, sort
            # conflict, free variable, …): honestly unsupported, never a
            # silent mistranslation.
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           detail=f"{type(exc).__name__}: {exc}")

        if url is None:
            url, _ = discover_hets_url()   # raises BackendUnavailable

        # Hets takes its budget in whole seconds; the HTTP timeout must
        # outlast it (upload + translation + prover startup).
        time_limit = max(1, timeout // 1000)
        client = HetsClient(url, timeout=float(time_limit + 30))

        try:
            start = time.perf_counter()
            iri = client.upload(spec, "kit_problem.casl")
            goals = client.prove(iri, _SPEC_NAME, reasoner=reasoner,
                                 translation=translation,
                                 time_limit=time_limit)
            elapsed = time.perf_counter() - start
        except RuntimeError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           detail=f"{type(exc).__name__}: {exc}")

        if len(goals) != 1:
            # Exactly one %implied conjecture was emitted, so anything else
            # means the server answered a different question than asked.
            return Verdict(ERROR, self.name, reason="infra",
                           detail=f"hets returned {len(goals)} goal results "
                                  "for a single-conjecture spec")

        goal = goals[0]
        provenance = (f"reasoner={_prover_id(goal)}, "
                      f"translation={goal.get('used_translation')}")
        result = (goal.get("result") or "").strip()

        if result == "Proved":
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           detail=provenance)
        if result == "Disproved":
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           detail=provenance)
        # "Open" and anything unrecognised: not settled. Open is NOT a
        # refutation (and in this image often just a broken wrapper).
        tail = (goal.get("prover_output") or "").strip()[-200:]
        return Verdict(UNKNOWN, self.name, reason="incomplete",
                       wall_time=elapsed,
                       detail=f"{provenance}, result={result or 'absent'}"
                              + (f", output tail: {tail}" if tail else ""))

    def check_consistency(self, premises: Sequence[Node],
                          timeout: int = 10000, **options) -> dict:
        """Ask ``POST /consistency-check``: do the premises have a model?

        Returns ``{"consistent": True | False | None, "result": <verbatim>,
        "reasoner": …, "translation": …, "wall_time": …}`` — ``None`` when
        the checker did not settle it. Raises ``BackendUnavailable`` when no
        server is reachable, ``ValueError``/``NotImplementedError`` when
        the premises leave the CASL fragment, and ``RuntimeError`` when the
        server itself fails mid-flight (HTTP error, ``*** Error`` body,
        malformed JSON — ``HetsClient``'s contract, passed through): unlike
        ``decide`` there is no Verdict envelope to absorb ANY of these, so
        every failure raises rather than being half-mapped.
        """
        from ..fol.casl_export import to_casl_spec
        from ..hets import HetsClient, discover_hets_url

        reasoner = options.pop("reasoner", "darwin-non-fd")
        translation = options.pop("translation", None)
        url = options.pop("url", None)

        spec = to_casl_spec(list(premises), spec_name=_SPEC_NAME)
        if url is None:
            url, _ = discover_hets_url()
        time_limit = max(1, timeout // 1000)
        client = HetsClient(url, timeout=float(time_limit + 30))

        start = time.perf_counter()
        iri = client.upload(spec, "kit_consistency.casl")
        goals = client.consistency_check(iri, _SPEC_NAME, reasoner=reasoner,
                                         time_limit=time_limit)
        elapsed = time.perf_counter() - start

        result = (goals[0].get("result") or "").strip() if goals else ""
        consistent = {"Consistent": True, "Inconsistent": False}.get(result)
        first = goals[0] if goals else {}
        return {"consistent": consistent, "result": result,
                "reasoner": _prover_id(first),
                "translation": first.get("used_translation"),
                "wall_time": elapsed}
