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

**A typed reading that differs from the kit's is refused.** The CASL export is a
typed text: it infers the sort of every position (an unannotated constant, or the
value of a function, is declared at the sort of the position it is used in) and its
sorts are disjoint types, while the kit has ONE universe, sorts that are subsets of
it, and constants and function values that are in a sort only when a formula says
so. :class:`HetsBackend` decides, so for a problem on which the two readings differ
it answers ``UNKNOWN`` / ``"unsupported"`` with the reason in ``detail`` (the
checks are those of :func:`~unicode_fol_kit.atp.tptp_tff.check_typed_reading`, shared
with the TF0 and NXF writers) instead of a verdict about another problem; the
fof route (``backends=["vampire"], tff=False`` and the like) asks the kit's question
for those. The export itself (``to_casl_spec``) keeps writing the typed reading.
The sort the export gives every unsorted position is ``Thing``, or ``Thing1``, ``Thing2``, ...
when the problem has a sort spelled like it: a user sort of the default sort's name would
be one sort with it.

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
(skip discovery and use this server). The gate in
:func:`~unicode_fol_kit.atp.protocol.run_backend` asks
:meth:`HetsBackend.available_for` with the options of the call, so a call that
names ``url=`` is answered for THAT server (``GET /version`` on it), not for
``$UFK_HETS_URL`` / localhost, which are only probed when the call names no
``url=``.

:meth:`HetsBackend.check_consistency` is the extra non-protocol route over
``POST /consistency-check``: it asks whether the PREMISES have a model at
all. It deliberately returns a plain dict (``consistent`` True/False/None +
provenance), not a :class:`Verdict` — Verdict's status axis answers
"entailed?", and overloading PROVED to mean "consistent" would corrupt
every consumer that treats PROVED as "goal follows".
"""

import time
from typing import Dict, Optional, Sequence

from ..fol.nodes import Node
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["HetsBackend"]

#: The reasoner used when the caller does not choose one. SPASS is the
#: verified-working prover of the official image (translation CASL2TPTP_FOF);
#: eprover and Vampire are broken there (always Open) — see hets/docker.py.
_DEFAULT_REASONER = "SPASS"

_SPEC_NAME = "KitProblem"


def _default_sort_for(formulas: Sequence[Node]) -> str:
    """The sort the CASL export gives every unsorted position: ``Thing``, or the first of
    ``Thing1``, ``Thing2``, ... that no sort of ``formulas`` is spelled like. A user sort of
    the default sort's name would be one sort with it (the export refuses that), and the
    kit's reading of an unsorted position is the whole universe, not a sort of the user's."""
    taken = {n.sort for f in formulas for n in f.walk() if isinstance(getattr(n, "sort", None), str)}
    candidate, i = "Thing", 0
    while candidate in taken:
        i += 1
        candidate = f"Thing{i}"
    return candidate

# ---------------------------------------------------------------------------
# Solver-version provenance (K1). HETS is an HTTP server, not a spawned
# binary, so the analogue of atp.protocol._binary_version's subprocess memo
# is one GET /version per discovered base_url, memoized process-wide via
# the already-existing but (until now) unused HetsClient.version().
# ---------------------------------------------------------------------------

_VERSION_CACHE: Dict[str, Optional[str]] = {}


def _hets_version(client, url: str) -> Optional[str]:
    """``client.version()`` (``GET /version``), memoized per ``url`` for the
    life of this process — every call after the first for the same
    ``base_url`` returns the cached string (or cached ``None``) without a
    second HTTP round trip. A failure degrades to ``None`` rather than
    raising — this is best-effort provenance, never grounds to turn a sound
    decide() result into an ERROR verdict, so this catches broadly: a real
    ``HetsClient.version()`` only ever raises ``RuntimeError`` (server
    dropped between the availability check and this call, a malformed
    response — see ``hets.client``'s own contract), but ``client`` here is
    whatever :meth:`HetsBackend.decide`/:meth:`HetsBackend.solver_version`
    constructed (or, in a test double that stands in for the whole
    ``HetsClient`` surface but has not modelled this one extra method,
    might not even implement ``version()`` at all — an ``AttributeError``
    must degrade exactly like a ``RuntimeError`` does, not propagate and
    turn a working ``decide()`` call into a crash over a provenance nicety).
    """
    if url in _VERSION_CACHE:
        return _VERSION_CACHE[url]
    try:
        version: Optional[str] = client.version()
    except Exception:   # noqa: BLE001 - best-effort provenance, must not sink a sound verdict
        version = None
    _VERSION_CACHE[url] = version
    return version


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

    def available_for(self, options: dict) -> bool:
        """Whether the server :meth:`decide` will talk to answers: the one named by
        ``url=`` when the call names one (``decide`` then skips discovery), else
        :meth:`available`. Never starts a container."""
        url = options.get("url")
        if url is None:
            return self.available()
        from ..hets.docker import _probe_health

        return _probe_health(url)

    def solver_version(self) -> Optional[str]:
        """The reachable server's ``GET /version`` banner, via
        :meth:`~unicode_fol_kit.hets.client.HetsClient.version` — memoized
        per discovered ``base_url`` for the life of the process (see
        :func:`_hets_version`). ``None`` when no server is currently
        reachable (the same "never guess" discipline as :meth:`available`),
        so callers such as
        :func:`~unicode_fol_kit.eval.batch.batch_decide`'s cache key can
        call this unconditionally, with no prior availability check.
        """
        from ..hets import HetsClient, discover_hets_url
        from .protocol import BackendUnavailable

        try:
            url, _container = discover_hets_url()
        except BackendUnavailable:
            return None
        return _hets_version(HetsClient(url), url)

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..fol.casl_export import to_casl_spec
        from ..hets import HetsClient, discover_hets_url
        from .tptp_tff import check_typed_reading

        reasoner = options.pop("reasoner", _DEFAULT_REASONER)
        translation = options.pop("translation", None)
        url = options.pop("url", None)

        # Solver-version provenance (K1): resolve it up front ONLY when the
        # caller passed an explicit `url=` override — they already opted
        # into contacting THAT specific server (see the module docstring's
        # `url=` CAVEAT), so looking its version up before the CASL-fragment
        # check below adds no network touch beyond what was already asked
        # for, and even an out-of-fragment formula's UNKNOWN/"unsupported"
        # verdict then carries it. Without an explicit `url=`, this stays
        # None here: resolving it would mean running discover_hets_url()'s
        # own network health probe for a formula that will never reach a
        # prover, which test_out_of_fragment_is_unsupported_before_any_network
        # (tests/test_hets_backend.py, unowned) deliberately forbids —
        # discovery must never run before the fragment check for the
        # default-discovery path (see that test's own docstring). In that
        # path solver_version is instead resolved below, right after
        # discover_hets_url() succeeds.
        solver_version = _hets_version(HetsClient(url), url) if url is not None else None

        default_sort = _default_sort_for(list(premises) + [formula])
        try:
            spec = to_casl_spec(list(premises), conjectures=[formula],
                                spec_name=_SPEC_NAME, default_sort=default_sort)
            # The export is a typed text: it gives an unannotated constant or a
            # function value the sort of the position it is used at, and its sorts
            # are disjoint types. A decision must answer the kit's question, so a
            # problem for which that reading differs is refused (see
            # check_typed_reading), not answered about something else.
            check_typed_reading(list(premises) + [formula], writer="hets",
                                unsorted_type=default_sort)
        except (ValueError, NotImplementedError) as exc:
            # Outside the CASL FOL/MSFOL fragment (modal node, sort
            # conflict, free variable, …), or a typed reading that differs from
            # the kit's: honestly unsupported, never a silent mistranslation.
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=solver_version,
                           detail=f"{type(exc).__name__}: {exc}")

        if url is None:
            url, _ = discover_hets_url()   # raises BackendUnavailable
            # Memoized per base_url (see _hets_version) — resolved only now
            # (not above) because discovery itself must not run before the
            # fragment check just above.
            solver_version = _hets_version(HetsClient(url), url)

        # Hets takes its budget in whole seconds; the HTTP timeout must
        # outlast it (upload + translation + prover startup).
        time_limit = max(1, timeout // 1000)
        client = HetsClient(url, timeout=float(time_limit + 30))
        # Memoized per base_url (see _hets_version) — the first decide() (or
        # solver_version()) call for this server pays one GET /version, every
        # later one for the same url is free (including the lookup above,
        # under either path: this is the SAME cache, keyed by url).

        try:
            start = time.perf_counter()
            iri = client.upload(spec, "kit_problem.casl")
            goals = client.prove(iri, _SPEC_NAME, reasoner=reasoner,
                                 translation=translation,
                                 time_limit=time_limit)
            elapsed = time.perf_counter() - start
        except RuntimeError as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=f"{type(exc).__name__}: {exc}")

        if len(goals) != 1:
            # Exactly one %implied conjecture was emitted, so anything else
            # means the server answered a different question than asked.
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=f"hets returned {len(goals)} goal results "
                                  "for a single-conjecture spec")

        goal = goals[0]
        provenance = (f"reasoner={_prover_id(goal)}, "
                      f"translation={goal.get('used_translation')}")
        result = (goal.get("result") or "").strip()

        if result == "Proved":
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           solver_version=solver_version, detail=provenance)
        if result == "Disproved":
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           solver_version=solver_version, detail=provenance)
        # "Open" and anything unrecognised: not settled. Open is NOT a
        # refutation (and in this image often just a broken wrapper).
        tail = (goal.get("prover_output") or "").strip()[-200:]
        return Verdict(UNKNOWN, self.name, reason="incomplete",
                       wall_time=elapsed, solver_version=solver_version,
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
        from .tptp_tff import check_typed_reading

        reasoner = options.pop("reasoner", "darwin-non-fd")
        translation = options.pop("translation", None)
        url = options.pop("url", None)

        default_sort = _default_sort_for(list(premises))
        spec = to_casl_spec(list(premises), spec_name=_SPEC_NAME, default_sort=default_sort)
        # Same refusal as decide(): a consistency answer about a typed reading that
        # differs from the kit's is an answer about another problem.
        check_typed_reading(list(premises), writer="hets", unsorted_type=default_sort)
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
