"""Hets comorphisms as dynamic edges in the kit's translation registry.

The kit's :mod:`unicode_fol_kit.comorphism` registry is the OFFLINE core:
native, AST-to-AST edges (modal→fol, ALC→modal-K, …) that work with no
external process. This module adds the ONLINE extension: every comorphism a
running hets-server offers for CASL input (``GET /translations``) becomes a
registered :class:`~unicode_fol_kit.comorphism.Comorphism` edge named
``hets:<Name>`` — e.g. ``hets:CASL2SoftFOL``, or the composed
``hets:CASL2PCFOL:CASL2SoftFOL`` (Hets composes with ``:``).

Edge typing — TEXT to TEXT, deliberately
----------------------------------------
Native kit edges map kit ASTs. The Hets edges map **CASL specification
text** (as produced by :func:`unicode_fol_kit.fol.casl_export.to_casl_spec`)
to the **translated theory text** Hets renders (``GET
/theory?translation=<Name>&format=dol`` — e.g. SoftFOL/DFG syntax for
``CASL2SoftFOL``). The kit has no AST for SoftFOL, THF-as-Hets-prints-it,
etc., and pretending otherwise would mean parsing every target language.
The registry contract explicitly allows this ("the term type is whatever
the source logic's AST is"): for the source label ``"casl"`` that term type
is ``str``.

Edge labels: every edge runs from ``"casl"`` to the UNIQUE target label
``"hets:<Name>"``. Uniqueness is deliberate: deriving shared target labels
by parsing comorphism names (splitting on ``"2"``) would mis-label
``CASL2SoftFOLInduction`` and friends, and identical target labels would
invite BFS compositions through edges that are not actually composable.
Composition on the Hets side is already expressed by Hets itself via the
``:``-composed names in the discovery list.

Lifetime: an edge's ``apply`` closure talks to the server it was discovered
from on every call (fresh upload → ``/theory``). If that server goes away,
``apply`` raises ``RuntimeError`` — re-run :func:`register_hets_comorphisms`
against a live server to refresh. A refresh REPLACES the whole Hets edge
set: edges the new server still offers are re-bound to the new URL, and
edges it no longer offers are UNREGISTERED (via
``ComorphismRegistry.unregister``) — never left behind as stale closures
pointing at the old server (review-hardened).
"""

from typing import List, Optional, Set

from ..comorphism import Comorphism, DEFAULT_REGISTRY, register_comorphism
from .client import HetsClient
from .docker import discover_hets_url

__all__ = ["register_hets_comorphisms", "HETS_EDGE_PREFIX"]

#: Prefix of every dynamically registered Hets edge name/target label.
HETS_EDGE_PREFIX = "hets:"

#: Edge names registered by the LAST register_hets_comorphisms call — the
#: set a refresh diffs against to unregister edges the new server dropped.
_CURRENTLY_REGISTERED: Set[str] = set()

#: Minimal CASL probe used only to make ``GET /translations`` answer for the
#: CASL logic (the endpoint is per-IRI, so SOME CASL file must exist first).
_PROBE_SPEC = """spec TranslationsProbe =
  sort Thing
  pred P : Thing
  . forall x : Thing . P(x)
end
"""


def _make_edge(name: str, url: str, timeout: float) -> Comorphism:
    """One ``casl -> hets:<name>`` edge whose apply calls the live server."""

    def apply(spec_text: str) -> str:
        client = HetsClient(url, timeout=timeout)
        iri = client.upload(spec_text, "kit_translate.casl")
        # /theory with a translation REQUIRES an explicit node (verified
        # live: HTTP 500 "development graph node missing" otherwise), so
        # resolve it from the uploaded file's development graph. One node
        # is the shape to_casl_spec emits; anything else is ambiguous and
        # refused rather than guessed.
        dg_nodes = (client.dg(iri).get("DGraph") or {}).get("DGNode") or []
        names = [n.get("name") for n in dg_nodes]
        if len(names) != 1:
            raise RuntimeError(
                f"hets: comorphism edge {name!r} needs exactly one "
                f"development-graph node to translate, found {names!r} — "
                "translate single-spec CASL text (as to_casl_spec emits).")
        return client.theory(iri, node=names[0], translation=name)

    return Comorphism(
        name=f"{HETS_EDGE_PREFIX}{name}",
        source="casl",
        target=f"{HETS_EDGE_PREFIX}{name}",
        apply=apply,
        lossy=False,
        note=(f"Hets comorphism {name} on a running hets-server ({url}); "
              "input: CASL spec text (to_casl_spec), output: translated "
              "theory text as Hets renders it (format=dol)."),
    )


def register_hets_comorphisms(*, url: Optional[str] = None,
                              timeout: float = 60.0) -> List[str]:
    """Discover a hets-server and register its CASL comorphisms as edges.

    ``url`` skips discovery (else ``$UFK_HETS_URL`` → ``localhost:8000``,
    raising ``BackendUnavailable`` when nothing answers — never a silent
    no-op). Returns the registered edge names, sorted. Idempotent AND
    complete: re-registration rebinds every edge the new server offers
    (``replace=True``) and UNREGISTERS every previously-registered Hets
    edge the new server does not offer — the registry's Hets edge set
    always mirrors exactly one server.
    """
    global _CURRENTLY_REGISTERED
    if url is None:
        url, _ = discover_hets_url()
    client = HetsClient(url, timeout=timeout)
    iri = client.upload(_PROBE_SPEC, "kit_translations_probe.casl")
    names = client.translations(iri)

    registered = []
    for name in sorted(set(names)):
        register_comorphism(_make_edge(name, url, timeout), replace=True)
        registered.append(f"{HETS_EDGE_PREFIX}{name}")
    for stale in _CURRENTLY_REGISTERED - set(registered):
        DEFAULT_REGISTRY.unregister(stale)
    _CURRENTLY_REGISTERED = set(registered)
    return registered
