r"""REST binding to a Dockerized HETS (Heterogeneous Tool Set) server.

`HETS <https://github.com/spechub/Hets>`_ is the reference heterogeneous
proof-management system for CASL and its extensions (and, via comorphisms,
many other logics): a development-graph manager over a network of theories
that dispatches proof obligations to external provers (SPASS, darwin,
Vampire, E, ...) through translations/comorphisms it selects. This subpackage
does not reimplement any of that — it is a thin client that lets the rest of
the kit drive a real HETS instance and read back its verdicts.

Architecture: process/network separation, not in-process linking
--------------------------------------------------------------------
HETS is GPL-licensed Haskell with a build realistically only reproducible via
its official Docker image. Two integration routes exist:

* **In-process bindings** — the ``hets``/``spechub`` Python API some
  installs expose links this process directly against the GPL Haskell
  library via its GHC-built shared objects, and is only buildable on Linux
  with a working GHC toolchain. That is wrong for this kit on two independent
  axes: it would pull a GPL dependency into an MIT-licensed process, and it
  is not available on this kit's primary development platform (Windows) at
  all. Documented here as the alternative that was considered and rejected,
  not silently omitted.
* **REST against Docker** — the route this subpackage takes.
  :mod:`~unicode_logic_kit.hets.docker` starts (or discovers) a
  ``spechub2/hets:latest`` container running HETS's own bundled HTTP server;
  :mod:`~unicode_logic_kit.hets.client` speaks plain HTTP/JSON to it via
  stdlib ``urllib`` (no ``requests`` dependency, matching this kit's other
  external-tool adapters). This process and the HETS process share nothing
  but a TCP socket — no linking, no shared address space, no GPL code ever
  imported into this Python process. The boundary is enforced structurally,
  not by a license header: :class:`~unicode_logic_kit.hets.client.HetsClient`
  cannot reach HETS internals any way other than the documented REST API.

This mirrors the kit-wide convention for external provers that are
subprocess-spawned rather than linked (``atp.prover9_entailment``,
``atp.vampire_entailment``, ``hol.isabelle_runner``) — HETS just uses a
network boundary instead of a process boundary, because that is how its
official distribution ships (a server, not a CLI batch tool).

Modules
-------
* :mod:`~unicode_logic_kit.hets.docker` — :class:`~unicode_logic_kit.hets.docker.HetsContainer`
  (start/stop/health-poll one container) and
  :func:`~unicode_logic_kit.hets.docker.discover_hets_url` (the precedence
  ``$UFK_HETS_URL`` -> localhost -> optionally auto-start, never a silent
  guess — raises :class:`~unicode_logic_kit.atp.protocol.BackendUnavailable`
  with an actionable message otherwise). Also documents which reasoners in
  the shipped image actually work.
* :mod:`~unicode_logic_kit.hets.client` — :class:`~unicode_logic_kit.hets.client.HetsClient`,
  the REST binding itself (upload, development-graph inspection, prover /
  translation listing, theory rendering/translation, prove,
  consistency-check).
* :mod:`~unicode_logic_kit.hets.bridge` — the server's CASL comorphisms as
  dynamic ``hets:<Name>`` edges in the kit's translation registry
  (:func:`~unicode_logic_kit.hets.bridge.register_hets_comorphisms`).
* :mod:`~unicode_logic_kit.hets.dol` — DOL library EMISSION
  (:func:`~unicode_logic_kit.hets.dol.to_dol_library`): multiple named CASL
  specs, ``then``-extension structure and ``%implied`` goals in one
  ``library`` document a HETS server turns into a multi-node development
  graph (no DOL *parsing* — same emission-only cut as the rest of the
  CASL route; the importer for single basic specs is
  :func:`unicode_logic_kit.fol.casl_import.parse_casl_spec`).
* :mod:`~unicode_logic_kit.hets.owl_backend` — a second, independent external
  OWL 2 DL reasoner (FaCT++ via the server's ``Fact`` prover identifier),
  over the ALCHQ + I + O fragment; mirrors
  :mod:`~unicode_logic_kit.dl.owl_reasoner`'s function-per-namesake shape,
  opt-in and never in a default chain.
* :mod:`~unicode_logic_kit.hets.haskell_json` —
  :func:`~unicode_logic_kit.hets.haskell_json.repair_haskell_json`, which
  recovers the Haskell ``show`` escapes HETS 0.108.0 leaks into its JSON
  (``"Verdi\226\128\153s Requiem"`` for ``"Verdi’s Requiem"``). Without it
  ``GET /dg`` is unreadable for any library with one non-ASCII annotation,
  and with it the real 8.3 MB OEO graph loads. Applied by
  :meth:`~unicode_logic_kit.hets.client.HetsClient.dg` only on the failure
  path, so a body ``json`` already accepts is never touched.
* :mod:`~unicode_logic_kit.hets.symbols` — the join between HETS' mangled TPTP
  symbols and the OWL entities they came from
  (:func:`~unicode_logic_kit.hets.symbols.hets_symbol_table`), plus the axioms
  a translation silently dropped
  (:func:`~unicode_logic_kit.hets.symbols.untranslated_axioms`). Pure
  functions over a ``/dg`` dict and a TPTP string: no network, no Docker.
* :mod:`~unicode_logic_kit.hets.owl_cli` —
  :func:`~unicode_logic_kit.hets.owl_cli.owl_to_tptp`, the COMMAND-LINE route
  (``docker exec`` into a running container). It exists for exactly one
  reason: ``hets-server``'s lossy ``-Y`` switch, which translates an
  ontology whose sublogic a comorphism does not cover and which has no REST
  equivalent. It runs the non-lossy translation first so the loss is always
  reported, never silent.

The TPTP a HETS ``GET /theory`` returns is NOT a TPTP problem — HETS
prefixes it with a DOL ``logic TPTP.FOF`` line and a CASL ``%{ ... }%``
signature block. :func:`~unicode_logic_kit.hets.client.strip_hets_theory_header`
splits the two (and
:meth:`~unicode_logic_kit.hets.client.HetsClient.theory_tptp` does it for you);
:func:`unicode_logic_kit.fol.tptp_input.parse_tptp` refuses the unstripped text
BY NAME and points here, rather than learning a comment syntax that is not
TPTP's.

Kit formulas reach HETS through the Verdict layer:
:class:`unicode_logic_kit.atp.hets_backend.HetsBackend` (registry name
``"hets"``, never in a default chain) exports FOL/MSFOL problems to CASL
via :mod:`unicode_logic_kit.fol.casl_export` and maps the per-goal results
back onto the kit's :class:`~unicode_logic_kit.atp.protocol.Verdict`.
"""

from .bridge import HETS_EDGE_PREFIX, register_hets_comorphisms
from .client import (
    HetsClient,
    HetsNoTranslationsError,
    HetsSublogicError,
    strip_hets_theory_header,
)
from .docker import HETS_IMAGE, HetsContainer, discover_hets_url, hets_available
from .haskell_json import (
    HaskellJsonRepair,
    HaskellJsonRepairError,
    repair_haskell_json,
)
from .owl_cli import (
    HetsOwlNormalizationError,
    OwlTptpResult,
    SublogicMismatch,
    owl_to_tptp,
)
from .symbols import (
    HetsSymbol,
    HetsSymbolCollisionError,
    HetsSymbolTable,
    UntranslatedAxiom,
    hets_prefixes,
    hets_symbol_table,
    untranslated_axioms,
)
from .dol import DolSpec, to_dol_library, to_dol_library_from_modal, sanitize_modal_identifiers
from .owl_backend import (
    hets_owl_available,
    external_concept_satisfiable, external_concept_unsatisfiable,
    external_subsumes, external_equivalent,
    external_abox_consistent, external_instance_check, external_instance_retrieval,
    external_realize, external_realize_all,
    HetsOwlError,
)

__all__ = [
    "HetsClient",
    "HetsNoTranslationsError", "HetsSublogicError", "strip_hets_theory_header",
    "HaskellJsonRepair", "HaskellJsonRepairError", "repair_haskell_json",
    "owl_to_tptp", "OwlTptpResult", "SublogicMismatch",
    "HetsOwlNormalizationError",
    "hets_symbol_table", "HetsSymbolTable", "HetsSymbol",
    "HetsSymbolCollisionError",
    "untranslated_axioms", "UntranslatedAxiom", "hets_prefixes",
    "HETS_IMAGE", "HetsContainer", "discover_hets_url", "hets_available",
    "HETS_EDGE_PREFIX", "register_hets_comorphisms",
    "DolSpec", "to_dol_library", "to_dol_library_from_modal", "sanitize_modal_identifiers",
    "hets_owl_available",
    "external_concept_satisfiable", "external_concept_unsatisfiable",
    "external_subsumes", "external_equivalent",
    "external_abox_consistent", "external_instance_check", "external_instance_retrieval",
    "external_realize", "external_realize_all",
    "HetsOwlError",
]
