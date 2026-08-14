r"""HTTP client for the HETS (Heterogeneous Tool Set) REST server.

Stdlib ``urllib`` only — no ``requests`` dependency, matching this kit's
external-tool adapters elsewhere (``atp.prover9_entailment`` /
``atp.vampire_entailment`` shell out via ``subprocess`` with no extra
dependency either; this one talks HTTP instead of spawning a process, but the
"no new hard dependency for one adapter" principle is the same).
:class:`HetsClient` is deliberately dumb about *how* it got its ``base_url``
— see :mod:`~unicode_fol_kit.hets.docker` for discovery/lifecycle.

Wire protocol (verified live against ``spechub2/hets:latest``, HETS 0.108.0,
2026-08-12 — treat every claim below as ground truth for THIS client, not
general HETS documentation, since the REST API is not versioned separately
from the server and has changed shape across releases before)

--------------------------------------------------------------------------

1. ``GET /version`` → plain text, e.g. ``"The Heterogeneous Tool Set, version
   0.108.0"``.
2. Upload is a two-step handshake: ``GET /folder`` → a plain-text absolute
   scratch-folder path (e.g. ``/tmp/hetsUserFolder_zvNMsf``); then
   ``POST /uploadFile/<folderBasename>/<filename>`` with the raw file text as
   the request body → a plain-text STORED path (e.g.
   ``/tmp/hetsUserFolder_zvNMsf/probe.casl``). An error body starts with
   ``"*** Error"`` regardless of HTTP status.
3. The stored path IS the IRI for every subsequent endpoint below, but
   URL-ENCODED IN FULL — including the ``/`` characters — e.g.
   ``/tmp/hetsUserFolder_zvNMsf/probe.casl`` becomes
   ``%2Ftmp%2FhetsUserFolder_zvNMsf%2Fprobe.casl``. :meth:`upload` returns the
   RAW (unencoded) path; every method that takes ``iri`` encodes it
   internally via ``urllib.parse.quote(iri, safe="")`` — ``safe=""`` matters,
   the stdlib default ``safe="/"`` would leave the path unencoded and every
   endpoint below would 404 on it.
4. ``GET /dg/<iri>?format=json`` → the parsed development graph:
   ``{"DGraph": {"filename", "libname", "dgnodes", "DGNode": [{"name",
   "logic", "Declarations": [...], "Axioms": [...]}], ...}}``. A bad IRI
   comes back as an error BODY (``"*** Error:\nfile does not exist: ..."``)
   — HETS can still answer HTTP 200 for this, so the body-prefix check in
   :meth:`_get`/:meth:`_post` is load-bearing, not defensive boilerplate.
5. ``GET /provers/<iri>?format=json`` → ``{"provers": [{"identifier":
   "eprover", "name": "eprover"}, ...]}``.
6. ``GET /translations/<iri>`` → XML (the one endpoint that is NOT JSON):
   ``<Translations><translations><li>CASL2SoftFOL</li>
   <li>CASL2NNF:CASL2SoftFOL</li>...</translations></Translations>``.
   Composed comorphisms use a ``:`` separator.
7. ``POST /prove/<iri>`` with JSON body
   ``{"format":"json","goals":[{"node":"<NodeName>",
   "translation":"<optional comorphism>",
   "reasonerConfiguration":{"timeLimit":10,"reasoner":"<optional id>"}}]}``
   → a large, deeply-nested JSON object in which each attempted goal appears
   as ``{"name":"Ax3","result":"Proved\n"|"Disproved\n"|"Open\n",
   "used_prover":{"identifier":...},"used_translation":"CASL2TPTP_FOF",
   "tactic_script":{...},"proof_tree":"","used_time":{...},
   "used_axioms":[...],"prover_output":"..."}`` — the EXACT nesting path
   varies (goals come from ``%implied`` axioms and get axiom-item names,
   e.g. ``"Ax3"`` = third axiom item in the spec), so this client extracts
   goal objects with a recursive structural walk (see
   :func:`_extract_goal_objects`) rather than hard-coding a JSON path.
8. ``POST /consistency-check/<iri>`` — same request/response SHAPE as
   ``/prove``, with ``"result"`` values like ``"Consistent\n"``.
9. ``"Open\n"`` means UNKNOWN (budget/prover gave up), never REFUTED — see
   :mod:`~unicode_fol_kit.hets.docker`'s module docstring for which
   reasoners in the shipped image actually work (``SPASS``, ``darwin``,
   ``darwin-non-fd``) versus which are broken in this image and always
   report ``Open`` (``eprover``, ``Vampire``).
"""

from __future__ import annotations

import json
import urllib.error
import http.client
import urllib.parse
import urllib.request
from typing import Dict, List, Optional

__all__ = ["HetsClient"]

_ERROR_PREFIX = "*** Error"
_EXCERPT_CHARS = 2000

# The stable field set every normalized goal-result dict carries, whatever
# extra keys this HETS version's raw JSON happens to include.
_GOAL_FIELDS = (
    "name", "result", "used_prover", "used_translation",
    "prover_output", "used_time", "tactic_script",
)


def _encode_iri(iri: str) -> str:
    """Percent-encode a stored-file path for use as a HETS REST IRI segment.

    ``safe=""`` is required (not the ``urllib.parse.quote`` default of
    ``safe="/"``): HETS's IRI convention encodes the path separators too —
    see point 3 of this module's wire-protocol docstring.
    """
    return urllib.parse.quote(iri, safe="")


def _extract_goal_objects(node) -> List[dict]:
    """Recursively collect every dict shaped like a goal result.

    A "goal result" is identified structurally — any dict carrying BOTH a
    ``"result"`` and a ``"used_prover"`` key — rather than by a fixed JSON
    path, because the nesting HETS wraps goals in has already varied between
    ``/prove`` and ``/consistency-check`` responses and across HETS
    versions (see point 7 of the module docstring). A dict matching the
    signature is not itself recursed into further: its own values (e.g.
    ``used_prover``, ``used_time``) are metadata about THIS goal, not
    containers of further sibling goals.
    """
    found: List[dict] = []
    if isinstance(node, dict):
        if "result" in node and "used_prover" in node:
            found.append(node)
        else:
            for value in node.values():
                found.extend(_extract_goal_objects(value))
    elif isinstance(node, list):
        for item in node:
            found.extend(_extract_goal_objects(item))
    return found


def _normalize_goal(raw: dict) -> dict:
    """Project a raw goal-result dict onto :data:`_GOAL_FIELDS`.

    ``"result"`` is stripped of surrounding whitespace — HETS appends a
    trailing newline (``"Proved\n"``) — so callers can compare against
    plain ``"Proved"`` / ``"Disproved"`` / ``"Open"`` / ``"Consistent"``
    without repeating ``.strip()`` at every call site. Missing fields become
    ``None`` rather than raising ``KeyError``, since which optional fields a
    given prover populates is itself prover-specific (e.g. a failed run may
    omit ``used_time``).
    """
    out = {field: raw.get(field) for field in _GOAL_FIELDS}
    if isinstance(out["result"], str):
        out["result"] = out["result"].strip()
    return out


class HetsClient:
    """Thin REST client for one HETS server instance.

    Holds no state about the server beyond ``base_url`` — every call is a
    fresh HTTP request. Errors are never silent: an HTTP error status, an
    HETS ``"*** Error"`` body (which can arrive with HTTP 200 — see point 4
    of the module docstring), or a JSON body that fails to parse all raise
    ``RuntimeError`` carrying an excerpt of the offending body, so a failure
    is always visible in the traceback rather than degrading to an empty
    result the caller might mistake for "no goals found".
    """

    def __init__(self, base_url: str, *, timeout: float = 30.0):
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout

    # -- low-level HTTP -----------------------------------------------------

    def _get(self, path: str) -> str:
        return self._request("GET", path)

    def _post(self, path: str, data: bytes, content_type: str) -> str:
        return self._request("POST", path, data=data, content_type=content_type)

    def _request(self, method: str, path: str, *, data: Optional[bytes] = None,
                 content_type: Optional[str] = None) -> str:
        url = self.base_url + path
        headers = {"Content-Type": content_type} if content_type else {}
        req = urllib.request.Request(url, data=data, method=method, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                body = resp.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", "replace") if exc.fp else ""
            raise RuntimeError(
                f"hets: {method} {path} -> HTTP {exc.code}: "
                f"{body[:_EXCERPT_CHARS]!r}"
            ) from exc
        except urllib.error.URLError as exc:
            raise RuntimeError(f"hets: {method} {path} failed: {exc.reason}") from exc
        except http.client.HTTPException as exc:
            # e.g. http.client.InvalidURL for control characters that
            # slipped past encoding — a sibling of URLError, not a subclass,
            # so it needs its own clause to honour the RuntimeError contract
            # (review-confirmed leak).
            raise RuntimeError(
                f"hets: {method} {path} failed: {type(exc).__name__}: {exc}"
            ) from exc
        self._check_error_body(method, path, body)
        return body

    @staticmethod
    def _check_error_body(method: str, path: str, body: str) -> None:
        """Raise if ``body`` is a HETS ``"*** Error"`` payload despite HTTP 200."""
        if body.lstrip().startswith(_ERROR_PREFIX):
            raise RuntimeError(
                f"hets: {method} {path} returned an error body: "
                f"{body[:_EXCERPT_CHARS]!r}"
            )

    @staticmethod
    def _parse_json(path: str, body: str) -> dict:
        try:
            return json.loads(body)
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                f"hets: {path} response was not valid JSON ({exc}); "
                f"body excerpt: {body[:_EXCERPT_CHARS]!r}"
            ) from exc

    # -- endpoints ------------------------------------------------------------

    def version(self) -> str:
        """``GET /version`` -> the server's plain-text version banner, stripped."""
        return self._get("/version").strip()

    def upload(self, text: str, filename: str) -> str:
        """Upload ``text`` as ``filename``; return the stored-path IRI, RAW.

        Two round trips per the wire protocol (points 2-3 above): fetch a
        scratch folder, then POST the file into it. The return value is
        deliberately the raw (unencoded) stored path — every other method on
        this class takes that same raw ``iri`` and encodes it internally
        (:func:`_encode_iri`), so callers never have to think about encoding,
        and a caller that wants to log/join/inspect the path is not fighting
        a pre-escaped string.
        """
        folder = self._get("/folder").strip()
        folder_basename = folder.rsplit("/", 1)[-1]
        # Both path segments are percent-encoded like every IRI is: an
        # unencoded '#' in a filename would be parsed as a URL fragment and
        # SILENTLY truncate the stored name (review-confirmed live), and a
        # space would crash urllib below the URLError layer.
        stored_path = self._post(
            f"/uploadFile/{urllib.parse.quote(folder_basename, safe='')}"
            f"/{urllib.parse.quote(filename, safe='')}",
            data=text.encode("utf-8"),
            content_type="text/plain; charset=utf-8",
        ).strip()
        return stored_path

    def dg(self, iri: str) -> dict:
        """``GET /dg/<iri>?format=json`` -> the parsed development-graph dict."""
        body = self._get(f"/dg/{_encode_iri(iri)}?format=json")
        return self._parse_json("dg", body)

    def provers(self, iri: str) -> List[str]:
        """``GET /provers/<iri>?format=json`` -> prover identifiers HETS can invoke."""
        body = self._get(f"/provers/{_encode_iri(iri)}?format=json")
        data = self._parse_json("provers", body)
        return [p["identifier"] for p in data.get("provers", [])]

    def translations(self, iri: str) -> List[str]:
        """``GET /translations/<iri>`` -> comorphism names, from the ``<li>`` XML list.

        The one endpoint that answers XML rather than JSON (point 6 of the
        module docstring). Parsed with :mod:`xml.etree.ElementTree`, not a
        regex, since comorphism names are free text HETS controls, not this
        client.
        """
        import xml.etree.ElementTree as ET

        body = self._get(f"/translations/{_encode_iri(iri)}")
        try:
            root = ET.fromstring(body)
        except ET.ParseError as exc:
            raise RuntimeError(
                f"hets: /translations response was not valid XML ({exc}); "
                f"body excerpt: {body[:_EXCERPT_CHARS]!r}"
            ) from exc
        return [li.text or "" for li in root.iter("li")]

    def theory(self, iri: str, *, node: Optional[str] = None,
               translation: Optional[str] = None) -> str:
        """``GET /theory/<iri>?…&format=dol`` -> the theory as rendered text.

        Without ``translation`` this is the (sublogic-annotated) CASL theory
        itself; with a comorphism name (from :meth:`translations`, e.g.
        ``CASL2SoftFOL``) it is the TRANSLATED theory in the target logic's
        own concrete syntax (verified live: ``CASL2SoftFOL`` renders
        SoftFOL/DFG ``list_of_symbols``/``formula(...)`` text). ``node``
        selects a development-graph node by name and is EFFECTIVELY
        MANDATORY: this HETS version answers HTTP 500 ``development graph
        node missing`` when it is omitted — with AND without a translation,
        even for single-node libraries (review-corrected; the bridge
        resolves the node from :meth:`dg` for exactly this reason). Callers
        should always pass it; the parameter stays optional only so a
        future server that grows a default keeps working.
        """
        params = ["format=dol"]
        if node is not None:
            params.append(f"node={urllib.parse.quote(node, safe='')}")
        if translation is not None:
            params.append(
                f"translation={urllib.parse.quote(translation, safe='')}")
        return self._get(f"/theory/{_encode_iri(iri)}?{'&'.join(params)}")

    @staticmethod
    def _prove_body(node: str, *, reasoner: Optional[str], translation: Optional[str],
                     time_limit: int) -> dict:
        """Build the JSON body shared by ``/prove`` and ``/consistency-check``.

        ``translation`` is omitted from the goal dict entirely when ``None``
        (not sent as ``null``) — HETS picks its own default translation for
        the chosen reasoner in that case (e.g. SPASS defaults to
        ``CASL2TPTP_FOF``), and an explicit ``null`` is a different, untested
        wire shape this client does not want to invent.
        """
        goal: Dict[str, object] = {"node": node}
        if translation is not None:
            goal["translation"] = translation
        reasoner_config: Dict[str, object] = {"timeLimit": time_limit}
        if reasoner is not None:
            reasoner_config["reasoner"] = reasoner
        goal["reasonerConfiguration"] = reasoner_config
        return {"format": "json", "goals": [goal]}

    def _run_goal_endpoint(self, endpoint: str, iri: str, node: str, *,
                            reasoner: Optional[str], translation: Optional[str],
                            time_limit: int) -> List[dict]:
        body = self._prove_body(node, reasoner=reasoner, translation=translation,
                                 time_limit=time_limit)
        response = self._post(
            f"/{endpoint}/{_encode_iri(iri)}",
            data=json.dumps(body).encode("utf-8"),
            content_type="application/json",
        )
        # Wire-protocol special case (review-discovered): a node with ZERO
        # %implied goals answers the literal plain-text "nothing to prove"
        # instead of JSON. That is the legitimate empty result, not a
        # malformed response — "one dict per attempted goal" of zero goals.
        if response.strip().lower() == "nothing to prove":
            return []
        parsed = self._parse_json(endpoint, response)
        return [_normalize_goal(g) for g in _extract_goal_objects(parsed)]

    def prove(self, iri: str, node: str, *, reasoner: Optional[str] = None,
              translation: Optional[str] = None, time_limit: int = 10) -> List[dict]:
        """``POST /prove/<iri>`` for one goal node; normalized goal-result dicts.

        Args:
            iri: a stored-path IRI as returned by :meth:`upload` (raw,
                unencoded — this method encodes it).
            node: the development-graph node name to prove goals for.
            reasoner: prover identifier (e.g. ``"SPASS"``, ``"darwin"``);
                ``None`` lets HETS pick its default for the node's logic.
            translation: comorphism name (e.g. ``"CASL2TPTP_FOF"``); ``None``
                lets HETS pick its default for the chosen reasoner.
            time_limit: per-goal seconds budget (HETS's ``timeLimit``).

        Returns:
            One dict per attempted goal (typically one per ``%implied``
            axiom in the node), each with keys ``"name"``, ``"result"``
            (whitespace-stripped — ``"Proved"`` / ``"Disproved"`` /
            ``"Open"``), ``"used_prover"``, ``"used_translation"``,
            ``"prover_output"``, ``"used_time"``, ``"tactic_script"``.
            ``"Open"`` is UNKNOWN, never a disproof — see this module's
            docstring point 9.
        """
        return self._run_goal_endpoint(
            "prove", iri, node, reasoner=reasoner, translation=translation,
            time_limit=time_limit)

    def consistency_check(self, iri: str, node: str, *,
                           reasoner: str = "darwin-non-fd",
                           time_limit: int = 10) -> List[dict]:
        """``POST /consistency-check/<iri>`` for one node; same shape as :meth:`prove`.

        Defaults ``reasoner`` to ``"darwin-non-fd"`` (unlike :meth:`prove`,
        which defaults to ``None``/HETS's own choice) because
        consistency-checking specifically wants a FINITE model finder able
        to certify ``"Consistent"`` by exhibiting one — plain ``darwin`` and
        the broken ``eprover``/``Vampire`` reasoners in this image are not
        reliable for that (see :mod:`~unicode_fol_kit.hets.docker`'s
        docstring on image quirks).
        """
        return self._run_goal_endpoint(
            "consistency-check", iri, node, reasoner=reasoner, translation=None,
            time_limit=time_limit)
