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
import re
import urllib.error
import http.client
import urllib.parse
import urllib.request
from typing import Dict, List, Optional, Tuple

from ..fol.tptp_input import _HETS_LOGIC_REFERENCE
from .haskell_json import repair_haskell_json

__all__ = [
    "HetsClient",
    "HetsNoTranslationsError",
    "HetsSublogicError",
    "strip_hets_theory_header",
]

_ERROR_PREFIX = "*** Error"
_EXCERPT_CHARS = 2000

#: HETS' own 422 body for a theory whose sublogic the requested comorphism
#: does not cover. Verified verbatim against the live server::
#:
#:     *** Error:
#:     for 'OWL22CASL;CASL2TPTP_FOF' expected sublogic 'NP-sROIQux-D|-|'
#:      but found sublogic 'NP-sROIQ-D|Literal|dateTime|decimal|integer|string|' with signature sublogic 'ELQLRL-ALC'
#:
#: A stable, machine-readable signature — which is what makes
#: :class:`HetsSublogicError` branchable rather than prose a caller has to
#: grep. Note HETS writes the composition with ``;`` here while the URL (and
#: the command line) take ``:``; the exception carries HETS' spelling
#: verbatim rather than normalising it, because that is the string HETS'
#: other messages use.
_SUBLOGIC_RE = re.compile(
    r"for '([^']+)' expected sublogic '([^']*)'\s*\n?\s*"
    r"but found sublogic '([^']*)'")

#: A TPTP problem must contain at least one of these. Used by
#: :meth:`HetsClient.theory_tptp` to refuse a CASL (or error) body rather
#: than hand back something that would parse to an empty formula list.
_TPTP_STATEMENT_RE = re.compile(r"(?:^|[\s)(.])(fof|cnf|tff|thf)\s*\(")

#: The DOL ``logic <Name>.<Sublogic>`` line HETS puts in front of every
#: ``/theory`` rendering, and CASL's ``%{ ... }%`` block comment (which
#: carries HETS' own ``constants:``/``predicates:``/``sorts:`` signature
#: listing). Neither is TPTP syntax — see :func:`strip_hets_theory_header`.
#:
#: The WHOLE line is ``logic`` plus one DOL logic reference — the SAME notion of
#: "a Hets header" as :mod:`unicode_fol_kit.fol.tptp_input`'s refusal pointer
#: (it is imported from there, so the two cannot disagree): a logic NAME, an
#: identifier, optionally ``.`` and a free-form sublogic. The previous ``logic``
#: plus any whitespace-free word also matched the first line of a bare formula
#: such as ``logic &p``, and the splitter then ate it as a "header".
_LOGIC_LINE_RE = re.compile(
    r"logic[ \t]+" + _HETS_LOGIC_REFERENCE + r"[ \t\r]*$", re.MULTILINE)

# The stable field set every normalized goal-result dict carries, whatever
# extra keys this HETS version's raw JSON happens to include.
_GOAL_FIELDS = (
    "name", "result", "used_prover", "used_translation",
    "prover_output", "used_time", "tactic_script",
)


class HetsNoTranslationsError(RuntimeError):
    """``GET /translations`` answered a well-formed list with no comorphism.

    A ``RuntimeError`` subclass, like :class:`HetsOwlError`
    (:mod:`~unicode_fol_kit.hets.owl_backend`) and for the same reason: the
    server is up and the request was understood, the ANSWER is the problem.
    Every existing ``except RuntimeError`` caller therefore keeps working.

    Why this is raised rather than returned as ``[]``: an empty list reads as
    "this logic has no comorphisms", and what HETS actually means is "I am not
    telling you why". Measured on the real server — for an ontology whose
    sublogic ``OWL22CASL`` does not cover, ``/translations`` answers
    ``<Translations><translations></translations></Translations>`` with HTTP
    200, no exception and no reason, while ``/theory`` for the very same
    library answers HTTP 422 with the sublogic mismatch spelled out. So the
    reason exists; it just lives at a different endpoint, and this exception's
    message is where that is written down.

    ``translations(..., allow_empty=True)`` restores the old return-``[]``
    behaviour for a caller that genuinely wants it.
    """


class HetsSublogicError(RuntimeError):
    """HETS refused a translation because the theory's sublogic is too rich.

    Carries HETS' own three strings, parsed from the 422 body by
    :data:`_SUBLOGIC_RE`, so a caller can BRANCH on the refusal instead of
    grepping prose:

    Attributes:
        comorphism: the comorphism HETS was asked for, as HETS spells it
            (``"OWL22CASL;CASL2TPTP_FOF"`` — with a semicolon, even though
            the URL and the command line both take ``:``).
        expected: the sublogic the comorphism covers
            (``"NP-sROIQux-D|-|"``).
        found: the sublogic the theory actually is
            (``"NP-sROIQ-D|Literal|dateTime|decimal|integer|string|"``).
        body: the 422 body, verbatim.

    A ``RuntimeError`` subclass for the same reason as
    :class:`HetsNoTranslationsError`.
    """

    def __init__(self, message: str, *, comorphism: str, expected: str,
                 found: str, body: str):
        super().__init__(message)
        self.comorphism = comorphism
        self.expected = expected
        self.found = found
        self.body = body


def strip_hets_theory_header(text: str) -> Tuple[str, str]:
    r"""Split HETS' theory rendering into ``(header, body)``. Never raises.

    ``GET /theory?...&format=dol`` prefixes its output with DOL/CASL syntax
    that is NOT part of the target logic::

        logic TPTP.FOF

        %{

        constants:  op_a,
                    op_b

        predicates:  pred_p: $i > $o

        }%

        fof(ax_ax1, axiom, ...).

    TPTP has exactly two comment forms, ``%`` to end of line and
    ``/* ... */``. ``%{ ... }%`` is CASL's BLOCK comment and ``logic
    <Name>.<Sublogic>`` is DOL library syntax, so a TPTP reader must not
    learn either: ``%`` already swallows ``%{`` as an ordinary line comment
    and the reader then chokes on the block's first content line, and
    teaching it the block form would make it accept a CASL theory header,
    treat the whole CASL body as a comment and return an EMPTY formula list
    — a silent empty answer to a wrong-translation request. So the split
    happens here, in the adapter that knows its input is a HETS rendering,
    exactly as :func:`unicode_fol_kit.ace.runner._repair_ape_tptp` repairs
    APE's pretty-printer inside the ACE adapter and
    :mod:`unicode_fol_kit.fol.tptp_repair` sits OVER the reader rather than
    inside its grammar.

    The split is structural, never ``text[text.index("fof("):]``: a blind cut
    would also swallow a HETS ``*** Error`` body whole, and a symbol whose
    name happens to end in ``_fof`` inside the 2267-line signature block
    would move the cut point. The rule, verified against both the real TPTP
    and the real CASL rendering:

    1. skip leading whitespace; if what follows is a WHOLE line of the form
       ``logic <Name>`` or ``logic <Name>.<Sublogic>`` (a logic name is an
       identifier, so ``logic &p`` — a formula — is not a header), consume
       through the end of that line;
    2. repeatedly skip whitespace and, while what follows starts with
       ``%{``, consume through the first following ``}%`` (CASL block
       comments do not nest);
    3. what remains is the body.

    An unterminated ``%{`` is left in the body rather than truncating the
    text to nothing — the caller then gets a named refusal from
    :meth:`HetsClient.theory_tptp` instead of a silently empty result.

    Args:
        text: a ``/theory`` rendering, or any text at all.

    Returns:
        ``(header, body)``. ``("", text)`` when there is no header, so the
        call is safe to make unconditionally.

    Example:
        >>> strip_hets_theory_header("fof(a, axiom, p).")
        ('', 'fof(a, axiom, p).')
    """
    index = 0
    length = len(text)
    while index < length and text[index].isspace():
        index += 1
    match = _LOGIC_LINE_RE.match(text, index)
    if match:
        end = text.find("\n", match.end())
        index = length if end == -1 else end + 1
    else:
        index = 0
    while True:
        cursor = index
        while cursor < length and text[cursor].isspace():
            cursor += 1
        if not text.startswith("%{", cursor):
            break
        close = text.find("}%", cursor + 2)
        if close == -1:
            # Unterminated: consume nothing, so the text survives for the
            # caller's own refusal rather than vanishing into the header.
            break
        index = close + 2
    return text[:index], text[index:]


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
            generic = RuntimeError(
                f"hets: {method} {path} -> HTTP {exc.code}: "
                f"{body[:_EXCERPT_CHARS]!r}"
            )
            # HTTP 422 with HETS' sublogic signature is the one HTTP error
            # worth a TYPED exception: it is the server saying "this theory
            # is richer than the comorphism you asked for", which a caller
            # can act on (fall back to the lossy command-line route, or
            # reduce the theory). Any OTHER 422 keeps the generic wording
            # above, so the typed exception never swallows an unrelated
            # failure.
            if exc.code == 422:
                signature = _SUBLOGIC_RE.search(body)
                if signature:
                    comorphism, expected, found = signature.groups()
                    raise HetsSublogicError(
                        f"hets: {method} {path} -> HTTP 422: HETS refuses the "
                        f"comorphism {comorphism!r} for this theory — it "
                        f"covers sublogic {expected!r} but the theory is "
                        f"{found!r}. Either reduce the theory to that "
                        "sublogic, or take the LOSSY command-line route, "
                        "which translates anyway and reports what it omitted: "
                        "unicode_fol_kit.hets.owl_to_tptp(path, lossy=True) "
                        "(hets-server's -Y switch; the REST API has no "
                        f"equivalent). HETS' body was: "
                        f"{body[:_EXCERPT_CHARS]!r}",
                        comorphism=comorphism, expected=expected, found=found,
                        body=body,
                    ) from exc
            raise generic from exc
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

    def dg_raw(self, iri: str) -> str:
        """``GET /dg/<iri>?format=json`` -> the body exactly as HETS sent it.

        No JSON parsing and NO escape repair. This is the method to reach for
        when :meth:`dg` raises and the body itself needs inspecting — see
        :mod:`~unicode_fol_kit.hets.haskell_json` for the one known reason a
        HETS development-graph body is not valid JSON.
        """
        return self._get(f"/dg/{_encode_iri(iri)}?format=json")

    def dg(self, iri: str) -> dict:
        """``GET /dg/<iri>?format=json`` -> the parsed development-graph dict.

        ``json.loads`` is tried FIRST and the repair runs only when it
        raises. That ordering is the whole design: a body the standard
        library already accepts is never touched at all, so no legitimate
        escape can be mangled by the repair, and the identity invariant is
        structural rather than argued.

        When the body IS invalid, :func:`~unicode_fol_kit.hets.haskell_json.repair_haskell_json`
        gets one attempt at HETS' Haskell-``show`` escapes (``\\226\\128\\153``
        for ``’`` and friends — see that module for why this is lossless
        recovery of a known emitter). If it finds nothing to repair, the
        original error is re-raised with its original wording; if it repairs
        something and the result STILL does not parse, the error names the
        repair, so a failure is attributable rather than mysterious.

        Raises:
            RuntimeError: the body is not valid JSON, with or without the
                repair.
            ~unicode_fol_kit.hets.haskell_json.HaskellJsonRepairError: a
                Haskell escape in the body is not a Unicode scalar value.
        """
        body = self.dg_raw(iri)
        try:
            return json.loads(body)
        except json.JSONDecodeError:
            pass
        repair = repair_haskell_json(body)
        if not repair:
            return self._parse_json("dg", body)
        return self._parse_json(f"dg (after repairing {repair.summary()})",
                                repair.text)

    def provers(self, iri: str) -> List[str]:
        """``GET /provers/<iri>?format=json`` -> prover identifiers HETS can invoke."""
        body = self._get(f"/provers/{_encode_iri(iri)}?format=json")
        data = self._parse_json("provers", body)
        return [p["identifier"] for p in data.get("provers", [])]

    def translations(self, iri: str, *, node: Optional[str] = None,
                     allow_empty: bool = False) -> List[str]:
        """``GET /translations/<iri>`` -> comorphism names, from the ``<li>`` XML list.

        The one endpoint that answers XML rather than JSON (point 6 of the
        module docstring). Parsed with :mod:`xml.etree.ElementTree`, not a
        regex, since comorphism names are free text HETS controls, not this
        client.

        HETS' own IDENTITY entry — an ``<li/>`` with no text — is DROPPED,
        and so is a whitespace-only one. It is not a comorphism name and not
        a legal ``translation=`` value: a caller looping
        ``for t in translations(iri): theory(iri, node=n, translation=t)``
        would send ``translation=`` for it, and
        :func:`~unicode_fol_kit.hets.bridge.register_hets_comorphisms` would
        register an edge literally named ``hets:``. "No translation" is
        already expressible as ``translation=None``, so dropping it loses no
        capability. Order and duplicates among the real names are preserved,
        and each name is returned STRIPPED of surrounding whitespace (a name
        with a stray space or newline round-trips into ``translation=`` as a
        different, unknown comorphism).

        The root element must be ``<Translations>``: any other well-formed
        document is the server refusing the request, which is raised, never
        read as an empty list.

        Args:
            iri: a stored-path IRI as returned by :meth:`upload`.
            node: a development-graph node name, sent as ``?node=<name>``.
                Purely additive and worth passing: measured on the real
                server, 3.21 s without it against 0.12 s with it for the same
                library. For a single-ontology library the node name is the
                ontology IRI (which :meth:`dg` reports).
            allow_empty: return ``[]`` instead of raising when HETS offers
                nothing.

        Raises:
            HetsNoTranslationsError: the list came back with no comorphism in
                it and ``allow_empty`` is false. See that class for why an
                empty list is not an answer.
            RuntimeError: the body was not valid XML, or was a well-formed
                document whose root is not ``<Translations>`` (raised even
                with ``allow_empty=True``).
        """
        import xml.etree.ElementTree as ET

        path = f"/translations/{_encode_iri(iri)}"
        if node is not None:
            path += f"?node={urllib.parse.quote(node, safe='')}"
        body = self._get(path)
        try:
            root = ET.fromstring(body)
        except ET.ParseError as exc:
            raise RuntimeError(
                f"hets: /translations response was not valid XML ({exc}); "
                f"body excerpt: {body[:_EXCERPT_CHARS]!r}"
            ) from exc
        if root.tag != "Translations":
            # A well-formed document of another shape is the server REFUSING
            # (or answering something else), not "this library has no
            # comorphism": with allow_empty=True it used to come back as [],
            # and without it as HetsNoTranslationsError, whose wording
            # ("offers no comorphism") blames the library for it.
            raise RuntimeError(
                f"hets: GET {path} answered an XML document whose root is "
                f"<{root.tag}>, not the <Translations> list this endpoint "
                "returns — the server refused the request or answered "
                "something else, so there is no list to read (and an empty "
                "list is not substituted for it, allow_empty or not); "
                f"body excerpt: {body[:_EXCERPT_CHARS]!r}")
        names = [(li.text or "").strip() for li in root.iter("li")]
        kept = [name for name in names if name]
        if not kept and not allow_empty:
            raise HetsNoTranslationsError(
                f"hets: GET {path} offers no comorphism for this library "
                f"({len(names)} <li> entr{'y' if len(names) == 1 else 'ies'}, "
                "none of them a name). That is not the same as 'there are "
                "none': this endpoint reports no reason at all, and the "
                "reason lives on /theory, which answers HTTP 422 with the "
                "sublogic mismatch spelled out — call "
                "theory(iri, node=..., translation=...) and catch "
                "HetsSublogicError to read it, or take the lossy "
                "command-line route, unicode_fol_kit.hets.owl_to_tptp("
                "path, lossy=True), which translates anyway and reports the "
                "axioms it omitted. Pass allow_empty=True to get [] back "
                "instead of this exception.")
        return kept

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

    def theory_tptp(self, iri: str, *, node: str,
                    translation: str = "OWL22CASL:CASL2TPTP_FOF") -> str:
        """``GET /theory`` with a TPTP-target comorphism, header stripped.

        The text :meth:`theory` returns for a TPTP comorphism is NOT a TPTP
        problem: HETS puts a DOL ``logic TPTP.FOF`` line and a CASL
        ``%{ ... }%`` signature block in front of it, and
        :func:`unicode_fol_kit.fol.tptp_input.parse_tptp` refuses both by
        name. This method returns what the reader actually accepts, so the
        usual call is ``parse_tptp(client.theory_tptp(iri, node=n))``.

        Measured against the command-line route: for the real 1,554,903-char
        rendering the stripped remainder is byte-identical (after leading
        newlines) to the 1,367,212-byte file ``hets-server -o tptp`` writes,
        so the REST route and the CLI route deliver the same text.

        Args:
            iri: a stored-path IRI as returned by :meth:`upload`.
            node: the development-graph node name. Mandatory here (unlike
                :meth:`theory`, where it stays optional for a future server):
                this HETS version answers HTTP 500 without it.
            translation: a comorphism whose TARGET is TPTP. The default is
                the one the OWL route needs; ``"OWL22CASL"`` alone returns
                CASL and is refused below rather than silently parsed to an
                empty formula list.

        Returns:
            The TPTP problem text, header removed.

        Raises:
            HetsSublogicError: the server answered HTTP 422 because the
                theory is richer than the comorphism covers.
            RuntimeError: the stripped text holds no ``fof``/``cnf``/``tff``
                statement — the comorphism's target was not TPTP, or HETS
                answered something else entirely.
        """
        text = self.theory(iri, node=node, translation=translation)
        _header, body = strip_hets_theory_header(text)
        if not _TPTP_STATEMENT_RE.search(body):
            first_line = body.strip().split("\n", 1)[0] if body.strip() else ""
            raise RuntimeError(
                f"hets: /theory for node {node!r} with "
                f"translation={translation!r} did not return a TPTP problem "
                "— after stripping HETS' theory header the text has no "
                f"fof/cnf/tff statement; its first line is {first_line!r}. "
                "Pass a translation whose target is TPTP (e.g. "
                "'OWL22CASL:CASL2TPTP_FOF'); 'OWL22CASL' alone returns CASL.")
        return body

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
