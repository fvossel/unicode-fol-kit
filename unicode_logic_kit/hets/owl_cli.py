r"""The HETS COMMAND-LINE route: ``owl_to_tptp``, the only way to the lossy translation.

Why a second route at all
-------------------------
:mod:`~unicode_logic_kit.hets.client` speaks HETS' REST API and never shells
out. That covers everything the server offers — except one switch. HETS
refuses a comorphism whose source sublogic does not cover the theory, and
``GET /theory`` then answers HTTP 422 (see
:class:`~unicode_logic_kit.hets.client.HetsSublogicError`). ``hets-server``'s
``-Y`` flag translates ANYWAY, dropping the axioms it cannot express, and
``-Y`` exists ONLY on the command line: the REST API has no equivalent. For a
real ontology that one flag is the difference between a FOL image and nothing
at all — measured on OEO 2.13.0, two ``DataPropertyRange(d rdfs:Literal)``
axioms out of 4041 push the whole ontology out of ``OWL22CASL``'s sublogic.

So this module exists, and it is deliberately thin: it builds a command line,
runs it through ``docker exec``, copies the output back and reads the console. All the
interpretation lives in :mod:`~unicode_logic_kit.hets.symbols`, which is pure
and fully offline-testable — that split is what makes this specifiable on a
machine with no HETS.

``lossy=True`` runs the NON-LOSSY translation FIRST, on purpose
---------------------------------------------------------------
``-Y`` is SILENT. Measured from HETS' own console output: the lossy run prints
only ``Translated using comorphism OWL22CASL;CASL2TPTP_FOF : OWL -> TPTP``,
while the sublogic warning appears only in the run WITHOUT ``-Y``::

    ### Warning:
    for 'OWL22CASL;CASL2TPTP_FOF' expected sublogic 'NP-sROIQux-D|-|'
    but found sublogic 'NP-sROIQ-D|Literal|dateTime|decimal|integer|string|' ...
    Keeping untranslated theory

A single ``-Y`` run would therefore hand the caller a quietly smaller theory
with nothing to indicate it. That is exactly the silent approximation this kit
refuses, so ``lossy=True`` runs the probe first and fills
:attr:`OwlTptpResult.sublogic_mismatch` from HETS' own warning text. The
mismatch is then reported even when no ``client=`` was passed and
:attr:`OwlTptpResult.omitted_axioms` is consequently ``None``.

The COST, stated rather than hidden: two HETS runs per call, measured at
4.6 s + 4.4 s for OEO's 3.85 MB, so ~9 s instead of ~4.5 s. On a much larger
ontology that doubling is the dominant cost of the call, and the only way to
avoid it is to pass ``client=`` and let :func:`~unicode_logic_kit.hets.symbols.untranslated_axioms`
compute the loss from ``/dg`` against the TPTP instead — which is both exact
and free. ``lossy=False`` does one run and raises
:class:`~unicode_logic_kit.hets.client.HetsSublogicError`.

EXIT 0 is not success
---------------------
Both non-lossy runs above exit 0 and write the UNTRANSLATED theory; with
``-o tptp`` no ``.tptp`` file is written at all. The wrong separator exits 0
too (``### Warning: Cannot find logic comorphism OWL22CASL;CASL2TPTP_FOF``).
So success is the CONJUNCTION of: a ``.tptp`` file appeared in the output
directory, AND the console contains ``Translated using comorphism``. Anything
else is a named refusal.

What this module will NOT do: normalise the ontology
----------------------------------------------------
HETS 0.108.0 rejects an ``AnnotationAssertion`` whose subject is not declared
(``Incorrect AnnotationAssertion axiom. Axiom subject is not declared:
'obo:BFO_0000134'``), which OWL 2 does not require. Fixing that inside this
kit would need three things it must not do silently: (1) CHOOSE an entity kind
for an annotation-only IRI — the requesting project's own log reads "kind not
stated in the file, assumed ObjectProperty", i.e. a guess that puts a symbol
into the logical signature; (2) an RDF/XML WRITER, which this kit does not
have and should not grow for this; (3) DELETE two ``rdfs:isDefinedBy``
annotations, i.e. lose information. So :func:`owl_to_tptp` instead DETECTS the
pattern in HETS' console, collects every undeclared subject and raises
:class:`HetsOwlNormalizationError` listing them with both remedies and the
explicit statement that this kit will not choose the kind. That turns an
opaque HETS failure into a one-line instruction and leaves the semantic
choice with the ontology's owner.

Two routes
----------
No ``unicode_logic_kit.dl`` file is touched and no construct reaches the
description-logic tableau. The two-route rule applies at the level the whole
OEO request is about: :func:`owl_to_tptp` produces the SECOND route's FOL
image of an ontology, to be compared against
:func:`unicode_logic_kit.dl.tbox_to_fol` / :func:`unicode_logic_kit.dl.kb_to_fol`
plus :func:`unicode_logic_kit.api.prove`. The helper therefore must never
present an incomplete image as complete — which is what
:attr:`~OwlTptpResult.sublogic_mismatch`, :attr:`~OwlTptpResult.omitted_axioms`,
:attr:`~unicode_logic_kit.hets.symbols.HetsSymbol.in_tptp` and
:attr:`~unicode_logic_kit.hets.symbols.HetsSymbolTable.unmapped_tptp` are for —
and HETS' own translation defects are listed in
:mod:`~unicode_logic_kit.hets.symbols`' docstring so a disagreement is
attributable rather than blamed on this kit.
"""

from __future__ import annotations

import os
import posixpath
import re
import shutil
import subprocess
import uuid
from dataclasses import dataclass
from typing import List, Optional, Tuple, Union

from ..atp.protocol import BackendUnavailable
from .client import HetsClient, HetsSublogicError, _SUBLOGIC_RE
from .docker import HETS_IMAGE, HetsContainer
from .symbols import (
    HetsSymbolTable,
    UntranslatedAxiom,
    hets_prefixes,
    hets_symbol_table,
    untranslated_axioms,
)

__all__ = [
    "SublogicMismatch",
    "OwlTptpResult",
    "HetsOwlNormalizationError",
    "owl_to_tptp",
    "UFK_HETS_CONTAINER",
]

#: The environment variable naming a running HETS container to ``docker
#: exec`` into. Deliberately NOT ``$UFK_HETS_URL``:
#: :func:`~unicode_logic_kit.hets.docker.discover_hets_url` may legitimately
#: return a URL that is not a local container at all (its own docstring says
#: so — a shared server, a CI sidecar), and ``docker exec`` into a URL is
#: impossible. So the command-line route gets its own discovery and its own
#: variable, mirroring ``discover_hets_url``'s "never guess, list every
#: option tried" contract rather than reusing it.
UFK_HETS_CONTAINER = "UFK_HETS_CONTAINER"

#: The console line that means the translation actually happened. HETS writes
#: the composition with ``;`` here even though the command line takes ``:``.
_TRANSLATED_RE = re.compile(
    r"Translated using comorphism\s+(\S+)\s*:\s*(\S+)\s*->\s*(\S+)")

#: HETS could not resolve the comorphism name at all — what the ``;``
#: spelling produces on the command line, with EXIT 0 and no output file.
_NO_COMORPHISM_RE = re.compile(r"Cannot find logic comorphism\s+(\S+)")

#: ``Incorrect AnnotationAssertion axiom. Axiom subject is not declared:
#: 'obo:BFO_0000134'`` — HETS may report only the first, so the refusal says
#: the list may be incomplete.
_UNDECLARED_RE = re.compile(
    r"Axiom subject is not declared:\s*'([^']*)'")


class HetsOwlNormalizationError(RuntimeError):
    """HETS refused the ontology because an annotation subject is undeclared.

    Attributes:
        undeclared: every IRI HETS named, in the order it named them. HETS
            may stop at the first, so this list can be incomplete — the
            message says so.

    A ``RuntimeError`` subclass, like the other HETS exceptions: the server
    (here, the binary) is fine and the request was understood; the INPUT is
    the problem. This kit will not repair it — see the module docstring for
    the three things such a repair would have to guess.
    """

    def __init__(self, message: str, *, undeclared: Tuple[str, ...]):
        super().__init__(message)
        self.undeclared = undeclared


@dataclass(frozen=True)
class SublogicMismatch:
    """HETS' sublogic complaint, parsed into its three parts.

    Fields:

    * ``comorphism`` — as HETS spells it, with ``;``
      (``"OWL22CASL;CASL2TPTP_FOF"``).
    * ``expected`` — the sublogic the comorphism covers.
    * ``found`` — the sublogic the theory actually is.
    """

    comorphism: str
    expected: str
    found: str


@dataclass(frozen=True)
class OwlTptpResult:
    """The outcome of one :func:`owl_to_tptp` call.

    Fields:

    * ``tptp`` — the ``.tptp`` text, exactly as HETS wrote it. Ready for
      :func:`unicode_logic_kit.fol.tptp_input.parse_tptp` — unlike the
      REST ``/theory`` rendering, the ``-o tptp`` file carries no
      header.
    * ``node`` — the development-graph node name, recovered from the output
      file name (HETS percent-encodes the node IRI into it).
    * ``comorphism`` — the comorphism HETS reports having used, in HETS'
      ``;`` spelling.
    * ``lossy`` — whether ``-Y`` was actually used for the run that produced
      :attr:`tptp`.
    * ``sublogic_mismatch`` — the loss REPORT. ``None`` means the probe run
      succeeded without ``-Y``, so nothing was dropped for sublogic
      reasons. Non-``None`` means ``-Y`` was needed, and names the
      sublogic gap.
    * ``console`` — HETS' stdout and stderr for the run that produced
      :attr:`tptp`, verbatim.
    * ``theory`` — the ``-o th`` text — the TRANSLATED theory.
    * ``pretty`` — the ``-o pp.dol`` text — HETS' pretty-printed rendering of the
      SOURCE ontology, and the only one of the three outputs that
      carries the ``Prefix: p: <iri>`` lines (measured: the translated
      ``.th`` of a TPTP chain has none). Feed it to
      :func:`~unicode_logic_kit.hets.symbols.hets_prefixes`; that is what
      :attr:`symbols` already does.
    * ``symbols`` — the OWL-entity/TPTP-symbol join, or ``None`` when no
      ``client=`` was given. ``None`` means NOT COMPUTED, never
      "nothing found": the join needs ``/dg``, which needs the REST
      client.
    * ``omitted_axioms`` — the axioms with no formula in :attr:`tptp`, or
      ``None`` when no ``client=`` was given. An empty tuple ``()``
      means "computed, and the answer is none".
    """

    tptp: str
    node: str
    comorphism: str
    lossy: bool
    sublogic_mismatch: Optional[SublogicMismatch]
    console: str
    theory: str
    pretty: str = ""
    symbols: Optional[HetsSymbolTable] = None
    omitted_axioms: Optional[Tuple[UntranslatedAxiom, ...]] = None


@dataclass(frozen=True)
class _Run:
    """One ``hets-server`` invocation's raw outcome."""

    argv: List[str]
    returncode: int
    console: str
    out_dir: str
    outputs: dict          # basename -> text, for the files HETS wrote


def _docker_bin() -> str:
    found = shutil.which("docker")
    if found is None:
        raise BackendUnavailable(
            "hets: no `docker` binary found on PATH, and owl_to_tptp reaches "
            "hets-server through `docker exec`. Install Docker Desktop "
            "(https://www.docker.com/products/docker-desktop/) and ensure "
            "`docker` is on PATH. A remote $UFK_HETS_URL cannot substitute: "
            "the lossy switch (-Y) exists only on the command line and HETS' "
            "REST route has no equivalent.")
    return found


def _resolve_container(container, start_container: bool
                       ) -> Tuple[str, Optional[HetsContainer]]:
    """Name the container to exec into; never guess, list every option tried.

    Returns ``(name, owned)`` where ``owned`` is a container this call
    started (and must stop) or ``None``.
    """
    if isinstance(container, HetsContainer):
        return container.name, None
    if isinstance(container, str) and container.strip():
        return container.strip(), None
    from_env = os.environ.get(UFK_HETS_CONTAINER, "").strip()
    if from_env:
        return from_env, None
    if start_container:
        started = HetsContainer()
        started.start()
        return started.name, started
    raise BackendUnavailable(
        "hets: owl_to_tptp needs a Hets CONTAINER to 'docker exec' into, not "
        "just a server URL. Tried, in order:\n"
        "  1. container= — not given\n"
        f"  2. ${UFK_HETS_CONTAINER} — not set\n"
        "Fix one of:\n"
        "  - set $" + UFK_HETS_CONTAINER + " to a running spechub2/hets "
        "container name\n"
        "  - pass container=<name> or container=<HetsContainer>\n"
        "  - call owl_to_tptp(..., start_container=True) to have this kit "
        "start and own one (needs Docker Desktop / a running daemon; image "
        f"{HETS_IMAGE})\n"
        "A remote $UFK_HETS_URL cannot be used instead: the lossy switch "
        "(-Y) exists only on the command line and Hets' REST route has no "
        "equivalent.")


def _exec(docker: str, container: str, command: str, timeout: float) -> Tuple[int, str]:
    """Run one shell command inside the container; return (exit code, console)."""
    argv = [docker, "exec", container, "sh", "-c", command]
    proc = subprocess.run(argv, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


def _hets_command(remote_in: str, remote_out: str, comorphism: str,
                  lossy: bool) -> str:
    """The exact ``hets-server`` command line, as the evidence records it.

    ``hets-server -v2 -a none [-Y] -t <comorphism> -o th,tptp,pp.dol -O <dir> <file>``
    — ``-v2`` so the ``Translated using comorphism`` line is printed at all,
    ``-a none`` so HETS does not try to PROVE anything, and ``-O`` into a
    directory this call owns.

    Three outputs, each for a measured reason. ``tptp`` is the problem itself.
    ``th`` is the translated theory. ``pp.dol`` is the PRETTY-PRINTED SOURCE,
    and it is the only one of the three that carries HETS' ``Prefix: p: <iri>``
    lines: measured on the real ontology, the translated ``.th`` of a TPTP
    chain has ZERO prefix lines (it is a TPTP theory, not an OWL one) while
    ``pp.dol`` has all 15. Without it :attr:`OwlTptpResult.symbols` would
    silently leave every CURIE unexpanded. All three come out of ONE
    ``hets-server`` run — verified live; adding ``pp.dol`` costs no extra
    invocation.
    """
    parts = ["hets-server", "-v2", "-a", "none"]
    if lossy:
        parts.append("-Y")
    parts += ["-t", comorphism, "-o", "th,tptp,pp.dol",
              "-O", remote_out, remote_in]
    return " ".join(parts)


def _refuse_bad_comorphism(comorphism: str) -> None:
    """Refuse the two comorphism spellings that fail silently or abort."""
    if ";" in comorphism:
        raise RuntimeError(
            "hets: Hets could not find the comorphism "
            f"{comorphism!r} (its console says \"Cannot find logic "
            "comorphism\"). On the command line the composition separator is "
            "':' — pass comorphism="
            f"\"{comorphism.replace(';', ':')}\". Hets spells it with ';' in "
            "its own messages; that spelling is not accepted as input.")
    if "SoftFOL" in comorphism:
        raise RuntimeError(
            "hets: owl_to_tptp does not offer the SoftFOL/DFG route: Hets "
            "0.108.0 aborts on CASL numerals "
            "(\"SuleCFOL2SoftFOL.transOPSYMB: unknown op: Qual_op_name 1 "
            "...\", exit 1), which any ontology with a DataHasValue numeral "
            "or a DatatypeRestriction produces. Use "
            "OWL22CASL:CASL2TPTP_FOF.")


def _check_console(run: _Run, comorphism: str) -> None:
    """Turn HETS' known console failures into named refusals."""
    undeclared = tuple(_UNDECLARED_RE.findall(run.console))
    if undeclared:
        listed = "\n".join(f"  - {iri}" for iri in undeclared)
        raise HetsOwlNormalizationError(
            "hets: Hets refuses this ontology because an AnnotationAssertion "
            "names a subject the file never declares. OWL 2 does not require "
            "such a declaration, so this is a Hets restriction, not an error "
            "in the ontology. Hets named:\n"
            f"{listed}\n"
            "(Hets may report only the FIRST one, so this list can be "
            "incomplete — fix these and re-run.)\n"
            "Two remedies, both yours to choose:\n"
            "  - add a Declaration( <Kind>( <iri> ) ) for each IRI above, or\n"
            "  - remove the annotation assertions that name them.\n"
            "This kit will NOT choose the Kind for you: an annotation-only "
            "IRI has no kind stated in the file, and guessing one would put a "
            "symbol into the logical signature on a guess — which changes "
            "what the translated theory means. Nor will it rewrite your "
            "RDF/XML: this kit has no OWL writer and will not grow one to "
            "edit your ontology behind your back.",
            undeclared=undeclared)
    missing = _NO_COMORPHISM_RE.search(run.console)
    if missing:
        raise RuntimeError(
            f"hets: Hets could not find the comorphism {missing.group(1)!r} "
            "(its console says \"Cannot find logic comorphism\"). On the "
            "command line the composition separator is ':' — pass "
            f"comorphism=\"{comorphism}\" spelled with ':'. Hets spells it "
            "with ';' in its own messages; that spelling is not accepted as "
            "input.")


def _sublogic_mismatch(console: str) -> Optional[SublogicMismatch]:
    """HETS' sublogic warning, parsed, or ``None`` if it did not complain."""
    match = _SUBLOGIC_RE.search(console)
    if not match:
        return None
    comorphism, expected, found = match.groups()
    return SublogicMismatch(comorphism=comorphism, expected=expected, found=found)


def _pick_output(run: _Run, suffix: str) -> Tuple[str, str]:
    """The one file with this suffix; never a pick between two.

    Returns ``(basename, text)``.
    """
    candidates = sorted(name for name in run.outputs if name.endswith(suffix))
    if len(candidates) == 1:
        return candidates[0], run.outputs[candidates[0]]
    if not candidates:
        raise RuntimeError(
            f"hets: hets-server exited {run.returncode} and reported a "
            f"translation, but wrote no {suffix} file into {run.out_dir} "
            f"(it wrote {sorted(run.outputs) or 'nothing'}). Its console "
            "was:\n" + run.console)
    raise RuntimeError(
        f"hets: hets-server wrote {len(candidates)} {suffix} files into "
        f"{run.out_dir} ({', '.join(candidates)}) and this helper will not "
        "pick between them — one ontology file should produce one translated "
        "theory. Translate a single-ontology file, or inspect the directory "
        "yourself.")


def _node_from_filename(basename: str, suffix: str) -> str:
    """Recover the development-graph node IRI from HETS' output file name.

    HETS writes ``<stem>_<percent-encoded node IRI><suffix>``, e.g.
    ``oeo-hets_https%3A%2F%2Fopenenergyplatform.org%2Fontology%2Foeo%2F.tptp``.
    """
    import urllib.parse

    stem = basename[:-len(suffix)] if basename.endswith(suffix) else basename
    _, sep, encoded = stem.partition("_")
    return urllib.parse.unquote(encoded) if sep else stem


def _run_hets(docker: str, container: str, remote_dir: str, remote_in: str,
              comorphism: str, lossy: bool, timeout: float) -> _Run:
    """One translation attempt, with its own output directory, read back."""
    out_dir = posixpath.join(remote_dir, "out_lossy" if lossy else "out_probe")
    command = _hets_command(remote_in, out_dir, comorphism, lossy)
    argv = [docker, "exec", container, "sh", "-c",
            f"mkdir -p {out_dir} && cd {remote_dir} && {command}"]
    proc = subprocess.run(argv, capture_output=True, text=True, timeout=timeout)
    console = (proc.stdout or "") + (proc.stderr or "")
    _code, listing = _exec(docker, container,
                           f"ls -1 {out_dir} 2>/dev/null || true", timeout)
    outputs = {}
    for name in (line.strip() for line in listing.splitlines()):
        if not name:
            continue
        code, text = _exec(docker, container,
                           f"cat {posixpath.join(out_dir, name)}", timeout)
        if code == 0:
            outputs[name] = text
    return _Run(argv=argv, returncode=proc.returncode, console=console,
                out_dir=out_dir, outputs=outputs)


def owl_to_tptp(path: str, *, lossy: bool = True,
                comorphism: str = "OWL22CASL:CASL2TPTP_FOF",
                container: Union[str, HetsContainer, None] = None,
                start_container: bool = False,
                client: Optional[HetsClient] = None,
                timeout: float = 900.0) -> OwlTptpResult:
    r"""Translate an OWL ontology file to TPTP through ``hets-server``.

    The command line, exactly as the evidence records it working::

        hets-server -v2 -a none [-Y] -t <comorphism> -o th,tptp -O <dir> <file>

    Args:
        path: a local OWL file (RDF/XML or functional syntax — whatever HETS
            reads). It is copied into the container and removed again.
        lossy: ``True`` (the default) runs the NON-LOSSY translation first as
            a probe and only falls back to ``-Y`` when HETS complains about
            the sublogic, so a loss is always REPORTED on
            :attr:`OwlTptpResult.sublogic_mismatch` rather than being silent.
            Costs a second HETS run; see the module docstring for the
            measured price and the ``client=`` alternative. ``False`` does
            one run and raises
            :class:`~unicode_logic_kit.hets.client.HetsSublogicError` instead.
        comorphism: a HETS comorphism composition, ``:``-separated. The
            ``;`` spelling HETS uses in its own messages is refused by name
            (it exits 0 and silently writes nothing), and any ``SoftFOL``
            target is refused by name too (HETS 0.108.0 aborts on CASL
            numerals).
        container: a running container's name, or a
            :class:`~unicode_logic_kit.hets.docker.HetsContainer`. Falls back
            to ``$UFK_HETS_CONTAINER``.
        start_container: start (and stop) a container owned by this call when
            nothing else is available.
        client: a :class:`~unicode_logic_kit.hets.client.HetsClient` for the
            SAME HETS. Given one, the result also carries
            :attr:`~OwlTptpResult.symbols` and
            :attr:`~OwlTptpResult.omitted_axioms`, computed from ``/dg``.
            Without one both are ``None`` — not empty.
        timeout: seconds for each ``docker exec``.

    Returns:
        An :class:`OwlTptpResult`.

    Raises:
        ~unicode_logic_kit.atp.protocol.BackendUnavailable: no container to
            exec into, or no ``docker`` on PATH.
        ~unicode_logic_kit.hets.client.HetsSublogicError: ``lossy=False`` and
            HETS refused the comorphism for this theory.
        HetsOwlNormalizationError: HETS refused the ontology because an
            annotation subject is undeclared.
        RuntimeError: a bad comorphism spelling, or HETS exited without
            writing a ``.tptp``.
    """
    _refuse_bad_comorphism(comorphism)
    docker = _docker_bin()
    container_name, owned = _resolve_container(container, start_container)
    remote_dir = posixpath.join("/tmp", f"ufk_owl_to_tptp_{uuid.uuid4().hex[:12]}")
    local_name = os.path.basename(path) or "ontology.owl"
    remote_in = posixpath.join(remote_dir, local_name)
    try:
        _exec(docker, container_name, f"mkdir -p {remote_dir}", timeout)
        copy = subprocess.run(
            [docker, "cp", path, f"{container_name}:{remote_in}"],
            capture_output=True, text=True, timeout=timeout)
        if copy.returncode != 0:
            raise RuntimeError(
                f"hets: `docker cp {path} {container_name}:{remote_in}` failed "
                f"(exit {copy.returncode}): "
                f"{(copy.stderr or '').strip()!r}")

        probe = _run_hets(docker, container_name, remote_dir, remote_in,
                          comorphism, lossy=False, timeout=timeout)
        _check_console(probe, comorphism)
        mismatch = _sublogic_mismatch(probe.console)
        translated = _TRANSLATED_RE.search(probe.console)

        if translated and not mismatch:
            run, used_lossy = probe, False
        elif not lossy:
            if mismatch:
                raise HetsSublogicError(
                    "hets: Hets refuses the comorphism "
                    f"{mismatch.comorphism!r} for this ontology — it covers "
                    f"sublogic {mismatch.expected!r} but the theory is "
                    f"{mismatch.found!r}, so hets-server kept the "
                    "UNTRANSLATED theory and wrote no .tptp. Pass lossy=True "
                    "to run hets-server -Y, which translates anyway and "
                    "reports the axioms it omitted on the result's "
                    ".omitted_axioms.",
                    comorphism=mismatch.comorphism,
                    expected=mismatch.expected, found=mismatch.found,
                    body=probe.console)
            run, used_lossy = probe, False
        else:
            run = _run_hets(docker, container_name, remote_dir, remote_in,
                            comorphism, lossy=True, timeout=timeout)
            _check_console(run, comorphism)
            used_lossy = True
            translated = _TRANSLATED_RE.search(run.console)

        if not translated:
            raise RuntimeError(
                f"hets: hets-server exited {run.returncode} but wrote no "
                ".tptp into the output directory and its console does not "
                "contain \"Translated using comorphism\" — Hets keeps the "
                "UNTRANSLATED theory and only warns. Its console was:\n"
                + run.console)
        tptp_name, tptp_text = _pick_output(run, ".tptp")
        try:
            _theory_name, theory_text = _pick_output(run, ".th")
        except RuntimeError:
            theory_text = ""
        try:
            _pretty_name, pretty_text = _pick_output(run, ".pp.dol")
        except RuntimeError:
            pretty_text = ""
        node = _node_from_filename(tptp_name, ".tptp")

        symbols = None
        omitted = None
        if client is not None:
            with open(path, encoding="utf-8") as handle:
                iri = client.upload(handle.read(), local_name)
            dg = client.dg(iri)
            # pp.dol first: it is the SOURCE rendering and the only output
            # that carries the Prefix: lines. The translated .th is tried as
            # a fallback for a comorphism whose target keeps them.
            prefixes = hets_prefixes(pretty_text) or hets_prefixes(theory_text)
            symbols = hets_symbol_table(dg, tptp_text, prefixes=prefixes)
            omitted = untranslated_axioms(dg, tptp_text)

        return OwlTptpResult(
            tptp=tptp_text,
            node=node,
            comorphism=translated.group(1),
            lossy=used_lossy,
            sublogic_mismatch=mismatch,
            console=run.console,
            theory=theory_text,
            pretty=pretty_text,
            symbols=symbols,
            omitted_axioms=omitted,
        )
    finally:
        # Never leave anything behind in a container this kit does not own,
        # and never write outside /tmp.
        try:
            _exec(docker, container_name, f"rm -rf {remote_dir}", timeout)
        except Exception:
            pass
        if owned is not None:
            owned.stop()
