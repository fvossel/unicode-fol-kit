"""Drive the Attempto Parsing Engine (APE) — ACE text in, kit formulas out.

`Attempto Controlled English <https://github.com/Attempto/APE>`_ (ACE) is a
controlled natural language with exactly one reading per sentence: ambiguity is
resolved by CONVENTION (documented interpretation rules), not by a guesser. Its
reference parser APE translates ACE into a Discourse Representation Structure
and, from there, into several formats including TPTP. This module runs APE as a
subprocess and routes its TPTP output through the kit's own reader
(:func:`unicode_fol_kit.fol.tptp_input.parse_tptp`).

APE is DRIVEN, not reimplemented, for the same reason the kit drives Isabelle,
E and HETS instead of cloning them: a partial re-implementation of APE's DCG
grammar, lexicon and anaphora resolution would not be ACE — it would be an
ACE-shaped language with undocumented differences, which is the worst possible
property for a tool whose entire point is that the interpretation rules are
fixed. APE is LGPL and stays an external binary; nothing of it is vendored.

Version pin
-----------
Everything measured in this module and recorded in the test fixtures comes from
APE at commit ``5f4d5354a45fb772763bf1a9543f508f15b28982`` (2024-04-21, the
Attempto/APE default branch), built with ``make install`` under SWI-Prolog
(8.4.2 and 9.x both work; the saved state is bound to the exact SWI-Prolog
that built it, which is why CI rebuilds APE instead of caching the binary —
the build is seconds, unlike E's minutes-long C build). Bump the pin and the
fixtures together or not at all; the fixture filename carries the commit.

What one APE call looks like
-----------------------------
``ape.exe -text "..." -cdrs -ctptp`` prints one XML document::

    <apeResult>
      <duration .../>
      <drs>drs([A],[predicate(A,wait,named('John'))-1/2])</drs>
      <tptp>fof(f1, axiom, (? [A] : (predicate1(A,wait,'John')))).</tptp>
      <messages/>
    </apeResult>

and the three outcomes this module distinguishes are all visible in it
(measured, not assumed — each of these is pinned by a recorded fixture):

- **accepted, TPTP available**: non-empty ``<tptp>``. Event predicates come
  out arity-marked (``predicate1`` intransitive, ``predicate2`` transitive,
  ``predicate3`` ditransitive), simple singular nouns are prettified to unary
  predicates (``man(A)``), proper names become quoted constants (``'John'``).
- **accepted, TPTP unavailable**: non-trivial ``<drs>`` but EMPTY ``<tptp>``.
  In XML mode that refusal is SILENT — nothing on stderr (measured); only a
  ``-solo tptp`` call prints the reason, e.g. ``ERROR: DRS condition not
  supported: must: tptp/4: must(drs(...))``, so this module makes one extra
  ~20 ms call on exactly this path to harvest it (never on the happy path).
  This is Attempto's own translator declining, and
  it is exactly the set of constructs the kit can do better with than plain
  FOL: the four modal boxes (``must``/``can``/``should``/``may``), negation
  as failure (``~``, "it is not provable that"), ``question(...)`` and
  ``command(...)`` boxes. Routing those into the kit's modal family is
  milestone ACE-3; until then they surface as
  :class:`AceTptpUnsupportedError` carrying the DRS text.
- **not ACE**: ``<messages>`` holds ``importance="error"`` entries with the
  sentence number, the failing token, and often a repair suggestion; the DRS
  is the trivial ``drs([],[])``. APE's exit code is 0 in EVERY one of these
  cases, so exit codes decide nothing here — the XML does.

One caveat the numbers force on us: a non-trivial cardinality SURVIVES the
TPTP route but only reified — "At least 3 men wait." becomes
``? [A,B] : predicate1(A,wait,B) & object(B,man,countable,na,geq,3)``, a
single witness ``B`` plus an inert 6-ary annotation. As kit-level FOL that
does NOT mean "at least three": :func:`ace_coverage` flags such sentences
(``reified_cardinality=True``) rather than letting the under-translation
pass silently; the honest Count-based translation landed with ACE-4/5 on
the DRS and formula routes (:mod:`unicode_fol_kit.ace.mapping`,
:mod:`unicode_fol_kit.ace.translate`) — this route keeps Attempto's own
export verbatim, flag included.

Discovery
---------
Same contract as ``atp.eprover_backend``: ``$UFK_APE_CMD`` (prefix ``wsl:``
to force the WSL route, e.g. ``wsl:/home/me/APE/ape.exe``) → native
``ape.exe``/``ape`` on PATH → ``wsl.exe which ape.exe`` → finally
``$HOME/APE/ape.exe`` inside WSL, because ``git clone … ~/APE && make
install`` is the documented build and probing its default location makes a
fresh build work with zero configuration. Only the binary probes are cached;
the env override is read fresh on every call so a test can monkeypatch it.

The user lexicon is passed as TEXT (``-ulextext``), not as a file: a Windows
file path is meaningless inside WSL, and translating paths (``wslpath``) for
a lexicon that is typically a handful of generated lines buys nothing over
handing APE the lines themselves.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import xml.etree.ElementTree as _ET
from dataclasses import dataclass, field
from typing import List, Optional, Sequence, Tuple

from ..fol.nodes import Node

__all__ = [
    "ape_available", "run_ape", "ace_to_fol", "ace_coverage",
    "ApeResult", "ApeMessage", "CoverageRow",
    "AceError", "ApeUnavailableError", "AceParseError",
    "AceTptpUnsupportedError", "AceTptpUnreadError",
]

#: The APE commit everything here was measured against (see module docstring).
APE_PINNED_COMMIT = "5f4d5354a45fb772763bf1a9543f508f15b28982"

#: The DRS of an empty (or entirely rejected) text — APE's "nothing".
_TRIVIAL_DRS = "drs([],[])"


class AceError(Exception):
    """Base class for everything this module raises on purpose."""


class ApeUnavailableError(AceError):
    """No APE binary reachable (env, PATH, WSL) — see the module docstring."""


class AceParseError(AceError):
    """The text is not ACE. ``messages`` carries APE's own diagnosis:
    sentence number, failing token, and (for unknown words) a repair
    suggestion — surfaced verbatim because APE's repair hints ("waitz" →
    "wait") are the single most useful thing to show a caller."""

    def __init__(self, message: str, messages: Tuple["ApeMessage", ...]):
        super().__init__(message)
        self.messages = messages


class AceTptpUnsupportedError(AceError):
    """The text IS ACE but Attempto's own TPTP translator cannot express it
    (modal boxes, negation as failure, questions, commands — see the module
    docstring). ``drs`` carries APE's DRS term so a caller — and, from
    milestone ACE-3 on, the kit's own DRS reader — can still work with the
    sentence; ``reason`` is APE's stderr line naming the unsupported
    condition."""

    def __init__(self, message: str, drs: str, reason: str):
        super().__init__(message)
        self.drs = drs
        self.reason = reason


class AceTptpUnreadError(AceError):
    """APE DID produce TPTP, but the kit's TPTP reader does not accept it.

    The measured case: "1 + 2 = 3." comes out as ``fof(f1, axiom, (1+2=3)).``
    — infix arithmetic over plain integers, which is neither standard FOF
    (that would be TFA's ``$sum``) nor inside the fragment
    :func:`unicode_fol_kit.fol.tptp_input.parse_tptp` covers. Arithmetic
    reaches the kit in milestone ACE-4 through the DRS (``formula``/``expr``
    conditions → the z3_arith fragment), not by teaching the TPTP reader
    Attempto's private dialect. ``tptp`` carries APE's raw output, ``cause``
    the reader's error.
    """

    def __init__(self, message: str, tptp: str, cause: Exception):
        super().__init__(message)
        self.tptp = tptp
        self.cause = cause


@dataclass(frozen=True)
class ApeMessage:
    """One ``<message>`` element from APE's output.

    ``importance`` is ``"error"`` or ``"warning"``; ``type`` is APE's own
    category (``"word"``, ``"sentence"``, ...). ``sentence``/``token`` are
    ``None`` when APE printed them empty (word-level messages carry no token
    index). ``repair`` is APE's suggestion and may be empty.
    """

    importance: str
    type: str
    sentence: Optional[int]
    token: Optional[int]
    value: str
    repair: str

    @property
    def is_error(self) -> bool:
        return self.importance == "error"


@dataclass(frozen=True)
class ApeResult:
    """One APE run, undigested: the raw DRS term, the raw TPTP text, every
    message, and stderr (where APE reports TPTP-translator gaps)."""

    drs: str
    tptp: str
    messages: Tuple[ApeMessage, ...]
    stderr: str

    @property
    def error_messages(self) -> Tuple[ApeMessage, ...]:
        return tuple(m for m in self.messages if m.is_error)

    @property
    def accepted(self) -> bool:
        """True iff APE parsed the whole text as ACE (no error messages)."""
        return not self.error_messages

    @property
    def tptp_supported(self) -> bool:
        """True iff Attempto's own TPTP translator produced output."""
        return bool(self.tptp.strip())


# (argv-prefix, use_wsl) — or None when nothing was found. Cached because
# discovery may spawn WSL probe processes; the env override is NOT cached.
_DISCOVERY_CACHE: dict = {}


def _probe_wsl(argv: Sequence[str]) -> Optional[str]:
    """Run a short WSL probe; first stdout line or None. Never raises."""
    try:
        result = subprocess.run(list(argv), capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=15)
    except (OSError, subprocess.TimeoutExpired):
        return None
    line = (result.stdout or "").strip().splitlines()
    return line[0] if result.returncode == 0 and line else None


def _discover() -> Optional[Tuple[List[str], bool]]:
    """Resolve APE to ``(argv_prefix, use_wsl)``, or ``None``.

    ``argv_prefix`` is what to put before APE's own arguments — either
    ``[command]`` natively or ``["wsl.exe", "-e", command]``. ``-e`` matters:
    without it wsl.exe hands the command line to the default LOGIN SHELL,
    which re-parses quoting, and ACE text is full of apostrophes ("John's
    dog"); ``-e`` executes the binary directly with argv passed verbatim.
    """
    override = os.environ.get("UFK_APE_CMD")
    if override:
        if override.startswith("wsl:"):
            return (["wsl.exe", "-e", override[4:]], True)
        return ([override], False)
    if "probe" in _DISCOVERY_CACHE:
        return _DISCOVERY_CACHE["probe"]
    found: Optional[Tuple[List[str], bool]] = None
    for name in ("ape.exe", "ape"):
        native = shutil.which(name)
        if native:
            found = ([native], False)
            break
    if found is None:
        # The documented build location (`git clone … ~/APE && make install`
        # leaves ape.exe in the checkout) — probed so a fresh build works
        # with zero configuration. Natively first (a Linux/macOS home), then
        # the same two probes inside WSL (a Windows host driving a WSL
        # build; on a wsl.exe-less machine the probes fail fast to None).
        home_build = os.path.join(os.path.expanduser("~"), "APE", "ape.exe")
        if os.access(home_build, os.X_OK):
            found = ([home_build], False)
    if found is None:
        path = _probe_wsl(["wsl.exe", "-e", "sh", "-c", "which ape.exe"])
        if path is None:
            path = _probe_wsl(["wsl.exe", "-e", "sh", "-c",
                               'test -x "$HOME/APE/ape.exe" && echo "$HOME/APE/ape.exe"'])
        if path is not None:
            found = (["wsl.exe", "-e", path], True)
    _DISCOVERY_CACHE["probe"] = found
    return found


def ape_available() -> bool:
    """Pure discovery: is an APE binary reachable (env, PATH, or WSL)?"""
    return _discover() is not None


def _parse_ape_xml(stdout: str) -> Tuple[str, str, Tuple[ApeMessage, ...]]:
    """``<apeResult>`` XML → ``(drs, tptp, messages)``; raises on non-XML."""
    try:
        root = _ET.fromstring(stdout)
    except _ET.ParseError as exc:
        raise RuntimeError(
            f"APE printed something that is not the expected <apeResult> "
            f"XML — broken installation or changed CLI? First 200 chars: "
            f"{stdout[:200]!r}") from exc

    def _index(raw: Optional[str]) -> Optional[int]:
        return int(raw) if raw and raw.isdigit() else None

    messages = tuple(
        ApeMessage(
            importance=m.get("importance", ""),
            type=m.get("type", ""),
            sentence=_index(m.get("sentence")),
            token=_index(m.get("token")),
            value=m.get("value", ""),
            repair=m.get("repair", ""),
        )
        for m in root.iter("message"))
    drs = (root.findtext("drs") or "").strip()
    tptp = (root.findtext("tptp") or "").strip()
    return drs, tptp, messages


def run_ape(text: str, *, ulex: Optional[str] = None, guess: bool = False,
            timeout: float = 30.0) -> ApeResult:
    """Run APE on ``text``; the undigested :class:`ApeResult`.

    ``ulex`` is user-lexicon TEXT in APE's ``-ulextext`` format (one Prolog
    clause per line, e.g. ``noun_sg(molecule, molecule, neutr).``) — see the
    module docstring for why there is no file variant. ``guess=True`` turns
    on APE's unknown-word guessing; it defaults to off because guessing
    trades the "not ACE" verdict for a silently different lexicon, and this
    kit's callers want the verdict.

    Raises :class:`ApeUnavailableError` when discovery finds no binary, and
    ``subprocess.TimeoutExpired`` when APE (a ~20 ms tool, measured) blows a
    ``timeout`` that generous — at which point something is genuinely wrong
    with the installation, not with the text.
    """
    found = _discover()
    if found is None:
        raise ApeUnavailableError(
            "ape: no binary found ($UFK_APE_CMD, PATH, WSL, ~/APE/ape.exe). "
            "Build one: git clone https://github.com/Attempto/APE ~/APE && "
            f"cd ~/APE && git checkout {APE_PINNED_COMMIT[:7]} && make install "
            "(needs swi-prolog).")
    prefix, _use_wsl = found
    argv = [*prefix, "-text", text, "-cdrs", "-ctptp"]
    if ulex is not None:
        argv += ["-ulextext", ulex]
    if guess:
        argv += ["-guess"]
    result = subprocess.run(argv, capture_output=True, text=True,
                            encoding="utf-8", errors="replace",
                            timeout=timeout)
    drs, tptp, messages = _parse_ape_xml(result.stdout or "")
    return ApeResult(drs=drs, tptp=tptp, messages=messages,
                     stderr=(result.stderr or "").strip())


# APE at the pinned commit has one pretty-printer bug in its TPTP output:
# in a COLLECTIVE reading ("John and Mary lift a table.") the noun atom for
# the lifted object is printed juxtaposed — ``(table C)`` — instead of
# applied — ``table(C)`` — while every other sentence shape prints ``man(A)``
# correctly. The intent is unambiguous (there is no legal TPTP in which a
# lower-word is followed by a bare variable inside parentheses, so this
# pattern can ONLY match APE's malformation, never legal output), hence the
# repair below rather than a refusal. The raw, unrepaired text stays
# available on :class:`ApeResult`; :class:`CoverageRow` reports the repair.
_JUXTAPOSED_ATOM = re.compile(r"\(([a-z][a-zA-Z0-9_]*) ([A-Z][A-Za-z0-9]*)\)")


def _repair_ape_tptp(tptp: str) -> Tuple[str, int]:
    """``(table C)`` → ``(table(C))``; returns (text, number of repairs)."""
    return _JUXTAPOSED_ATOM.subn(r"(\1(\2))", tptp)


def _formulas_from(result: ApeResult) -> Tuple[List[Node], bool]:
    """TPTP text of an accepted result → kit formulas, plus whether the
    upstream-bug repair above had to fire.

    Role guard: a yes/no question ("Does John wait?") survives APE's TPTP
    route — as ``fof(f1, conjecture, …)``, a statement to PROVE (measured;
    wh-questions do not survive at all, their ``query/2`` condition is
    refused). :func:`ace_to_fol` returns assertions, and dropping the role
    would silently turn the question into the claim that John waits — so a
    non-axiom role raises instead, same category as the constructs Attempto
    itself refuses."""
    from ..fol.tptp_input import TptpParsingError, parse_tptp

    tptp_text, n_repairs = _repair_ape_tptp(result.tptp)
    try:
        parsed = parse_tptp(tptp_text)
    except TptpParsingError as exc:
        raise AceTptpUnreadError(
            f"APE produced TPTP the kit reader does not accept: {exc} — "
            "raw output on .tptp (arithmetic reaches the kit via the DRS "
            "in milestone ACE-4)",
            tptp=result.tptp, cause=exc) from exc
    non_axiom = [tf for tf in parsed if tf.role != "axiom"]
    if non_axiom:
        raise AceTptpUnsupportedError(
            "the text contains a yes/no question: APE renders it as "
            f"fof role {non_axiom[0].role!r} — a statement to PROVE, which "
            "ace_to_fol must not flatten into an assertion (question "
            "routing is milestone ACE-3); the DRS is on .drs",
            drs=result.drs,
            reason=f"non-axiom fof role {non_axiom[0].role!r} "
                   f"({len(non_axiom)} of {len(parsed)} clauses)")
    return [tf.formula for tf in parsed], n_repairs > 0


def ace_to_fol(text: str, *, ulex: Optional[str] = None,
               guess: bool = False, timeout: float = 30.0) -> List[Node]:
    """ACE text → kit formulas, via APE's own TPTP output.

    Returns one :class:`~unicode_fol_kit.fol.nodes.Node` per ``fof`` clause
    APE emitted, in order. APE materializes cross-sentence anaphora into the
    clauses themselves, so the formulas are self-contained; an empty text
    yields ``[]``.

    Symbol conventions are the TPTP reader's, documented there: predicates
    upper-cased into the kit convention (``man`` → ``Man``, and events keep
    APE's arity marker: ``Predicate1``/``Predicate2``/``Predicate3``),
    quoted proper names read as constants.

    Raises:
        AceParseError: the text is not ACE (carries APE's messages).
        AceTptpUnsupportedError: the text is ACE, but its DRS uses a
            condition Attempto's own TPTP translator refuses — modality,
            negation as failure, a question or a command (carries the DRS
            and APE's stderr reason). These become kit-expressible in
            milestone ACE-3, not silently mistranslated today.
        ApeUnavailableError: no APE binary reachable.
    """
    return _ace_to_fol_detailed(text, ulex=ulex, guess=guess,
                                timeout=timeout)[0]


def _ace_to_fol_detailed(text: str, *, ulex: Optional[str], guess: bool,
                         timeout: float) -> Tuple[List[Node], bool]:
    """:func:`ace_to_fol` plus the did-the-upstream-bug-repair-fire bit,
    which :func:`ace_coverage` reports and the public signature drops."""
    result = run_ape(text, ulex=ulex, guess=guess, timeout=timeout)
    if not result.accepted:
        first = result.error_messages[0]
        where = (f"sentence {first.sentence}" if first.sentence is not None
                 else "input")
        hint = f" (repair hint: {first.repair!r})" if first.repair else ""
        raise AceParseError(
            f"not ACE at {where}: {first.value!r}{hint} — "
            f"{len(result.error_messages)} error message(s) in .messages",
            result.error_messages)
    if not result.tptp_supported:
        if result.drs == _TRIVIAL_DRS:
            return [], False  # empty text: nothing asserted
        reason = result.stderr or _tptp_refusal_reason(text, ulex=ulex,
                                                       guess=guess,
                                                       timeout=timeout)
        raise AceTptpUnsupportedError(
            "ACE accepted, but Attempto's TPTP translator does not cover "
            f"this construct: {reason or 'reason not reported'} — the DRS "
            "is on .drs (modality/naf/question/command routing is "
            "milestone ACE-3)",
            drs=result.drs, reason=reason)
    return _formulas_from(result)


def _tptp_refusal_reason(text: str, *, ulex: Optional[str], guess: bool,
                         timeout: float) -> str:
    """One ``-solo tptp`` call, stderr only — the refusal reason.

    In XML mode APE's TPTP translator declines SILENTLY (empty ``<tptp>``,
    empty stderr — measured); the diagnostic line naming the unsupported
    condition (``must``, ``query/2``, ``~``, ``command``) is printed only in
    solo mode. Runs exclusively on the already-failed path, so the happy
    path stays a single process spawn. Never raises: worst case is an empty
    reason on an exception that is being raised anyway.
    """
    found = _discover()
    if found is None:
        return ""
    prefix, _use_wsl = found
    argv = [*prefix, "-text", text, "-solo", "tptp"]
    if ulex is not None:
        argv += ["-ulextext", ulex]
    if guess:
        argv += ["-guess"]
    try:
        result = subprocess.run(argv, capture_output=True, text=True,
                                encoding="utf-8", errors="replace",
                                timeout=timeout)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return (result.stderr or "").strip()


@dataclass(frozen=True)
class CoverageRow:
    """One corpus sentence's fate on the APE → TPTP → kit route.

    ``status`` is one of ``"ok"`` (kit formulas produced),
    ``"tptp_unsupported"`` (ACE, but Attempto's TPTP translator declined —
    detail carries the stderr reason), ``"tptp_unread"`` (ACE and TPTP
    produced, but outside the kit reader's fragment — Attempto's infix
    arithmetic, see :class:`AceTptpUnreadError`), ``"not_ace"`` (rejected —
    detail carries APE's first error), or ``"infra"`` (APE itself failed).
    ``reified_cardinality`` is the honesty flag from the module docstring:
    the TPTP contains a reified ``object(...)`` atom, so a plural/cardinality
    was under-translated by Attempto's own export and the kit formula does
    NOT carry its intended counting force (the DRS and formula routes do,
    since ACE-4/5).
    ``tptp_repaired`` reports that the juxtaposed-atom repair (see
    ``_JUXTAPOSED_ATOM``) had to fire on APE's raw TPTP.
    """

    sentence: str
    status: str
    reified_cardinality: bool = False
    tptp_repaired: bool = False
    detail: str = ""
    formulas: Tuple[Node, ...] = field(default=())


def ace_coverage(sentences: Sequence[str], *, ulex: Optional[str] = None,
                 timeout: float = 30.0) -> List[CoverageRow]:
    """Classify each sentence's fate on the TPTP route — the ACE-1 report.

    Mechanical, one APE call per sentence (~20 ms each, measured): no
    judgment calls beyond the three-way outcome split plus the
    ``reified_cardinality`` flag, both defined at :class:`CoverageRow`.
    """
    rows: List[CoverageRow] = []
    for sentence in sentences:
        try:
            formulas, repaired = _ace_to_fol_detailed(
                sentence, ulex=ulex, guess=False, timeout=timeout)
        except AceParseError as exc:
            first = exc.messages[0]
            rows.append(CoverageRow(sentence, "not_ace",
                                    detail=f"{first.value!r}"
                                           + (f" -> {first.repair!r}"
                                              if first.repair else "")))
        except AceTptpUnsupportedError as exc:
            rows.append(CoverageRow(sentence, "tptp_unsupported",
                                    detail=exc.reason))
        except AceTptpUnreadError as exc:
            rows.append(CoverageRow(sentence, "tptp_unread",
                                    detail=str(exc.cause).splitlines()[0]))
        except (RuntimeError, subprocess.TimeoutExpired) as exc:
            rows.append(CoverageRow(sentence, "infra", detail=str(exc)))
        else:
            rows.append(CoverageRow(sentence, "ok",
                                    reified_cardinality=_has_reified_object(formulas),
                                    tptp_repaired=repaired,
                                    formulas=tuple(formulas)))
    return rows


def _has_reified_object(formulas: Sequence[Node]) -> bool:
    """True iff any formula contains a reified ``Object`` atom — Attempto's
    TPTP export keeps ``object/6`` verbatim exactly when it could not
    prettify a noun phrase into a unary predicate (any cardinality other
    than a simple singular), so this atom's presence IS the
    under-translation marker :class:`CoverageRow` documents."""
    from ..fol.nodes import Atom

    return any(isinstance(sub, Atom) and sub.predicate == "Object"
               for formula in formulas for sub in formula.walk())
