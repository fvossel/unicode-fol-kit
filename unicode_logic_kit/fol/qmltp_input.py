"""QMLTP input: read QMLTP (Quantified Modal Logic Theorem Proving library) ``.p``
problems into the kit AST.

QMLTP (Raths & Otten, "Building a Problem Library for First-Order Modal
Logics", TABLEAUX 2009; Raths & Otten, "The QMLTP Problem Library for
First-Order Modal Logics", CADE 2012) is a 600-problem benchmark for
first-order modal logic, in an extension of plain TPTP ``fof`` syntax. This
is a SEPARATE, only loosely-related dialect from NXF (see
:mod:`unicode_logic_kit.atp.tptp_ncl`): QMLTP predates NXF, uses its own
statement keyword and unary modal connectives, and records a problem's
per-logic/per-domain-regime status in a structured comment header rather than
NXF's ``$modal``/``$domains`` logic-specification statement.

Verified DIRECTLY against the real library (downloaded and inspected
2026-09-18 from ``https://www.iltp.de/qmltp/download/QMLTP-v1.1.tar.gz`` —
see "License" below) before writing a line of this module, rather than
assumed from the roadmap description that named this module, which turned
out to describe QMLTP's syntax and header format INCORRECTLY in two ways
corrected here (see the deviations noted at each point):

* **Statement keyword is ``qmf``, not ``fof``.** Every QMLTP problem file's
  formula statements read ``qmf(name, role, formula).`` — literally,
  verbatim, in all 600 problems (confirmed: ``grep -c '^qmf('`` across the
  whole library's ``Problems/`` tree returns exactly 600 hits, zero for
  ``^fof(``). This reader therefore accepts ONLY ``qmf(...)``, refusing
  ``fof``/``cnf``/``tff`` (and QMLTP's own ``tpi(...)`` — see below) by
  name.
* **The modal connectives are ``#box``/``#dia`` (a ``#``-prefixed keyword
  applied with ``:``), not the ``box:(...)``/``dia:(...)`` (no ``#``) the
  roadmap item that named this module described** — e.g. SYM002+1.p's
  conjecture reads ``( (#box : ( ! [X] : ( f(X) ) ) ) => ( ! [X] : (#box :
  ( f(X) ) ) ) )``. This is the syntax the grammar extension below actually
  implements.
* **Multi-modal problems (the ``MML`` domain, 20 of the 600) use a
  DIFFERENT top-level statement, ``tpi(1,set_logic,modal([...],[(name,
  system), ...])).``, to declare one or more NAMED modalities before using
  indexed connectives ``#box(name)``/``#dia(name)`` for each** — e.g.
  ``#box(fool)``, ``#box(a)``. This is itself a genuine QMLTP construct
  (unlike the roadmap's guess of a NXF-style integer index), but its
  ``set_logic`` payload (``modal([cumulative,rigid,local], [(fool,s4),
  (a,s4), ...])``) does not fit this reader's reused ``fof``/``tff`` term
  grammar (it needs bracketed lists and name/system pairs as TERMS, which
  plain TPTP terms are not) — refused by name, see "Scope" below, rather
  than guessed at.

Public API: :func:`parse_qmltp_formula` (one bare formula), :func:`parse_qmltp`
/ :func:`load_qmltp` (a whole problem: its formulas AND its parsed header
metadata, combined — see "Deviation from ``fol.tptp_input``'s shape" below),
and the :class:`QmltpFormula` / :class:`QmltpHeader` / :class:`QmltpStatus` /
:class:`QmltpProblem` records they return.

Grammar reuse (per this item's own instructions: reuse
:mod:`unicode_logic_kit.fol.tptp_input`'s Lark grammar rather than rewrite
one). :mod:`fol.tptp_input`'s ``stmt`` production does not hard-code the
statement keyword in the GRAMMAR at all — ``LOWER "(" fof_name "," LOWER ","
formula ...")" "."`` accepts any lower-case keyword, and it is
``_TptpTransformer.stmt`` that checks for ``fof``/``cnf``/``tff`` — so
``qmf(...)`` already parses under the UNMODIFIED base grammar; this module's
:data:`_GRAMMAR` only ADDS four new ``?unary`` alternatives (``#box:(...)``,
``#dia:(...)``, and the indexed forms, refused by name once recognised — see
above) to :data:`fol.tptp_input._GRAMMAR`'s own text, and
:class:`_QmltpTransformer` SUBCLASSES :class:`fol.tptp_input._TptpTransformer`,
inheriting every classical connective/quantifier/atom/term rule UNCHANGED and
overriding only ``stmt`` (accept ``qmf``, not ``fof``/``cnf``/``tff``),
``stmt_type``/``include_stmt`` (QMLTP has neither TFF type declarations nor
``include(...)`` — refused by name), and the four new modal rules. This
reader can therefore never disagree with :mod:`fol.tptp_input` about how to
read a classical connective, quantifier or term — the SAME code decides both.

Scope — the mono-modal alethic fragment only, matching
:mod:`unicode_logic_kit.atp.tptp_ncl`'s own writer-side boundary (see that
module's docstring):

* Supported: ``qmf(name, role, formula).`` statements over
  ¬/∧/∨/→/↔/=/!=, ``!``/``?`` quantifiers (UNSORTED — no QMLTP problem in
  the library uses a typed quantifier; every one reads plain ``! [X] :
  ...``), and the unindexed ``#box``/``#dia`` connectives.
* NOT supported, each raising :class:`NotImplementedError` naming the
  construct (never silently dropped or approximated):
    - ``tpi(...)`` multi-modal ``set_logic`` directives, and the indexed
      ``#box(name)``/``#dia(name)`` connectives that depend on one (the
      ``MML`` domain) — see "the roadmap's guess" note above.
    - ``include(...)`` directives and ``tff(...,type,...)`` declarations —
      neither construct occurs anywhere in the library, so both are refused
      rather than silently mis-parsed if one ever appeared.

License
-------
No redistribution licence for the QMLTP library itself could be found (as of
2026-09-18, neither the v1.1 archive ``QMLTP-v1.1.tar.gz`` nor
``https://www.iltp.de/qmltp/`` states one). This module therefore ships no
QMLTP file: it was developed and checked against the real v1.1 problems, and
the test suite uses small stand-ins written for it in the same syntax and
header layout (``tests/fixtures/qmltp``), each with a hand-derived status
table re-checked against :func:`~unicode_logic_kit.fol.qml.qml_is_valid`. Point
:func:`load_qmltp` at your own copy of the library to read real problems.
"""

import re
from dataclasses import dataclass
from typing import Optional, Tuple

from lark import Lark
from lark.exceptions import VisitError

from .nodes import Node, Box, Diamond
from .naming import ParsingError
from .tptp_input import (
    _GRAMMAR as _TPTP_GRAMMAR, _TptpTransformer, _functor_name,
)

__all__ = [
    "QmltpParsingError", "QmltpFormula", "QmltpStatus", "QmltpHeader",
    "QmltpProblem", "parse_qmltp_formula", "parse_qmltp", "load_qmltp",
]


class QmltpParsingError(ParsingError):
    """A QMLTP import failure, carrying a plain message.

    The exact mirror of :class:`fol.tptp_input.TptpParsingError` — subclasses
    :class:`ParsingError` (so ``except ParsingError`` still catches it) but
    takes a string instead of a Lark exception.
    """

    def __init__(self, message: str):
        self.args = (message,)

    def __str__(self):
        return self.args[0]


# =============================================================================
# Grammar: fol.tptp_input's own grammar text, extended with #box/#dia.
# =============================================================================

# The exact anchor line fol.tptp_input._GRAMMAR uses for its "~" (negation)
# alternative -- the new QMLTP modal alternatives are inserted right after
# it. A drift guard (the count() check below) turns a future, unrelated
# change to that grammar text into a loud ImportError here rather than a
# silent "#box/#dia never actually parse" failure.
_UNARY_ANCHOR = '?unary: "~" unary       -> neg\n'
_QMLTP_UNARY_EXTRA = (
    '      | "#box" ":" "(" formula ")"                -> box\n'
    '      | "#dia" ":" "(" formula ")"                -> dia\n'
    '      | "#box" "(" LOWER ")" ":" "(" formula ")"  -> box_indexed\n'
    '      | "#dia" "(" LOWER ")" ":" "(" formula ")"  -> dia_indexed\n'
)

if _TPTP_GRAMMAR.count(_UNARY_ANCHOR) != 1:
    raise ImportError(
        "fol.qmltp_input: fol.tptp_input's grammar text no longer contains "
        "the exact anchor line this module extends ('?unary: \"~\" unary "
        "-> neg') -- fol.tptp_input.py must have changed; update "
        "_UNARY_ANCHOR in fol/qmltp_input.py to match.")

_GRAMMAR = _TPTP_GRAMMAR.replace(_UNARY_ANCHOR, _UNARY_ANCHOR + _QMLTP_UNARY_EXTRA, 1)


class _QmltpTransformer(_TptpTransformer):
    """Extends :class:`fol.tptp_input._TptpTransformer` with QMLTP's own
    statement keyword and modal connectives.

    Every classical rule (connectives, quantifiers, atoms, terms) is
    inherited UNCHANGED — only the five methods below are new or overridden;
    see the module docstring's "Grammar reuse" section.
    """

    def stmt(self, items):
        """``qmf(name, role, formula).`` -> :class:`QmltpFormula`.

        Anything else at the top level (``fof``/``cnf``/``tff``, or
        QMLTP's own ``tpi(...)`` multi-modal directive — which this
        base grammar cannot even fully parse, see the module docstring's
        "Statement keyword" note, but a short ``tpi(name,...)`` prefix
        CAN reach this far before its payload fails to match `formula`)
        is refused BY NAME.
        """
        keyword = str(items[0])
        if keyword == "tpi":
            raise NotImplementedError(
                "qmltp_input: 'tpi(...)' multi-modal set_logic directives "
                "(the MML domain) are outside this reader's supported "
                "mono-modal fragment -- see module docstring 'Scope'.")
        if keyword != "qmf":
            raise QmltpParsingError(
                f"SYNTAX_ERROR: only 'qmf(...)' statements are QMLTP "
                f"formulas (got '{keyword}(...)').")
        name, role, formula = str(items[1]), str(items[2]), items[3]
        return QmltpFormula(name, role, formula)

    def stmt_type(self, items):
        raise QmltpParsingError(
            "SYNTAX_ERROR: a TFF-style type declaration "
            "('name,type,...') is not part of the QMLTP dialect -- no "
            "problem in the library uses one.")

    def include_stmt(self, items):
        raise QmltpParsingError(
            "SYNTAX_ERROR: include(...) directives are not supported by "
            "this QMLTP reader -- no problem in the library uses one.")

    def box(self, items):
        return Box(items[0])

    def dia(self, items):
        return Diamond(items[0])

    def box_indexed(self, items):
        name = _functor_name(items[0])
        raise NotImplementedError(
            f"qmltp_input: indexed multi-modal '#box({name})' is outside "
            "this reader's supported mono-modal alethic fragment -- see "
            "module docstring 'Scope'. Only the unindexed #box/#dia are "
            "supported in this release.")

    def dia_indexed(self, items):
        name = _functor_name(items[0])
        raise NotImplementedError(
            f"qmltp_input: indexed multi-modal '#dia({name})' is outside "
            "this reader's supported mono-modal alethic fragment -- see "
            "module docstring 'Scope'. Only the unindexed #box/#dia are "
            "supported in this release.")


_FORMULA_PARSER = Lark(_GRAMMAR, start="formula", parser="earley")
_FILE_PARSER = Lark(_GRAMMAR, start="file", parser="earley")
_TRANSFORMER = _QmltpTransformer()


def _parse(text: str, parser: Lark, what: str):
    """Parse + transform with unified error handling (unwrapping lark's
    VisitError) -- the exact mirror of fol.tptp_input._parse."""
    try:
        tree = parser.parse(text)
    except QmltpParsingError:
        raise
    except Exception as exc:
        raise QmltpParsingError(f"SYNTAX_ERROR: could not parse QMLTP {what}: {exc}")
    try:
        return _TRANSFORMER.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        if isinstance(original, (ParsingError, NotImplementedError)):
            raise original
        raise QmltpParsingError(f"SYNTAX_ERROR: in QMLTP {what}: {original}")


# =============================================================================
# Formula / header records
# =============================================================================

@dataclass(frozen=True)
class QmltpFormula:
    """One annotated QMLTP statement: its ``name``, ``role``, and parsed ``formula``."""

    name: str
    role: str
    formula: Node


@dataclass(frozen=True)
class QmltpStatus:
    """One ``(logic, domain) -> verdict`` cell from a QMLTP ``% Status`` table.

    ``logic`` is one of ``"K"``, ``"D"``, ``"T"``, ``"S4"``, ``"S5"``
    (the literal row label QMLTP's header prints — matching
    :mod:`unicode_logic_kit.fol.qml`'s own ``frame=`` names one-to-one, so a
    cell reads straight into ``qml_is_valid(..., frame=status.logic)``);
    ``domain`` is one of ``"varying"``, ``"cumulative"``, ``"constant"``
    (the literal column label — matching ``qml_is_valid``'s ``mode=`` names,
    since ``"cumulative"`` is itself one of :mod:`fol.qml`'s accepted mode
    spellings, an alias of ``"increasing"``); ``verdict`` is the literal
    recorded status string, kept AS-IS (``"Theorem"``, ``"Non-Theorem"``,
    or occasionally ``"Unsolved"``/``"Open"``), never normalised or
    validated against a fixed vocabulary.
    """

    logic: str
    domain: str
    verdict: str


@dataclass(frozen=True)
class QmltpHeader:
    """Metadata recovered from a QMLTP problem file's ``%`` comment header.

    ``file`` / ``domain`` / ``problem`` / ``source`` are ``None`` when the
    corresponding ``% <Field> : ...`` line is absent. ``statuses`` holds
    every ``(logic, domain) -> verdict`` cell of the ``% Status`` table (see
    :class:`QmltpStatus`), in the file's own row/column order; empty if no
    such table was found (e.g. a multi-modal problem's single-line ``%
    Status : Theorem`` form, which this reader does not parse -- see module
    docstring 'Scope', since multi-modal problems are refused before a
    header lookup would matter). ``comments`` holds every raw ``%`` line
    verbatim (stripped of its trailing newline), in source order.
    """

    file: Optional[str]
    domain: Optional[str]
    problem: Optional[str]
    source: Optional[str]
    statuses: Tuple[QmltpStatus, ...]
    comments: Tuple[str, ...]

    def status_for(self, logic: str, domain: str) -> str:
        """The recorded verdict for ``(logic, domain)``, e.g. ``status_for("K",
        "constant")`` -> ``"Theorem"``.

        Raises:
            KeyError: no cell for that exact ``(logic, domain)`` pair was
                recorded (an unknown logic/domain name, or a header this
                reader could not parse a status table from at all).
        """
        for status in self.statuses:
            if status.logic == logic and status.domain == domain:
                return status.verdict
        available = sorted({(s.logic, s.domain) for s in self.statuses})
        raise KeyError(
            f"qmltp_input: no recorded status for logic={logic!r}, "
            f"domain={domain!r} in this header (available: {available}).")


@dataclass(frozen=True)
class QmltpProblem:
    """A whole QMLTP problem: its parsed ``formulas`` plus the recovered ``header``.

    Deviation from :mod:`fol.tptp_input`'s shape: that module splits "just
    the formulas" (:func:`~fol.tptp_input.parse_tptp`, a bare list) from
    "formulas plus header" (:func:`~fol.tptp_input.parse_tptp_problem`, a
    combined record), because a plain TPTP problem's header is optional,
    decorative metadata. A QMLTP problem's header is NOT decorative — it
    carries the per-logic/per-domain ``Theorem``/``Non-Theorem`` status that
    is this whole format's reason for existing (see this item's own
    test_oracle: reading a problem WITHOUT its status is reading half of
    it), so :func:`parse_qmltp` / :func:`load_qmltp` return this combined
    record directly rather than offering a "formulas only" variant nothing
    would realistically use.
    """

    formulas: Tuple[QmltpFormula, ...]
    header: QmltpHeader


def parse_qmltp_formula(text: str) -> Node:
    """Parse a single bare QMLTP formula (no ``qmf(...)`` wrapper) into a Node.

    Args:
        text: a QMLTP formula, e.g. ``"#box : ( ! [X] : ( f(X) ) )"``.

    Returns:
        The formula as a toolkit :class:`Node` (``#box``/``#dia`` become
        :class:`~fol.nodes.Box` / :class:`~fol.nodes.Diamond`; everything
        else parses exactly as :func:`fol.tptp_input.parse_tptp_formula`
        would).

    Raises:
        ParsingError: ``text`` is not a well-formed QMLTP formula.
        NotImplementedError: ``text`` uses an indexed ``#box(...)``/
            ``#dia(...)`` connective — see module docstring 'Scope'.
    """
    return _parse(text, _FORMULA_PARSER, "formula")


# A header field line: optional leading whitespace, '%', optional whitespace,
# one of the four recognised QMLTP field names (matched case-sensitively),
# optional whitespace, ':', optional whitespace, then the rest of the line as
# the raw value. Mirrors fol.tptp_input._HEADER_FIELD_RE, with QMLTP's own
# extra "Source" field and WITHOUT "Status"/"Rating" (QMLTP's Status is a
# multi-row TABLE, not a single value -- parsed separately below).
_QMLTP_FIELD_RE = re.compile(r"^\s*%\s*(File|Domain|Problem|Source)\s*:\s*(.*)$")
# The "% Status   :      varying      cumulative   constant" header line --
# group(1) captures the column (domain-condition) labels, whitespace-joined.
_QMLTP_STATUS_HEADER_RE = re.compile(r"^\s*%\s*Status\s*:\s*(.*)$")
# One status TABLE row: "%             K   Non-Theorem  Theorem      Theorem".
# The row label is restricted to the five logic names QMLTP actually uses,
# so this can never accidentally match the "% Rating :" header line that
# immediately follows the table (its own row label would be "Rating", which
# this pattern does not accept) or a Rating-table row (whose FIRST token
# after the logic-name label is a float, not a Theorem/Non-Theorem word --
# though the label check alone already prevents any bleed-through, since a
# rating row starts "% K 0.50 ..." and IS syntactically a candidate match
# here; the boundary that actually stops the scan is the "% Rating :" HEADER
# line between the two tables, which this pattern does not match at all --
# see _parse_qmltp_header's row-consuming loop).
_QMLTP_STATUS_ROW_RE = re.compile(r"^\s*%\s*(K|D|T|S4|S5)\s+(.*)$")


def _parse_qmltp_header(text: str) -> QmltpHeader:
    """Scan raw QMLTP text for its ``%`` header block, independent of the
    grammar -- the QMLTP counterpart of
    :func:`fol.tptp_input._parse_tptp_header`, with its own regex-based
    parser for the ``% Status`` TABLE (QMLTP's header shape, verified
    directly against the real library, is a multi-row/multi-column table,
    not the single ``% Status : Theorem`` line a plain TPTP problem or the
    roadmap description that named this module would suggest -- see module
    docstring).

    Every line whose first non-whitespace character is ``%`` is collected
    verbatim (trailing newline stripped) into ``comments``, in source
    order. Among those: a ``File``/``Domain``/``Problem``/``Source`` field
    line populates the matching :class:`QmltpHeader` attribute (first
    occurrence wins); the FIRST ``% Status :`` line starts the status-table
    scan, which reads the header's own column (domain-condition) labels and
    then consumes every immediately-following ``% <logic> <verdict>...``
    row, stopping at the first ``%`` line that is not one (the blank ``%``
    separator that precedes ``% Rating`` in every problem checked, though
    the row pattern's restriction to the five known logic names would stop
    it there regardless -- see :data:`_QMLTP_STATUS_ROW_RE`).

    Args:
        text: the raw contents of a QMLTP problem file (or any QMLTP text).

    Returns:
        A :class:`QmltpHeader`; every field is ``None``, ``statuses`` is
        ``()`` and ``comments`` is ``()`` if the text has no ``%`` lines at
        all (or none matching the recognised shapes).
    """
    comments = []
    fields = {}
    statuses = []
    lines = text.splitlines()
    i, n = 0, len(lines)
    status_table_seen = False
    while i < n:
        line = lines[i]
        if not line.lstrip().startswith("%"):
            i += 1
            continue
        comments.append(line)

        field_match = _QMLTP_FIELD_RE.match(line)
        if field_match:
            field, value = field_match.group(1), field_match.group(2)
            if field not in fields:
                fields[field] = value.strip()
            i += 1
            continue

        status_header_match = _QMLTP_STATUS_HEADER_RE.match(line)
        if status_header_match and not status_table_seen:
            status_table_seen = True
            domain_names = status_header_match.group(1).split()
            i += 1
            while i < n:
                row_line = lines[i]
                if not row_line.lstrip().startswith("%"):
                    break
                row_match = _QMLTP_STATUS_ROW_RE.match(row_line)
                if not row_match:
                    break
                comments.append(row_line)
                logic = row_match.group(1)
                tokens = row_match.group(2).split()
                for domain_name, verdict in zip(domain_names, tokens):
                    statuses.append(QmltpStatus(logic, domain_name, verdict))
                i += 1
            continue

        i += 1

    return QmltpHeader(
        file=fields.get("File"),
        domain=fields.get("Domain"),
        problem=fields.get("Problem"),
        source=fields.get("Source"),
        statuses=tuple(statuses),
        comments=tuple(comments),
    )


# A top-level "tpi(...)" statement's own payload (a bracketed
# name/system-pair list, e.g. "modal([cumulative,rigid,local],
# [(fool,s4),(a,s4)])") does not fit this reader's reused fof/tff TERM
# grammar at all (a "[...]" list or a "(name,system)" pair is not a legal
# TPTP term) -- so a real multi-modal file fails to parse with a generic,
# unhelpful "no terminal matches '['" syntax error before _QmltpTransformer
# .stmt ever runs (that method's own "keyword == 'tpi'" check is kept as a
# defensive fallback for the rare tpi(...) whose payload WOULD otherwise
# parse). This cheap pre-scan catches the real construct up front and
# refuses it BY NAME instead.
# (?:^|(?<=\r)): a line also starts after a bare CR, which (?m)^ ignores.
_TPI_STATEMENT_RE = re.compile(r"(?:^|(?<=\r))\s*tpi\s*\(", re.MULTILINE)


def parse_qmltp(text: str) -> QmltpProblem:
    """Parse a whole QMLTP problem into its formulas *and* its header metadata.

    Args:
        text: the contents of a QMLTP problem file — one or more
            ``qmf(...)`` statements (``%`` line comments are ignored by the
            grammar; the header scan below reads them independently).

    Returns:
        A :class:`QmltpProblem` with ``formulas`` (in source order) and
        ``header``.

    Raises:
        ParsingError: ``text`` is not a well-formed QMLTP problem.
        NotImplementedError: ``text`` uses a construct outside this
            reader's supported fragment (a ``tpi(...)`` multi-modal
            directive, or an indexed ``#box(...)``/``#dia(...)``
            connective) — see module docstring 'Scope'.
    """
    if _TPI_STATEMENT_RE.search(text):
        raise NotImplementedError(
            "qmltp_input: 'tpi(...)' multi-modal set_logic directives (the "
            "MML domain) are outside this reader's supported mono-modal "
            "fragment -- see module docstring 'Scope'.")
    items = _parse(text, _FILE_PARSER, "problem")
    return QmltpProblem(formulas=tuple(items), header=_parse_qmltp_header(text))


def load_qmltp(path: str) -> QmltpProblem:
    """Read a QMLTP problem file and :func:`parse_qmltp` its contents.

    Args:
        path: path to a ``.p`` QMLTP problem file, read as UTF-8.

    Returns:
        A :class:`QmltpProblem`.
    """
    with open(path, "r", encoding="utf-8") as handle:
        text = handle.read()
    return parse_qmltp(text)
