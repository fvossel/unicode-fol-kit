"""Dialect detection for formula text — the single source of truth.

:func:`unicode_fol_kit.api.parse_any` auto-detects which surface syntax a
formula text is written in before parsing it. The detection ORDER is
load-bearing (a Prover9 formula also contains ``->`` which the unicode
ladder would half-read; SMT-LIB text is full of parentheses every other
grammar chokes on), so it lives here as one pure, importable, testable
function instead of an if-cascade buried in the facade. ``parse_any``
consumes exactly this candidate list; nothing else defines an order.

The detectors are deliberately cheap syntactic signals (regex hits), not
parsers: detection NOMINATES candidates in order, the real parsers then
accept or reject. A signal miss therefore never loses a formula — the
unicode mode ladder is always the terminal catch-all — it only costs the
nominated dialect its early slot.

Signals (each with the concrete give-away it keys on):

* ``smtlib`` — an S-expression command head: ``(assert``,
  ``(declare-fun``, ``(declare-const``, ``(set-logic``, ``(define-fun``.
* ``tptp`` (annotated) — a role wrapper ``fof(`` / ``cnf(`` / ``tff(`` /
  ``thf(``.
* ``latex`` — a backslash command from the FOL vocabulary
  (``\\forall``, ``\\exists``, ``\\land``, …, ``\\Box``, ``\\Diamond``).
* ``tptp_bare`` (ASCII only) — TPTP quantifier blocks ``![…]`` / ``?[…]``
  or the ASCII connectives ``=>``/``<=>``/``~``.
* ``prover9`` (ASCII only) — ``->``/``<->``, the word quantifiers
  ``all`` / ``exists``, or ``&``/``|``.
* ``unicode`` — the kit's own surface syntax (mode ladder, classical
  first); always the last candidate. Non-ASCII text that carries none of
  the above signals goes STRAIGHT here — the two ASCII-only detectors are
  skipped because any unicode connective already disambiguates.
"""

import re
from typing import Tuple

__all__ = ["detect_dialects", "DIALECT_SIGNALS"]

_SMT_RE = re.compile(r"\(\s*(assert|declare-fun|declare-const|set-logic|define-fun)\b")
_TPTP_ANNOTATED_RE = re.compile(r"\b(fof|cnf|tff|thf)\s*\(")
_TPTP_BARE_RE = re.compile(r"(!\s*\[|\?\s*\[|=>|<=>|~)")
_LATEX_RE = re.compile(
    r"\\(forall|exists|land|lor|lnot|neg|rightarrow|to|leftrightarrow|Box|Diamond)\b")
_PROVER9_RE = re.compile(r"(->|<->)|(\ball\s)|(\bexists\s)|(&)|(\|)")

#: (dialect name, signal regex, ascii_only) in nomination order — the
#: importable form of the table in the module docstring.
DIALECT_SIGNALS: Tuple[Tuple[str, "re.Pattern[str]", bool], ...] = (
    ("smtlib", _SMT_RE, False),
    ("tptp", _TPTP_ANNOTATED_RE, False),
    ("latex", _LATEX_RE, False),
    ("tptp_bare", _TPTP_BARE_RE, True),
    ("prover9", _PROVER9_RE, True),
)


def detect_dialects(text: str) -> Tuple[str, ...]:
    """The ORDERED dialect candidates for ``text``, ``"unicode"`` last.

    Pure and side-effect free: no parser runs. ``parse_any`` tries the
    returned candidates front to back and falls through on each parse
    failure, so the order here IS the facade's detection order. The result
    always ends in ``"unicode"`` and never contains duplicates.
    """
    is_ascii = text.isascii()
    candidates = [name for name, signal, ascii_only in DIALECT_SIGNALS
                  if (is_ascii or not ascii_only) and signal.search(text)]
    candidates.append("unicode")
    return tuple(candidates)
