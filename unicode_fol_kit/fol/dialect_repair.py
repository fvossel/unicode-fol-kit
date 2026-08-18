"""Repair layer for LLM-generated formulas in the kit's OWN surface syntax.

Sibling of :mod:`unicode_fol_kit.fol.tptp_repair`, which repairs in TPTP the
three shapes LLM-generated formulas fail on for pure SYNTAX — worth repairing
rather than retrying, since a syntax rejection costs a whole generation
attempt. Carrying those three over to the kit's unicode dialect gives three
DIFFERENT answers, and which is which is this module's entire content:

1. **Biimplication structure error** — **does not exist here.** A strict
   TPTP parser (gavel, for one) rejects ``p(X) <=> a(X) & b(X)`` for lacking
   brackets around the right side. The kit's unicode grammar accepts it, and
   ``Node.to_unicode_str`` renders it back in exactly that form, so there is
   nothing to normalise in either direction. It is unambiguous because the
   grammar's ladder puts ``↔``/``→`` below ``∧``/``∨`` — and because the one
   shape that WOULD be ambiguous, mixing ``∧`` and ``∨`` at the same level,
   is refused outright rather than silently resolved by precedence.

   That refusal is why this module never inserts a bracket. ``A ∧ B ∨ C`` has
   two readings, they are different formulas, and picking one would throw
   away the exact property that makes this dialect worth generating in: the
   parser says "cannot mix" *before* a wrong reading reaches a model checker.
   Reported as a ``"mixed_connectives"`` issue with the grammar's own hint;
   never repaired.

2. **Invalid predicate name** — **repaired differently.** A chemical name
   used as a predicate (``1,2-diacyl-sn-glycero-3-phospho‐
   choline``, ``(2S)Flavan4One``) is not a legal token in any FOL surface
   syntax. TPTP has an escape hatch, single quoting, which preserves the
   name exactly; the unicode grammar has **no quoting mechanism at all**
   (``'1,2-diacyl'(x)`` fails on the quote character itself), so the fix
   here is a sanitising RENAME through
   :class:`~unicode_fol_kit.fol.sanitize.NameMapping`.

   Renaming such a name to a plain camelCase identifier is the obvious
   fallback, and it is a loss: the mapping back to the original chemical
   class name is gone. Here the mapping IS the return value (``names``, and
   the caller's own :class:`NameMapping`), so the original spelling is
   recoverable and the same original renames identically in every formula of
   a run when the caller passes one mapping through. Nothing is lost; it just
   lives beside the formula instead of inside it.

3. **Unbound variable error** — **repaired identically.** Free variables are
   read off the AST, which no longer knows what dialect it was written in, so
   this module calls tptp_repair's own two fixes
   (:func:`~unicode_fol_kit.fol.tptp_repair._drop_argument_fix`,
   :func:`~unicode_fol_kit.fol.tptp_repair._close_universally`) rather than
   reimplementing them — the two paths cannot drift apart if there is only
   one implementation.

Public API: :func:`repair_formula`, returning a :class:`DialectRepairResult`
(a :class:`~unicode_fol_kit.fol.tptp_repair.RepairResult` plus the dialect
that parsed and the renamings applied), so a caller that already handles TPTP
repairs handles these with the same code.

Hard limits (refuse rather than silently reinterpret)
-------------------------------------------------------
* Mixed same-level connectives are reported, never bracketed (above).
* A rename is only ever attempted on text that FAILED to parse, and only for
  a name-shaped span in functor position that is legal in no symbol class —
  and it is kept only if the rewritten text then parses. A rewrite that does
  not make the input parseable is discarded whole: ``ok=False``, the original
  text returned untouched, and the parser's own farthest diagnosis reported.
* The rename always picks the PREDICATE spelling (``[A-Z][a-zA-Z0-9]*``).
  A functor-position name is a predicate or a function depending only on its
  spelling, so this is a choice, not a reading — stated in the issue message
  each time. A case-2 name of this shape is a class predicate in practice; a
  name meant as a function symbol must be written legally by hand.
* A legalised name never collides with a symbol already in the text: the
  mapping's reserved set is preseeded with every identifier the text
  contains, so ``1,2-diacyl`` beside an existing ``P12diacyl`` yields
  ``P12diacyl2`` instead of merging the two predicates.
"""

import re
from dataclasses import dataclass
from functools import lru_cache
from typing import List, Optional, Tuple

from .nodes import Node, free_variables
# The three symbol-class patterns come from fol._identifiers — the SAME
# generated character classes the grammar itself lexes PREDICATE/NAME/
# VARIABLE with — rather than from sanitize.py. sanitize.py's patterns are a
# DIFFERENT, deliberately narrower thing: the strictly-ASCII subset safe to
# emit into TPTP/Prover9/SMT-LIB/Isabelle/CASL (see its module docstring), not
# "every name this dialect's parser accepts". Using sanitize's patterns here
# used to be harmless because they happened to coincide with the grammar's
# own (then-ASCII) terminals; once the grammar widened to Unicode letters,
# underscores, and digit-leading names, that coincidence broke — a legal name
# like `family_History` would fail sanitize's ASCII-only _NAME_RE and get
# needlessly (and destructively) renamed, even though it already parses fine.
# _is_legal_name has to ask what THIS dialect's grammar accepts, which is
# _identifiers, not what sanitize.py is willing to export.
from ._identifiers import (
    predicate_pattern as _predicate_pattern,
    name_pattern as _name_pattern,
    variable_pattern as _variable_pattern,
    uppercase_class as _uppercase_class,
    lowercase_class as _lowercase_class,
    combining_class as _combining_class,
)
from .sanitize import NameMapping
from .tptp_repair import (
    Issue, RepairResult, _close_universally, _drop_argument_fix, _squash,
)

__all__ = ["DialectRepairResult", "repair_formula"]


@dataclass(frozen=True)
class DialectRepairResult(RepairResult):
    """A :class:`~unicode_fol_kit.fol.tptp_repair.RepairResult` for
    :func:`repair_formula`.

    ``repaired_text`` is the kit's unicode rendering of the repaired AST
    (``Node.to_unicode_str``), not TPTP — it re-parses to ``formula``.

    ``dialect`` is what actually parsed (``parse_any``'s report), ``None``
    when nothing did. ``names`` lists the ``(original, legal)`` renamings
    case 2 applied, in application order — empty when nothing was renamed.
    The originals are recoverable from this alone; pass a shared
    :class:`~unicode_fol_kit.fol.sanitize.NameMapping` to
    :func:`repair_formula` to keep them consistent across a whole run.
    """

    dialect: Optional[str] = None
    names: Tuple[Tuple[str, str], ...] = ()

    def to_dict(self) -> dict:
        out = super().to_dict()
        out["dialect"] = self.dialect
        out["names"] = [{"original": o, "legal": l} for o, l in self.names]
        return out


# ---------------------------------------------------------------------------
# Case 2 — invalid names: raw-text detection
# ---------------------------------------------------------------------------
#
# Mirrors tptp_repair._CANDIDATE_RE (a name-shaped span immediately before an
# argument list's "(", optionally preceded by one non-nested parenthesised
# fragment, with a left-boundary lookbehind so scanning is non-overlapping)
# with one deliberate difference: "_" is a candidate character here. TPTP's
# lower_word admits underscores, so tptp_repair never has to fix a name that
# merely contains one; the kit's own predicate class ([A-Z][a-zA-Z0-9]*) does
# not, so `Foo_bar(x)` IS a case-2 name in this dialect and has to be
# detectable as one.
_CANDIDATE_RE = re.compile(
    r"(?<![A-Za-z0-9_,\-)])"
    r"((?:\([^()\n]{1,40}\))?[A-Za-z0-9][A-Za-z0-9_,\-]*)"
    r"(?=\s*\()"
)

# The three symbol-class patterns (and the broader IDENT scan below) are
# built from fol._identifiers lazily, behind lru_cache, rather than at this
# module's import time: fol/__init__.py imports this module eagerly, so a
# module-level ``re.compile(_predicate_pattern())`` here would force
# _identifiers' once-per-process codepoint scan (~0.1-1s) onto every
# ``import unicode_fol_kit`` — even one that never calls repair_formula. The
# lru_cache still means the scan runs at most once per process; it just runs
# on first actual USE instead of on import.

@lru_cache(maxsize=1)
def _legal_name_patterns():
    return (
        re.compile(_predicate_pattern()),
        re.compile(_name_pattern()),
        re.compile(_variable_pattern()),
    )


@lru_cache(maxsize=1)
def _ident_re():
    """Every identifier-shaped span in the dialect's widened alphabet: a
    letter or digit, then letters/digits/underscores/combining marks — a
    superset of PREDICATE/NAME/VARIABLE/CONSTANT (permissive on purpose,
    since this only feeds the collision-avoidance preseed below, not a
    legality check)."""
    letters = f"{_uppercase_class()}{_lowercase_class()}"
    cont = f"{letters}0-9_{_combining_class()}"
    return re.compile(f"[{letters}0-9][{cont}]*")


#: Substring of a parse-error message that means the grammar refused a mix of
#: same-level connectives. Matching on the message text is the same small,
#: documented heuristic ``unicode_fol_kit.mcp.server._SPEC_HINTS`` already
#: uses to route a diagnosis; the hint itself is built in
#: ``unicode_fol_kit.fol.naming._MIXING_INFO``.
_MIXING_MARKER = "cannot mix"


def _is_legal_name(name: str) -> bool:
    """Is ``name`` already a legal token in SOME symbol class of THIS
    dialect's grammar?

    Predicate, function/bare constant (NAME, including its underscored and
    digit-leading forms), or variable — see :mod:`unicode_fol_kit.fol.
    _identifiers` for the exact shapes. The variable class matters even
    though a variable is never a functor: ``∀x (…)`` puts ``x`` immediately
    before a "(" and so matches :data:`_CANDIDATE_RE` — renaming a bound
    variable to a predicate would destroy the formula, and the one thing
    keeping it out of the candidate list is that ``x`` is legal here.
    """
    pred_re, name_re, var_re = _legal_name_patterns()
    return bool(pred_re.fullmatch(name) or name_re.fullmatch(name)
                or var_re.fullmatch(name))


def _find_name_candidates(text: str) -> List[str]:
    """Distinct, order-preserving functor-position names in ``text`` that are
    legal in no symbol class."""
    seen = set()
    out: List[str] = []
    for match in _CANDIDATE_RE.finditer(text):
        name = match.group(1)
        if _is_legal_name(name) or name in seen:
            continue
        seen.add(name)
        out.append(name)
    return out


def _apply_renames(text: str, renames: Tuple[Tuple[str, str], ...]) -> str:
    """Replace every functor-position occurrence of each original name.

    By name rather than by span (the same mis-written predicate legitimately
    occurs more than once, and substituting by name catches every occurrence
    without tracking shifting offsets), LONGEST FIRST: one invalid name can
    end with another (``3-oxo-steroid`` and ``oxo-steroid``), and rewriting
    the shorter one first would eat the tail of the longer one's occurrences
    and leave a half-renamed name behind.
    """
    out = text
    for name, legal in sorted(renames, key=lambda pair: -len(pair[0])):
        out = re.sub(re.escape(name) + r"(?=\s*\()", legal, out)
    return out


def _farthest(errors) -> str:
    """The most informative of ``parse_any``'s per-dialect messages.

    The FARTHEST failure, not the last listed — the dialects at the end of
    the detection order are the specialised ones that give up earliest on
    ordinary input. Same rule, same implementation, as
    :func:`unicode_fol_kit.api._suggest`'s.
    """
    from ..api import _message_progress  # deferred: api imports fol

    if not errors:
        return "no parser accepted the text"
    best = max(errors, key=lambda e: _message_progress(e.get("message", "")))
    return best.get("message", "")


def _failed(text: str, kind: str, message: str,
            suggestion: Optional[str] = None) -> DialectRepairResult:
    """An honest failure: nothing rewritten, the diagnosis handed back."""
    return DialectRepairResult(
        ok=False, formula=None, repaired_text=text,
        issues=(Issue(kind, message, suggestion=suggestion),), changed=False)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def repair_formula(text: str, *, dialect: Optional[str] = None,
                   sanitize_invalid_names: bool = True,
                   close_free_variables: bool = False,
                   mapping: Optional[NameMapping] = None
                   ) -> DialectRepairResult:
    """Repair one formula written in the kit's own surface syntax.

    Pipeline:

    1. Parse via :func:`unicode_fol_kit.api.parse_any`. On failure, if the
       grammar refused a mix of same-level connectives, report it and stop
       (case 1' — never bracketed, see the module docstring). Otherwise, if
       ``sanitize_invalid_names``, rename every functor-position name that is
       legal in no symbol class (case 2) and re-parse; a rewrite that still
       does not parse is discarded entirely.
    2. Free variables (case 3) are read off the AST: always reported, and
       additionally closed — argument-drop where that exact shape holds, else
       universal closure — only when ``close_free_variables=True``.
    3. ``repaired_text`` is the unicode rendering of the resulting AST.

    Args:
        text: one formula in the kit's unicode syntax.
        dialect: pin the dialect (``parse_any``'s ``hint``) instead of
            detecting it. ``"unicode"`` for the whole mode ladder, a mode
            name (``"fol"``, ``"modal"``, …) for one mode.
        sanitize_invalid_names: attempt case 2's rename when parsing fails.
            ``False`` reports the syntax error unchanged.
        close_free_variables: apply case 3's fix instead of only reporting
            it. Default ``False``: report, never touch — an unclosed free
            variable never blocks ``ok=True``, because the AST is valid; the
            kit just will not guess whether you meant universal closure or an
            argument that should be dropped.
        mapping: an existing :class:`NameMapping` to extend, so the same
            original name renames to the same token across a whole run. A
            fresh one is used when omitted.

    Returns:
        A :class:`DialectRepairResult`.
    """
    from ..api import parse_any  # deferred: api imports fol

    issues: List[Issue] = []
    renames: Tuple[Tuple[str, str], ...] = ()

    parsed = parse_any(text, hint=dialect)
    if not parsed.ok:
        message = _farthest(parsed.errors)
        if _MIXING_MARKER in message.lower():
            return _failed(
                text, "mixed_connectives",
                f"{message} The kit does not bracket this for you: the two "
                "readings are different formulas and choosing one would be a "
                "guess. Write the brackets you mean.")
        if not sanitize_invalid_names:
            return _failed(text, "syntax_error", message)

        candidates = _find_name_candidates(text)
        if not candidates:
            return _failed(text, "syntax_error", message)

        if mapping is None:
            mapping = NameMapping()
        # Preseed with the identifiers already in the text so a legalised
        # name can never collide with a symbol that is already there (see
        # the module docstring's collision limit).
        mapping.used.update(match.group(0) for match in _ident_re().finditer(text))
        renames = tuple((name, mapping.for_predicate(name)) for name in candidates)

        retried = _apply_renames(text, renames)
        parsed = parse_any(retried, hint=dialect)
        if not parsed.ok:
            names = sorted(name for name, _legal in renames)
            return _failed(
                text, "syntax_error",
                f"renaming {names!r} did not make the formula parseable: "
                f"{_farthest(parsed.errors)}")
        for name, legal in renames:
            issues.append(Issue(
                "invalid_predicate_name",
                f"{name!r} is a legal token in no symbol class of this "
                f"dialect; renamed to the predicate {legal!r}. The original "
                "spelling is preserved in this result's `names` (and in the "
                "NameMapping, if you passed one) — nothing about the name is "
                "lost, but it now lives beside the formula rather than in it.",
                suggestion=legal))

    formula: Node = parsed.formula
    final_formula = formula
    free = free_variables(formula)
    if free:
        names_text = ", ".join(sorted(v.name for v in free))
        if close_free_variables:
            dropped = (_drop_argument_fix(formula, next(iter(free)))
                       if len(free) == 1 else None)
            if dropped is not None:
                final_formula = dropped
                issues.append(Issue(
                    "free_variable",
                    f"unbound variable {names_text!r} is the sole argument of "
                    "the left-hand definiendum and does not recur on the "
                    "right — dropped it: the definition is, in substance, a "
                    "0-ary property that only accidentally carries an "
                    "argument.",
                    suggestion=dropped.to_unicode_str()))
            else:
                final_formula = _close_universally(formula, free)
                issues.append(Issue(
                    "free_variable",
                    f"unbound variable(s) {names_text} closed via universal "
                    "quantification (standard universal-closure convention; "
                    "the argument-drop fix does not apply — the formula is "
                    "not a `P(x) ↔ …`/`P(x) → …` definition with x absent "
                    "from the right-hand side).",
                    suggestion=final_formula.to_unicode_str()))
        else:
            issues.append(Issue(
                "free_variable",
                f"unbound variable(s) {names_text} — not closed (default "
                "close_free_variables=False). The kit will not guess whether "
                "you meant universal closure or an argument that should be "
                "dropped; pass close_free_variables=True to apply the "
                "documented conservative fix, or rewrite by hand."))

    repaired_text = final_formula.to_unicode_str()
    return DialectRepairResult(
        ok=True, formula=final_formula, repaired_text=repaired_text,
        issues=tuple(issues),
        changed=_squash(text) != _squash(repaired_text),
        dialect=parsed.dialect, names=renames)
