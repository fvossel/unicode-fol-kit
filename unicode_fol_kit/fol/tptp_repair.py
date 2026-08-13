"""Repair layer over :mod:`unicode_fol_kit.fol.tptp_input` for LLM-generated TPTP.

Context (ChEBI2FOL, NeSy 2026, Appendix B.1): of 136 ChEBI class definitions an
LLM failed to translate to FOL, 89 failed on pure SYNTAX, each burning a whole
LLM attempt. Three shapes account for (nearly) all of them:

  1. **Biimplication structure error** (46 classes) — the LLM writes
     ``predicate(x) <=> condition1 & condition2`` and the paper's parser
     (gavel) rejects it for lacking explicit brackets around the right side.
  2. **Invalid predicate name** (29 classes) — a chemical name used as a
     predicate/function symbol starts with a digit or contains characters TPTP
     forbids in a bare ``lower_word`` (hyphens, commas, parentheses — e.g. a
     stereodescriptor prefix like ``(2S)`` or a positional prefix like
     ``1,2-``). The paper's own fallback (renaming to a camelCase identifier)
     *loses* exactly the chemical information those characters encode and
     severs the link back to the ChEBI class; TPTP single-quoting
     (``'1,2-diacyl-sn-glycero-3-phosphocholine'``) keeps both.
  3. **Unbound variable error** (14 classes) — e.g.
     ``threeOxoSteroid(X) <=> (steroid & ?[A1,A2]: (c(A1) & o(A2))))``: ``X``
     on the left never occurs on the right. The paper's own fix drops the
     argument (``threeOxoSteroid <=> …``) precisely because the definition is
     a 0-ary, molecule-level property, not a property of some individual
     ``X`` — and holds this class is NOT reliably fixable by a parser
     heuristic in general.

This module's premise (verified against :func:`parse_tptp_formula` before
writing a line here): the kit's own Lark TPTP grammar already ACCEPTS all
three shapes — case 1 by having the same precedence ladder gavel wants made
explicit, case 2 via its single-quoted-atom (``SQ``) token, case 3 by simply
leaving the variable free in the AST rather than rejecting it. So repairing is
not "write a smarter TPTP parser"; it is: parse with the grammar the kit
already has, look at what came out, and turn that into gavel-compatible text
— or, for case 2 alone (the one shape the grammar cannot even tokenise
unquoted), a narrow, auditable text rewrite BEFORE parsing.

Public API
----------
:func:`repair_tptp_formula` — repair one bare TPTP formula, returning a
:class:`RepairResult` (``ok``, ``formula``, ``repaired_text``, ``issues``,
``changed``). :func:`repair_tptp_problem` — the same over a whole
``fof(name, role, formula).`` file, formula by formula, preserving every
statement's name/role/comments and touching only the formula span that needed
it.

Hard limits (refuse rather than silently reinterpret)
-------------------------------------------------------
* Case 2's raw-text detector is a narrow, two-shape heuristic (see
  :data:`_CANDIDATE_RE`), not a general TPTP-syntax-error corrector: genuinely
  broken input (e.g. unbalanced parentheses) that isn't explained by an
  unquoted invalid name is reported ``ok=False`` with the parser's own
  diagnosis, never guessed at.
* Case 3's fix is applied ONLY with ``close_free_variables=True`` (default
  ``False``: report, don't touch), and even then only the narrow
  ``predicate(X) <=> …`` / ``predicate(X) => …`` shape (paper's exact
  pattern: the free variable is the sole argument of the definiendum on the
  LEFT, and does not recur on the right) gets the meaning-preserving
  argument-drop; anything else gets the standard, well-understood universal
  closure (∀-wrap every free variable) — never a guess at what the author
  meant that could go either way.
* A predicate name that needed quoting because :mod:`tptp_input` failed to
  parse it unquoted is quoted using the EXACT original substring, tracked
  through re-parsing by exact ``_cap()``-image lookup (see the
  ``known_names`` machinery below ``_uncap``) — no case folding, no
  character loss, EVER, for a name this module itself detected and fixed.
  If two DISTINCT such candidate names would reduce to the SAME ``_cap()``
  image (e.g. ``"N-acetyl-x"`` and ``"n-acetyl-x"``, differing only in the
  case of their first letter — both invalid unquoted, both quoted by this
  module, both reparsing to the identical ``Atom`` predicate), quoting
  BOTH would silently merge two distinct predicates into one; this is
  detected while ``known_names`` is built and reported ``ok=False`` (a
  ``"name_collision"`` issue) rather than silently keeping one of the two.
* For a name the CALLER already had quoted before this module saw the
  text, the raw text is scanned independently (:func:`_find_prequoted_names`
  — a best-effort, position-agnostic sibling of the case-2 detector above)
  for every single-quoted literal and its exact original spelling recovered
  by the same ``_cap()``-image lookup; this covers every already-quoted name
  that appears unambiguously (its ``_cap()`` image doesn't collide with a
  DIFFERENT quoted original found elsewhere in the same text). It cannot
  distinguish a quoted name's PREDICATE vs. term (function/constant) role
  from raw text alone, but that distinction is immaterial here: only
  ``Atom.predicate`` rendering ever consults it (``Function``/``Constant``
  rendering never folds case in the first place, so it never needs it).
  The one case this cannot recover — two DIFFERENT quoted originals sharing
  one ``_cap()`` image (e.g. both ``'Foo'`` and ``'foo'`` literally present
  in the text) — falls back to :func:`_uncap`'s guess for either, exactly as
  before this scan existed, never worse. :func:`_uncap` assumes the true
  original was lower-case, which is always correct for a name that arrived
  via a bare (unquoted) functor — the TPTP grammar itself requires that
  first character to already be lower-case, so there is no other
  possibility for such a name — and is otherwise a last-resort, irreversible
  GUESS reached only when neither of the two recovery mechanisms above
  applies. This residual gap is real but narrow and fully documented at
  :func:`_uncap`; it never fires on either literal paper example (both start
  with a digit / a parenthesis, so :func:`_uncap` is a no-op regardless of
  which branch computes it).
"""

import re
from dataclasses import dataclass
from typing import Optional, Tuple

from ._fol_nodes import constant_name_to_ascii
from .naming import ParsingError
from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    free_variables,
)
from .tptp_input import parse_tptp_formula, _cap, _functor_name

__all__ = [
    "Issue", "RepairResult", "repair_tptp_formula",
    "ProblemRepairEntry", "ProblemRepairResult", "repair_tptp_problem",
    "TptpRepairError",
]


class TptpRepairError(Exception):
    """Raised when :func:`repair_tptp_problem` cannot even locate statement
    boundaries in a ``fof(...)``/``cnf(...)`` file (malformed wrapper) — a
    structural problem this module refuses to guess through, distinct from a
    per-formula syntax issue (which :func:`repair_tptp_formula` reports
    instead of raising)."""


@dataclass(frozen=True)
class Issue:
    """One diagnostic from a repair pass.

    ``kind`` is one of ``"bracket_normalisation"``, ``"invalid_predicate_name"``,
    ``"free_variable"``, ``"syntax_error"`` (input :func:`repair_tptp_formula`
    could not turn into a valid formula at all), or ``"name_collision"`` (two
    of THIS module's own case-2 candidate names would be indistinguishable
    once rendered — see :func:`repair_tptp_formula`'s known_names collision
    check). ``suggestion`` is optional and, when present, is the concrete
    text that either WAS applied (``changed=True``) or COULD be applied by
    opting in to the relevant flag.
    """

    kind: str
    message: str
    suggestion: Optional[str] = None

    def to_dict(self) -> dict:
        return {"kind": self.kind, "message": self.message, "suggestion": self.suggestion}


@dataclass(frozen=True)
class RepairResult:
    """Outcome of :func:`repair_tptp_formula`.

    ``ok``: a valid :class:`Node` was produced (either the input already
    parsed, or a case-2 text rewrite made it parse). ``False`` only for
    genuinely unrepairable syntax — see the module docstring's hard limits.
    Note ``ok=True`` does NOT mean issue-free: an unclosed free variable
    (case 3, default ``close_free_variables=False``) still yields
    ``ok=True`` with a ``"free_variable"`` issue, because the AST is
    perfectly valid — the kit just refuses to guess how to close it.

    ``formula``: the repaired AST (``None`` iff ``ok`` is ``False``).

    ``repaired_text``: canonical, gavel-compatible TPTP — fully bracketed,
    every name that needs quoting quoted — that re-parses to ``formula``
    exactly (see :func:`repair_tptp_formula`'s docstring for the precedence
    argument backing this for case 1). Equal to the ORIGINAL input text when
    ``ok`` is ``False`` (nothing is ever silently rewritten into something
    unverified).

    ``issues``: every :class:`Issue` found, in detection order (name issues,
    then free-variable issues; bracket normalisation — if any — is implicit
    in whether ``repaired_text`` differs and is reported explicitly too).

    ``changed``: whether ``repaired_text`` differs from ``text`` (whitespace
    collapsed away — pure reformatting is not "changed").
    """

    ok: bool
    formula: Optional[Node]
    repaired_text: str
    issues: Tuple[Issue, ...]
    changed: bool

    def to_dict(self) -> dict:
        return {
            "ok": self.ok,
            "formula": self.formula.to_dict() if self.formula is not None else None,
            "repaired_text": self.repaired_text,
            "issues": [i.to_dict() for i in self.issues],
            "changed": self.changed,
        }


# ---------------------------------------------------------------------------
# Case 2 — invalid predicate/function/constant names: raw-text detection
# ---------------------------------------------------------------------------
#
# tptp_input.py's grammar requires an unquoted functor name to be a TPTP
# `lower_word` (LOWER token: `[a-z][A-Za-z0-9_]*`) — this is not a gavel
# quirk, it is the TPTP standard, so a name violating it is rejected by ANY
# conformant parser, this kit's own included, unless quoted. That means the
# raw text genuinely fails to PARSE (not merely fails some downstream
# validator) before we ever get an AST to inspect — the fix has to happen at
# the text level, on the ORIGINAL characters, before parsing.
#
# _CANDIDATE_RE looks for a name-shaped span immediately followed by an
# argument list's "(" (i.e. a functor application), built from the two
# concrete shapes the paper's Appendix B.1 names:
#
#   (a) a stray parenthesised prefix glued to more identifier characters,
#       e.g. "(2S)Flavan4One" — `(?:\([^()\n]{1,40}\))?` optionally eats a
#       single, non-nested parenthesised fragment first;
#   (b) a run of letters/digits/commas/hyphens, e.g.
#       "1,2-diacyl-sn-glycero-3-phosphocholine".
#
# A left-boundary negative lookbehind stops the match from starting mid-run
# (so scanning is deterministic and non-overlapping), and the whole candidate
# is discarded (never rewritten) if it ALREADY satisfies TPTP's lower_word
# rule — i.e. this only ever fires on text that would otherwise fail to
# parse, never on an ordinary `steroid(x)`-style call.

_VALID_UNQUOTED = re.compile(r"^[a-z][A-Za-z0-9_]*$")

_CANDIDATE_RE = re.compile(
    r"(?<![A-Za-z0-9,\-)])"
    r"((?:\([^()\n]{1,40}\))?[A-Za-z0-9][A-Za-z0-9,\-]*)"
    r"(?=\s*\()"
)


def _tptp_quote(name: str) -> str:
    """Wrap ``name`` in TPTP single quotes, escaping exactly ``\\`` and ``'``.

    The inverse of :func:`unicode_fol_kit.fol.tptp_input._functor_name`'s
    unescaping (``re.sub(r"\\\\(.)", r"\\1", s[1:-1])``): escaping only these
    two characters — backslash first, so a literal backslash in the name
    never gets swallowed by the quote-escaping step that follows — produces
    exactly the ``'(\\\\.|[^'\\\\])*'`` shape the grammar's ``SQ`` token
    requires, so the result always re-parses to ``name`` unchanged.
    """
    escaped = name.replace("\\", "\\\\").replace("'", "\\'")
    return f"'{escaped}'"


def _find_name_candidates(text: str):
    """Distinct, order-preserving ``(span, name)`` pairs :data:`_CANDIDATE_RE`
    finds in ``text`` that are NOT already valid unquoted TPTP names."""
    seen = set()
    out = []
    for m in _CANDIDATE_RE.finditer(text):
        name = m.group(1)
        if _VALID_UNQUOTED.match(name):
            continue
        if name not in seen:
            seen.add(name)
            out.append((m.span(1), name))
    return out


def _apply_name_quoting(text: str, candidates) -> str:
    """Quote every distinct candidate NAME wherever it occurs immediately
    before an argument list, by name rather than by the single span
    :func:`_find_name_candidates` returned for it — the same invalid name can
    legitimately appear more than once (e.g. the same mis-written predicate
    used on both sides of a formula), and substituting by name catches every
    occurrence in one pass without having to track shifting offsets."""
    out = text
    for _span, name in candidates:
        pattern = re.compile(re.escape(name) + r"(?=\s*\()")
        out = pattern.sub(lambda m, n=name: _tptp_quote(n), out)
    return out


# ---------------------------------------------------------------------------
# Canonical renderer — full bracketing (case 1) + correct quoting (case 2)
# ---------------------------------------------------------------------------
#
# Node.to_tptp() (see _fol_nodes.py) already fully brackets every connective
# and quantifier UNCONDITIONALLY — that is exactly case 1's fix, for free.
# What it does NOT do is quote a name that needs quoting (it just
# lower-cases and emits it bare), which would silently re-emit an invalid
# case-2 name. _render duplicates to_tptp()'s exact structural/operator
# choices (so behaviour is identical for everything that was already valid)
# and adds the one thing to_tptp() is missing: a quoting decision for every
# Atom/Function/Constant name.

def _needs_quote(name: str) -> bool:
    return not bool(_VALID_UNQUOTED.match(name))


def _uncap(name: str) -> str:
    """Undo :mod:`tptp_input`'s ``Atom``-predicate ``_cap()``: that parser
    force-uppercases the first character of EVERY parsed predicate name — its
    "predicate names are capitalised" convention — whether the name came
    from a bare ``LOWER`` token (whose first character the TPTP grammar
    itself REQUIRES to already be lower-case) or an already single-quoted
    ``SQ`` token (arbitrary content); everything from the second character
    on is untouched by ``_cap()`` either way. Recovering the true original
    first character is needed here to decide (and correctly render) whether
    a predicate name needs quoting; force-lowercasing it back is the exact
    inverse whenever the true original was lower-case. That covers the
    ``LOWER``-token case UNCONDITIONALLY (the grammar leaves no other
    possibility). The ``SQ``-quoted case is instead recovered exactly by
    :func:`_find_prequoted_names` (a raw-text scan of the original quoted
    spelling) BEFORE this function is ever consulted for such a name — see
    :func:`_render_predicate_name`; this function is reached for an
    ``SQ``-quoted name only as the last-resort fallback when that scan
    could not recover it unambiguously (see the module docstring for that
    one residual case).
    """
    return (name[:1].lower() + name[1:]) if name and name[0].isalpha() else name


_NO_KNOWN_NAMES: dict = {}

_SQ_TOKEN_RE = re.compile(r"'(?:\\.|[^'\\])*'")


def _find_prequoted_names(text: str) -> dict:
    """Best-effort ``_cap(original) -> original`` map recovered from every
    single-quoted TPTP atom (``'...'``) literally present in ``text`` — i.e.
    every name the CALLER already had quoted before this module ever touched
    the text, as opposed to the case-2 ``known_names`` entries built in
    :func:`repair_tptp_formula`, which cover names THIS module quoted itself.

    This is a raw-text scan (:data:`_SQ_TOKEN_RE`, mirroring the grammar's
    own ``SQ`` token), not a re-parse: it cannot tell a predicate-position
    quoted name (``'Foo'(a)`` as an atom, or ``'Foo'`` as a 0-ary atom) from
    a term-position one (``'Foo'`` used as a constant, or nested as a
    function argument) — but that distinction never matters for correctness
    here, because :func:`_render_functor_name` (``Function``/``Constant``)
    never consults this map at all; only :func:`_render_predicate_name`
    (``Atom.predicate``) does, and only for names ``_cap()`` has already
    folded. Two DIFFERENT quoted originals sharing one ``_cap()`` image
    (e.g. both ``'Foo'`` and ``'foo'`` literally present) are unrecoverably
    ambiguous for that shared image from text alone — silently dropped from
    the returned map (falls back to :func:`_uncap`'s pre-existing guess for
    either predicate that ends up with that image, exactly today's
    behaviour — never worse than before this scan existed) rather than
    picking one arbitrarily.
    """
    found: dict = {}
    ambiguous: set = set()
    for m in _SQ_TOKEN_RE.finditer(text):
        original = _functor_name(m.group(0))
        capped = _cap(original)
        prior = found.get(capped)
        if prior is not None and prior != original:
            ambiguous.add(capped)
            continue
        found[capped] = original
    for key in ambiguous:
        found.pop(key, None)
    return found


def _render_predicate_name(name: str, known_names: dict) -> str:
    """An ``Atom.predicate`` name, quoted iff it needs it.

    ``known_names`` maps ``_cap(original) -> original`` for every name this
    module recovered the true original spelling of before ``_cap()`` folded
    it: names THIS module's own case-2 raw-text repair just quoted (an
    exact, ambiguity-free record — see :func:`repair_tptp_formula`), merged
    with every name :func:`_find_prequoted_names` recovered from the raw
    input text (a best-effort record for names the CALLER already had
    quoted). When ``name`` (the stored, ``_cap()``'d predicate) is a hit in
    either source, that recovered original is used; otherwise the
    best-effort :func:`_uncap` guess is used (correct whenever the name
    truly arrived as a bare unquoted functor — the realistic residual gap is
    now limited to a quoted name whose distinct original spelling could not
    be recovered from raw text at all, e.g. it collided ambiguously with
    another quoted name sharing the same ``_cap()`` image — see the module
    docstring).
    """
    original = known_names[name] if name in known_names else _uncap(name)
    return _tptp_quote(original) if _needs_quote(original) else original


def _render_functor_name(name: str) -> str:
    """A ``Function``/``Constant`` name — never touched by ``_cap()`` (only
    ``Atom.predicate`` is), so the stored name IS the original: quoted iff it
    is not already a valid bare TPTP ``lower_word``, unchanged otherwise."""
    return _tptp_quote(name) if _needs_quote(name) else name


def _render(node: Node, known_names: dict = _NO_KNOWN_NAMES) -> str:
    """Render ``node`` as canonical, gavel-compatible TPTP.

    Structurally identical to :meth:`Node.to_tptp` for every connective,
    quantifier, and already-valid name (same brackets, same operators, same
    variable upper-casing) — the two behavioural differences are: (1) a name
    failing TPTP's unquoted ``lower_word`` rule is single-quoted instead of
    emitted bare (case 2), via :func:`_render_predicate_name` /
    :func:`_render_functor_name`; (2) an already-valid ``Atom`` predicate
    name is emitted via ``known_names``/:func:`_uncap` (see
    :func:`_render_predicate_name`) rather than :meth:`Node.to_tptp`'s
    whole-string ``.lower()`` — the whole-string fold is lossy for a
    mixed-case name like ``threeOxoSteroid`` (it would come back as
    ``threeoxosteroid``, a DIFFERENT ``LOWER`` token, breaking this module's
    own case-1 meaning-preservation guarantee for exactly the camelCase
    names ChEBI definitions use); touching only the character ``_cap()``
    actually touched reparses to the identical predicate string.
    """
    if isinstance(node, Variable):
        return node.name.upper()
    if isinstance(node, Number):
        return str(node.value)
    if isinstance(node, Constant):
        return _render_functor_name(constant_name_to_ascii(node.name))
    if isinstance(node, Function):
        if node.name in Function.TPTP_ARITH_OPS:
            args = ",".join(_render(a, known_names) for a in node.args)
            return f"{Function.TPTP_ARITH_OPS[node.name]}({args})"
        name = _render_functor_name(node.name)
        if not node.args:
            return name
        args = ",".join(_render(a, known_names) for a in node.args)
        return f"{name}({args})"
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_TPTP and len(node.args) == 2:
            op = Atom.INFIX_PREDS_TPTP[node.predicate]
            return f"({_render(node.args[0], known_names)} {op} {_render(node.args[1], known_names)})"
        if node.predicate in Atom.PREFIX_PREDS_TPTP and len(node.args) == 2:
            op = Atom.PREFIX_PREDS_TPTP[node.predicate]
            return f"{op}({_render(node.args[0], known_names)},{_render(node.args[1], known_names)})"
        name = _render_predicate_name(node.predicate, known_names)
        if not node.args:
            return name
        args = ",".join(_render(a, known_names) for a in node.args)
        return f"{name}({args})"
    if isinstance(node, Not):
        return f"~({_render(node.formula, known_names)})"
    if isinstance(node, And):
        return f"({_render(node.left, known_names)} & {_render(node.right, known_names)})"
    if isinstance(node, Or):
        return f"({_render(node.left, known_names)} | {_render(node.right, known_names)})"
    if isinstance(node, Xor):
        return f"({_render(node.left, known_names)} <~> {_render(node.right, known_names)})"
    if isinstance(node, Implies):
        return f"({_render(node.left, known_names)} => {_render(node.right, known_names)})"
    if isinstance(node, Iff):
        return f"({_render(node.left, known_names)} <=> {_render(node.right, known_names)})"
    if isinstance(node, Quantifier):
        var = _render(node.variable, known_names)
        body = _render(node.formula, known_names)
        if node.type in ("forall", "∀"):
            return f"(![{var}]: {body})"
        if node.type in ("exists", "∃"):
            return f"(?[{var}]: {body})"
        raise ValueError(f"tptp_repair: unknown quantifier type {node.type!r}")
    raise NotImplementedError(
        f"tptp_repair: {type(node).__name__} is outside the fof/cnf fragment "
        "parse_tptp_formula can produce (this module's scope, per "
        "tptp_input.py's own docstring) — nothing built from TPTP text can "
        "reach this branch; it would only fire on a hand-built AST using a "
        "node type outside classical FOL.")


_WS_RE = re.compile(r"\s+")


def _squash(text: str) -> str:
    """Whitespace-insensitive comparison key: TPTP tokens never depend on
    inter-token whitespace to disambiguate (unlike e.g. Python), so this is a
    safe basis for "is this really the same formula, modulo formatting"."""
    return _WS_RE.sub("", text)


# ---------------------------------------------------------------------------
# Case 3 — free variables: report, or (opt-in) close
# ---------------------------------------------------------------------------

def _drop_argument_fix(formula: Node, var: Variable) -> Optional[Node]:
    """The paper's Case-3 fix: ``P(X) <=> …`` / ``P(X) => …`` becomes
    ``P <=> …`` when ``X`` is the SOLE free variable, is the entire (single)
    argument list of the left-hand definiendum, and does not recur on the
    right — i.e. exactly when the formula is, in substance, already a 0-ary
    molecule-level definition that only accidentally carries an argument.
    Returns ``None`` (defer to universal closure) whenever this precise shape
    does not hold — this function never guesses.
    """
    if not isinstance(formula, (Iff, Implies)):
        return None
    left = formula.left
    if not (isinstance(left, Atom) and len(left.args) == 1 and left.args[0] == var):
        return None
    if var in free_variables(formula.right):
        return None
    cls = type(formula)
    return cls(Atom(left.predicate, []), formula.right)


def _close_universally(formula: Node, variables) -> Node:
    """Standard universal closure: wrap ``formula`` in ``∀v`` for every free
    ``v``, outermost quantifier first in alphabetical order (order among
    universal quantifiers never changes truth, so this is purely for
    deterministic, readable output)."""
    result = formula
    for var in sorted(variables, key=lambda v: v.name, reverse=True):
        result = Quantifier("∀", var, result)
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def repair_tptp_formula(text: str, *, quote_invalid_names: bool = True,
                         close_free_variables: bool = False) -> RepairResult:
    """Repair one bare TPTP FOF/CNF formula (no ``fof(...)`` wrapper).

    Pipeline:

    1. Try :func:`parse_tptp_formula` directly. If ``text`` fails to parse
       AND ``quote_invalid_names`` is true, look for case-2 candidates (see
       :data:`_CANDIDATE_RE`) and retry on the quoted text. Neither
       candidate found nor the retry succeeding is honest failure:
       ``ok=False``, ``repaired_text`` left as the untouched input, a single
       ``"syntax_error"`` issue carrying the parser's own message. If two
       DISTINCT candidates would reduce to the same predicate once quoted
       and re-parsed (see the module docstring's ``"name_collision"``
       paragraph), that is honest failure too — ``ok=False`` rather than
       silently merging them.
    2. Free variables (case 3) are read off the resulting AST via
       :func:`~unicode_fol_kit.fol.nodes.free_variables`. Reported via a
       ``"free_variable"`` issue always; additionally CLOSED (via
       :func:`_drop_argument_fix` if that exact shape applies, else
       :func:`_close_universally`) only when ``close_free_variables=True``.
    3. ``repaired_text`` is :func:`_render` of the (possibly closed) AST —
       always fully bracketed (case 1, for free: ``Node.to_tptp`` already
       brackets unconditionally and :func:`_render` matches it exactly) and
       with every name that needs it quoted (case 2, render-time half: a
       name that arrived ALREADY quoted in ``text`` — recovered by
       :func:`_find_prequoted_names`, independently of whether it still
       needs quoting on output for the same reason it arrived quoted, e.g.
       an internal hyphen, or for a different reason entirely, e.g. it
       merely starts upper-case — is preserved quoted, with its exact
       original spelling, rather than accidentally emitted bare or
       mis-cased).

    **Case-1 meaning-preservation argument** (why ``repaired_text``
    reparses to a formula structurally ``==`` the one parsed from ``text``,
    not just logically equivalent to it): the grammar's operator ladder is
    ``equiv > imp > disj > conj > unary`` (``<=>``/``<~>`` loosest, ``&``
    tightest among binary connectives), applied consistently whether or not
    the input carries redundant parentheses — parentheses only ever
    OVERRIDE precedence, they never change how already-unambiguous text
    parses. So ``p <=> a & b`` and ``p <=> (a & b)`` walk the identical
    production sequence (``equiv`` → two ``imp``s, the right one reducing
    through ``conj: conj "&" unary``) and build the identical tree,
    ``Iff(P, And(A, B))``, in either surface form. ``repaired_text`` is
    :func:`_render` of the AST parsed from ``text`` — by the identity above,
    reparsing it is guaranteed to retrace the same production sequence and
    rebuild the same tree, not merely an equivalent one. See
    ``test_bracket_normalisation_preserves_ast`` for the executable form of
    this argument (AST identity, plus an independent
    :func:`unicode_fol_kit.equivalent` check as a second witness).

    Args:
        text: a bare TPTP formula (as accepted by ``parse_tptp_formula``, or
            one violating unquoted-name syntax in the specific ways
            :data:`_CANDIDATE_RE` targets).
        quote_invalid_names: attempt the case-2 raw-text quoting fallback
            when direct parsing fails. ``False`` disables ONLY this
            fallback attempt (unparseable input then reports ``ok=False``
            immediately) — it never suppresses the render-time quoting an
            already-parseable formula's own names may still need, since
            that is required for ``repaired_text`` to be valid TPTP at all.
        close_free_variables: apply case 3's fix (see step 2) instead of
            only reporting it. Default ``False``: report, never touch — an
            unclosed free variable never blocks ``ok=True``.

    Returns:
        A :class:`RepairResult`.
    """
    issues = []
    working_text = text
    formula = None
    known_names = {}  # _cap(original) -> original, for names THIS call quoted itself

    try:
        formula = parse_tptp_formula(working_text)
    except ParsingError as exc:
        if quote_invalid_names:
            candidates = _find_name_candidates(text)
            if candidates:
                retried_text = _apply_name_quoting(text, candidates)
                try:
                    formula = parse_tptp_formula(retried_text)
                except ParsingError as exc2:
                    return RepairResult(
                        ok=False, formula=None, repaired_text=text,
                        issues=(Issue(
                            "syntax_error",
                            f"quoting {sorted(n for _s, n in candidates)!r} did not "
                            f"make the formula parseable: {exc2}",
                        ),),
                        changed=False)
                working_text = retried_text
                for _span, name in candidates:
                    capped = _cap(name)
                    prior = known_names.get(capped)
                    if prior is not None and prior != name:
                        # Two DISTINCT case-2 candidates (e.g. "N-acetyl-x"
                        # and "n-acetyl-x") that differ only in the case of
                        # their first letter both reduce to the same
                        # tptp_input _cap() image and would already reparse
                        # to the IDENTICAL Atom predicate — silently keeping
                        # only one of them in known_names would merge two
                        # distinct predicates into one without any warning.
                        # Refuse rather than choose (see the module
                        # docstring's "refuse rather than silently
                        # reinterpret" line).
                        return RepairResult(
                            ok=False, formula=None, repaired_text=text,
                            issues=(Issue(
                                "name_collision",
                                f"case-2 quoting {name!r} and {prior!r} both "
                                f"reduce to the same predicate name {capped!r} "
                                "once tptp_input capitalises the first "
                                "character of every parsed Atom predicate "
                                "(_cap) — quoting both would silently merge "
                                "two distinct predicates into one; refusing "
                                "rather than picking one arbitrarily.",
                            ),),
                            changed=False)
                    known_names[capped] = name
                    issues.append(Issue(
                        "invalid_predicate_name",
                        f"{name!r} is not a valid unquoted TPTP name "
                        "(fails lower_word: [a-z][A-Za-z0-9_]*); single-quoted "
                        "so the name is preserved exactly.",
                        suggestion=_tptp_quote(name)))
            if formula is None:
                return RepairResult(
                    ok=False, formula=None, repaired_text=text,
                    issues=(Issue("syntax_error", str(exc)),), changed=False)
        else:
            return RepairResult(
                ok=False, formula=None, repaired_text=text,
                issues=(Issue("syntax_error", str(exc)),), changed=False)

    # Independent of the case-2 path above: recover the exact spelling of
    # every name the CALLER already had quoted in the raw input (Finding-2
    # fix — see _find_prequoted_names), so _render never has to fall back to
    # _uncap's lossy guess for a name this module never itself quoted.
    # setdefault: the case-2 known_names entries above are exact/authoritative
    # (built from text this module itself controlled the quoting of) and
    # always take precedence over this best-effort text scan.
    for capped, original in _find_prequoted_names(text).items():
        known_names.setdefault(capped, original)

    canonical_before_close = _render(formula, known_names)
    if _squash(working_text) != _squash(canonical_before_close):
        issues.append(Issue(
            "bracket_normalisation",
            "the input parsed only via operator precedence; brackets made "
            "explicit (meaning-preserving — see repair_tptp_formula's "
            "docstring for the argument).",
            suggestion=canonical_before_close))

    free = free_variables(formula)
    final_formula = formula
    if free:
        names = ", ".join(sorted(v.name for v in free))
        if close_free_variables:
            dropped = _drop_argument_fix(formula, next(iter(free))) if len(free) == 1 else None
            if dropped is not None:
                final_formula = dropped
                issues.append(Issue(
                    "free_variable",
                    f"unbound variable {names!r} is the sole argument of the "
                    "left-hand definiendum and does not recur on the right — "
                    "dropped it (the definition is a 0-ary, molecule-level "
                    "property), per the paper's own fix for this shape.",
                    suggestion=_render(dropped, known_names)))
            else:
                final_formula = _close_universally(formula, free)
                issues.append(Issue(
                    "free_variable",
                    f"unbound variable(s) {names} closed via universal "
                    "quantification (standard universal-closure convention; "
                    "the paper's argument-drop fix does not apply — the "
                    "formula is not a `predicate(X) <=> …`/`predicate(X) => …` "
                    "definition with X absent from the right-hand side).",
                    suggestion=_render(final_formula, known_names)))
        else:
            issues.append(Issue(
                "free_variable",
                f"unbound variable(s) {names} — not closed (default "
                "close_free_variables=False). The kit will not guess whether "
                "you meant universal closure or an argument that should be "
                "dropped; pass close_free_variables=True to apply the "
                "documented conservative fix, or rewrite by hand."))

    repaired_text = _render(final_formula, known_names)
    changed = _squash(text) != _squash(repaired_text)
    return RepairResult(ok=True, formula=final_formula, repaired_text=repaired_text,
                         issues=tuple(issues), changed=changed)


# ---------------------------------------------------------------------------
# Whole-problem repair
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _Statement:
    name: str
    role: str
    formula_text: str
    formula_span: Tuple[int, int]


def _skip_ws_and_comments(text: str, i: int) -> int:
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == "%":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i:i + 2] == "/*":
            end = text.find("*/", i + 2)
            i = (end + 2) if end != -1 else n
        else:
            break
    return i


def _read_ident(text: str, i: int, what: str) -> Tuple[str, int]:
    n = len(text)
    start = i
    while i < n and (text[i].isalnum() or text[i] == "_"):
        i += 1
    if i == start:
        raise TptpRepairError(
            f"tptp_repair: expected {what} at position {start} in TPTP problem text")
    return text[start:i], i


def _expect(text: str, i: int, ch: str, what: str) -> int:
    if i >= len(text) or text[i] != ch:
        raise TptpRepairError(
            f"tptp_repair: expected {ch!r} ({what}) at position {i} in TPTP problem text")
    return i + 1


def _split_tptp_statements(text: str) -> Tuple[_Statement, ...]:
    """Locate every ``fof(name, role, FORMULA).`` / ``cnf(...)`` statement's
    exact ``FORMULA`` text span, without requiring the formula itself to be
    parseable — the whole point is to hand each formula to
    :func:`repair_tptp_formula` individually, so one broken statement must
    never prevent locating the others.

    A hand-rolled character scanner (not the Lark grammar) because the
    grammar's own ``file`` rule parses formulas inline: a syntax error in
    ANY one statement fails the whole file, which is exactly what per-formula
    repair needs to route around. Tracks ``'...'`` quoted atoms (backslash
    escapes) and ``%``/``/* */`` comments so parens/quotes inside them never
    perturb paren-depth tracking; a statement's formula ends at the first
    ``)`` seen at depth 0, which must be followed (after whitespace/comments)
    by ``.``.
    """
    n = len(text)
    i = 0
    out = []
    while True:
        i = _skip_ws_and_comments(text, i)
        if i >= n:
            break
        keyword, i = _read_ident(text, i, "'fof' or 'cnf'")
        if keyword not in ("fof", "cnf"):
            raise TptpRepairError(
                f"tptp_repair: unsupported TPTP statement keyword {keyword!r} "
                "(only fof and cnf are supported)")
        i = _skip_ws_and_comments(text, i)
        i = _expect(text, i, "(", "statement opening paren")
        i = _skip_ws_and_comments(text, i)
        name, i = _read_ident(text, i, "statement name")
        i = _skip_ws_and_comments(text, i)
        i = _expect(text, i, ",", "name/role separator")
        i = _skip_ws_and_comments(text, i)
        role, i = _read_ident(text, i, "statement role")
        i = _skip_ws_and_comments(text, i)
        i = _expect(text, i, ",", "role/formula separator")
        i = _skip_ws_and_comments(text, i)
        formula_start = i

        depth = 0
        in_quote = False
        m = i
        while m < n:
            c = text[m]
            if in_quote:
                if c == "\\":
                    m += 2
                    continue
                if c == "'":
                    in_quote = False
                m += 1
                continue
            if c == "'":
                in_quote = True
                m += 1
                continue
            if c == "%":
                while m < n and text[m] != "\n":
                    m += 1
                continue
            if text[m:m + 2] == "/*":
                end = text.find("*/", m + 2)
                m = (end + 2) if end != -1 else n
                continue
            if c == "(":
                depth += 1
                m += 1
                continue
            if c == ")":
                if depth == 0:
                    break
                depth -= 1
                m += 1
                continue
            m += 1
        if m >= n:
            raise TptpRepairError(
                f"tptp_repair: statement {name!r} has unbalanced parentheses "
                "(no closing ')' found for its formula)")
        formula_end = m
        after = _skip_ws_and_comments(text, m + 1)
        after = _expect(text, after, ".", "statement terminator")

        out.append(_Statement(name=name, role=role,
                               formula_text=text[formula_start:formula_end],
                               formula_span=(formula_start, formula_end)))
        i = after
    return tuple(out)


@dataclass(frozen=True)
class ProblemRepairEntry:
    """One statement's repair, with its ``fof(...)`` name/role preserved."""

    name: str
    role: str
    result: RepairResult

    def to_dict(self) -> dict:
        return {"name": self.name, "role": self.role, "result": self.result.to_dict()}


@dataclass(frozen=True)
class ProblemRepairResult:
    """Whole-file repair: every statement's :class:`ProblemRepairEntry`, plus
    the reassembled file text (each statement's ``fof(``/``, name, role,``/
    ``).`` wrapper and every byte between statements — comments included —
    kept byte-for-byte; only each formula's own span is replaced by its
    ``RepairResult.repaired_text``, and only when that repair succeeded).
    """

    entries: Tuple[ProblemRepairEntry, ...]
    ok: bool
    repaired_text: str
    changed: bool

    def to_dict(self) -> dict:
        return {
            "entries": [e.to_dict() for e in self.entries],
            "ok": self.ok,
            "repaired_text": self.repaired_text,
            "changed": self.changed,
        }


def repair_tptp_problem(text: str, *, quote_invalid_names: bool = True,
                         close_free_variables: bool = False) -> ProblemRepairResult:
    """:func:`repair_tptp_formula`, applied statement-by-statement to a whole
    TPTP problem file (one or more ``fof(name, role, formula).`` /
    ``cnf(...)`` statements).

    Each statement is repaired independently (see :func:`_split_tptp_statements`
    for why a whole-file Lark parse cannot be used here: one broken formula
    must not block the rest), and only its formula span is rewritten in the
    reassembled ``repaired_text`` — the wrapper, name, role, and every
    comment/blank line survive untouched. ``ok`` is the conjunction of every
    per-statement ``RepairResult.ok``; ``changed`` the disjunction.

    Raises:
        TptpRepairError: the file's statement STRUCTURE (not a formula's
            content) is malformed — an unrecognised keyword, a missing
            ``,``/``.``, or unbalanced parentheses that prevent even locating
            where a formula ends. Distinct from a per-formula syntax issue,
            which is reported per-entry instead.
    """
    statements = _split_tptp_statements(text)
    entries = []
    pieces = []
    cursor = 0
    all_ok = True
    any_changed = False
    for stmt in statements:
        result = repair_tptp_formula(
            stmt.formula_text, quote_invalid_names=quote_invalid_names,
            close_free_variables=close_free_variables)
        entries.append(ProblemRepairEntry(stmt.name, stmt.role, result))
        all_ok = all_ok and result.ok
        any_changed = any_changed or result.changed
        start, end = stmt.formula_span
        pieces.append(text[cursor:start])
        pieces.append(result.repaired_text)
        cursor = end
    pieces.append(text[cursor:])
    return ProblemRepairResult(entries=tuple(entries), ok=all_ok,
                                repaired_text="".join(pieces), changed=any_changed)
