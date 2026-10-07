"""The core facade: seven verbs for NL→logic pipelines.

``unicode_logic_kit.api`` bundles the whole toolkit behind a small, stable
vocabulary designed so that an LLM verification loop can consume every answer
without extra parsing:

    from unicode_logic_kit import api

    api.parse_any(text)          # dialect detection + tolerant parsing
    api.check(formula)           # well-formedness + optional signature check
    api.equivalent(f, g)         # graded equivalence (structural → solver)
    api.prove(f)                 # backend chain → one Verdict with provenance
    api.countermodel(f)          # refutation witness + plain-English gloss
    api.repair(text, fixer=llm)  # diagnose → suggest → (caller) fix → re-check
    api.translate(t, "alc", "fol")   # comorphism registry, composed via BFS

Every result object has ``to_dict()`` returning JSON-compatible data.

STABILITY POLICY (this module, :class:`~unicode_logic_kit.atp.protocol.Verdict`,
and the result dataclasses here): within a minor release line (0.N.x) nothing
is renamed or removed and dict keys only ever gain siblings; breaking changes
happen only at a minor bump, are listed in the CHANGELOG, and keep a
deprecation shim for one minor cycle where feasible. Downstream consumers
(e.g. FitchAsATP) should pin ``unicode-logic-kit>=0.N,<0.N+1`` per line.

Deliberately NOT re-exported at the package top level: ``prove`` would collide
with the resolution prover's ``prove`` that existing consumers already import
from ``unicode_logic_kit`` — the facade lives in this namespace, use
``api.prove``.
"""

import functools
import re
import sys
import threading
from dataclasses import dataclass
from typing import Callable, Iterator, Optional, Sequence, Tuple, TypeVar, Union

from .fol.nodes import Node, And
from .atp.protocol import (
    Verdict, BackendUnavailable, PROVED, REFUTED, UNKNOWN, ERROR,
    get_backend, default_chain, run_backend, _no_definitive_verdict,
    plan_options,
)
from .eval.equivalence import EquivalenceResult
from .eval.equivalence import equivalent as _equivalent
from .comorphism import DEFAULT_REGISTRY, TranslationResult

__all__ = [
    "ParseResult", "CheckResult", "RepairStep",
    "parse_any", "check", "equivalent", "prove", "countermodel",
    "repair", "translate",
    "EquivalenceResult", "Verdict", "TranslationResult", "CountermodelResult",
]


# ---------------------------------------------------------------------------
# parse_any — dialect detection + tolerant parsing
# ---------------------------------------------------------------------------

# The unicode-surface parser modes tried, in order, when the text is (or falls
# back to) the kit's own syntax. Broadest-first would mask mode-specific
# meanings (⊕ is Xor in fol but StrongDisjunction in fl), so classical first.
_UNICODE_MODES: Tuple[Tuple[str, dict], ...] = (
    ("fol", {}),
    ("modal", {"modal": True}),
    ("second_order", {"second_order": True}),
    # Second-order syntax plus predicates in argument position, and NOTHING
    # else: it is served by the same LALR table as the mode above it, so the
    # only inputs it newly accepts are the ones with a predicate really standing
    # in an argument slot -- which no mode above can express.
    #
    # Its MODAL sibling is deliberately NOT on the ladder. That one falls back
    # to Earley (inherited from `modal`, which needs it), and Earley reaches
    # readings LALR does not: with a second-order binder available, "∀ P(x)" parses
    # as a quantifier over the propositional atom `x` instead of failing. Every
    # other dialect reports that string as the malformed quantifier it is, and
    # the repair / error-routing machinery depends on their agreeing. Reach the
    # mode explicitly with MSFLParser(third_order=True, modal=True).
    ("third_order", {"third_order": True}),
    ("dependence", {"dependence": True}),
    ("msfol", {"many_sorted": True}),
    ("msfl", {"many_sorted": True, "fuzzy": True}),
    ("fl", {"fuzzy": True}),
    ("linear", {"linear": True}),
    ("lambek", {"lambek": True}),
)
_UNICODE_HINTS = {name: kwargs for name, kwargs in _UNICODE_MODES}

# The detection signals and their order live in fol.dialect_detect — one
# importable source of truth; parse_any consumes its candidate list.
from .fol.dialect_detect import detect_dialects


@dataclass(frozen=True)
class ParseResult:
    """Outcome of :func:`parse_any`.

    ``dialect`` names what succeeded (a unicode mode name, or ``"tptp"`` /
    ``"tptp_bare"`` / ``"latex"`` / ``"prover9"`` / ``"smtlib"``); ``errors``
    records every failed attempt as ``{"dialect": ..., "message": ...}`` so a
    repair loop can see exactly what each parser objected to.
    """

    ok: bool
    formula: Optional[Node] = None
    dialect: Optional[str] = None
    errors: Tuple[dict, ...] = ()

    def __bool__(self) -> bool:
        return self.ok

    def to_dict(self) -> dict:
        return {
            "ok": self.ok,
            "dialect": self.dialect,
            "formula": self.formula.to_dict() if self.formula is not None else None,
            "errors": list(self.errors),
        }


def _try(fn, dialect: str, errors: list) -> Optional[ParseResult]:
    """Run one parse attempt; success → ParseResult, failure → recorded."""
    try:
        node = fn()
    except Exception as exc:                      # each parser has its own error types
        errors.append({"dialect": dialect, "message": str(exc)})
        return None
    return ParseResult(ok=True, formula=node, dialect=dialect,
                       errors=tuple(errors))


def _parse_smtlib(text: str) -> Node:
    from .atp.z3_input import parse_smtlib
    asserts = parse_smtlib(text)
    if not asserts:
        raise ValueError("smtlib: no assertions found")
    conj = asserts[0]
    for a in asserts[1:]:                          # multiple asserts = their conjunction
        conj = And(conj, a)
    return conj


def _parse_tptp_annotated(text: str) -> Node:
    from .fol.tptp_input import parse_tptp
    records = parse_tptp(text)
    if len(records) != 1:
        raise ValueError(
            f"tptp: {len(records)} annotated formulas — parse_any handles a single "
            "formula; use parse_tptp / load_tptp_problem for whole problems")
    return records[0].formula


def _unicode_ladder(text: str, errors: list) -> ParseResult:
    """Try every unicode-surface mode in order; first success wins."""
    from .fol.msflparser import MSFLParser

    for name, kwargs in _UNICODE_MODES:
        result = _try(lambda k=kwargs: MSFLParser(**k).parse(text), name, errors)
        if result is not None:
            return result
    return ParseResult(ok=False, errors=tuple(errors))


def parse_any(text: str, *, hint: Optional[str] = None) -> ParseResult:
    """Parse ``text`` in whatever dialect it appears to be written.

    Detection order: SMT-LIB (``(assert`` …) → annotated TPTP (``fof(...)``) →
    LaTeX (``\\forall`` …) → the kit's own unicode surface syntax (mode ladder,
    classical first) → for pure-ASCII leftovers, bare TPTP (``![X]: ...``) and
    Prover9. Nothing raises: failure returns ``ok=False`` with every attempt's
    error message, ready for a repair loop.

    ``hint`` pins the dialect instead of detecting: a unicode mode name
    (``"fol"``, ``"modal"``, …), ``"unicode"`` (the whole mode ladder), or
    ``"tptp"`` / ``"tptp_bare"`` / ``"latex"`` / ``"prover9"`` / ``"smtlib"``.
    Multiple SMT-LIB assertions fold into their conjunction; a multi-formula
    TPTP problem is refused (use ``load_tptp_problem``).
    """
    errors: list = []

    if hint is not None:
        if hint in _UNICODE_HINTS:
            from .fol.msflparser import MSFLParser
            kwargs = _UNICODE_HINTS[hint]
            result = _try(lambda: MSFLParser(**kwargs).parse(text), hint, errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        if hint == "unicode":
            return _unicode_ladder(text, errors)
        if hint == "smtlib":
            result = _try(lambda: _parse_smtlib(text), "smtlib", errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        if hint == "tptp":
            result = _try(lambda: _parse_tptp_annotated(text), "tptp", errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        if hint == "tptp_bare":
            from .fol.tptp_input import parse_tptp_formula
            result = _try(lambda: parse_tptp_formula(text), "tptp_bare", errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        if hint == "latex":
            from .fol.latex_input import parse_latex
            result = _try(lambda: parse_latex(text), "latex", errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        if hint == "prover9":
            from .fol.prover9_input import parse_prover9
            result = _try(lambda: parse_prover9(text), "prover9", errors)
            return result or ParseResult(ok=False, errors=tuple(errors))
        raise ValueError(
            f"parse_any: unknown hint {hint!r} (unicode modes "
            f"{sorted(_UNICODE_HINTS)}, or 'unicode'/'tptp'/'tptp_bare'/"
            f"'latex'/'prover9'/'smtlib')")

    # detect_dialects nominates candidates in order (always ending in
    # "unicode", the mode-ladder catch-all); each one is tried and a parse
    # failure falls through to the next, accumulating its error.
    for dialect in detect_dialects(text):
        if dialect == "unicode":
            return _unicode_ladder(text, errors)
        if dialect == "smtlib":
            result = _try(lambda: _parse_smtlib(text), "smtlib", errors)
        elif dialect == "tptp":
            result = _try(lambda: _parse_tptp_annotated(text), "tptp", errors)
        elif dialect == "latex":
            from .fol.latex_input import parse_latex
            result = _try(lambda: parse_latex(text), "latex", errors)
        elif dialect == "tptp_bare":
            from .fol.tptp_input import parse_tptp_formula
            result = _try(lambda: parse_tptp_formula(text), "tptp_bare", errors)
        else:                                   # "prover9"
            from .fol.prover9_input import parse_prover9
            result = _try(lambda: parse_prover9(text), "prover9", errors)
        if result is not None:
            return result
    raise AssertionError("detect_dialects always ends in 'unicode'")


# ---------------------------------------------------------------------------
# Formulas nested deeper than the interpreter's recursion limit
#
# Most readers of a formula (a prover's translation, a validity check, a
# canonical form) recurse over it, and CPython's recursion limit (1000 by default)
# stops them at a nesting of a few hundred levels. A verb of this module does not
# let that surface as an exception: a formula nested at least ``_SHALLOW_DEPTH``
# levels deep is read on a worker thread whose stack and recursion limit are sized
# for it, and a reader that still runs out says so by the nesting depth.
# ---------------------------------------------------------------------------

_T = TypeVar("_T")

#: A formula nested fewer levels than this is handled on the calling thread under the
#: interpreter's own recursion limit, as every formula was before.
_SHALLOW_DEPTH = 100

#: What a deep run asks of the interpreter: the stack of its worker thread, the bytes
#: one Python frame may take of it (generous: a frame takes a few hundred), the frames
#: that one level of nesting costs a recursive reader (the backends that recurse most
#: take three on a chain of negations; eight leaves room for the other connectives) and
#: the frames the callers above the reader need.
_DEEP_STACK_BYTES = 128 * 1024 * 1024
_FRAME_BYTES = 2048
_FRAMES_PER_LEVEL = 8
_FRAME_HEADROOM = 1000

#: The deepest nesting a deep run takes on: the recursion limit it needs still fits the
#: stack, so a runaway recursion ends in a ``RecursionError``, never in a crash.
_DEEP_MAX_LEVELS = (_DEEP_STACK_BYTES // _FRAME_BYTES - _FRAME_HEADROOM) // _FRAMES_PER_LEVEL

#: The recursion limit and the stack size of new threads are process-wide settings; one
#: deep run at a time changes them.
_deep_run_lock = threading.Lock()

#: Set on the worker of a deep run: a call made from there is already where a deep formula
#: can be read, and waiting for the lock its own caller holds would wait for itself.
_on_deep_worker = threading.local()


def _nesting_depth(*formulas) -> int:
    """The most nodes on one path from a root down, over ``formulas`` (computed iteratively)."""
    from .atp.tableau import nesting_depth

    return nesting_depth(*(f for f in formulas if isinstance(f, Node)))


def _call_deep(depth: int, function: Callable[[], _T]) -> _T:
    """The result of ``function()``, run where a formula nested ``depth`` levels deep can be read.

    A ``depth`` below ``_SHALLOW_DEPTH``, above what the worker's stack carries
    (``_DEEP_MAX_LEVELS``), or within a recursion limit the caller has already raised
    is called on the calling thread, unchanged. Otherwise the call runs on a worker
    thread with a stack of ``_DEEP_STACK_BYTES`` and a recursion limit of
    ``_FRAMES_PER_LEVEL`` frames per level, both restored when it returns; what the
    function raises is raised on the calling thread. A worker that cannot be started
    leaves the call on the calling thread. Calls of this kind do not overlap: the
    recursion limit belongs to the whole process.
    """
    if not _SHALLOW_DEPTH <= depth <= _DEEP_MAX_LEVELS or getattr(_on_deep_worker, "on", False):
        return function()
    needed = depth * _FRAMES_PER_LEVEL + _FRAME_HEADROOM
    if sys.getrecursionlimit() >= needed:
        return function()

    outcome: dict = {}

    def work() -> None:
        _on_deep_worker.on = True
        try:
            outcome["value"] = function()
        except BaseException as exc:                  # re-raised on the calling thread
            outcome["error"] = exc

    with _deep_run_lock:
        limit = sys.getrecursionlimit()
        stack = threading.stack_size()
        started = False
        try:
            sys.setrecursionlimit(max(limit, needed))
            threading.stack_size(_DEEP_STACK_BYTES)
            worker = threading.Thread(target=work, name="unicode-logic-kit-deep", daemon=True)
            try:
                worker.start()
                started = True
            finally:
                threading.stack_size(stack)
            worker.join()
        except (ValueError, RuntimeError):
            if started:
                raise
        finally:
            sys.setrecursionlimit(limit)
    if not started:
        return function()                              # no worker could be started
    if "error" in outcome:
        raise outcome["error"]
    return outcome["value"]


def _deep_detail(depth: int, who: str) -> str:
    """The sentence that names the nesting depth a reader could not follow."""
    return (f"a formula nested {depth} levels deep is deeper than {who} can read within the "
            f"interpreter's recursion limit ({sys.getrecursionlimit()}): nothing was decided")


def _name_nesting(verdict: Verdict, depth: int) -> Verdict:
    """``verdict`` with the nesting depth named, when the member failed because of it.

    A backend that ran out of recursion on a deep formula answers ``error`` /
    ``infra`` with the bare ``RecursionError``; here it becomes ``unknown`` /
    ``bound_hit`` with the depth in its detail, the way the tableau reports a formula
    nested deeper than it can read (the recursion limit is a bound of the search). Any
    other member that mentions the recursion limit gets the depth appended to what it said.
    """
    if depth < _SHALLOW_DEPTH or verdict.is_definitive:
        return verdict
    from dataclasses import replace as _replace

    detail = verdict.detail or ""
    if verdict.status == ERROR and verdict.reason == "infra" and detail.startswith("RecursionError"):
        return _replace(verdict, status=UNKNOWN, reason="bound_hit", szs_status=None,
                        detail=_deep_detail(depth, f"the {verdict.backend} backend"))
    said = detail.lower()
    if ("recursion limit" in said or "recursion depth" in said) and "levels deep" not in said:
        return _replace(verdict, detail=f"{detail} ({_deep_detail(depth, 'the backend')})")
    return verdict


# ---------------------------------------------------------------------------
# check — well-formedness + optional signature conformance
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CheckResult:
    """Outcome of :func:`check` — a ValidationReport plus signature errors.

    ``ok`` is the headline: parseable AND closed AND arity-consistent AND
    lambda-free AND (when a signature was given) signature-conformant.
    ``signature_errors`` entries are dicts with ``kind`` ∈
    ``{"unknown_predicate", "unknown_function", "unknown_constant",
    "wrong_arity"}`` plus ``symbol`` and, where applicable,
    ``expected``/``seen`` and a ``suggestion`` (closest signature symbol).
    """

    ok: bool
    parseable: bool
    is_closed: bool
    free_variables: Tuple[str, ...]
    arity_consistent: bool
    arity_conflicts: Tuple[dict, ...]
    has_lambdas: bool
    predicates: Tuple[str, ...]
    functions: Tuple[str, ...]
    constants: Tuple[str, ...]
    signature_errors: Tuple[dict, ...] = ()
    error: Optional[str] = None

    def __bool__(self) -> bool:
        return self.ok

    def to_dict(self) -> dict:
        return {
            "ok": self.ok,
            "parseable": self.parseable,
            "is_closed": self.is_closed,
            "free_variables": list(self.free_variables),
            "arity_consistent": self.arity_consistent,
            "arity_conflicts": list(self.arity_conflicts),
            "has_lambdas": self.has_lambdas,
            "predicates": list(self.predicates),
            "functions": list(self.functions),
            "constants": list(self.constants),
            "signature_errors": list(self.signature_errors),
            "error": self.error,
        }


def _closest(name: str, candidates) -> Optional[str]:
    """The lexically closest candidate for a did-you-mean suggestion."""
    import difflib
    matches = difflib.get_close_matches(name, list(candidates), n=1, cutoff=0.6)
    return matches[0] if matches else None


def _signature_errors(report, signature: dict) -> Tuple[dict, ...]:
    """Compare a ValidationReport's inventories against a signature spec.

    ``signature`` keys (all optional): ``"predicates"`` / ``"functions"`` map
    name → arity (or an iterable of allowed arities); ``"constants"`` is an
    iterable of names. Symbols absent from a PROVIDED section are unknown;
    a section left out entirely is unconstrained.
    """
    def allowed_arities(spec_value):
        if isinstance(spec_value, int):
            return {spec_value}
        return set(spec_value)

    errors = []
    for section, kind_unknown, inventory in (
        ("predicates", "unknown_predicate", report.predicates),
        ("functions", "unknown_function", report.functions),
    ):
        if section not in signature:
            continue
        spec = signature[section]
        for entry in inventory:                    # entries look like "Name/2"
            name, _, arity_text = entry.rpartition("/")
            arity = int(arity_text)
            if name not in spec:
                errors.append({
                    "kind": kind_unknown, "symbol": name, "arity": arity,
                    "suggestion": _closest(name, spec),
                })
            elif arity not in allowed_arities(spec[name]):
                errors.append({
                    "kind": "wrong_arity", "symbol": name,
                    "expected": sorted(allowed_arities(spec[name])), "seen": arity,
                    "suggestion": None,
                })
    if "constants" in signature:
        known = set(signature["constants"])
        for name in report.constants:
            if name not in known:
                errors.append({
                    "kind": "unknown_constant", "symbol": name,
                    "suggestion": _closest(name, known),
                })
    return tuple(errors)


def _declares_sorts(signature) -> bool:
    """Whether a signature dict is in the rich form :meth:`Signature.to_dict` emits.

    That is the case when it has a ``"sorts"`` or a ``"subsorts"`` key, when an
    entry of ``"predicates"`` / ``"functions"`` is itself a dict
    (``{"arity": 1, "arg_sorts": None}``), or when ``"constants"`` is a dict that
    gives some constant a sort. Everything else is the loose convention of
    :func:`_signature_errors`.
    """
    from collections.abc import Mapping

    if "sorts" in signature or "subsorts" in signature:
        return True
    for section in ("predicates", "functions"):
        spec = signature.get(section)
        if isinstance(spec, Mapping) and any(isinstance(v, Mapping) for v in spec.values()):
            return True
    constants = signature.get("constants")
    return isinstance(constants, Mapping) and any(v is not None for v in constants.values())


def _loose_signature(signature) -> dict:
    """The loose spec of ``signature`` (a dict), after checking its shape.

    ``ValueError`` naming the offending key for what :func:`_signature_errors` could
    not read: a key other than ``predicates`` / ``functions`` / ``constants``, a
    section that is not a dict from a name to an arity (an ``int``, or a list of
    allowed arities), a ``constants`` section that is not a list of names. It is a
    ``ValueError`` (not a ``TypeError``) because the dict is a document, often a
    JSON file, whose content is invalid; the command line reports that one cleanly.
    """
    from collections.abc import Mapping

    allowed = ("constants", "functions", "predicates")
    unknown = sorted(str(key) for key in signature if key not in allowed)
    if unknown:
        raise ValueError(
            f"check: signature has the unknown key(s) {unknown}; the loose form has "
            f"{list(allowed)} (the form Signature.to_dict() emits also has 'sorts' and "
            "'subsorts')")
    for section in ("predicates", "functions"):
        if section not in signature:
            continue
        spec = signature[section]
        if not isinstance(spec, Mapping):
            raise ValueError(
                f"check: signature[{section!r}] must be a dict from each name to its arity "
                f"(an int, or a list of allowed arities), got {type(spec).__name__} {spec!r}")
        for name, value in spec.items():
            arities = value if isinstance(value, (list, tuple, set, frozenset)) else (value,)
            if not all(isinstance(a, int) and not isinstance(a, bool) for a in arities):
                raise ValueError(
                    f"check: signature[{section!r}][{name!r}] must be an arity (an int) or a "
                    f"list of allowed arities, got {value!r}")
    if "constants" in signature:
        constants = signature["constants"]
        if (isinstance(constants, str) or not isinstance(constants, (list, tuple, set, frozenset, Mapping))
                or not all(isinstance(c, str) for c in constants)):
            raise ValueError(
                f"check: signature['constants'] must be a list of constant names, got "
                f"{type(constants).__name__} {constants!r}")
    return dict(signature)


def _read_signature(signature):
    """``(loose spec, Signature or None)`` for the ``signature=`` of :func:`check`.

    A :class:`~unicode_logic_kit.fol.signature.Signature` is projected onto the loose
    convention (name → arity per namespace, constant name list) and kept as the
    object, because its sort declarations have no loose counterpart. A dict in the
    rich form that :meth:`~unicode_logic_kit.fol.signature.Signature.to_dict` emits is
    read as the ``Signature`` it describes (:meth:`~unicode_logic_kit.fol.signature.Signature.from_dict`,
    whose own refusals name the entry), so what ``to_dict`` returns passes
    :func:`check` unchanged. Any other dict is the loose convention, shape-checked.
    ``None`` is ``(None, None)``. ``TypeError`` for an argument that is neither a
    ``Signature`` nor a dict, ``ValueError`` (naming the entry) for a dict that is
    malformed: a malformed ``signature=`` is a mistake of the caller's, never a
    verdict about a formula.
    """
    from collections.abc import Mapping
    from .fol.signature import Signature as _Signature

    if signature is None:
        return None, None
    if isinstance(signature, Mapping):
        if not _declares_sorts(signature):
            return _loose_signature(signature), None
        try:
            signature = _Signature.from_dict(signature)
        except TypeError as exc:                 # from_dict says "wrong type" with a TypeError
            raise ValueError(str(exc)) from exc
    if not isinstance(signature, _Signature):
        raise TypeError(
            f"check: signature= must be a unicode_logic_kit.fol.signature.Signature or a dict, got "
            f"{type(signature).__name__}")
    # Project onto the loose convention for the classic diagnostics (unknown
    # symbol / wrong arity, with did-you-mean suggestions), but KEEP the object:
    # its sort declarations have no loose-dict counterpart and are checked
    # additionally in check() (dropping them silently returned ok=True on
    # sort-violating formulas the object itself rejects).
    return {
        "predicates": {d.name: d.arity for d in signature.predicates.values()},
        "functions": {d.name: d.arity for d in signature.functions.values()},
        "constants": sorted(signature.constants),
    }, signature


def check(formula: Union[Node, str], *, signature=None,
          dialect: Optional[str] = None) -> CheckResult:
    """Well-formedness report for a formula (or raw text) — never raises for a formula.

    Accepts a parsed ``Node`` or a raw string (which goes through
    :func:`parse_any` first, honouring ``dialect`` as its hint). The
    structural checks are :func:`unicode_logic_kit.eval.validate`'s: closedness,
    per-namespace arity consistency, lambda residue. ``signature`` adds
    vocabulary conformance with did-you-mean suggestions (see
    :func:`_signature_errors` for the loose-dict spec format) — and also
    accepts a first-class :class:`unicode_logic_kit.fol.signature.Signature`,
    which is projected onto that loose convention (name → arity per
    namespace, constant name list) so the structured did-you-mean
    diagnostics stay identical either way, and the dict that
    :meth:`~unicode_logic_kit.fol.signature.Signature.to_dict` returns (what the
    ``get_signature`` tool hands out), which is read as the ``Signature`` it
    describes. The two truth constants (``⊤`` / ``$true``, ``⊥`` / ``$false``) are
    logical constants, not predicates: they are listed in no inventory and are
    never an unknown predicate. A malformed ``signature`` is a mistake of the
    caller's, not a property of the formula: ``TypeError`` for an argument that is
    neither a ``Signature`` nor a dict, ``ValueError`` naming the entry for a dict
    with a key that is none of the sections, a section of the wrong type, or a rich
    entry ``Signature.from_dict`` refuses. A formula nested too deeply for the
    checks to read it (see :func:`prove`) comes back as ``ok=False`` with ``error``
    naming the nesting depth, never as a ``RecursionError``.
    """
    from .eval.validate import validate

    signature, signature_object = _read_signature(signature)

    if isinstance(formula, str):
        parsed = parse_any(formula, hint=dialect)
        if not parsed.ok or parsed.formula is None:    # an ok result always carries its formula
            message = parsed.errors[-1]["message"] if parsed.errors else "unparseable"
            return CheckResult(
                ok=False, parseable=False, is_closed=False, free_variables=(),
                arity_consistent=False, arity_conflicts=(), has_lambdas=False,
                predicates=(), functions=(), constants=(), error=message)
        formula = parsed.formula

    def examine() -> CheckResult:
        report = validate(formula)
        conflicts = tuple(
            {"namespace": ns, "symbol": name, "arities": list(arities)}
            for (ns, name), arities in sorted(report.arity_conflicts.items()))
        sig_errors = _signature_errors(report, signature) if signature else ()
        if signature_object is not None:
            # The Signature's own validate() covers what the projection cannot:
            # declared argument/result/constant SORTS. Only its sort messages
            # are added (the undeclared/arity classes are already reported
            # above with richer, did-you-mean-carrying dicts).
            sort_errors = tuple(
                {"kind": "sort_mismatch", "message": message, "suggestion": None}
                for message in signature_object.validate(formula)
                if "sort" in message)
            sig_errors = tuple(sig_errors) + sort_errors
        ok = (report.is_closed and report.arity_consistent
              and not report.has_lambdas and not sig_errors)
        return CheckResult(
            ok=ok, parseable=True,
            is_closed=report.is_closed, free_variables=report.free_variable_names,
            arity_consistent=report.arity_consistent, arity_conflicts=conflicts,
            has_lambdas=report.has_lambdas,
            predicates=report.predicates, functions=report.functions,
            constants=report.constants,
            signature_errors=sig_errors)

    depth = _nesting_depth(formula)
    try:
        return _call_deep(depth, examine)
    except RecursionError:
        # nested deeper than a recursive reader can follow, even on the deep worker: the
        # report is not made up, the result says why there is none
        return CheckResult(
            ok=False, parseable=True, is_closed=False, free_variables=(),
            arity_consistent=False, arity_conflicts=(), has_lambdas=False,
            predicates=(), functions=(), constants=(),
            error=_deep_detail(depth, "the checks"))


@functools.wraps(_equivalent)
def equivalent(prediction: Node, reference: Node, **options) -> EquivalenceResult:
    depth = _nesting_depth(prediction, reference)
    try:
        return _call_deep(depth, lambda: _equivalent(prediction, reference, **options))
    except RecursionError:
        # nested deeper than a recursive level can follow, even on the deep worker: the
        # question stays undecided, and the result says why
        method = options.get("method", "auto")
        return EquivalenceResult(
            equivalent=None,
            method_used="solver" if method == "auto" else method,
            reason=_deep_detail(depth, "the equivalence levels"))


# ---------------------------------------------------------------------------
# prove / countermodel — the backend chain
# ---------------------------------------------------------------------------

#: Node types that are the SOLE occupant of their own parser mode — a formula
#: containing one of these can only have come from that mode's grammar, so
#: routing on it is sound (see logic_backends' module docstring). Order
#: matters: hybrid is checked before the general modal test because
#: `atp.modal_tableau.has_modal` itself also counts Nominal/At as "modal"
#: (so the classical tableau gets a clean hybrid-specific rejection) — here
#: we want the MORE SPECIFIC "hybrid" logic label, not "modal", for exactly
#: those formulas. Intuitionistic and relevant logic reuse the plain
#: classical AST with no marker of their own, so they are deliberately
#: ABSENT from this table — `logic=` must be given explicitly for those two.
def _detect_logic(formula: Node, premises: Sequence[Node]) -> str:
    from .atp.modal_tableau import has_modal
    from .fol.nodes import Nominal, At, Product, Under, Over
    from .fol._linear_nodes import (
        Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero,
    )

    formulas = (formula, *premises)

    def _contains(*node_types) -> bool:
        return any(isinstance(node, node_types)
                  for f in formulas for node in f.walk())

    if _contains(Nominal, At):
        return "hybrid"
    if _contains(Product, Under, Over):
        return "lambek"
    if _contains(Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero):
        return "ill"
    if any(has_modal(f) for f in formulas):
        return "modal"
    return "fol"


#: Which backend names this facade knows how to ask for premise relevance,
#: and the free function that answers it — see :func:`_attach_relevant_premises`.
#: Deliberately NOT every backend :func:`prove` can route to: a route with no
#: entry here leaves ``Verdict.relevant_premises`` at its default ``None``
#: rather than guessing. Vampire has no entry either, for the opposite reason:
#: its own verdict already carries the caller's premise indices (the backend asks
#: Vampire for the names of the axioms of its proof), so there is nothing to
#: re-ask.
def _relevant_premises_for(backend_name: str, formula: Node, premises: Sequence[Node],
                           timeout: int) -> Optional[Tuple[int, ...]]:
    if backend_name == "z3":
        from .atp.protocol import z3_relevant_premises
        return z3_relevant_premises(formula, premises, timeout=timeout)
    if backend_name == "eprover":
        from .atp.eprover_backend import eprover_relevant_premises
        return eprover_relevant_premises(list(premises), formula, timeout=max(1, timeout // 1000))
    return None


def _attach_relevant_premises(verdict: Verdict, formula: Node, premises: Sequence[Node],
                              timeout: int) -> Verdict:
    """Best-effort: fill ``relevant_premises`` on a PROVED verdict, using
    whichever route :func:`_relevant_premises_for` supports for the backend
    that actually produced ``verdict`` — re-running that SAME query, not a
    different one, so the reported premises are relevant to the ANSWER the
    caller got, not to some other backend's independent proof of the same
    entailment. Leaves ``verdict`` untouched (``relevant_premises`` stays its
    default ``None``) when the winning backend has no route, or that route
    itself could not produce a trustworthy answer.
    """
    if verdict.status != PROVED or verdict.relevant_premises is not None:
        return verdict          # a backend that already reports them (Vampire) is not asked again
    try:
        indices = _relevant_premises_for(verdict.backend, formula, premises, timeout)
    except RecursionError:
        return verdict          # a formula nested deeper than the re-run can read: no breakdown
    if indices is None:
        return verdict
    from dataclasses import replace as _replace
    return _replace(verdict, relevant_premises=indices)


def _unwrap_sentences(formula, premises, route: str):
    """Accept :class:`unicode_logic_kit.logic.Sentence` values next to bare nodes.

    A Sentence carries the side axioms of the translation that produced it (the
    non-emptiness of every sort AND the membership atom ``S(c)`` of every sorted
    constant of a many-sorted formula, frame conditions, a domain regime). Those are exactly the
    premises the question needs, so a Sentence handed to a decision route is
    unwrapped WITH them instead of having them silently dropped — dropping them
    is how a valid formula comes back REFUTED. A Sentence in a logic other than
    classical FOL is refused by name: convert it first.
    """
    from .logic import Sentence                       # local: logic imports api-free
    extra = []
    def one(value, what):
        if not isinstance(value, Sentence):
            return value
        if value.logic not in ("fol", "msfol"):
            raise ValueError(
                f"{route}: {what} is a Sentence in logic {value.logic!r}, which "
                f"these routes do not decide — convert it first, e.g. "
                f"FOL(sentence) (unicode_logic_kit.logic), and pass that")
        extra.extend(value.axioms)
        return value.term
    formula = one(formula, "the goal")
    premises = [one(p, f"premise {i}") for i, p in enumerate(premises)]
    return formula, premises + extra


def _signature_premises(caller: str, signature, logic: str) -> Tuple[Node, ...]:
    """The premises that ``signature=`` adds to a call: :func:`~unicode_logic_kit.fol.signature_axioms`.

    ``TypeError`` for anything but a :class:`~unicode_logic_kit.fol.signature.Signature`
    (a dict is turned into one with ``Signature.from_dict``), and ``ValueError`` for a
    logic other than classical first-order logic: the sentences are plain first-order
    assumptions, and a modal, hybrid, intuitionistic or substructural route would read
    them at one world or one resource only, where a sort guard is world-relative and a
    constant is a rigid designator.
    """
    from .fol.signature import Signature
    from .fol._msfl_nodes import signature_axioms

    if not isinstance(signature, Signature):
        raise TypeError(
            f"{caller}: signature= must be a unicode_logic_kit.fol.signature.Signature, got "
            f"{type(signature).__name__}; build one from a dict with Signature.from_dict(d)")
    if logic != "fol":
        raise ValueError(
            f"{caller}: signature= is read by the classical first-order routes only, and "
            f"the logic of this call is {logic!r}: what a signature declares is added as "
            "plain first-order assumptions, and a route for another logic would read them "
            "at one world (or one resource) only -- a sort guard is world-relative and a "
            "constant is a rigid designator there. Leave signature= out, or state the "
            "declarations in the formula.")
    return signature_axioms(signature)


def _name_background(options: dict, passed: int, total: int, caller: str) -> dict:
    """``options`` with ``premise_names=`` extended by names for the premises that were
    appended to the ``passed`` the caller gave (the signature's sentences, the side axioms of
    a Sentence): ``total`` premises are asked, the caller named only its own.

    The names are the caller's premises', so what a prover reports about its proof is read as
    the caller's own premises; the appended ones are background and are named by the writer
    (:func:`~unicode_logic_kit.atp._writer_support.name_background_premises`). Without
    ``premise_names=``, or when nothing was appended, ``options`` is returned as it is."""
    names = options.get("premise_names")
    if names is None or total == passed:
        return options
    from .atp._writer_support import name_background_premises
    return {**options, "premise_names": name_background_premises(names, passed, total,
                                                                  where=caller)}


def _without_background(verdict: Verdict, given: int) -> Verdict:
    """``verdict`` with the premises that ``signature=`` appended removed from what it indexes.

    A backend that tracks its premises (Z3's unsat core, a premise-relevance query)
    names them by position, and the signature's sentences stand after the caller's
    ``given`` premises. Only the caller's own premises are reported back, as indices
    into the caller's own list.
    """
    from dataclasses import replace as _replace

    changes: dict = {}
    if verdict.relevant_premises is not None:
        kept = tuple(i for i in verdict.relevant_premises if i < given)
        if kept != tuple(verdict.relevant_premises):
            changes["relevant_premises"] = kept
    proof = verdict.proof
    if isinstance(proof, dict) and proof.get("kind") == "z3_unsat_core":
        core = list(proof.get("core", ()))
        kept_core = [tag for tag in core
                     if not (tag.startswith("p") and tag[1:].isdigit() and int(tag[1:]) >= given)]
        if kept_core != core:
            changes["proof"] = {**proof, "core": kept_core}
    return _replace(verdict, **changes) if changes else verdict


def prove(formula: Node, premises: Sequence[Node] = (), *,
          logic: str = "auto", backends: Optional[Sequence[str]] = None,
          timeout: int = 10000, require_agreement: int = 1,
          relevant_premises: bool = False, signature=None,
          **options) -> Verdict:
    """Decide ``premises ⊨ formula`` over a chain of backends.

    ``logic="auto"`` routes by syntax (modal operators → the modal chain).
    ``backends=None`` uses :func:`~unicode_logic_kit.atp.protocol.default_chain`
    — fast, deterministic, and never silently expensive (the minutes-per-call
    ``isabelle`` backend runs only when named explicitly). An explicitly named
    backend that is missing raises
    :class:`~unicode_logic_kit.atp.protocol.BackendUnavailable`; one that does
    not support the detected logic raises ``ValueError``.

    The chain runs in order and returns the first DEFINITIVE verdict (proved /
    refuted). With ``require_agreement=n`` > 1 it keeps going until ``n``
    backends report the same definitive status — the returned verdict's
    ``agreement`` then lists them all. If nothing definitive emerges, the
    result is an UNKNOWN verdict from the pseudo-backend ``"chain"`` whose
    ``detail`` summarises every member's answer: for each member that ran, its
    status, its reason, and its own account of them when it gave one (the
    refusal of a prover that would not read its input, the bound a search hit).
    When EVERY member failed the result is an ERROR verdict
    rather than an UNKNOWN one: nothing was asked and answered, and "unknown"
    would read like a question that ran out of time.

    ``relevant_premises=True`` additionally fills the returned verdict's
    ``relevant_premises`` field on a PROVED result, by re-asking the SAME
    winning backend which premises it actually needed (see
    :mod:`unicode_logic_kit.atp.protocol`'s ``z3_relevant_premises`` and
    :mod:`unicode_logic_kit.atp.eprover_backend`'s
    ``eprover_relevant_premises``) — currently supported only when that
    backend is ``"z3"`` or ``"eprover"``; any other winning backend (or a
    query that route itself could not answer) leaves the field at its
    default ``None`` rather than guessing. Off by default: it re-runs the
    winning backend's decision procedure a second time, so only pay for it
    when the caller actually wants the breakdown. The ``"vampire"`` backend
    needs no second run: its verdict carries the caller's premise indices
    whenever its proof names its axioms (see
    :class:`~unicode_logic_kit.atp.protocol.VampireBackend`), with or without
    this flag, and ``premise_names=`` names the premises it reads them by.
    The indices are indices into ``premises`` as the caller gave them: the side
    axioms that a :class:`~unicode_logic_kit.logic.Sentence` brings along (the
    non-emptiness of its sorts, the membership atoms of its sorted constants) and
    the sentences of ``signature=`` are background, and are never reported as
    premises.

    ``signature=`` (a :class:`~unicode_logic_kit.fol.signature.Signature`; a dict
    is a ``TypeError`` that points at ``Signature.from_dict``) states what the
    caller declared: the sorts, the sort of each constant, the argument and result
    sorts of each function, the subsort edges. What it declares is added to the
    premises of every backend of the chain as the sentences
    :func:`~unicode_logic_kit.fol.signature_axioms` returns, so ``f: A → B`` makes
    ``∃x:B x = f(carl:A)`` valid, a constant declared in a sort is in it, and a
    subsort edge ``A < B`` is the inclusion ``A ⊆ B``. A predicate's declared
    argument sorts add nothing: a predicate is a relation over the whole universe.
    Indices that come back (``relevant_premises``, the Z3 core) stay indices into
    ``premises``. The input is NOT checked against the signature -- a formula
    that uses an undeclared symbol is decided as written; that check is
    ``api.check(formula, signature=...)``. Only the classical first-order routes
    read a signature (``ValueError`` for another logic).

    Extra keyword ``options`` go to the backends that read them, each backend
    being handed only the options it declares
    (:meth:`~unicode_logic_kit.atp.protocol.ProverBackend.accepted_options`). An
    option that NO backend of the chain reads is a ``ValueError`` naming the
    option and the chain, raised before anything runs: it would otherwise be
    ignored, and the answer given to a question the caller did not ask. A backend
    that does not read an option that changes the question (a modal ``frame=``,
    ``bridges=``, a ``subsorts=`` edge) while another backend of the chain does is
    not run: it is listed in the chain's ``detail`` as ``unknown/unsupported``,
    with the option named. An option that only bounds a search or says where a
    binary lives (``max_steps=``, ``use_wsl=``) is simply not handed to a backend
    that has no use for it.

    A formula nested a hundred levels deep or more is decided on a worker thread
    whose stack and recursion limit are sized for it (up to a nesting of about
    eight thousand levels), so the interpreter's recursion limit does not decide
    which backend can read it. A backend that still cannot is ``unknown`` /
    ``bound_hit`` and its detail names the nesting depth; nothing in this
    function raises ``RecursionError``.
    """
    premises = list(premises)
    passed_premises = len(premises)
    formula, premises = _unwrap_sentences(formula, premises, "prove")
    if logic == "auto":
        logic = _detect_logic(formula, premises)
    chain = tuple(backends) if backends is not None else default_chain(logic)

    for name in chain:
        backend = get_backend(name)                # ValueError on unknown names
        if logic not in backend.logics:
            raise ValueError(
                f"prove: backend {name!r} does not support logic {logic!r} "
                f"(it handles {sorted(backend.logics)})")

    if signature is not None:
        premises = [*premises, *_signature_premises("prove", signature, logic)]
    options = _name_background(options, passed_premises, len(premises), "prove")
    plan = plan_options("prove", chain, logic, options)
    depth = _nesting_depth(formula, *premises)

    def run_chain() -> Verdict:
        verdicts = []
        agreeing: dict = {}
        for name in chain:
            passed, refusal = plan[name]
            if refusal is not None:
                verdicts.append(Verdict(UNKNOWN, name, logic=logic, reason="unsupported",
                                        detail=refusal))
                continue
            extra = dict(passed)
            if name == "isabelle":
                extra["logic"] = logic                # the dual-logic backend routes on it
            verdict = _name_nesting(
                run_backend(name, formula, premises, timeout=timeout, **extra), depth)
            verdicts.append(verdict)
            if verdict.is_definitive:
                group = agreeing.setdefault(verdict.status, [])
                group.append(verdict)
                if len(group) >= require_agreement:
                    first = group[0]
                    if len(group) == 1:
                        result = first
                    else:
                        from dataclasses import replace as _replace
                        result = _replace(first, agreement=tuple(v.backend for v in group))
                    if relevant_premises:
                        result = _attach_relevant_premises(result, formula, premises, timeout)
                    # what the signature and the side axioms of a Sentence added is
                    # background: only the caller's own premises are indexed back
                    return (_without_background(result, passed_premises)
                            if len(premises) > passed_premises else result)

        return _no_definitive_verdict("chain", logic, verdicts, "empty backend chain")

    return _call_deep(depth, run_chain)


@dataclass(frozen=True)
class CountermodelResult:
    """Outcome of :func:`countermodel`.

    ``found`` says whether a witness exists; ``model`` is the JSON-able
    witness dict (same shapes as ``Verdict.countermodel``), ``backend`` names
    the route that found it, and ``explanation_nl`` is a short plain-English
    rendering from :func:`unicode_logic_kit.eval.explain.explain_countermodel`
    (a structured Kripke witness is rebuilt and narrated world by world; a
    Z3 assignment is read out; an opaque witness falls back to a one-line
    gloss of its kind). ``reason`` is ``None`` unless a backend could not read
    the formula it was given: a formula nested deeper than a recursive reader
    can follow is named there by its nesting depth, so that ``found=False`` is
    not mistaken for a finished search.
    """

    found: bool
    model: Optional[dict] = None
    backend: Optional[str] = None
    explanation_nl: Optional[str] = None
    reason: Optional[str] = None

    def __bool__(self) -> bool:
        return self.found

    def to_dict(self) -> dict:
        return {"found": self.found, "model": self.model,
                "backend": self.backend, "explanation_nl": self.explanation_nl,
                "reason": self.reason}


_WITNESS_GLOSS = {
    "finite_structure": "A finite first-order structure satisfies the premises "
                        "but falsifies the conclusion.",
    "z3_model": "An assignment of the symbols (found by Z3) makes the premises "
                "true and the conclusion false.",
    "kripke": "A Kripke model falsifies the formula at its root world.",
    "nitpick": "Isabelle's nitpick found a finite counter-interpretation.",
}


def _explain_witness(witness: dict, formula: Node,
                     premises: Sequence[Node]) -> Optional[str]:
    """Best-effort plain-English rendering of a Verdict witness dict.

    A ``"kripke"`` witness carrying the structured ``"data"`` payload is
    rebuilt into a real KripkeModel so
    :func:`~unicode_logic_kit.eval.explain.explain_countermodel` can narrate
    its worlds (the formula handed along for the world-0 check is the folded
    goal ``(∧ premises) → formula`` — that is what the model falsifies, not
    the bare conclusion). Every other shape goes to ``explain_countermodel``
    directly. This field is presentational: if the rendering fails for an
    unforeseen witness payload, the one-line kind gloss is the fallback —
    never an exception out of :func:`countermodel`.
    """
    from .eval.explain import explain_countermodel

    try:
        data = witness.get("data")
        if witness.get("kind") == "kripke" and isinstance(data, dict):
            from .atp.kripke_enum import kripke_model_from_dict
            from .fol.nodes import Implies
            goal = formula
            if premises:
                conj = premises[0]
                for p in premises[1:]:
                    conj = And(conj, p)
                goal = Implies(conj, goal)
            return explain_countermodel(kripke_model_from_dict(data), goal)
        return explain_countermodel(witness)
    except Exception:
        kind = witness.get("kind")
        return _WITNESS_GLOSS.get(kind) if kind is not None else None


def countermodel(formula: Node, premises: Sequence[Node] = (), *,
                 logic: str = "auto", backends: Optional[Sequence[str]] = None,
                 timeout: int = 10000, signature=None,
                 **options) -> CountermodelResult:
    """Search for a countermodel to ``premises ⊨ formula``.

    Runs the refutation-capable backends for the logic (FOL: the finite model
    finder first — its structures are the most readable — then Z3; modal: the
    labelled tableau, then the bounded Kripke-model enumeration — the only
    route that can refute a temporal-closure formula) and returns the first
    witness. ``found=False`` means "no countermodel within the budgets",
    never a validity claim.

    ``signature=`` and the extra ``options`` mean here what they mean in
    :func:`prove`: what a :class:`~unicode_logic_kit.fol.signature.Signature`
    declares is added to the premises of every backend, so the witness is a
    structure in which the declarations hold; an option that no backend of the
    chain reads is a ``ValueError``, and a backend is handed only the options it
    reads.
    """
    premises = list(premises)
    if logic == "auto":
        logic = _detect_logic(formula, premises)
    chain = tuple(backends) if backends is not None else (
        ("modelfinder", "z3") if logic == "fol"
        else ("modal-tableau", "kripke-enum"))

    asked = premises
    if signature is not None:
        asked = premises + list(_signature_premises("countermodel", signature, logic))
    options = _name_background(options, len(premises), len(asked), "countermodel")
    plan = plan_options("countermodel", chain, logic, options)
    depth = _nesting_depth(formula, *asked)

    def search() -> CountermodelResult:
        unread = None
        for name in chain:
            passed, refusal = plan[name]
            if refusal is not None:
                continue                       # it would answer a different question
            verdict = _name_nesting(
                run_backend(name, formula, asked, timeout=timeout, **passed), depth)
            if verdict.status == REFUTED and verdict.countermodel is not None:
                return CountermodelResult(
                    found=True, model=verdict.countermodel, backend=verdict.backend,
                    explanation_nl=_explain_witness(verdict.countermodel,
                                                    formula, premises))
            if unread is None and "levels deep" in (verdict.detail or ""):
                unread = f"{verdict.backend}: {verdict.detail}"
        return CountermodelResult(found=False, reason=unread)

    return _call_deep(depth, search)


# ---------------------------------------------------------------------------
# repair — the diagnose→suggest→fix loop (the caller's LLM supplies the fix)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RepairStep:
    """One round of the repair loop.

    ``diagnostics`` carries the machine-readable evidence (parse errors or a
    ``CheckResult`` dict), ``suggestion`` a one-line human/LLM-readable
    instruction, ``converged`` whether this text finally passed.
    """

    attempt: int
    text: str
    ok: bool
    diagnostics: dict
    suggestion: Optional[str]
    converged: bool

    def to_dict(self) -> dict:
        return {"attempt": self.attempt, "text": self.text, "ok": self.ok,
                "diagnostics": self.diagnostics, "suggestion": self.suggestion,
                "converged": self.converged}


_POSITION_RE = re.compile(r"at position (\d+)")


def _message_progress(message: str) -> float:
    """How far into the input the dialect that produced ``message`` got.

    A message reporting that the input "ended unexpectedly" consumed all of
    it — the farthest any attempt can get; everything else is located by the
    position the parser names. Used to pick the most informative of several
    competing diagnoses (:func:`_suggest`, and the MCP server's spec-topic
    routing, which imports this rather than reimplementing it).
    """
    if "ended unexpectedly" in message.lower():
        return float("inf")
    return max((int(p) for p in _POSITION_RE.findall(message)), default=0)


def _suggest(parse_result: Optional[ParseResult],
             check_result: Optional[CheckResult]) -> Optional[str]:
    """One actionable sentence out of the strongest diagnostic available."""
    if parse_result is not None and not parse_result.ok:
        if parse_result.errors:
            # The FARTHEST failure, not the last one listed. Errors arrive one
            # per candidate dialect in detection order, and the dialects at
            # the end of that order are the specialised ones that give up
            # earliest on ordinary input: for 'A ∧ B ∨ C' the last entry is
            # lambek's "Invalid predicate 'A'" at position 3, while seven
            # other dialects read to the ∨ and name the real cause (mixed
            # connectives). Handing back the last one sends the reader off
            # renaming a predicate that is already well formed.
            best = max(parse_result.errors,
                       key=lambda e: _message_progress(e.get("message", "")))
            return f"Fix the syntax: {best['message']}"
        return "Fix the syntax (no parser accepted the text)."
    if check_result is None or check_result.ok:
        return None
    if not check_result.is_closed:
        free = ", ".join(check_result.free_variables)
        return (f"Bind or replace the free variable(s) {free}: quantify them "
                f"(∀/∃) or use constant names (multi-letter lowercase, e.g. "
                f"'alice' — single lowercase letters are variables).")
    if not check_result.arity_consistent:
        c = check_result.arity_conflicts[0]
        arities = "/".join(str(a) for a in c["arities"])
        return (f"Use {c['symbol']} with ONE arity — it appears with "
                f"arities {arities}.")
    if check_result.has_lambdas:
        return "Eliminate the lambda residue (beta-reduce before finalising)."
    if check_result.signature_errors:
        e = check_result.signature_errors[0]
        base = f"{e['kind'].replace('_', ' ')}: {e['symbol']}"
        if e.get("suggestion"):
            return f"{base} — did you mean {e['suggestion']!r}?"
        return f"{base} is not in the signature."
    return None


def repair(text: str, *, dialect: Optional[str] = None,
           signature: Optional[dict] = None,
           fixer: Optional[Callable[[str, dict], str]] = None,
           max_attempts: int = 5) -> Iterator[RepairStep]:
    """Generator driving a diagnose→suggest→fix loop over raw formula text.

    Each round parses (``parse_any``), checks (``check``), and yields a
    :class:`RepairStep` with machine-readable diagnostics and a one-line
    suggestion. The kit deliberately does NOT rewrite the text itself — the
    ``fixer`` callback (typically the caller's LLM, prompted with
    ``step.diagnostics`` / ``step.suggestion``) returns the next candidate
    text; without a fixer the generator yields the diagnosis for the input
    and stops. The loop ends on convergence (``converged=True``), on fixer
    absence, or after ``max_attempts`` rounds.
    """
    if max_attempts < 1:
        raise ValueError("repair: max_attempts must be >= 1")
    _read_signature(signature)         # a malformed signature is refused before any round, also for text that does not parse
    current = text
    for attempt in range(1, max_attempts + 1):
        parsed = parse_any(current, hint=dialect)
        diagnostics: dict
        if parsed.ok and parsed.formula is not None:   # an ok result always carries its formula
            checked = check(parsed.formula, signature=signature)
            ok = checked.ok
            diagnostics = {"parse": None, "check": checked.to_dict()}
            suggestion = _suggest(None, checked)
        else:
            ok = False
            checked = None
            diagnostics = {"parse": list(parsed.errors), "check": None}
            suggestion = _suggest(parsed, None)
        yield RepairStep(attempt=attempt, text=current, ok=ok,
                         diagnostics=diagnostics, suggestion=suggestion,
                         converged=ok)
        if ok or fixer is None:
            return
        current = fixer(current, diagnostics)
        if not isinstance(current, str):
            raise TypeError("repair: fixer must return the next candidate text (str)")


# ---------------------------------------------------------------------------
# translate — the comorphism registry
# ---------------------------------------------------------------------------

def translate(term, from_logic: str, to_logic: str,
              **options) -> TranslationResult:
    """Translate ``term`` between logics via the comorphism registry.

    Composes registered edges by BFS when there is no direct one (e.g.
    ``alc → modal → fol`` if the direct ``alc → fol`` edge were absent). See
    :mod:`unicode_logic_kit.comorphism` for the default edges, their term types
    and conventions (free anchors, fragment limits), and how to register your
    own.

    ``options`` are forwarded to the edges on the path that declare them
    (``frame=``/``systems=``/``temporal_closure=`` for the modal edge,
    ``signature=`` for the sorted one, ``mode=``/``bridges=`` for the
    quantified-modal one); one that no edge on the path accepts raises
    ``ValueError`` naming what is accepted, so an option can never be
    ignored into a different question.

    The result's ``axioms`` are the translation's SIDE CONDITIONS, already
    in the target logic, and belong in the premises::

        t = api.translate(f, "msfol", "fol")
        api.prove(t.result, [*premises, *t.axioms])

    or carry the pair around as a :class:`unicode_logic_kit.logic.Sentence`,
    which :func:`prove` unwraps together with its axioms. Dropping them is
    how a valid formula comes back REFUTED.

    A formula nested a hundred levels deep or more is translated on a worker
    thread sized for it (see :func:`prove`). One that is still too deep for a
    recursive translation is a ``ValueError`` that names the nesting depth.
    """
    depth = _nesting_depth(term)
    try:
        return _call_deep(
            depth, lambda: DEFAULT_REGISTRY.translate(term, from_logic, to_logic, **options))
    except RecursionError:
        if depth < _SHALLOW_DEPTH:
            raise
        raise ValueError(f"translate: {_deep_detail(depth, 'the translation')}") from None
