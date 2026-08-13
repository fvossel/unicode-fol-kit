"""The core facade: seven verbs for NL→logic pipelines.

``unicode_fol_kit.api`` bundles the whole toolkit behind a small, stable
vocabulary designed so that an LLM verification loop can consume every answer
without extra parsing:

    from unicode_fol_kit import api

    api.parse_any(text)          # dialect detection + tolerant parsing
    api.check(formula)           # well-formedness + optional signature check
    api.equivalent(f, g)         # graded equivalence (structural → solver)
    api.prove(f)                 # backend chain → one Verdict with provenance
    api.countermodel(f)          # refutation witness + plain-English gloss
    api.repair(text, fixer=llm)  # diagnose → suggest → (caller) fix → re-check
    api.translate(t, "alc", "fol")   # comorphism registry, composed via BFS

Every result object has ``to_dict()`` returning JSON-compatible data.

STABILITY POLICY (this module, :class:`~unicode_fol_kit.atp.protocol.Verdict`,
and the result dataclasses here): within a minor release line (0.N.x) nothing
is renamed or removed and dict keys only ever gain siblings; breaking changes
happen only at a minor bump, are listed in the CHANGELOG, and keep a
deprecation shim for one minor cycle where feasible. Downstream consumers
(e.g. FitchAsATP) should pin ``unicode-fol-kit>=0.N,<0.N+1`` per line.

Deliberately NOT re-exported at the package top level: ``prove`` would collide
with the resolution prover's ``prove`` that existing consumers already import
from ``unicode_fol_kit`` — the facade lives in this namespace, use
``api.prove``.
"""

import re
from dataclasses import dataclass
from typing import Callable, Iterator, Optional, Sequence, Tuple, Union

from .fol.nodes import Node, And
from .atp.protocol import (
    Verdict, BackendUnavailable, PROVED, REFUTED, UNKNOWN,
    get_backend, default_chain, run_backend,
)
from .eval.equivalence import EquivalenceResult, equivalent  # re-export  # noqa: F401
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


def check(formula: Union[Node, str], *, signature: Optional[dict] = None,
          dialect: Optional[str] = None) -> CheckResult:
    """Well-formedness report for a formula (or raw text) — never raises.

    Accepts a parsed ``Node`` or a raw string (which goes through
    :func:`parse_any` first, honouring ``dialect`` as its hint). The
    structural checks are :func:`unicode_fol_kit.eval.validate`'s: closedness,
    per-namespace arity consistency, lambda residue. ``signature`` adds
    vocabulary conformance with did-you-mean suggestions (see
    :func:`_signature_errors` for the loose-dict spec format) — and also
    accepts a first-class :class:`unicode_fol_kit.fol.signature.Signature`,
    which is projected onto that loose convention (name → arity per
    namespace, constant name list) so the structured did-you-mean
    diagnostics stay identical either way.
    """
    from .eval.validate import validate
    from .fol.signature import Signature as _Signature

    signature_object = None
    if isinstance(signature, _Signature):
        # Project onto the loose convention for the classic diagnostics
        # (unknown symbol / wrong arity, with did-you-mean suggestions) —
        # but KEEP the object: its sort declarations have no loose-dict
        # counterpart and are checked additionally below
        # (adversarial-review: dropping them silently returned ok=True on
        # sort-violating formulas the object itself rejects).
        signature_object = signature
        signature = {
            "predicates": {d.name: d.arity
                           for d in signature.predicates.values()},
            "functions": {d.name: d.arity
                          for d in signature.functions.values()},
            "constants": sorted(signature.constants),
        }

    if isinstance(formula, str):
        parsed = parse_any(formula, hint=dialect)
        if not parsed.ok:
            message = parsed.errors[-1]["message"] if parsed.errors else "unparseable"
            return CheckResult(
                ok=False, parseable=False, is_closed=False, free_variables=(),
                arity_consistent=False, arity_conflicts=(), has_lambdas=False,
                predicates=(), functions=(), constants=(), error=message)
        formula = parsed.formula

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


# ---------------------------------------------------------------------------
# prove / countermodel — the backend chain
# ---------------------------------------------------------------------------

def _detect_logic(formula: Node, premises: Sequence[Node]) -> str:
    from .atp.modal_tableau import has_modal
    if has_modal(formula) or any(has_modal(p) for p in premises):
        return "modal"
    return "fol"


def prove(formula: Node, premises: Sequence[Node] = (), *,
          logic: str = "auto", backends: Optional[Sequence[str]] = None,
          timeout: int = 10000, require_agreement: int = 1,
          **options) -> Verdict:
    """Decide ``premises ⊨ formula`` over a chain of backends.

    ``logic="auto"`` routes by syntax (modal operators → the modal chain).
    ``backends=None`` uses :func:`~unicode_fol_kit.atp.protocol.default_chain`
    — fast, deterministic, and never silently expensive (the minutes-per-call
    ``isabelle`` backend runs only when named explicitly). An explicitly named
    backend that is missing raises
    :class:`~unicode_fol_kit.atp.protocol.BackendUnavailable`; one that does
    not support the detected logic raises ``ValueError``.

    The chain runs in order and returns the first DEFINITIVE verdict (proved /
    refuted). With ``require_agreement=n`` > 1 it keeps going until ``n``
    backends report the same definitive status — the returned verdict's
    ``agreement`` then lists them all. If nothing definitive emerges, the
    result is an UNKNOWN verdict from the pseudo-backend ``"chain"`` whose
    ``detail`` summarises every member's answer.

    Extra keyword ``options`` are forwarded to EVERY backend in the chain, so
    only use them with an explicit single-backend list (e.g.
    ``backends=["modal-tableau"], frame="S4"``).
    """
    premises = list(premises)
    if logic == "auto":
        logic = _detect_logic(formula, premises)
    chain = tuple(backends) if backends is not None else default_chain(logic)

    for name in chain:
        backend = get_backend(name)                # ValueError on unknown names
        if logic not in backend.logics:
            raise ValueError(
                f"prove: backend {name!r} does not support logic {logic!r} "
                f"(it handles {sorted(backend.logics)})")

    verdicts = []
    agreeing: dict = {}
    for name in chain:
        extra = dict(options)
        if name == "isabelle":
            extra["logic"] = logic                # the dual-logic backend routes on it
        verdict = run_backend(name, formula, premises, timeout=timeout, **extra)
        verdicts.append(verdict)
        if verdict.is_definitive:
            group = agreeing.setdefault(verdict.status, [])
            group.append(verdict)
            if len(group) >= require_agreement:
                first = group[0]
                if len(group) == 1:
                    return first
                from dataclasses import replace as _replace
                return _replace(first,
                                agreement=tuple(v.backend for v in group))

    summary = "; ".join(
        f"{v.backend}:{v.status}" + (f"/{v.reason}" if v.reason else "")
        for v in verdicts)
    return Verdict(UNKNOWN, "chain", logic=logic,
                   detail=f"no definitive verdict — {summary}" if summary
                   else "empty backend chain")


@dataclass(frozen=True)
class CountermodelResult:
    """Outcome of :func:`countermodel`.

    ``found`` says whether a witness exists; ``model`` is the JSON-able
    witness dict (same shapes as ``Verdict.countermodel``), ``backend`` names
    the route that found it, and ``explanation_nl`` is a short plain-English
    rendering from :func:`unicode_fol_kit.eval.explain.explain_countermodel`
    (a structured Kripke witness is rebuilt and narrated world by world; a
    Z3 assignment is read out; an opaque witness falls back to a one-line
    gloss of its kind).
    """

    found: bool
    model: Optional[dict] = None
    backend: Optional[str] = None
    explanation_nl: Optional[str] = None

    def __bool__(self) -> bool:
        return self.found

    def to_dict(self) -> dict:
        return {"found": self.found, "model": self.model,
                "backend": self.backend, "explanation_nl": self.explanation_nl}


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
    :func:`~unicode_fol_kit.eval.explain.explain_countermodel` can narrate
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
        return _WITNESS_GLOSS.get(witness.get("kind"))


def countermodel(formula: Node, premises: Sequence[Node] = (), *,
                 logic: str = "auto", backends: Optional[Sequence[str]] = None,
                 timeout: int = 10000, **options) -> CountermodelResult:
    """Search for a countermodel to ``premises ⊨ formula``.

    Runs the refutation-capable backends for the logic (FOL: the finite model
    finder first — its structures are the most readable — then Z3; modal: the
    labelled tableau, then the bounded Kripke-model enumeration — the only
    route that can refute a temporal-closure formula) and returns the first
    witness. ``found=False`` means "no countermodel within the budgets",
    never a validity claim.
    """
    premises = list(premises)
    if logic == "auto":
        logic = _detect_logic(formula, premises)
    chain = tuple(backends) if backends is not None else (
        ("modelfinder", "z3") if logic == "fol"
        else ("modal-tableau", "kripke-enum"))

    for name in chain:
        verdict = run_backend(name, formula, premises, timeout=timeout, **options)
        if verdict.status == REFUTED and verdict.countermodel is not None:
            return CountermodelResult(
                found=True, model=verdict.countermodel, backend=verdict.backend,
                explanation_nl=_explain_witness(verdict.countermodel,
                                                formula, premises))
    return CountermodelResult(found=False)


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
    current = text
    for attempt in range(1, max_attempts + 1):
        parsed = parse_any(current, hint=dialect)
        if parsed.ok:
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

def translate(term, from_logic: str, to_logic: str) -> TranslationResult:
    """Translate ``term`` between logics via the comorphism registry.

    Composes registered edges by BFS when there is no direct one (e.g.
    ``alc → modal → fol`` if the direct ``alc → fol`` edge were absent). See
    :mod:`unicode_fol_kit.comorphism` for the default edges, their term types
    and conventions (free anchors, fragment limits), and how to register your
    own.
    """
    return DEFAULT_REGISTRY.translate(term, from_logic, to_logic)
