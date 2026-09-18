"""The MCP tool layer over :mod:`unicode_fol_kit.api`.

Design contract (see the package docstring for the why):

* every tool accepts formula TEXT and parses it with ``api.parse_any``
  (dialect auto-detection; an optional ``dialect`` hint) — a parse failure
  ALWAYS comes back as ``{"ok": False, "argument": <which input failed —
  "text", "conclusion", "formula1", "premise[2]", …>, "errors": [...]}``
  with every attempted dialect's diagnostics, exactly what a repair loop
  needs, never a bare exception string. One uniform shape across every
  tool and every argument position (review-hardened: a generic client
  checks ``result.get("ok") is False``, full stop);
* results are the ``to_dict()`` payloads of the underlying API objects,
  untouched — the MCP layer adds no vocabulary of its own;
* exceptions that ARE the API's documented contract surface as structured
  ``{"error": {"type": ..., "message": ...}}`` dicts (``BackendUnavailable``
  carries its actionable install/start instructions verbatim), so an agent
  can react without parsing tracebacks.

The functions below are plain synchronous callables registered on an
:class:`mcp.server.MCPServer`; they are importable and testable without any
transport running.

STABILITY POLICY (the registered tool SURFACE — names and input schemas):
within a minor release line (0.N.x) a registered tool is never renamed or
removed, and its ``input_schema`` (auto-derived by the ``mcp`` SDK from the
function signature: property names, types, required-ness) only ever gains
new OPTIONAL parameters — an existing parameter's name, type and
required/optional flag are stable. Tool bodies are thin wrappers over
:mod:`unicode_fol_kit.api`, so the payload *contents* already inherit that
module's own STABILITY POLICY (see its docstring); this paragraph covers
the tool *surface* specifically, which a schema/name-based MCP client
depends on in a way a ``pip`` version pin cannot express for a JSON-RPC
session. ``tests/test_mcp_stability.py`` pins the current tool-schema
baseline (derived from a real ``list_tools()`` call) and fails with a
readable diff on any surface drift.
"""

from typing import List, Optional

from .. import api
from ..atp.protocol import (
    PROVED,
    BackendUnavailable,
    available_backends,
    default_chain,
    _REGISTRY,
)

__all__ = ["create_server", "main"]

_SERVER_NAME = "unicode-fol-kit"

_INSTRUCTIONS = """Logic toolbox for NL->FOL work: parse (any dialect:
unicode, TPTP, LaTeX, Prover9, SMT-LIB), well-formedness checks, graded
equivalence, proving/refuting over a multi-backend portfolio (list_backends
shows what is registered and available right now), self-explaining
countermodels, formula diagnosis for repair loops (you are the fixer:
diagnose -> apply the suggestion -> diagnose again), mechanical repair of
the failures that have one right answer (repair_formula: an illegal symbol
name renamed invertibly, a free variable closed on request -- but never a
bracket guessed into a mixed conjunction/disjunction), logic-to-logic
translation, and English verbalization. Error-analysis layer:
compare_formulas gives the full prediction-vs-gold breakdown (structural /
canonical / vocabulary-aligned match, solver equivalence, symbol diff),
score_batch aggregates it over a corpus, check_consistency decides whether
a premise SET is satisfiable (with a model witness), get_signature extracts
the vocabulary of a formula set, detect_dialect shows what the input looks
like, normalize/render convert between normal forms and concrete syntaxes,
truth_table decides propositional formulas by enumeration (classical/K3/LP),
drs_to_fol turns discourse boxes (donkey sentences, cross-sentence
anaphora) into provable FOL, and list_translations enumerates the
logic-to-logic edges translate can follow. Probabilistic layer (exact,
no sampling): probability_bounds computes Nilsson-style entailed bounds
from probability-interval premises, probability_query answers
ProbLog-style queries under distribution semantics. Formulas are passed
as plain text; results are structured JSON.

Self-correction loop: every parse failure comes back as {"ok": false,
"argument": ..., "errors": [...], "spec_topic": ...}. Call get_syntax_spec
with that topic to retrieve the exact rule (naming conventions, operator
precedence, quantifier scope, the counting quantifier, the chemical
signature, or the catalogue of known failure modes), then regenerate. The
grammar therefore does not need to live in your prompt."""


#: Lowercased substring of a parse-error message -> the syntax_spec topic
#: that explains it. Deliberately a small, honest heuristic: it tells the
#: caller where to LOOK, it does not claim to have diagnosed the formula —
#: which is why the fallback is "overview" (whose first entry is the
#: naming/dialect confusion behind most failures) rather than a guess.
#:
#: ORDER IS PRIORITY, most specific first: within ONE message a generic
#: needle such as "unexpected character" also matches the precise
#: mixed-connective diagnosis, so the earlier entry decides what that message
#: is about (see :func:`_spec_topic_for`).
_SPEC_HINTS = (
    # Mixed same-level connectives: the kit's unicode grammar refuses
    # 'A ∧ B ∨ C' outright instead of resolving it by precedence, so the fix
    # is brackets and the topic is operators — never naming, however much the
    # message mentions a predicate.
    ("cannot mix", "operators"),
    ("without parentheses", "operators"),
    ("parenthesise", "operators"),
    # "… after universal quantifier '∀'" — a quantifier that never got its
    # bound variable, which is a scope question and not a name question.
    ("after universal quantifier", "quantifiers"),
    ("after existential quantifier", "quantifiers"),
    ("invalid name", "naming"),
    ("invalid variable", "naming"),
    ("invalid name/constant", "naming"),
    ("not bound", "quantifiers"),
    ("free variable", "quantifiers"),
    ("incomplete formula", "operators"),
    ("unexpected token", "operators"),
    ("unexpected character", "naming"),
)


#: How far into the input a dialect got before giving up — imported from the
#: core facade, which needs the same measure to pick the one error message it
#: turns into a repair suggestion. One implementation, two callers.
_message_progress = api._message_progress


def _spec_topic_for(errors) -> Optional[str]:
    """The syntax_spec topic most likely to explain these parse errors.

    ``errors`` holds one entry per candidate dialect that was tried, and the
    two available signals disagree often enough that neither decides alone:

    * how FAR a dialect got before giving up — the dialects without
      quantifiers abandon '∀x (P(x) ∧ Q(x) ⊕ R(x))' at position 1 and call it
      a naming problem, and they are the majority, but the ones that read as
      far as the ⊕ named the real cause;
    * how MANY dialects agree — in '∀ P(x)' six of them report a quantifier
      left without its variable and a single second-order reading happens to
      consume the whole string, so distance alone would hand the answer to
      the outlier.

    So each message votes with a weight given by the RANK of its distance
    among the distinct distances seen (farthest wins, but a near-unanimous
    verdict one step back still outweighs a lone outlier), and the topic with
    the highest total wins. Ties — including the case where every dialect
    stopped at the same place — go to the more specific needle
    (``_SPEC_HINTS`` order). This is a routing hint, not a diagnosis: the
    caller gets the rule most likely to explain the rejection, and the
    messages themselves stay in the response.

    Each message votes exactly once, for its first matching needle — a mixed
    connective is reported as an unexpected character too, and counting that
    message for both topics would let the vague reading dilute the precise
    one. Matching is case-insensitive: the parsers capitalise their messages
    inconsistently, and a hint that silently stops matching because of a
    capital letter is worse than no hint at all.
    """
    votes = []
    for entry in errors:
        message = entry.get("message", "").lower()
        for rank, (needle, topic) in enumerate(_SPEC_HINTS):
            if needle in message:
                votes.append((_message_progress(message), topic, rank))
                break
    if not votes:
        return "overview"

    weight_of = {distance: index for index, distance
                 in enumerate(sorted({v[0] for v in votes}))}
    scores: dict = {}
    for progress, topic, rank in votes:
        score, best_rank = scores.get(topic, (0, rank))
        scores[topic] = (score + weight_of[progress], min(best_rank, rank))
    return min(scores, key=lambda topic: (-scores[topic][0], scores[topic][1]))


def _parse(text: str, dialect: Optional[str], argument: str = "text"):
    """``(node, None)`` on success, ``(None, error_dict)`` on failure.

    ``argument`` names WHICH tool input failed in the uniform error shape
    (see the module docstring) so multi-argument tools stay distinguishable
    without inventing per-tool nesting. The failure also carries
    ``spec_topic``: the :func:`syntax_spec` topic to fetch before retrying —
    what turns a bare rejection into a correction loop the caller can close
    on its own.
    """
    parsed = api.parse_any(text, hint=dialect)
    if not parsed.ok:
        errors = parsed.to_dict()["errors"]
        return None, {"ok": False, "argument": argument, "errors": errors,
                      "spec_topic": _spec_topic_for(errors)}
    return parsed.formula, None


def _error(exc: Exception) -> dict:
    return {"error": {"type": type(exc).__name__, "message": str(exc)}}


def _normalize_converses(converses: List[dict]):
    """JSON-dict converse declarations -> the internal tuple form.

    ``converses`` (``compare_formulas``/``score_batch``'s own parameter) is
    a list of ``{"a": [name, arity], "b": [name, arity], "permutation":
    [...]}`` dicts — the JSON-friendly spelling of
    :data:`unicode_fol_kit.eval.converses.ConverseDeclaration`. Raises
    ``ValueError`` for a malformed entry (missing key, wrong shape) BEFORE
    ``api.equivalent``/``eval.compute_fol_metrics`` ever see it; the
    declaration's own semantic validity (arity match, permutation
    bijectivity, no self-pair, …) is ``validate_converses``'s job, run
    inside those calls — this function only bridges the wire shape.
    """
    normalized = []
    for i, entry in enumerate(converses):
        try:
            a_name, a_arity = entry["a"]
            b_name, b_arity = entry["b"]
            permutation = entry["permutation"]
            normalized.append((
                (a_name, int(a_arity)), (b_name, int(b_arity)),
                tuple(int(p) for p in permutation)))
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                f"converses[{i}]: expected "
                '{"a": [name, arity], "b": [name, arity], "permutation": '
                f'[...]}}, got {entry!r}') from exc
    return normalized


# --------------------------------------------------------------------------
# Tool implementations (plain functions; registered in create_server)
# --------------------------------------------------------------------------

def parse_formula(text: str, dialect: Optional[str] = None) -> dict:
    """Parse formula text (dialect auto-detected) to the kit's JSON AST."""
    parsed = api.parse_any(text, hint=dialect)
    result = parsed.to_dict()
    if parsed.ok:
        # The unicode rendering is what an LLM wants to read back.
        result["unicode"] = parsed.formula.to_unicode_str()
    else:
        result["argument"] = "text"
    return result


def check_formula(text: str, dialect: Optional[str] = None,
                  signature: Optional[dict] = None) -> dict:
    """Well-formedness + optional signature conformance for formula text."""
    node, err = _parse(text, dialect)
    if err is not None:
        return err
    return api.check(node, signature=signature).to_dict()


def prove(conclusion: str, premises: Optional[List[str]] = None,
          logic: str = "auto", backends: Optional[List[str]] = None,
          timeout_ms: int = 10000, dialect: Optional[str] = None) -> dict:
    """Decide premises |= conclusion; the Verdict dict carries provenance."""
    node, err = _parse(conclusion, dialect, argument="conclusion")
    if err is not None:
        return err
    parsed_premises = []
    for i, p in enumerate(premises or []):
        pnode, perr = _parse(p, dialect, argument=f"premise[{i}]")
        if perr is not None:
            return perr
        parsed_premises.append(pnode)
    try:
        verdict = api.prove(node, parsed_premises, logic=logic,
                            backends=backends, timeout=timeout_ms)
    except (BackendUnavailable, ValueError) as exc:
        return _error(exc)
    return verdict.to_dict()


def find_countermodel(formula: str, premises: Optional[List[str]] = None,
                      logic: str = "auto",
                      dialect: Optional[str] = None) -> dict:
    """A countermodel to premises |= formula, with an English explanation."""
    node, err = _parse(formula, dialect, argument="formula")
    if err is not None:
        return err
    parsed_premises = []
    for i, p in enumerate(premises or []):
        pnode, perr = _parse(p, dialect, argument=f"premise[{i}]")
        if perr is not None:
            return perr
        parsed_premises.append(pnode)
    try:
        return api.countermodel(node, parsed_premises, logic=logic).to_dict()
    except (BackendUnavailable, ValueError) as exc:
        return _error(exc)


def check_equivalence(formula1: str, formula2: str, method: str = "auto",
                      timeout_ms: int = 10000,
                      dialect: Optional[str] = None) -> dict:
    """Graded equivalence (exact -> canonical -> aligned -> solver)."""
    node1, err1 = _parse(formula1, dialect, argument="formula1")
    if err1 is not None:
        return err1
    node2, err2 = _parse(formula2, dialect, argument="formula2")
    if err2 is not None:
        return err2
    try:
        return api.equivalent(node1, node2, method=method,
                              timeout=timeout_ms).to_dict()
    except ValueError as exc:
        return _error(exc)


def diagnose(text: str, dialect: Optional[str] = None,
             signature: Optional[dict] = None) -> dict:
    """One diagnose round of the repair loop; YOU are the fixer.

    Returns ``{ok, diagnostics, suggestion, converged}`` for the given
    text, plus ``spec_topic`` when it did not parse. Apply the suggestion to
    the text yourself and call again; ``converged=True`` means the text
    parses and checks clean.
    """
    step = next(api.repair(text, dialect=dialect, signature=signature))
    result = step.to_dict()
    # Same routing every other tool's failure carries: the diagnosis names
    # WHAT broke, spec_topic names the rule to look up before retrying. A
    # loop that has only the message has to guess which rule it violated.
    parse_errors = result.get("diagnostics", {}).get("parse")
    if parse_errors:
        result["spec_topic"] = _spec_topic_for(parse_errors)
    return result


def repair_formula(text: str, dialect: Optional[str] = None,
                   close_free_variables: bool = False,
                   sanitize_invalid_names: bool = True) -> dict:
    """Mechanically repair what CAN be repaired; report the rest.

    The counterpart to ``diagnose`` (where you are the fixer): this fixes the
    two failure shapes that have one right answer, so they cost you no
    attempt. A name no symbol class of this dialect accepts (a chemical name
    with digits, commas or hyphens) is renamed to a legal predicate, with the
    original kept in ``names`` — nothing is lost. A free variable is reported
    and, with ``close_free_variables=True``, closed.

    What it deliberately does NOT do is bracket a formula that mixes ∧ and ∨
    at the same level: the readings differ and choosing one would be a guess.
    That comes back ``ok=False`` with kind ``"mixed_connectives"`` — write the
    brackets you mean and call again.

    Returns ``{ok, formula, repaired_text, issues, changed, dialect, names}``,
    plus ``spec_topic`` when nothing parsed. ``repaired_text`` is in the kit's
    unicode syntax and re-parses to ``formula``.
    """
    from ..fol.dialect_repair import repair_formula as _repair

    result = _repair(text, dialect=dialect,
                     close_free_variables=close_free_variables,
                     sanitize_invalid_names=sanitize_invalid_names).to_dict()
    if not result["ok"]:
        # Same routing every other tool's failure carries: the issue names
        # WHAT broke, spec_topic names the rule to look up before retrying.
        result["spec_topic"] = _spec_topic_for(result["issues"])
    return result


def translate(term: str, from_logic: str, to_logic: str,
              dialect: Optional[str] = None) -> dict:
    """Translate between logics over the comorphism registry.

    The term's PARSER follows the source logic's own term type: ``"casl"``
    terms are CASL spec TEXT passed through verbatim (the dynamic
    ``hets:<Name>`` edges); ``"alc"`` terms are description-logic concept
    text (``Human ⊓ ∃hasChild.Doctor``) parsed by the DL grammar —
    review-confirmed: the registered alc→modal/alc→fol edges take
    ``Concept`` objects that no FOL-family grammar can produce; every
    other source logic parses the term as a formula via ``parse_any``.
    Node/Concept results gain a ``"unicode"`` rendering.
    """
    if from_logic == "casl":
        payload = term
    elif from_logic == "alc":
        from ..dl import ConceptSyntaxError, parse_concept

        try:
            payload = parse_concept(term)
        except ConceptSyntaxError as exc:
            return {"ok": False, "argument": "term",
                    "errors": [{"dialect": "alc", "message": str(exc)}]}
    else:
        node, err = _parse(term, dialect, argument="term")
        if err is not None:
            return err
        payload = node
    try:
        result = api.translate(payload, from_logic, to_logic)
    except ValueError as exc:
        return _error(exc)
    rendered = result.to_dict()
    if hasattr(result.result, "to_unicode_str"):
        rendered["unicode"] = result.result.to_unicode_str()
    elif hasattr(result.result, "to_unicode"):     # dl.Concept spelling
        rendered["unicode"] = result.result.to_unicode()
    return rendered


def verbalize(text: str, dialect: Optional[str] = None) -> dict:
    """Render a formula as deterministic English (fol.to_english)."""
    from ..fol import to_english

    node, err = _parse(text, dialect)
    if err is not None:
        return err
    try:
        return {"ok": True, "english": to_english(node)}
    except (ValueError, NotImplementedError) as exc:
        return _error(exc)


def list_backends() -> dict:
    """Registry introspection: what can decide, and what runs by default."""
    return {
        "registered": sorted(_REGISTRY),
        "available": list(available_backends()),
        "default_chains": {"fol": list(default_chain("fol")),
                           "modal": list(default_chain("modal"))},
    }


# --------------------------------------------------------------------------
# Error-analysis / conversion layer (second tool wave)
# --------------------------------------------------------------------------

# form name -> (callable path, what the result means relative to the input).
# tseitin_cnf and skolemize deliberately do NOT claim equivalence — an agent
# that feeds the result back into prove() must know the difference.
_NORMALIZE_SEMANTICS = {
    "nnf": "equivalent", "pnf": "equivalent", "cnf": "equivalent",
    "dnf": "equivalent", "canonical": "equivalent",
    "tseitin_cnf": "equisatisfiable",
    "skolemize": "satisfiability-preserving",
}


def normalize(text: str, form: str = "nnf",
              dialect: Optional[str] = None) -> dict:
    """Rewrite a formula into a normal form.

    ``form``: ``nnf`` / ``pnf`` / ``cnf`` / ``dnf`` (equivalence-preserving),
    ``canonical`` (the eval layer's comparison normal form: alpha-renaming,
    commutativity/associativity, duplication, double negation quotiented
    out), ``tseitin_cnf`` (EQUISATISFIABLE only — fresh definitional atoms),
    ``skolemize`` (satisfiability-preserving — existentials become Skolem
    terms). The ``semantics`` key states which of those relations the result
    bears to the input, and ``is_horn`` reports whether the input's clausal
    form is Horn (``None`` where that computation is not applicable).
    """
    from ..fol import normalforms
    from ..eval import canonicalize as _canonicalize

    node, err = _parse(text, dialect)
    if err is not None:
        return err
    transforms = {
        "nnf": normalforms.to_nnf, "pnf": normalforms.to_pnf,
        "cnf": normalforms.to_cnf, "dnf": normalforms.to_dnf,
        "tseitin_cnf": normalforms.to_tseitin_cnf,
        "skolemize": normalforms.skolemize,
        "canonical": _canonicalize,
    }
    if form not in transforms:
        return _error(ValueError(
            f"normalize: unknown form {form!r} (one of {sorted(transforms)})"))
    try:
        result = transforms[form](node)
    except (ValueError, TypeError, NotImplementedError) as exc:
        return _error(exc)
    try:
        horn = normalforms.is_horn(node)
    except Exception:
        horn = None                      # presentational extra, never fatal
    return {"ok": True, "form": form,
            "semantics": _NORMALIZE_SEMANTICS[form],
            "unicode": result.to_unicode_str(),
            "formula": result.to_dict(),
            "is_horn": horn}


def render(text: str, to: str = "tptp",
           dialect: Optional[str] = None) -> dict:
    """Render a formula in another concrete syntax.

    ``to``: ``unicode`` / ``tptp`` / ``prover9`` / ``latex`` / ``smtlib``
    (a standalone SMT-LIB2 problem: ``(set-logic ...)``, the declaration
    preamble, and one ``(assert ...)`` — no premises through this tool; use
    ``unicode_fol_kit.atp.z3_input.to_smtlib`` directly for an entailment
    with premises) / ``casl`` (a bare CASL formula via ``formula_to_casl``)
    / ``json`` (the versioned ``serialize`` envelope — the only target whose
    ``rendered`` is a dict, not a string) / ``english`` (deterministic
    verbalization). A family without the requested rendering surfaces its
    own ``NotImplementedError``/``ValueError`` as a structured error — for
    ``smtlib`` this is ``to_z3``'s own refusal (second/third-order,
    modal/hybrid/linear/Lambek/team constructs have no first-order SMT-LIB2
    encoding), named by construct, reused rather than reimplemented.
    """
    node, err = _parse(text, dialect)
    if err is not None:
        return err
    try:
        if to == "unicode":
            rendered = node.to_unicode_str()
        elif to == "tptp":
            rendered = node.to_tptp()
        elif to == "prover9":
            rendered = node.to_prover9()
        elif to == "latex":
            rendered = node.to_latex()
        elif to == "smtlib":
            rendered = node.to_smtlib()
        elif to == "casl":
            from ..fol.casl_export import formula_to_casl
            rendered = formula_to_casl(node)
        elif to == "json":
            from ..fol.serialize import serialize
            rendered = serialize(node)
        elif to == "english":
            from ..fol import to_english
            rendered = to_english(node)
        else:
            return _error(ValueError(
                f"render: unknown target {to!r} (one of ['casl', 'english', "
                f"'json', 'latex', 'prover9', 'smtlib', 'tptp', 'unicode'])"))
    except (ValueError, TypeError, NotImplementedError) as exc:
        return _error(exc)
    return {"ok": True, "to": to, "rendered": rendered}


def detect_dialect(text: str) -> dict:
    """What syntax does this text look like, and what does it parse as?

    ``candidates`` is the detector's ordered nomination list (always ending
    in ``"unicode"``, the mode-ladder catch-all); ``parsed_as`` is the
    dialect that actually accepted the text (``None`` if nothing did, with
    every attempt's diagnostic in ``errors``).
    """
    from ..fol.dialect_detect import detect_dialects

    parsed = api.parse_any(text)
    return {"ok": parsed.ok,
            "candidates": list(detect_dialects(text)),
            "parsed_as": parsed.dialect if parsed.ok else None,
            "errors": [] if parsed.ok else parsed.to_dict()["errors"]}


def _vocabulary_diff(report_a, report_b) -> dict:
    """Per-namespace symbol diff between two ValidationReports."""
    diff = {}
    for section in ("predicates", "functions", "constants"):
        a = set(getattr(report_a, section))
        b = set(getattr(report_b, section))
        diff[section] = {"only_in_predicted": sorted(a - b),
                         "only_in_gold": sorted(b - a),
                         "shared": sorted(a & b)}
    return diff


def compare_formulas(predicted: str, gold: str, timeout_ms: int = 10000,
                     dialect: Optional[str] = None,
                     converses: Optional[List[dict]] = None) -> dict:
    """The full prediction-vs-gold error-analysis breakdown for one pair.

    Layers, strictest first: ``structural_equal`` (raw AST equality),
    ``canonical_exact_match`` (alpha-renaming, commutativity/associativity,
    duplication, double negation quotiented out),
    ``aligned_exact_match`` (canonical match after Levenshtein-guided,
    namespace- and arity-aware symbol renaming; ``aligned_predicted`` shows
    the renamed prediction), ``equivalence`` (the graded ladder's full
    verdict dict, solver level included). ``vocabulary`` lists the symbols
    (``Name/arity`` for predicates/functions) each side uses and the other
    does not — the usual first stop when a match fails.

    ``converses`` OPTIONALLY declares argument-permutation bridging axioms
    — e.g. ``LovedBy(x, y) ↔ Loves(y, x)`` — honoured ONLY by the solver
    level inside ``equivalence`` (see
    :func:`unicode_fol_kit.eval.equivalence.equivalent`'s ``converses``
    parameter and :mod:`unicode_fol_kit.eval.converses`); each entry is
    ``{"a": [name, arity], "b": [name, arity], "permutation": [...]}``, e.g.
    ``{"a": ["LovedBy", 2], "b": ["Loves", 2], "permutation": [1, 0]}``. A
    malformed entry (missing key, wrong shape) comes back as the top-level
    ``{"error": {...}}`` shape; a structurally invalid declaration (bad
    arity/permutation, self-pair, …) instead lands inside
    ``equivalence.error`` — the same place any other ``ValueError`` from the
    equivalence call surfaces — since it is only caught once the axioms are
    actually built. A modal ``predicted``/``gold`` pair with non-empty
    ``converses`` also lands in ``equivalence.error`` (``equivalent()``
    raises ``NotImplementedError`` there — no modal bridging route exists —
    which this tool catches alongside ``ValueError``, never lets escape as a
    raw exception). ``converse_axioms_applied`` lists the axioms that were
    actually built (unicode-rendered, e.g.
    ``"∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0))"``), or is ``None`` when no
    ``converses`` were given.
    """
    from ..eval import (exact_match, align_symbols, aligned_exact_match)
    from ..eval.validate import validate

    pred, err = _parse(predicted, dialect, argument="predicted")
    if err is not None:
        return err
    ref, err = _parse(gold, dialect, argument="gold")
    if err is not None:
        return err

    converses_tuples = None
    if converses:
        try:
            converses_tuples = _normalize_converses(converses)
        except ValueError as exc:
            return _error(exc)

    try:
        aligned = align_symbols(pred, ref)
        aligned_unicode = aligned.to_unicode_str()
        aligned_ok = aligned_exact_match(pred, ref)
    except (ValueError, NotImplementedError):
        aligned_unicode = None           # family without alignment support
        aligned_ok = None

    axioms_applied = None
    try:
        if converses_tuples:
            from ..eval.converses import converse_axioms
            axioms_applied = [ax.to_unicode_str()
                              for ax in converse_axioms(converses_tuples)]
        equivalence = api.equivalent(pred, ref, timeout=timeout_ms,
                                     converses=converses_tuples).to_dict()
    except (ValueError, NotImplementedError) as exc:
        # NotImplementedError: a modal pair with a non-empty `converses` --
        # equivalent() raises that deliberately (no modal bridging route
        # exists), and it must land in the same structured `equivalence.error`
        # shape as a ValueError, not escape as a raw exception over the wire.
        equivalence = {"error": str(exc)}
    return {
        "ok": True,
        "structural_equal": pred == ref,
        "canonical_exact_match": exact_match(pred, ref),
        "aligned_exact_match": aligned_ok,
        "aligned_predicted": aligned_unicode,
        "equivalence": equivalence,
        "vocabulary": _vocabulary_diff(validate(pred), validate(ref)),
        "converse_axioms_applied": axioms_applied,
    }


def score_batch(predictions: List[str], references: List[str],
                method: str = "auto", timeout_ms: int = 10000,
                converses: Optional[List[dict]] = None) -> dict:
    """Corpus-level NL->FOL metrics over aligned prediction/reference lists.

    The six-key dict of ``eval.compute_fol_metrics``: ``exact_match``,
    ``equivalence_accuracy`` (honest — undecided pairs are NOT counted as
    refuted), ``mean_partial_credit``, ``parse_failure_rate``,
    ``solver_unknown_rate``, ``n``. ``converses`` (same JSON shape as
    ``compare_formulas``'s own parameter — see its docstring) is forwarded
    to every pair; when non-empty the dict gains a seventh key,
    ``converse_matched_rate`` — the fraction of pairs the solver proved
    equivalent USING the declared axioms, separately visible from (and
    subtractable out of) ``equivalence_accuracy``. A malformed or
    structurally invalid ``converses`` declaration, or a modal pair in the
    batch hit with non-empty ``converses`` (``NotImplementedError`` — no
    modal bridging route exists), surfaces as the top-level ``{"error":
    {...}}`` shape rather than escaping as a raw exception.
    """
    from ..eval import compute_fol_metrics

    try:
        converses_tuples = _normalize_converses(converses) if converses else None
        return {"ok": True,
                **compute_fol_metrics(predictions, references,
                                      method=method, timeout_ms=timeout_ms,
                                      converses=converses_tuples)}
    except (ValueError, NotImplementedError) as exc:
        # NotImplementedError: same modal+converses case compare_formulas
        # guards against above -- must return the tool's structured error
        # shape (_error), never escape as a raw exception over the wire.
        return _error(exc)


def check_consistency(formulas: List[str], logic: str = "auto",
                      timeout_ms: int = 10000,
                      dialect: Optional[str] = None) -> dict:
    """Is this SET of formulas jointly satisfiable?

    Encoding: a fresh nullary atom ``q`` (guaranteed absent from the input
    vocabulary) gives the contradiction ``q ∧ ¬q``; classically (and under
    the kit's local-consequence modal reading) the set is unsatisfiable iff
    it entails that contradiction, and a countermodel to that entailment IS
    a model of the set. Verdicts: ``consistent=True`` carries the model
    witness + English gloss (``method="model"``), ``consistent=False``
    carries the refutation verdict (``method="refutation"``),
    ``consistent=None`` means both searches came back empty within the
    budgets (``method="inconclusive"`` — never a claim either way).
    """
    from ..fol.nodes import Atom, Not, And as _And
    from ..eval.validate import validate

    parsed = []
    for i, f in enumerate(formulas or []):
        node, err = _parse(f, dialect, argument=f"formula[{i}]")
        if err is not None:
            return err
        parsed.append(node)

    used = set()
    for node in parsed:
        report = validate(node)
        used.update(entry.rpartition("/")[0] for entry in report.predicates)
    fresh = "ufk_absurd"
    while fresh in used:
        fresh += "_"
    contradiction = _And(Atom(fresh, ()), Not(Atom(fresh, ())))

    try:
        witness = api.countermodel(contradiction, parsed, logic=logic,
                                   timeout=timeout_ms)
        if witness.found:
            return {"ok": True, "consistent": True, "method": "model",
                    "model": witness.model, "backend": witness.backend,
                    "explanation_nl": witness.explanation_nl}
        verdict = api.prove(contradiction, parsed, logic=logic,
                            timeout=timeout_ms)
    except (BackendUnavailable, ValueError) as exc:
        return _error(exc)
    if verdict.status == PROVED:
        return {"ok": True, "consistent": False, "method": "refutation",
                "verdict": verdict.to_dict()}
    return {"ok": True, "consistent": None, "method": "inconclusive",
            "verdict": verdict.to_dict()}


def get_signature(formulas: List[str],
                  dialect: Optional[str] = None) -> dict:
    """Extract the inferred vocabulary (Signature) of a formula set.

    The result dict is ``fol.Signature.from_formulas(...)``'s rich form —
    predicates/functions with arities and inferred sorts, constants, sort
    names — ready to pass back verbatim as ``check_formula``'s /
    ``diagnose``'s ``signature`` argument to hold FURTHER generations to
    this vocabulary.
    """
    from ..fol.signature import Signature

    parsed = []
    for i, f in enumerate(formulas or []):
        node, err = _parse(f, dialect, argument=f"formula[{i}]")
        if err is not None:
            return err
        parsed.append(node)
    try:
        return {"ok": True,
                "signature": Signature.from_formulas(parsed).to_dict()}
    except (ValueError, NotImplementedError) as exc:
        return _error(exc)


# Enumerating value_count**atom_count rows must not melt the transport: the
# cap bounds the ROW COUNT (4096 = 12 classical or ~7 three-valued atoms).
_TRUTH_TABLE_MAX_ROWS = 4096


def truth_table(text: str, logic: str = "classical",
                dialect: Optional[str] = None) -> dict:
    """Decide a propositional formula by full enumeration.

    ``logic``: ``classical`` (values {0,1}), ``K3`` (strong Kleene) or
    ``LP`` (Priest, paraconsistent designation). Quantified formulas and
    tables beyond 4096 rows are refused as structured errors. ``rows``
    aligns each assignment with ``atoms``; ``markdown`` is the rendered
    table for direct display.
    """
    from ..semantics.truthtable import (
        truth_table as _truth_table, _collect_atoms, _VALUES)

    node, err = _parse(text, dialect)
    if err is not None:
        return err
    if logic not in _VALUES:
        return _error(ValueError(
            f"truth_table: unknown logic {logic!r} "
            f"(one of {sorted(_VALUES)})"))
    try:
        atoms = _collect_atoms(node)     # rejects quantified formulas
    except ValueError as exc:
        return _error(exc)
    n_rows = len(_VALUES[logic]) ** len(atoms)
    if n_rows > _TRUTH_TABLE_MAX_ROWS:
        return _error(ValueError(
            f"truth_table: {len(atoms)} atoms give {n_rows} rows under "
            f"{logic} (cap {_TRUTH_TABLE_MAX_ROWS}); use prove or "
            f"find_countermodel instead"))
    try:
        # _collect_atoms only rejects QUANTIFIERS; a modal/temporal/fuzzy/
        # lambda node walks through it and only the evaluator refuses it
        # (NotImplementedError/TypeError from the Kleene tables) — that
        # refusal is part of the documented contract and must surface as a
        # structured error, not a traceback (review-hardened).
        tt = _truth_table(node, logic=logic)
    except (ValueError, TypeError, NotImplementedError) as exc:
        return _error(exc)
    return {"ok": True, "logic": tt.logic, "atoms": list(tt.atoms),
            "rows": [{"assignment": list(assignment), "value": value,
                      "designated": designated}
                     for assignment, value, designated in tt.rows],
            "is_tautology": tt.is_tautology,
            "is_contradiction": tt.is_contradiction,
            "is_satisfiable": tt.is_satisfiable,
            "markdown": tt.render()}


def drs_to_fol(text: str, format: str = "box",
               resolve_pronouns: bool = False) -> dict:
    """Translate a discourse representation structure into provable FOL.

    ``format="box"`` parses the compact box notation
    (``[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]``),
    ``format="sbn"`` the documented Parallel-Meaning-Bank SBN subset.
    ``resolve_pronouns=True`` runs accessibility-respecting anaphora
    resolution first (PRONOUN-marked referents; ambiguity/no-candidate
    failures surface as structured errors) and reports each resolution.
    The result is the standard translation — donkey-sentence universals
    come out right — as a formula ``prove``/``check_formula`` accept.
    """
    from .. import drt

    if format == "box":
        parse, error_type = drt.parse_drs, drt.DRSSyntaxError
    elif format == "sbn":
        parse, error_type = drt.parse_sbn, drt.SBNSyntaxError
    else:
        return _error(ValueError(
            f"drs_to_fol: unknown format {format!r} (one of ['box', 'sbn'])"))
    try:
        box = parse(text)
    except (error_type, ValueError) as exc:
        return {"ok": False, "argument": "text",
                "errors": [{"dialect": f"drs_{format}", "message": str(exc)}]}

    resolutions = None
    if resolve_pronouns:
        try:
            report = drt.resolve_anaphora(box)
        except ValueError as exc:
            return _error(exc)
        box = report.drs
        resolutions = [r.to_dict() for r in report.resolutions]
    try:
        node = drt.drs_to_fol(box)
    except (ValueError, NotImplementedError) as exc:
        return _error(exc)
    result = {"ok": True, "unicode": node.to_unicode_str(),
              "formula": node.to_dict()}
    if resolutions is not None:
        result["resolutions"] = resolutions
    return result


def _exact_fraction(value, where: str):
    """Coerce a JSON-transported probability to an exact Fraction.

    ints and strings go straight to ``Fraction`` (``"7/10"`` and ``"0.7"``
    are both exact); a float is read through its shortest-repr DECIMAL
    (``0.7`` → ``Fraction("0.7")`` = 7/10 — what the JSON author wrote, not
    the binary artefact ``Fraction(0.7)`` would preserve). The prob layer
    itself refuses floats outright; this adapter exists because JSON has no
    rational type. Booleans are refused (bool is an int subclass in Python,
    but a JSON ``true`` is not a probability — silently reading it as 1
    would be the quiet coercion this kit never does). Raises ValueError
    with ``where`` on everything else.
    """
    from fractions import Fraction

    try:
        if isinstance(value, float):
            return Fraction(repr(value))
        if isinstance(value, (int, str)) and not isinstance(value, bool):
            return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"{where}: not a probability: {value!r} ({exc})")
    raise ValueError(f"{where}: expected int, string or number, got "
                     f"{type(value).__name__}")


def probability_bounds(conclusion: str, constraints: List[dict],
                       max_atoms: int = 12,
                       dialect: Optional[str] = None,
                       strategy: str = "direct",
                       max_columns: int = 500) -> dict:
    """Nilsson-style probabilistic entailment: tightest bounds on P(conclusion).

    Each constraint dict: ``{"formula": <text>}`` plus either
    ``"probability"`` (pins the value exactly) or ``"lower"``/``"upper"``
    (interval; missing ends default to 0/1), plus optional ``"given"``
    (formula text — makes it the conditional ``P(formula | given)``).
    Probabilities travel as ``"7/10"`` / ``"0.7"`` strings, ints, or JSON
    numbers (read decimally). Propositional only; the answer is the EXACT
    ``[lower, upper]`` interval (fraction strings, with float shadows for
    convenience) entailed by the constraint polytope — ``lower == upper ==
    1`` is classical entailment as a corner case.

    ``strategy`` picks the solving ALGORITHM, never the semantics (see
    :func:`unicode_fol_kit.prob.nilsson.entailment_bounds`): ``"direct"``
    (the default, unchanged) enumerates all ``2^n`` worlds and is capped
    by ``max_atoms`` (12 by default); ``"column_generation"`` never
    materialises that many worlds, so it can go past ``max_atoms`` —
    its own brake is ``max_columns`` (500 by default, raising a
    structured error rather than ever returning an unproven bound).
    Both strategies solve the identical linear program and agree
    exactly (never a tolerance) wherever both can answer.
    """
    from ..prob import ProbConstraint, entailment_bounds

    if strategy not in ("direct", "column_generation"):
        return _error(ValueError(
            f"probability_bounds: unknown strategy {strategy!r} "
            "(one of ['direct', 'column_generation'])"))

    node, err = _parse(conclusion, dialect, argument="conclusion")
    if err is not None:
        return err
    parsed = []
    try:
        for i, c in enumerate(constraints or []):
            if "formula" not in c:
                return _error(ValueError(
                    f"constraints[{i}]: missing the 'formula' key"))
            fnode, ferr = _parse(c["formula"], dialect,
                                 argument=f"constraints[{i}].formula")
            if ferr is not None:
                return ferr
            given = None
            if c.get("given") is not None:
                given, gerr = _parse(c["given"], dialect,
                                     argument=f"constraints[{i}].given")
                if gerr is not None:
                    return gerr
            if "probability" in c:
                lo = hi = _exact_fraction(c["probability"],
                                          f"constraints[{i}].probability")
            else:
                lo = _exact_fraction(c.get("lower", 0),
                                     f"constraints[{i}].lower")
                hi = _exact_fraction(c.get("upper", 1),
                                     f"constraints[{i}].upper")
            parsed.append(ProbConstraint(fnode, lo, hi, given))
        bounds = entailment_bounds(parsed, node, max_atoms=max_atoms,
                                   strategy=strategy,
                                   max_columns=max_columns)
    except (ValueError, TypeError) as exc:
        return _error(exc)
    return {"ok": True, **bounds.to_dict(),
            "lower_float": float(bounds.lower),
            "upper_float": float(bounds.upper)}


def probability_query(goal: str, facts: List[dict],
                      rules: Optional[List[str]] = None,
                      hard_facts: Optional[List[str]] = None,
                      max_choice_facts: int = 16,
                      dialect: Optional[str] = None) -> dict:
    """Exact ProbLog-style query under Sato's distribution semantics.

    ``facts``: ``{"atom": <ground atom text>, "prob": <"3/10" | 0.3 | …>}``
    — independent Bernoulli facts. ``rules``/``hard_facts``: definite
    clauses (a ground atom, or ``∀``-quantified ``body → head`` with a
    positive conjunctive body and a single positive head atom — anything
    else is refused loudly). The goal may use ∧/∨/¬ and ∀/∃ over the
    program's finite constants; negation reads closed-world against each
    total choice's least model (the ProbLog convention). The result is the
    exact probability as a fraction string (float shadow included).
    """
    from ..prob import ProbFact, ProbProgram, query as _prob_query

    gnode, err = _parse(goal, dialect, argument="goal")
    if err is not None:
        return err
    try:
        prob_facts = []
        for i, f in enumerate(facts or []):
            if "atom" not in f or "prob" not in f:
                return _error(ValueError(
                    f"facts[{i}]: needs both 'atom' and 'prob' keys"))
            anode, aerr = _parse(f["atom"], dialect,
                                 argument=f"facts[{i}].atom")
            if aerr is not None:
                return aerr
            prob_facts.append(ProbFact(
                anode, _exact_fraction(f["prob"], f"facts[{i}].prob")))
        rule_nodes = []
        for i, r in enumerate(rules or []):
            rnode, rerr = _parse(r, dialect, argument=f"rules[{i}]")
            if rerr is not None:
                return rerr
            rule_nodes.append(rnode)
        hard_nodes = []
        for i, h in enumerate(hard_facts or []):
            hnode, herr = _parse(h, dialect, argument=f"hard_facts[{i}]")
            if herr is not None:
                return herr
            hard_nodes.append(hnode)
        program = ProbProgram(prob_facts, rule_nodes, hard_nodes)
        p = _prob_query(program, gnode, max_choice_facts=max_choice_facts)
    except (ValueError, TypeError) as exc:
        return _error(exc)
    return {"ok": True, "probability": str(p), "probability_float": float(p)}


def get_syntax_spec(topic: str = "overview",
                    dialect: Optional[str] = None) -> dict:
    """Retrieve the kit's syntax specification — look up the rule you broke.

    Topics: ``overview`` (dialects and the mistake everyone makes), ``naming``
    (what makes a symbol a variable / constant / predicate / function, and how
    TPTP inverts the convention), ``dialects``, ``operators`` (precedence
    table), ``quantifiers`` (scope rules), ``counting`` (the cardinality
    quantifier and why it replaces long existential chains), ``chemistry``
    (molecule-as-structure signature), ``description-logic`` (the ALC glyph
    and OWL Manchester concept syntaxes the ``dl_*`` tools accept, plus their
    TBox/ABox JSON row shapes), ``errors`` (measured LLM failure modes,
    each with a fix and the topic that explains it).

    Every parse failure this server returns carries a ``spec_topic`` naming
    the topic to fetch before retrying, so a generate → fail → look up → fix
    loop needs no grammar in the prompt. Every example served here is parsed
    and rendering-checked by the kit's own test suite, so the spec cannot
    drift from the parser.
    """
    from .syntax_spec import syntax_spec

    try:
        return {"ok": True, **syntax_spec(topic, dialect)}
    except ValueError as exc:
        return _error(exc)


def list_translations() -> dict:
    """Enumerate the logic-to-logic edges the translate tool can follow.

    The kit's own comorphism registry (BFS-composable); after a Hets bridge
    refresh the dynamic ``hets:<Name>`` edges appear here too. ``lossy``
    edges do not preserve the full source semantics; ``note`` carries the
    conventions a consumer must know.
    """
    from ..comorphism import DEFAULT_REGISTRY

    return {"edges": [{"name": e.name, "source": e.source,
                       "target": e.target, "lossy": e.lossy, "note": e.note}
                      for e in DEFAULT_REGISTRY.edges()]}


# --------------------------------------------------------------------------
# Description-logic (ALCHQ) reasoning tools — pure wiring over dl.tableau /
# dl.classification, with input parsed by dl.parser (the ALC glyph syntax,
# ``syntax="alc"``, default) or dl.owl_manchester (OWL 2 Manchester Syntax,
# ``syntax="manchester"``). Conventions match every tool above: a bad
# CONCEPT/AXIOM text is the uniform ``{"ok": False, "argument": ...,
# "errors": [...], "spec_topic": "description-logic"}`` shape (whether the
# grammar rejected it as :class:`~unicode_fol_kit.dl.ConceptSyntaxError` or
# :class:`~unicode_fol_kit.dl.ManchesterSyntaxError` — including a
# Manchester construct outside ALCHQ, e.g. ``value``/``Self``/``inverse``/a
# nominal, which that parser rejects by NAME rather than a bare syntax
# error); a documented, non-text exception —
# :class:`~unicode_fol_kit.dl.NonSimpleRoleError` (a qualified number
# restriction on a non-simple role) or the tableau's step-budget
# ``RuntimeError`` — is ``{"error": {"type": ..., "message": ...}}``. A
# :class:`Concept` has no ``to_dict()`` (see ``dl.concepts``), so results
# carry it as ``*_unicode`` text (``Concept.to_unicode()``) rather than a
# JSON AST, exactly like ``translate()``'s own ``alc`` branch above.
# --------------------------------------------------------------------------

def _check_dl_syntax(syntax: str):
    """Validate ``syntax`` against the two dialects DL tools understand.

    ``None`` on success. Otherwise the structured ``{"error": {...}}`` shape
    (a caller/config mistake, not a bad concept TEXT). Callers whose
    row-building loops may run zero iterations (an empty/absent
    ``tbox``/``abox``, so :func:`_parse_dl` is never reached) MUST call this
    unconditionally up front, or an invalid ``syntax`` is silently accepted
    instead of refused.
    """
    if syntax in ("alc", "manchester"):
        return None
    return _error(ValueError(
        f"dl: unknown syntax {syntax!r} (one of ['alc', 'manchester'])"))


def _parse_dl(text: str, syntax: str, argument: str):
    """Parse concept TEXT into a :class:`~unicode_fol_kit.dl.Concept`.

    ``syntax="alc"`` (default) reads the glyph syntax via ``dl.parse_concept``;
    ``syntax="manchester"`` reads OWL 2 Manchester Syntax via
    ``dl.parse_manchester``. ``(concept, None)`` on success, ``(None,
    error_dict)`` on failure — see this section's own header comment for the
    two error shapes.
    """
    from .. import dl

    if syntax == "alc":
        try:
            return dl.parse_concept(text), None
        except dl.ConceptSyntaxError as exc:
            return None, {"ok": False, "argument": argument,
                          "errors": [{"dialect": "alc", "message": str(exc)}],
                          "spec_topic": "description-logic"}
    if syntax == "manchester":
        try:
            return dl.parse_manchester(text), None
        except dl.ManchesterSyntaxError as exc:
            return None, {"ok": False, "argument": argument,
                          "errors": [{"dialect": "manchester", "message": str(exc)}],
                          "spec_topic": "description-logic"}
    return None, _check_dl_syntax(syntax)


def _build_dl_tbox(rows, syntax: str, argument: str = "tbox"):
    """Build a :class:`~unicode_fol_kit.dl.TBox` from JSON row dicts.

    Each row is one of ``TBox``'s four axiom shapes: a general concept
    inclusion ``{"sub": <text>, "sup": <text>}`` (``TBox.add``), an
    equivalence ``{"equiv": [<text>, <text>]}`` (``TBox.add_equivalence``), a
    role inclusion ``{"subrole": <role>, "suprole": <role>}``
    (``TBox.add_role_inclusion`` — the RBox's role-hierarchy axiom, "H"), or
    a transitivity declaration ``{"transitive": <role>}``
    (``TBox.add_transitive_role`` — the RBox's "S"). ``rows`` ``None``/``[]``
    is the empty TBox. ``(tbox, None)`` on success, ``(None, error_dict)`` on
    the first failure: concept TEXT inside a row is parsed with
    :func:`_parse_dl` under the same ``syntax`` (the uniform ``ok=False``
    shape); a malformed row SHAPE (missing/unrecognised keys, a non-2-element
    ``equiv``) is a caller/config mistake, reported as ``{"error": {...}}``.
    """
    from .. import dl

    tbox = dl.TBox()
    for i, row in enumerate(rows or []):
        if not isinstance(row, dict):
            return None, _error(ValueError(
                f"{argument}[{i}]: expected an object, got {type(row).__name__}"))
        if "sub" in row and "sup" in row:
            sub, err = _parse_dl(row["sub"], syntax, f"{argument}[{i}].sub")
            if err is not None:
                return None, err
            sup, err = _parse_dl(row["sup"], syntax, f"{argument}[{i}].sup")
            if err is not None:
                return None, err
            tbox.add(sub, sup)
        elif "equiv" in row:
            pair = row["equiv"]
            if not (isinstance(pair, list) and len(pair) == 2):
                return None, _error(ValueError(
                    f"{argument}[{i}].equiv: expected a 2-element list, got {pair!r}"))
            c, err = _parse_dl(pair[0], syntax, f"{argument}[{i}].equiv[0]")
            if err is not None:
                return None, err
            d, err = _parse_dl(pair[1], syntax, f"{argument}[{i}].equiv[1]")
            if err is not None:
                return None, err
            tbox.add_equivalence(c, d)
        elif "subrole" in row and "suprole" in row:
            tbox.add_role_inclusion(row["subrole"], row["suprole"])
        elif "transitive" in row:
            tbox.add_transitive_role(row["transitive"])
        else:
            return None, _error(ValueError(
                f"{argument}[{i}]: expected keys 'sub'+'sup', 'equiv', "
                f"'subrole'+'suprole', or 'transitive', got {sorted(row)}"))
    return tbox, None


def _build_dl_abox(concepts, roles, distinct, syntax: str):
    """Build a :class:`~unicode_fol_kit.dl.ABox` from JSON rows.

    ``concepts``: ``[individual, concept_text]`` pairs (``ABox.assert_concept``).
    ``roles``: ``[a, b, role]`` triples (``ABox.assert_role``). ``distinct``:
    ``[a, b]`` pairs (``ABox.assert_distinct`` — the only thing that forces two
    individuals apart, since this reasoner has no unique name assumption; see
    :mod:`unicode_fol_kit.dl.tableau`'s "Qualified number restrictions"
    section). ``(abox, None)`` on success, ``(None, error_dict)`` on the first
    failure: a concept TEXT failure is the uniform ``ok=False`` shape
    (argument ``"concepts[i][1]"``); a malformed row shape is
    ``{"error": {...}}``.
    """
    from .. import dl

    abox = dl.ABox()
    for i, pair in enumerate(concepts or []):
        if not (isinstance(pair, list) and len(pair) == 2):
            return None, _error(ValueError(
                f"concepts[{i}]: expected [individual, concept_text], got {pair!r}"))
        individual, text = pair
        if not isinstance(individual, str):
            return None, _error(ValueError(
                f"concepts[{i}][0]: individual name must be a str, got "
                f"{type(individual).__name__}"))
        concept, err = _parse_dl(text, syntax, f"concepts[{i}][1]")
        if err is not None:
            return None, err
        abox.assert_concept(individual, concept)
    for i, triple in enumerate(roles or []):
        if not (isinstance(triple, list) and len(triple) == 3):
            return None, _error(ValueError(
                f"roles[{i}]: expected [a, b, role], got {triple!r}"))
        a, b, role = triple
        abox.assert_role(a, b, role)
    for i, pair in enumerate(distinct or []):
        if not (isinstance(pair, list) and len(pair) == 2):
            return None, _error(ValueError(
                f"distinct[{i}]: expected [a, b], got {pair!r}"))
        a, b = pair
        abox.assert_distinct(a, b)
    return abox, None


def dl_concept_satisfiable(concept: str, tbox: Optional[List[dict]] = None,
                           syntax: str = "alc") -> dict:
    """Is ``concept`` satisfiable with respect to ``tbox`` (the ALCHQ tableau)?

    ``concept``/``tbox`` text and ``syntax`` follow this section's own header
    comment; ``tbox`` rows follow :func:`_build_dl_tbox`.

    Returns ``{"ok": True, "satisfiable": bool, "concept_unicode": str}``.
    """
    from .. import dl

    c, err = _parse_dl(concept, syntax, "concept")
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        satisfiable = dl.concept_satisfiable(c, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "satisfiable": satisfiable, "concept_unicode": c.to_unicode()}


def dl_subsumes(sub: str, sup: str, tbox: Optional[List[dict]] = None,
                syntax: str = "alc") -> dict:
    """Does ``tbox`` entail ``sub ⊑ sup`` (every model puts ``sub`` in ``sup``)?

    Returns ``{"ok": True, "subsumes": bool, "sub_unicode": str, "sup_unicode": str}``.
    """
    from .. import dl

    sub_c, err = _parse_dl(sub, syntax, "sub")
    if err is not None:
        return err
    sup_c, err = _parse_dl(sup, syntax, "sup")
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        holds = dl.subsumes(sub_c, sup_c, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "subsumes": holds,
            "sub_unicode": sub_c.to_unicode(), "sup_unicode": sup_c.to_unicode()}


def dl_equivalent(c: str, d: str, tbox: Optional[List[dict]] = None,
                  syntax: str = "alc") -> dict:
    """Does ``tbox`` entail ``c ≡ d`` (mutual subsumption)?

    Returns ``{"ok": True, "equivalent": bool, "c_unicode": str, "d_unicode": str}``.
    """
    from .. import dl

    c_concept, err = _parse_dl(c, syntax, "c")
    if err is not None:
        return err
    d_concept, err = _parse_dl(d, syntax, "d")
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        holds = dl.equivalent(c_concept, d_concept, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "equivalent": holds,
            "c_unicode": c_concept.to_unicode(), "d_unicode": d_concept.to_unicode()}


def dl_abox_consistent(concepts: List[List[str]],
                       roles: Optional[List[List[str]]] = None,
                       distinct: Optional[List[List[str]]] = None,
                       tbox: Optional[List[dict]] = None,
                       syntax: str = "alc") -> dict:
    """Is the knowledge base ``(tbox, abox)`` consistent (does it have a model)?

    ``concepts``/``roles``/``distinct`` build the ABox — see
    :func:`_build_dl_abox`; ``tbox`` follows :func:`_build_dl_tbox`.

    Returns ``{"ok": True, "consistent": bool}``.
    """
    from .. import dl

    err = _check_dl_syntax(syntax)
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        consistent = dl.abox_consistent(abox, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "consistent": consistent}


def dl_instance_check(individual: str, concept: str,
                      concepts: List[List[str]],
                      roles: Optional[List[List[str]]] = None,
                      distinct: Optional[List[List[str]]] = None,
                      tbox: Optional[List[dict]] = None,
                      syntax: str = "alc") -> dict:
    """Does the knowledge base entail ``individual : concept``?

    Open-world (:func:`~unicode_fol_kit.dl.instance_check`'s own contract):
    ``entailed=False`` means "not entailed", never "entailed to be false".
    ``concepts``/``roles``/``distinct``/``tbox`` build the KB exactly like
    :func:`dl_abox_consistent`; ``concept`` is the query, parsed the same way.

    Returns ``{"ok": True, "entailed": bool, "individual": str,
    "concept_unicode": str}``.
    """
    from .. import dl

    query, err = _parse_dl(concept, syntax, "concept")
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        entailed = dl.instance_check(abox, individual, query, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "entailed": entailed, "individual": individual,
            "concept_unicode": query.to_unicode()}


def dl_instance_retrieval(concept: str, concepts: List[List[str]],
                          roles: Optional[List[List[str]]] = None,
                          distinct: Optional[List[List[str]]] = None,
                          tbox: Optional[List[dict]] = None,
                          syntax: str = "alc") -> dict:
    """Every ABox individual the knowledge base entails is a ``concept``.

    Sweeps :func:`~unicode_fol_kit.dl.instance_check` over every individual
    named in the ABox — including one that appears only in a role assertion.
    Arguments as :func:`dl_instance_check`.

    Returns ``{"ok": True, "individuals": [str, ...], "concept_unicode": str}``
    (``individuals`` sorted, for a deterministic payload).
    """
    from .. import dl

    query, err = _parse_dl(concept, syntax, "concept")
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        individuals = dl.instance_retrieval(abox, query, tb)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True, "individuals": sorted(individuals),
            "concept_unicode": query.to_unicode()}


def dl_classify(tbox: Optional[List[dict]] = None,
                concepts: Optional[List[str]] = None,
                syntax: str = "alc") -> dict:
    """Classify every named concept of ``tbox`` into a subsumption hierarchy.

    ``tbox`` follows :func:`_build_dl_tbox` (``None``/``[]`` classifies the
    empty TBox — every concept is then its own isolated node). ``concepts``
    is extra concept TEXT to bring names of interest into the vocabulary even
    when they never occur in a ``tbox`` axiom (see
    :func:`~unicode_fol_kit.dl.classify`'s own ``concepts`` parameter) —
    parsed under the same ``syntax``.

    Returns ``{"ok": True, "equivalents": {name: [str, ...]}, "parents":
    {name: [str, ...]}, "children": {name: [str, ...]}, "ancestors": {name:
    [str, ...]}}`` — :class:`~unicode_fol_kit.dl.Classification`'s frozensets
    rendered as sorted lists for a deterministic JSON payload. ``equivalents``
    is keyed by, and includes, the lexicographically smallest name in each
    mutual-subsumption synonym class; ``parents``/``children`` are the
    transitively-reduced Hasse diagram (direct super-/sub-concepts only);
    ``ancestors`` is the full transitive closure.
    """
    from .. import dl

    err = _check_dl_syntax(syntax)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    extra = []
    for i, text in enumerate(concepts or []):
        concept, err = _parse_dl(text, syntax, f"concepts[{i}]")
        if err is not None:
            return err
        extra.append(concept)
    try:
        result = dl.classify(tb, extra or None)
    except (dl.NonSimpleRoleError, RuntimeError) as exc:
        return _error(exc)
    return {"ok": True,
            "equivalents": {k: sorted(v) for k, v in result.equivalents.items()},
            "parents": {k: sorted(v) for k, v in result.parents.items()},
            "children": {k: sorted(v) for k, v in result.children.items()},
            "ancestors": {k: sorted(v) for k, v in result.ancestors.items()}}


def dl_parse_manchester(text: str, kind: str = "concept") -> dict:
    """Parse OWL 2 Manchester Syntax text, three ways.

    ``kind="concept"`` (default): a class expression via ``dl.parse_manchester``
    — returns the parsed concept's unicode rendering plus a ``to_manchester``
    round-trip (``dl.to_manchester(dl.parse_manchester(text))``), so a caller
    can confirm ``text`` normalises the way it expects.
    ``kind="axiom"``: a ``SubClassOf``/``EquivalentTo`` axiom via
    ``dl.parse_manchester_axiom``.
    ``kind="role_axiom"``: a ``SubPropertyOf``/``Characteristics: Transitive``
    RBox axiom via ``dl.parse_manchester_role_axiom`` (see
    :mod:`unicode_fol_kit.dl.tableau`'s "Role hierarchies and transitive
    roles (RBox)").

    Returns, on success: ``{"ok": True, "concept_unicode": str, "manchester":
    str}`` (``kind="concept"``); ``{"ok": True, "kind": "subclass"|
    "equivalent", "sub_unicode": str, "sup_unicode": str}`` (``kind="axiom"``);
    ``{"ok": True, "kind": "subproperty", "sub_role": str, "super_role": str}``
    or ``{"ok": True, "kind": "transitive", "role": str}`` (``kind="role_axiom"``).
    Malformed/unsupported ``text`` is the uniform ``ok=False`` shape (see this
    section's own header comment); an unknown ``kind`` is
    ``{"error": {"type": "ValueError", ...}}``.
    """
    from .. import dl

    if kind == "concept":
        try:
            concept = dl.parse_manchester(text)
        except dl.ManchesterSyntaxError as exc:
            return {"ok": False, "argument": "text",
                    "errors": [{"dialect": "manchester", "message": str(exc)}],
                    "spec_topic": "description-logic"}
        return {"ok": True, "concept_unicode": concept.to_unicode(),
                "manchester": dl.to_manchester(concept)}
    if kind == "axiom":
        try:
            label, sub, sup = dl.parse_manchester_axiom(text)
        except dl.ManchesterSyntaxError as exc:
            return {"ok": False, "argument": "text",
                    "errors": [{"dialect": "manchester", "message": str(exc)}],
                    "spec_topic": "description-logic"}
        return {"ok": True, "kind": label,
                "sub_unicode": sub.to_unicode(), "sup_unicode": sup.to_unicode()}
    if kind == "role_axiom":
        try:
            axiom = dl.parse_manchester_role_axiom(text)
        except dl.ManchesterSyntaxError as exc:
            return {"ok": False, "argument": "text",
                    "errors": [{"dialect": "manchester", "message": str(exc)}],
                    "spec_topic": "description-logic"}
        if axiom[0] == "subproperty":
            _, sub_role, super_role = axiom
            return {"ok": True, "kind": "subproperty",
                    "sub_role": sub_role, "super_role": super_role}
        _, role = axiom
        return {"ok": True, "kind": "transitive", "role": role}
    return _error(ValueError(
        f"dl_parse_manchester: unknown kind {kind!r} "
        "(one of ['concept', 'axiom', 'role_axiom'])"))


# --------------------------------------------------------------------------
# Server assembly
# --------------------------------------------------------------------------

def create_server():
    """Build the :class:`mcp.server.MCPServer` with every tool registered.

    Imported lazily so the whole subpackage stays importable-in-theory even
    without the optional SDK — but this function needs it: a missing SDK
    raises ImportError with the install hint.
    """
    try:
        from mcp.server import MCPServer
    except ImportError as exc:
        raise ImportError(
            "unicode_fol_kit.mcp needs the MCP SDK: "
            "pip install 'unicode-fol-kit[mcp]' (or: pip install 'mcp>=2.0')"
        ) from exc

    from .chem_tools import (
        molecule_to_structure, check_molecule, check_molecules,
        explain_molecule_failure, simplify_definition, chemical_signature,
    )

    server = MCPServer(_SERVER_NAME, instructions=_INSTRUCTIONS)
    for fn in (parse_formula, check_formula, prove, find_countermodel,
               check_equivalence, diagnose, repair_formula, translate,
               verbalize, list_backends,
               normalize, render, detect_dialect, compare_formulas,
               score_batch, check_consistency, get_signature, truth_table,
               drs_to_fol, list_translations,
               probability_bounds, probability_query, get_syntax_spec,
               # Chemistry: molecules as structures, definitions checked
               # against them, failures explained (mcp.chem_tools).
               molecule_to_structure, check_molecule, check_molecules,
               explain_molecule_failure, simplify_definition,
               chemical_signature,
               # Description logic: ALCHQ tableau reasoning (concept
               # satisfiability, subsumption, ABox consistency, instance/
               # realization queries, TBox classification) plus OWL
               # Manchester Syntax parsing — ALC glyph or Manchester input,
               # selected by each tool's own `syntax` parameter.
               dl_concept_satisfiable, dl_subsumes, dl_equivalent,
               dl_abox_consistent, dl_instance_check, dl_instance_retrieval,
               dl_classify, dl_parse_manchester):
        server.tool()(fn)
    return server


def main() -> None:
    """Run the server on stdio (the transport MCP clients spawn)."""
    create_server().run("stdio")
