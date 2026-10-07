"""The MCP tool layer over :mod:`unicode_logic_kit.api`.

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
  untouched — the MCP layer adds no vocabulary of its own beyond TEXT
  renderings of what is already there (``unicode``, ``axioms_unicode``,
  ``box``), because every tool takes text and a result is only usable as the
  next call's input if it comes back as text;
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
:mod:`unicode_logic_kit.api`, so the payload *contents* already inherit that
module's own STABILITY POLICY (see its docstring); this paragraph covers
the tool *surface* specifically, which a schema/name-based MCP client
depends on in a way a ``pip`` version pin cannot express for a JSON-RPC
session. ``tests/test_mcp_stability.py`` pins the current tool-schema
baseline (derived from a real ``list_tools()`` call) and fails with a
readable diff on any surface drift.
"""

import functools
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

_SERVER_NAME = "unicode-logic-kit"

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
logic-to-logic edges translate can follow. A translation comes with side
axioms (frame conditions; for a many-sorted formula the non-emptiness of
every sort AND the membership of every sorted constant in its sort):
translate returns them next to the translated formula, and they go into
prove / find_countermodel as SEPARATE premises -- without them a valid
formula comes back refuted.
Probabilistic layer (exact,
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


def _text_size(value) -> int:
    """The length of the longest text inside ``value`` (a string, or lists and dicts of them)."""
    longest, pending = 0, [value]
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            longest = max(longest, len(item))
        elif isinstance(item, dict):
            pending.extend(item.values())
        elif isinstance(item, (list, tuple)):
            pending.extend(item)
    return longest


def _nesting(value) -> int:
    """How many containers (dicts, lists) lie on the longest path from ``value`` down."""
    deepest, pending = 0, [(value, 1)]
    while pending:
        item, level = pending.pop()
        if isinstance(item, dict):
            deepest = max(deepest, level)
            pending.extend((child, level + 1) for child in item.values())
        elif isinstance(item, (list, tuple)):
            deepest = max(deepest, level)
            pending.extend((child, level + 1) for child in item)
    return deepest


def _answers_deep_input(tool):
    """``tool``, which never lets a ``RecursionError`` leave it.

    A formula nested a few hundred levels deep is read by the parser and then walked by
    recursive code (a normal form, a renderer, a node comparison), which runs out of the
    interpreter's recursion limit. The call is then made again where ``api`` reads a deep
    formula (:func:`unicode_logic_kit.api._call_deep`: a worker thread whose stack and recursion
    limit are sized for it), with the nesting bounded by the length of the longest text of the
    arguments (a text cannot be nested deeper than it is long). A call that still runs out is
    answered as the structured ``{"error": ...}`` that every other refusal of this module is,
    never as an exception that leaves the tool.
    """
    @functools.wraps(tool)
    def guarded(*args, **kwargs):
        try:
            return tool(*args, **kwargs)
        except RecursionError:
            pass
        size = max((_text_size(value) for value in (*args, *kwargs.values())), default=0)
        try:
            return api._call_deep(min(size, api._DEEP_MAX_LEVELS), lambda: tool(*args, **kwargs))
        except RecursionError:
            return _error(RecursionError(
                f"{tool.__name__}: the input is nested more deeply than this tool can process "
                f"(the interpreter's recursion limit ran out, also on the worker that reads deep "
                f"formulas); no result was produced"))

    guarded.answers_deep_input = True
    return guarded


def _answers_serializable(tool):
    """``tool``, whose answer is one the transport can write out, or else a refusal by name.

    A tool answers with a dict, and the MCP SDK writes that dict as JSON with a limit of its own
    on how deeply it may be nested. An answer nested deeper (the abstract syntax tree of a formula
    a few hundred quantifiers deep) ends in the SDK's own ``ToolError`` whose text speaks of a
    circular reference, which this answer is not. The answer is tried with the SDK's own JSON
    writer; one it cannot write is replaced by the structured ``{"error": ...}`` that names the
    nesting and says what to ask for instead. A call from Python, which needs no JSON, reaches
    the tool itself and is not held to this limit (see :func:`_registered`).
    """
    @functools.wraps(tool)
    def guarded(*args, **kwargs):
        result = tool(*args, **kwargs)
        try:
            import pydantic_core
        except ImportError:                       # no SDK, nothing is written out
            return result
        try:
            pydantic_core.to_json(result, fallback=str)
        except ValueError:
            return _error(ValueError(
                f"{tool.__name__}: the input was read, but its answer is nested {_nesting(result)} "
                f"levels deep, more than the MCP transport can write as JSON. Ask for a text form "
                f"of it instead (render, which answers a formula as text), or give a shallower "
                f"input"))
        return result

    return guarded


def _registered(tool):
    """``tool`` as the server registers it: guarded against a deep input and a deep answer."""
    return _answers_serializable(
        tool if getattr(tool, "answers_deep_input", False) else _answers_deep_input(tool))


def _signature_argument(signature):
    """The ``signature`` a tool was handed, as ``api`` reads it.

    What ``get_signature`` returns is ``{"ok": True, "signature": {...}}``; the tools that take a
    signature accept that whole result, or just its ``signature`` value, or the loose form
    ``{"predicates": ..., "functions": ..., "constants": ...}``. A dict that is exactly such a
    result is replaced by its ``signature`` value; anything else is returned as it is, for
    ``api`` to read or to refuse.
    """
    if (isinstance(signature, dict) and set(signature) == {"ok", "signature"}
            and signature["ok"] is True and isinstance(signature["signature"], dict)):
        return signature["signature"]
    return signature


def _unicode_texts(*concepts):
    """``([text, ...], None)`` or ``(None, {"error": ...})`` for description-logic concepts.

    ``Concept.to_unicode`` refuses (``ValueError``) a concept one of whose names makes the glyph
    text read back as ANOTHER concept (a class named ``<A⊓B>`` prints as the intersection of
    ``<A`` and ``B>``). A tool answers that refusal like every other refusal of the ``dl``
    package: as the structured error, never as an exception that leaves the tool.
    """
    try:
        return [concept.to_unicode() for concept in concepts], None
    except ValueError as exc:
        return None, _error(exc)


def _normalize_converses(converses: List[dict]):
    """JSON-dict converse declarations -> the internal tuple form.

    ``converses`` (``compare_formulas``/``score_batch``'s own parameter) is
    a list of ``{"a": [name, arity], "b": [name, arity], "permutation":
    [...]}`` dicts — the JSON-friendly spelling of
    :data:`unicode_logic_kit.eval.converses.ConverseDeclaration`. Raises
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

@_answers_deep_input
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


@_answers_deep_input
def check_formula(text: str, dialect: Optional[str] = None,
                  signature: Optional[dict] = None) -> dict:
    """Well-formedness + optional signature conformance for formula text.

    ``signature`` is what ``get_signature`` returns (its whole result, or just its
    ``signature`` value), or
    the loose form ``{"predicates": {"Human": 1}, "functions": {"father": 1},
    "constants": ["socrates"]}``. The truth constants ``⊤`` / ``⊥`` are logical
    constants, never an unknown predicate. A malformed ``signature`` comes back
    as the structured ``{"error": ...}``.
    """
    node, err = _parse(text, dialect)
    if err is not None:
        return err
    try:
        return api.check(node, signature=_signature_argument(signature)).to_dict()
    except (TypeError, ValueError) as exc:
        return _error(exc)


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
def diagnose(text: str, dialect: Optional[str] = None,
             signature: Optional[dict] = None) -> dict:
    """One diagnose round of the repair loop; YOU are the fixer.

    Returns ``{ok, diagnostics, suggestion, converged}`` for the given
    text, plus ``spec_topic`` when it did not parse. Apply the suggestion to
    the text yourself and call again; ``converged=True`` means the text
    parses and checks clean. ``signature`` is read as ``check_formula`` reads
    it (``get_signature``'s whole result, or its ``signature`` value); a malformed one comes
    back as the structured ``{"error": ...}``.
    """
    try:
        step = next(api.repair(text, dialect=dialect, signature=_signature_argument(signature)))
    except (TypeError, ValueError) as exc:
        return _error(exc)
    result = step.to_dict()
    # Same routing every other tool's failure carries: the diagnosis names
    # WHAT broke, spec_topic names the rule to look up before retrying. A
    # loop that has only the message has to guess which rule it violated.
    parse_errors = result.get("diagnostics", {}).get("parse")
    if parse_errors:
        result["spec_topic"] = _spec_topic_for(parse_errors)
    return result


@_answers_deep_input
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


#: The per-edge options ``translate`` forwards, named EXACTLY as the
#: comorphism edges declare them (``Comorphism.options``) — this layer invents
#: no option of its own. ``tests/test_mcp_server.py`` pins that this tuple is
#: the union of what the registry's edges declare, so an edge that grows an
#: option cannot become silently unreachable over MCP.
_TRANSLATE_OPTIONS = ("frame", "systems", "temporal_closure", "signature",
                      "mode", "bridges")

#: Source logics whose text must NOT go through ``parse_any``'s classical-first
#: mode ladder, because an earlier mode reads the same string as a DIFFERENT
#: formula: 'P ⊕ Q' is classical Xor in the ``fol`` mode and a strong
#: Łukasiewicz disjunction in the fuzzy ones, so a fuzzy term parsed by the
#: ladder would be translated as the classical formula it is not. The dialects
#: are tried in order and used only when the caller gave no ``dialect`` of
#: their own; the two fuzzy modes are disjoint (``msfl`` accepts only SORTED
#: quantifiers, ``fl`` only unsorted ones), hence both.
_SOURCE_DIALECTS = {"fuzzy": ("fl", "msfl")}


def _translate_options(frame, systems, temporal_closure, signature, mode,
                       bridges) -> dict:
    """The per-edge options that were actually given, shaped for the registry.

    ``None`` means "not given" and is dropped, so an edge's own default
    (``frame="K"``, ``mode="constant"``, ``temporal_closure=True``) applies.
    This checks only the SHAPE of each value — a ``temporal_closure="false"``
    string would be truthy and silently mean ``True`` — and leaves membership
    (is that a known frame / mode / bridge / modal family?) and "does any edge
    on this path take that option?" to the edges and the registry, whose
    refusals already name what is accepted and which the tool returns as
    ``{"error": ...}``. ``ValueError`` on a malformed value.
    """
    options: dict = {}

    def given(name, value, kind, what):
        if value is None:
            return False
        # bool is an int subclass, but 'frame': true is not a frame name.
        if not isinstance(value, kind) or (kind is not bool
                                           and isinstance(value, bool)):
            raise ValueError(
                f"translate: {name} must be {what}, got {value!r}")
        return True

    if given("frame", frame, str,
             "a string — a modal system name such as 'S4', or a "
             "Scott–Lemmon spec like 'G(1,1,1,1)'"):
        options["frame"] = frame
    if given("mode", mode, str,
             "a string — the quantified-modal domain regime, such as "
             "'constant' or 'varying'"):
        options["mode"] = mode
    if given("temporal_closure", temporal_closure, bool, "true or false"):
        options["temporal_closure"] = temporal_closure
    if given("systems", systems, dict,
             "an object mapping a modal family to a system name, e.g. "
             '{"epistemic": "S5"}'):
        if not all(isinstance(k, str) and isinstance(v, str)
                   for k, v in systems.items()):
            raise ValueError(
                f"translate: systems must map a family name to a system "
                f"name (both strings), got {systems!r}")
        options["systems"] = dict(systems)
    if given("bridges", bridges, (list, tuple), "a list of bridge names"):
        if not all(isinstance(b, str) for b in bridges):
            raise ValueError(
                f"translate: bridges must be a list of strings, got "
                f"{bridges!r}")
        options["bridges"] = list(bridges)
    if given("signature", signature, dict,
             'a signature object, e.g. {"subsorts": {"Human": ["Animal"]}}'):
        from ..fol.signature import Signature

        # from_dict's own refusals (unknown key, wrong-typed section, a subsort
        # cycle) name the offending entry; they surface through _error.
        options["signature"] = Signature.from_dict(signature)
    return options


def _text_of(node) -> str:
    """The unicode rendering of ``node``, in a form the OTHER tools can read.

    Every tool here takes formula TEXT, so a translated formula and its side
    axioms are only usable as premises if their text parses again. A
    translation can render a name the text grammar does not accept: the bound
    variables the translations mint are legal names since 0.30.0, but a name
    the CALLER supplies is printed as it is, and the FOL grammar wants a
    predicate to start upper-case, so an OWL-style role (``hasChild``) or a
    description-logic individual spelled like a variable comes back out as text
    ``prove`` rejects. Rendered as it is, the result looks right and ``prove``
    rejects it. So the node is rendered as
    the kit prints it and, failing that, with its bound variables alpha-renamed
    to ``q0``, ``q1``, … — a renaming that changes no meaning — and the first
    spelling that reads back as EXACTLY the same formula wins. Failing both,
    the first that parses at all (a constant printed as ``a`` reads back as a
    variable, which no rendering can fix), and failing that the plain
    printing; the ``result`` / ``axioms`` ASTs next to it stay the authority.
    A rendering that already reads back is left exactly as the kit prints it.
    """
    from ..eval.canonical import _alpha_normalize

    spellings = (node, _alpha_normalize(node))
    texts = [spelling.to_unicode_str() for spelling in spellings]
    readings: dict = {}

    def reads(i: int, exact: bool) -> bool:
        if i not in readings:
            readings[i] = api.parse_any(texts[i])
        reading = readings[i]
        return reading.ok and (not exact or reading.formula == spellings[i])

    for exact in (True, False):
        for i in range(len(spellings)):
            if reads(i, exact):
                return texts[i]
    return texts[0]


def _text_of_term(value) -> Optional[str]:
    """``unicode`` text for a Node or a DL concept, else ``None``."""
    if hasattr(value, "to_unicode_str"):
        return _text_of(value)
    if hasattr(value, "to_unicode"):               # dl.Concept spelling
        return value.to_unicode()
    return None


def _parse_term(term: str, from_logic: str, dialect: Optional[str]):
    """``(payload, None)`` or ``(None, error_dict)`` for the source logic's
    own term type (see :func:`translate` for the list)."""
    if from_logic == "casl":
        return term, None
    if from_logic == "alc":
        from ..dl import ConceptSyntaxError, parse_concept

        try:
            return parse_concept(term), None
        except ConceptSyntaxError as exc:
            return None, {"ok": False, "argument": "term",
                          "errors": [{"dialect": "alc", "message": str(exc)}]}
    if from_logic == "drs":
        from .. import drt

        try:
            return drt.parse_drs(term), None
        except (drt.DRSSyntaxError, ValueError) as exc:
            return None, {"ok": False, "argument": "term",
                          "errors": [{"dialect": "drs_box",
                                      "message": str(exc)}]}
    hints = (dialect,) if dialect else _SOURCE_DIALECTS.get(from_logic, (None,))
    failures: list = []
    for hint in hints:
        node, err = _parse(term, hint, argument="term")
        if err is None:
            return node, None
        failures.append(err)
    err = failures[0]
    if len(failures) > 1:            # keep every attempted dialect's diagnosis
        errors = [e for failure in failures for e in failure["errors"]]
        err = {"ok": False, "argument": "term", "errors": errors,
               "spec_topic": _spec_topic_for(errors)}
    if from_logic == "qml" and dialect is None:
        # Quantified modal logic over SORTED quantifiers ('□∀x:Human …') is
        # something the qml edge translates, but no single parse_any mode
        # reads modal operators and sorts together — so only after the whole
        # ladder has failed, and only for this source logic, try that one
        # combination. A failure keeps the ladder's diagnostics.
        from ..fol.msflparser import MSFLParser

        try:
            return MSFLParser(many_sorted=True, modal=True).parse(term), None
        except Exception:                         # noqa: BLE001 - parser errors
            pass
    return None, err


@_answers_deep_input
def translate(term: str, from_logic: str, to_logic: str,
              dialect: Optional[str] = None,
              frame: Optional[str] = None,
              systems: Optional[dict] = None,
              temporal_closure: Optional[bool] = None,
              signature: Optional[dict] = None,
              mode: Optional[str] = None,
              bridges: Optional[List[str]] = None) -> dict:
    """Translate between logics over the comorphism registry — and pass every entry of the returned ``axioms`` as a SEPARATE premise next to ``result`` (never conjoined onto it, never dropped), or the translated formula answers a different question and a valid formula comes back refuted.

    The result is ``{result, unicode, axioms, axioms_unicode, guarantee,
    source, target, path, lossy, note}``. ``result`` is the translated term
    (JSON AST) and ``unicode`` its text; ``axioms`` are the side conditions of
    the translation, already in the TARGET logic (``axioms_unicode`` is the
    same list as text, entry for entry), e.g. the frame conditions of a modal
    system, or for a many-sorted formula BOTH the non-emptiness of every sort
    (an ``∃`` sentence about the sort ``Human``) AND the membership atom of
    every sorted constant (``Human(socrates)``: a constant written
    ``socrates:Human`` is an element of ``Human``) -- a caller who passes only
    the first answers a weaker question. To
    decide a question about the translated formula, call ``prove`` with the
    ``unicode`` as the conclusion and ``axioms_unicode`` among the
    ``premises``; ``find_countermodel`` and ``check_consistency`` take them
    the same way. ``guarantee`` is what the translation preserves ONCE those
    axioms are added — ``faithful`` (every question transfers),
    ``validity`` (validity and entailment transfer), ``satisfiability`` (only
    satisfiability: a validity answer through it means nothing), ``lossy``
    (neither; ``note`` says what is dropped) — or ``null`` when an edge on the
    path declares none, which is NOT the same as faithful. ``note`` carries
    the conventions (e.g. the free world variable ``w`` a modal image is
    anchored at). ``list_translations`` shows the logic labels, the edges and
    the options each edge takes.

    The term's PARSER follows the source logic's own term type: ``"casl"``
    terms are CASL spec TEXT passed through verbatim (the dynamic
    ``hets:<Name>`` edges); ``"alc"`` terms are description-logic concept
    text (``Human ⊓ ∃hasChild.Doctor``) parsed by the DL grammar —
    review-confirmed: the registered alc→modal/alc→fol edges take
    ``Concept`` objects that no FOL-family grammar can produce; ``"drs"``
    terms are discourse-representation boxes in the compact box notation
    (``[x | Farmer(x), Runs(x)]``, as ``drs_to_fol`` takes); ``"fuzzy"`` terms
    are read in the Łukasiewicz dialect (so ``⊕`` is the strong disjunction,
    not Xor); every other source logic parses the term as a formula via
    ``parse_any`` (``"qml"`` additionally reads sorted quantifiers under
    modal operators). Node/Concept results gain a ``"unicode"`` rendering; a
    DRS result gains ``"box"``, its box notation. Bound variables the
    translations name in a way the text grammar rejects are renamed ``q0``,
    ``q1``, … in the text renderings only, so every text here can be passed
    back to the other tools.

    Options are forwarded to the edges on the path that declare them and
    omitted ones keep the edge's default: ``frame`` (modal system, default
    ``K``), ``systems`` (``{"epistemic": "S5"}``-style, per agent family) and
    ``temporal_closure`` for ``modal``/``qml`` sources; ``mode`` (domain
    regime) and ``bridges`` (cross-family frame conditions) for ``qml``;
    ``signature`` (``{"subsorts": {"Human": ["Animal"]}}``) for ``msfol``,
    where it adds one axiom per declared subsort edge. An option no edge on the
    path takes, or an unknown frame / mode / bridge / family, is a structured
    error naming what is accepted.
    """
    try:
        options = _translate_options(frame, systems, temporal_closure,
                                     signature, mode, bridges)
    except (ValueError, TypeError) as exc:
        return _error(exc)
    payload, err = _parse_term(term, from_logic, dialect)
    if err is not None:
        return err
    from ..comorphism import DEFAULT_REGISTRY

    try:
        # The registry, not api.translate: that facade takes no options, and
        # a translation that silently ignores frame= is the wrong question.
        result = DEFAULT_REGISTRY.translate(payload, from_logic, to_logic,
                                            **options)
    except (ValueError, TypeError, NotImplementedError) as exc:
        return _error(exc)
    try:
        rendered = result.to_dict()
        text = _text_of_term(result.result)
        if text is not None:
            rendered["unicode"] = text
        elif hasattr(result.result, "to_box_notation"):           # drt.DRS
            rendered["box"] = result.result.to_box_notation()
        # Parallel to ``axioms`` (same length, same order); an axiom with no text
        # form falls back to the repr that ``to_dict`` already gave it.
        rendered["axioms_unicode"] = [_text_of_term(a) or repr(a)
                                      for a in result.axioms]
    except (ValueError, NotImplementedError) as exc:
        # A result with no faithful text (a concept whose name reads back as another
        # concept, see ``Concept.to_unicode``) is a refusal, not a crash.
        return _error(exc)
    return rendered


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
def render(text: str, to: str = "tptp",
           dialect: Optional[str] = None) -> dict:
    """Render a formula in another concrete syntax.

    ``to``: ``unicode`` / ``tptp`` / ``prover9`` / ``latex`` / ``smtlib``
    (a standalone SMT-LIB2 problem: ``(set-logic ...)``, the declaration
    preamble, and one ``(assert ...)`` — no premises through this tool; use
    ``unicode_logic_kit.atp.z3_input.to_smtlib`` directly for an entailment
    with premises) / ``casl`` (a bare CASL formula via ``formula_to_casl``)
    / ``json`` (the versioned ``serialize`` envelope — the only target whose
    ``rendered`` is a dict, not a string) / ``english`` (deterministic
    verbalization). A family without the requested rendering surfaces its
    own ``NotImplementedError``/``ValueError`` as a structured error — for
    ``smtlib`` this is ``to_z3``'s own refusal (second/third-order,
    modal/hybrid/linear/Lambek/team constructs have no first-order SMT-LIB2
    encoding), named by construct, reused rather than reimplemented.

    ``tptp`` also refuses a formula in which two DISTINCT names of one kind
    would be written as the same TPTP word (the constants ``θ`` and ``theta``,
    or ``gaseous`` and ``Gaseous`` read from TPTP text: both fold to one
    identifier, which would turn ``P(a) <-> P(b)`` into a tautology). The error
    names both symbols and the shared word; rename one of them and render
    again. It checks the one formula it renders — to build a problem from
    several formulas use ``unicode_logic_kit.atp.generate_tptp_problem_with_mapping``,
    which checks them together.
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


@_answers_deep_input
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


@_answers_deep_input
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
    :func:`unicode_logic_kit.eval.equivalence.equivalent`'s ``converses``
    parameter and :mod:`unicode_logic_kit.eval.converses`); each entry is
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


@_answers_deep_input
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


@_answers_deep_input
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
    from ..fol._identifiers import symbol_names

    parsed = []
    for i, f in enumerate(formulas or []):
        node, err = _parse(f, dialect, argument=f"formula[{i}]")
        if err is not None:
            return err
        parsed.append(node)

    # Fresh against EVERY name of the problem, of every kind (a predicate, a
    # constant, a sort, ...): a backend may keep them in one namespace.
    used = symbol_names(*parsed)
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


@_answers_deep_input
def get_signature(formulas: List[str],
                  dialect: Optional[str] = None) -> dict:
    """Extract the inferred vocabulary (Signature) of a formula set.

    The result dict is ``fol.Signature.from_formulas(...)``'s rich form —
    predicates/functions with arities and inferred sorts, constants, sort
    names — ready to pass back as ``check_formula``'s / ``diagnose``'s
    ``signature`` argument to hold FURTHER generations to this vocabulary:
    the whole result, ``{"ok": True, "signature": {...}}``, or just its
    ``signature`` value are both accepted.
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


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
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
    :func:`unicode_logic_kit.prob.nilsson.entailment_bounds`): ``"direct"``
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


@_answers_deep_input
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


@_answers_deep_input
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


@_answers_deep_input
def list_translations() -> dict:
    """Enumerate the logic-to-logic edges the translate tool can follow.

    The kit's own comorphism registry (BFS-composable); after a Hets bridge
    refresh the dynamic ``hets:<Name>`` edges appear here too. ``logics`` is
    every label ``translate`` accepts as ``from_logic`` / ``to_logic``.
    ``lossy`` edges do not preserve the full source semantics; ``note``
    carries the conventions a consumer must know. ``guarantee`` is what the
    edge preserves (``faithful`` / ``validity`` / ``satisfiability`` /
    ``lossy``, or ``null`` when the edge declares none — not the same as
    faithful). ``options`` are the ``translate`` parameters the edge reads
    (``frame``, ``systems``, ``temporal_closure``, ``signature``, ``mode``,
    ``bridges``), and ``side_axioms`` says whether the edge can return
    ``axioms`` that must be passed as separate premises.
    """
    from ..comorphism import DEFAULT_REGISTRY

    edges = DEFAULT_REGISTRY.edges()
    return {"logics": sorted({label for e in edges
                              for label in (e.source, e.target)}),
            "edges": [{"name": e.name, "source": e.source,
                       "target": e.target, "lossy": e.lossy, "note": e.note,
                       "guarantee": e.guarantee,
                       "options": sorted(e.options),
                       "side_axioms": e.axioms is not None}
                      for e in edges]}


# --------------------------------------------------------------------------
# Description-logic (ALCHQ) reasoning tools — pure wiring over dl.tableau /
# dl.classification, with input parsed by dl.parser (the ALC glyph syntax,
# ``syntax="alc"``, default) or dl.owl_manchester (OWL 2 Manchester Syntax,
# ``syntax="manchester"``). Conventions match every tool above: a bad
# CONCEPT/AXIOM text is the uniform ``{"ok": False, "argument": ...,
# "errors": [...], "spec_topic": "description-logic"}`` shape (whether the
# grammar rejected it as :class:`~unicode_logic_kit.dl.ConceptSyntaxError` or
# :class:`~unicode_logic_kit.dl.ManchesterSyntaxError` — including a
# Manchester construct outside ALCHQ, e.g. ``Self``/``inverse``/a
# nominal, which that parser rejects by NAME rather than a bare syntax
# error; a ``value`` restriction (``hasChild value Doctor``) is READ, and is
# then the tableau's refusal below, ``UnsupportedConceptError``, because it is
# a nominal in disguise); a documented, non-text exception — every refusal class the ``dl``
# package raises on purpose (:func:`_dl_errors`: a qualified number
# restriction on a non-simple role, an axiom KIND / concept / datatype the
# tableau does not decide, a malformed role) or the tableau's step-budget
# ``RuntimeError`` — is ``{"error": {"type": ..., "message": ...}}``. A
# :class:`Concept` has no ``to_dict()`` (see ``dl.concepts``), so results
# carry it as ``*_unicode`` text (``Concept.to_unicode()``) rather than a
# JSON AST, exactly like ``translate()``'s own ``alc`` branch above. A concept
# one of whose names would make that text read back as ANOTHER concept (a class
# named ``<A⊓B>``) has no faithful text: ``to_unicode()`` refuses it with a
# ``ValueError``, and the tool answers with the same structured error
# (:func:`_unicode_texts`) before it reasons, never with the exception.
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


def _dl_errors():
    """The exceptions a description-logic tool turns into an ``{"error": ...}``
    payload instead of letting them escape: the tableau's decidability refusal
    (a number restriction on a non-simple role), the NAMED refusals of a
    fragment it does not decide (an axiom kind, a concept, a datatype), the
    refusal of a malformed role (:class:`~unicode_logic_kit.dl.RoleExpressionError`,
    which the role builders raise and which a query-time check of a role name
    raises too) and the ``RuntimeError`` of an exhausted resource budget.

    ONE place, shared by every ``dl_*`` reasoning tool: a refusal class the
    ``dl`` package gains is added HERE and is then reported by all of them.
    ``tests/test_mcp_server.py`` classifies every exception class the package
    defines against this tuple, so a class added there and forgotten here fails
    that test instead of reaching a caller as a bare exception.

    The syntax errors of the two readers (``ConceptSyntaxError``,
    ``ManchesterSyntaxError``) are deliberately NOT here: they are text
    mistakes, reported by :func:`_parse_dl` in the uniform ``ok=False`` shape.
    ``dl`` is imported here, not at module level, like everywhere else in this
    file."""
    from .. import dl

    return (dl.NonSimpleRoleError, dl.UnsupportedAxiomError,
            dl.UnsupportedConceptError, dl.UnsupportedDatatypeError,
            dl.RoleExpressionError, RuntimeError)


def _dl_datatype_names(rows) -> List[str]:
    """The names a ``tbox`` row list DEFINES as datatypes (its ``{"datatype":
    name, "definition": ...}`` rows), in order.

    A user-defined datatype is an ordinary name, so the Manchester reader can
    tell ``d some Digit`` (data) from ``r some Dog`` (object) only if it is
    told ``Digit`` is a datatype; every tool that reads concept text next to a
    ``tbox`` passes these names on. A built-in datatype (``xsd:integer``) needs
    no listing."""
    return [row["datatype"] for row in rows or []
            if isinstance(row, dict) and isinstance(row.get("datatype"), str)]


def _parse_dl(text: str, syntax: str, argument: str, datatypes=()):
    """Parse concept TEXT into a :class:`~unicode_logic_kit.dl.Concept`.

    ``syntax="alc"`` (default) reads the glyph syntax via ``dl.parse_concept``;
    ``syntax="manchester"`` reads OWL 2 Manchester Syntax via
    ``dl.parse_manchester``. ``(concept, None)`` on success, ``(None,
    error_dict)`` on failure — see this section's own header comment for the
    two error shapes. ``datatypes``: the user-defined datatype names (see
    :func:`_dl_datatype_names`), used by the Manchester reader only — the glyph
    syntax has no data layer, so it cannot say a data restriction at all.
    """
    from .. import dl

    if not isinstance(text, str):
        # A malformed row shape, like every other non-str below: reported, not
        # raised (a JSON number in a concept slot used to escape as a TypeError
        # from inside the reader).
        return None, _error(ValueError(
            f"{argument}: expected concept text (str), got {type(text).__name__}"))
    if syntax == "alc":
        try:
            return dl.parse_concept(text), None
        except dl.ConceptSyntaxError as exc:
            return None, {"ok": False, "argument": argument,
                          "errors": [{"dialect": "alc", "message": str(exc)}],
                          "spec_topic": "description-logic"}
    if syntax == "manchester":
        try:
            return dl.parse_manchester(text, datatypes=datatypes), None
        except dl.ManchesterSyntaxError as exc:
            return None, {"ok": False, "argument": argument,
                          "errors": [{"dialect": "manchester", "message": str(exc)}],
                          "spec_topic": "description-logic"}
    return None, _check_dl_syntax(syntax)


def _parse_dl_data_range(text, argument: str, datatypes=()):
    """Parse DATA RANGE text (always Manchester: the glyph syntax has no data
    layer) into a :class:`~unicode_logic_kit.dl.datatypes.DataRange`.
    ``(range, None)`` / ``(None, error_dict)`` like :func:`_parse_dl`."""
    from .. import dl

    if not isinstance(text, str):
        return None, _error(ValueError(
            f"{argument}: expected data range text (str), got {type(text).__name__}"))
    try:
        return dl.parse_manchester_data_range(text, datatypes=datatypes), None
    except dl.ManchesterSyntaxError as exc:
        return None, {"ok": False, "argument": argument,
                      "errors": [{"dialect": "manchester", "message": str(exc)}],
                      "spec_topic": "description-logic"}


def _parse_dl_literal(text, argument: str):
    """Parse one LITERAL text (``"400"^^xsd:integer``, ``"abc"@en``, a bare
    numeral) into a :class:`~unicode_logic_kit.dl.datatypes.Literal`.
    ``(literal, None)`` / ``(None, error_dict)`` like :func:`_parse_dl`."""
    from .. import dl

    if not isinstance(text, str):
        return None, _error(ValueError(
            f"{argument}: expected literal text (str), got {type(text).__name__}"))
    try:
        return dl.parse_manchester_literal(text), None
    except dl.ManchesterSyntaxError as exc:
        return None, {"ok": False, "argument": argument,
                      "errors": [{"dialect": "manchester", "message": str(exc)}],
                      "spec_topic": "description-logic"}


#: ``row key -> (TBox builder, how many roles the value holds)`` for the
#: role-box row shapes that take ONE key. ``"one"`` is a single role name
#: (every characteristic axiom), ``"many"`` a list of role names.
_DL_ROLE_ROW_SHAPES = {
    "transitive": ("add_transitive_role", "one"),
    "symmetric": ("add_symmetric_role", "one"),
    "asymmetric": ("add_asymmetric_role", "one"),
    "reflexive": ("add_reflexive_role", "one"),
    "irreflexive": ("add_irreflexive_role", "one"),
    "functional": ("add_functional_role", "one"),
    "inversefunctional": ("add_inverse_functional_role", "one"),
    "inverseroles": ("add_inverse_roles", "many"),
    "disjointroles": ("add_disjoint_roles", "many"),
    "equivroles": ("add_equivalent_roles", "many"),
}

#: ``row key -> (TBox builder, OWL keyword)`` for the two role-box axioms
#: whose value is a ROLE plus a CLASS EXPRESSION: ``{"domainrole": r,
#: "domain": <concept text>}`` and its ``range`` twin. A table of their own
#: because the concept text has to go through :func:`_parse_dl` under the
#: caller's ``syntax``, which no role-name row needs.
_DL_FILLER_ROLE_ROW_SHAPES = {
    "domain": ("add_role_domain", "domainrole", "ObjectPropertyDomain"),
    "range": ("add_role_range", "rangerole", "ObjectPropertyRange"),
}


#: ``row key -> (TBox builder, how many property names the value holds)`` for
#: the data-box row shapes that take ONE key of property names, the data twin of
#: :data:`_DL_ROLE_ROW_SHAPES`.
_DL_DATA_NAME_ROW_SHAPES = {
    "equivdata": ("add_equivalent_data_properties", "many"),
    "disjointdata": ("add_disjoint_data_properties", "many"),
    "functionaldata": ("add_functional_data_property", "one"),
}

#: Every key that marks a row as a DATA-box row. Checked BEFORE the role rows:
#: ``{"domaindata": d, "domain": text}`` carries the key ``"domain"``, which the
#: role-domain branch would otherwise claim and reject for lacking ``domainrole``.
_DL_DATA_ROW_KEYS = ("subdata", "domaindata", "rangedata", "datatype",
                     *_DL_DATA_NAME_ROW_SHAPES)


def _add_dl_data_row(tbox, row, i: int, syntax: str, argument: str, datatypes):
    """Add the data-box row ``row`` (the ``i``-th) to ``tbox``; ``None`` on
    success, an error dict on the first failure (same two shapes as
    :func:`_build_dl_tbox`)."""
    from .. import dl

    where = f"{argument}[{i}]"
    names = [key for key in _DL_DATA_ROW_KEYS if key in row]
    if len(names) != 1:
        return _error(ValueError(
            f"{where}: a data-box row carries exactly one of {sorted(_DL_DATA_ROW_KEYS)}, "
            f"got {names}"))
    key = names[0]
    try:
        if key == "subdata":
            if "supdata" not in row:
                return _error(ValueError(
                    f"{where}: a 'subdata' row needs 'supdata', got {sorted(row)}"))
            tbox.add_data_property_inclusion(row["subdata"], row["supdata"])
        elif key == "domaindata":
            if "domain" not in row:
                return _error(ValueError(
                    f"{where}: a 'domaindata' row needs 'domain' (the class text), "
                    f"got {sorted(row)}"))
            concept, err = _parse_dl(row["domain"], syntax, f"{where}.domain", datatypes)
            if err is not None:
                return err
            tbox.add_data_property_domain(row["domaindata"], concept)
        elif key == "rangedata":
            if "range" not in row:
                return _error(ValueError(
                    f"{where}: a 'rangedata' row needs 'range' (the data range text), "
                    f"got {sorted(row)}"))
            datarange, err = _parse_dl_data_range(row["range"], f"{where}.range", datatypes)
            if err is not None:
                return err
            tbox.add_data_property_range(row["rangedata"], datarange)
        elif key == "datatype":
            if "definition" not in row:
                return _error(ValueError(
                    f"{where}: a 'datatype' row needs 'definition' (the data range "
                    f"text), got {sorted(row)}"))
            if not isinstance(row["datatype"], str):
                return _error(ValueError(
                    f"{where}.datatype: expected a datatype name (str), got "
                    f"{row['datatype']!r}"))
            datarange, err = _parse_dl_data_range(
                row["definition"], f"{where}.definition", datatypes)
            if err is not None:
                return err
            tbox.add_datatype_definition(row["datatype"], datarange)
        else:
            builder, arity = _DL_DATA_NAME_ROW_SHAPES[key]
            value = row[key]
            if arity == "one":
                if not isinstance(value, str):
                    return _error(ValueError(
                        f"{where}.{key}: expected a data property name (str), "
                        f"got {value!r}"))
                names_ = [value]
            else:
                if not (isinstance(value, list) and len(value) >= 2
                        and all(isinstance(name, str) for name in value)):
                    return _error(ValueError(
                        f"{where}.{key}: expected a list of at least 2 data "
                        f"property names, got {value!r}"))
                names_ = value
            getattr(tbox, builder)(*names_)
    except (dl.RoleExpressionError, dl.UnsupportedDatatypeError) as exc:
        return _error(exc)
    return None


def _build_dl_tbox(rows, syntax: str, argument: str = "tbox"):
    """Build a :class:`~unicode_logic_kit.dl.TBox` from JSON row dicts.

    Each row is one of ``TBox``'s axiom shapes. The concept-level two:

    * ``{"sub": <text>, "sup": <text>}`` — a general concept inclusion
      (``TBox.add``);
    * ``{"equiv": [<text>, <text>]}`` — an equivalence (``TBox.add_equivalence``).

    The role box (see "Role hierarchies and transitive roles (RBox)" and "The
    rest of the OWL 2 role box" in :mod:`unicode_logic_kit.dl.tableau`'s module
    docstring; the role values are NAMES, never concept text, so ``syntax``
    does not apply to them):

    * ``{"subrole": <role>, "suprole": <role>}`` — a role inclusion;
    * ``{"chain": [<role>, …], "suprole": <role>}`` — a property chain
      (``TBox.add_role_chain``), checked BEFORE ``subrole`` so the two
      ``suprole`` shapes cannot be confused;
    * ``{"inverseroles": [p, q]}``, ``{"disjointroles": [p, q, …]}``,
      ``{"equivroles": [p, q, …]}`` — the n-ary role axioms;
    * ``{"transitive": <role>}`` and its six siblings ``symmetric``,
      ``asymmetric``, ``reflexive``, ``irreflexive``, ``functional``,
      ``inversefunctional`` — the characteristic axioms;
    * ``{"domainrole": <role>, "domain": <text>}`` and
      ``{"rangerole": <role>, "range": <text>}`` — the two role-box axioms
      whose right-hand side is a CLASS EXPRESSION (``TBox.add_role_domain`` /
      ``add_role_range``), so that text IS parsed under ``syntax``.

    The data box (see "The data layer" in :mod:`unicode_logic_kit.dl.translate`'s
    module docstring; property and datatype values are NAMES, and the data range
    text is ALWAYS OWL 2 Manchester syntax, since the glyph syntax has no data
    layer):

    * ``{"subdata": <prop>, "supdata": <prop>}`` — ``SubDataPropertyOf``;
    * ``{"equivdata": [p, q, …]}`` and ``{"disjointdata": [p, q, …]}`` — the
      n-ary data property axioms;
    * ``{"functionaldata": <prop>}`` — ``FunctionalDataProperty``;
    * ``{"domaindata": <prop>, "domain": <class text>}`` — ``DataPropertyDomain``
      (the class text is parsed under ``syntax``);
    * ``{"rangedata": <prop>, "range": <data range text>}`` —
      ``DataPropertyRange``;
    * ``{"datatype": <name>, "definition": <data range text>}`` —
      ``DatatypeDefinition``. The name is then a datatype in every other row's
      text, which is how ``d some Digit`` is told from ``r some Dog``.

    A row is accepted even when the in-house tableau refuses to REASON over
    that kind: which kinds it decides is recorded in ``dl.tableau._AXIOM_KINDS``
    and enforced at query time, and the tool then reports that refusal rather
    than silently answering about a weaker knowledge base.

    ``rows`` ``None``/``[]`` is the empty TBox. ``(tbox, None)`` on success,
    ``(None, error_dict)`` on the first failure: concept TEXT inside a row is
    parsed with :func:`_parse_dl` under the same ``syntax`` (the uniform
    ``ok=False`` shape); a malformed row SHAPE (missing/unrecognised keys, a
    non-2-element ``equiv``, a role name that is not a string, an OWL 2
    built-in role name) is a caller/config mistake, reported as
    ``{"error": {...}}``.
    """
    from .. import dl

    tbox = dl.TBox()
    datatypes = _dl_datatype_names(rows)
    for i, row in enumerate(rows or []):
        if not isinstance(row, dict):
            return None, _error(ValueError(
                f"{argument}[{i}]: expected an object, got {type(row).__name__}"))
        if "sub" in row and "sup" in row:
            sub, err = _parse_dl(row["sub"], syntax, f"{argument}[{i}].sub", datatypes)
            if err is not None:
                return None, err
            sup, err = _parse_dl(row["sup"], syntax, f"{argument}[{i}].sup", datatypes)
            if err is not None:
                return None, err
            tbox.add(sub, sup)
        elif "equiv" in row:
            pair = row["equiv"]
            if not (isinstance(pair, list) and len(pair) == 2):
                return None, _error(ValueError(
                    f"{argument}[{i}].equiv: expected a 2-element list, got {pair!r}"))
            c, err = _parse_dl(pair[0], syntax, f"{argument}[{i}].equiv[0]", datatypes)
            if err is not None:
                return None, err
            d, err = _parse_dl(pair[1], syntax, f"{argument}[{i}].equiv[1]", datatypes)
            if err is not None:
                return None, err
            tbox.add_equivalence(c, d)
        elif any(key in row for key in _DL_DATA_ROW_KEYS):
            err = _add_dl_data_row(tbox, row, i, syntax, argument, datatypes)
            if err is not None:
                return None, err
        elif "chain" in row and "suprole" in row:
            chain = row["chain"]
            if not (isinstance(chain, list) and len(chain) >= 2
                    and all(isinstance(role, str) for role in chain)):
                return None, _error(ValueError(
                    f"{argument}[{i}].chain: expected a list of at least 2 role "
                    f"names, got {chain!r}"))
            try:
                tbox.add_role_chain(chain, row["suprole"])
            except dl.RoleExpressionError as exc:
                return None, _error(exc)
        elif "subrole" in row and "suprole" in row:
            try:
                tbox.add_role_inclusion(row["subrole"], row["suprole"])
            except dl.RoleExpressionError as exc:
                return None, _error(exc)
        elif any(key in row for key in _DL_FILLER_ROLE_ROW_SHAPES):
            key = next(k for k in _DL_FILLER_ROLE_ROW_SHAPES if k in row)
            builder, role_key, _keyword = _DL_FILLER_ROLE_ROW_SHAPES[key]
            if role_key not in row:
                return None, _error(ValueError(
                    f"{argument}[{i}]: a {key!r} row needs {role_key!r} "
                    f"(the role the axiom is about), got {sorted(row)}"))
            filler, err = _parse_dl(row[key], syntax, f"{argument}[{i}].{key}",
                                    datatypes)
            if err is not None:
                return None, err
            try:
                getattr(tbox, builder)(row[role_key], filler)
            except dl.RoleExpressionError as exc:
                return None, _error(exc)
        else:
            key = next((k for k in _DL_ROLE_ROW_SHAPES if k in row), None)
            if key is None:
                return None, _error(ValueError(
                    f"{argument}[{i}]: expected keys 'sub'+'sup', 'equiv', "
                    f"'subrole'+'suprole', 'chain'+'suprole', "
                    f"'domainrole'+'domain', 'rangerole'+'range', "
                    f"'subdata'+'supdata', 'domaindata'+'domain', "
                    f"'rangedata'+'range', 'datatype'+'definition', or one of "
                    f"{sorted(_DL_ROLE_ROW_SHAPES)} / "
                    f"{sorted(_DL_DATA_NAME_ROW_SHAPES)}, got {sorted(row)}"))
            builder, arity = _DL_ROLE_ROW_SHAPES[key]
            value = row[key]
            if arity == "one":
                if not isinstance(value, str):
                    return None, _error(ValueError(
                        f"{argument}[{i}].{key}: expected a role name (str), "
                        f"got {value!r}"))
                roles = [value]
            else:
                if not (isinstance(value, list) and len(value) >= 2
                        and all(isinstance(role, str) for role in value)):
                    return None, _error(ValueError(
                        f"{argument}[{i}].{key}: expected a list of at least 2 "
                        f"role names, got {value!r}"))
                roles = value
            try:
                getattr(tbox, builder)(*roles)
            except dl.RoleExpressionError as exc:
                return None, _error(exc)
    return tbox, None


def _build_dl_abox(concepts, roles, distinct, syntax: str,
                   same=None, negative_roles=None, data=None,
                   negative_data=None, datatypes=()):
    """Build a :class:`~unicode_logic_kit.dl.ABox` from JSON rows.

    ``concepts``: ``[individual, concept_text]`` pairs (``ABox.assert_concept``).
    ``roles``: ``[a, b, role]`` triples (``ABox.assert_role``). ``distinct``:
    ``[a, b]`` pairs (``ABox.assert_distinct`` — the only thing that forces two
    individuals apart, since this reasoner has no unique name assumption; see
    :mod:`unicode_logic_kit.dl.tableau`'s "Qualified number restrictions"
    section). ``same``: ``[a, b]`` pairs (``ABox.assert_same`` — the mirror of
    ``distinct``, decided by node merging). ``negative_roles``: ``[a, b, role]``
    triples (``ABox.assert_negative_role`` — ``¬role(a, b)``). The last two are
    optional; without them the MCP description-logic tools could express a
    strictly smaller class of knowledge bases than the Python API. The same
    holds for ``data`` and ``negative_data``: ``[individual, property, literal]``
    triples (``ABox.assert_data`` / ``assert_negative_data``), the literal being
    Manchester literal text (``"400"^^xsd:integer``, ``"abc"@en``, a bare
    numeral). ``datatypes``: the user-defined datatype names the concept texts
    may mention (see :func:`_dl_datatype_names`).
    ``(abox, None)`` on success, ``(None, error_dict)`` on the first
    failure: a concept TEXT failure is the uniform ``ok=False`` shape
    (argument ``"concepts[i][1]"``); a malformed row shape (a row of the wrong
    length, or an individual, role or property name that is not a string) is
    ``{"error": {...}}``, and so is a role or data property name an ABox
    builder refuses by name (:class:`~unicode_logic_kit.dl.RoleExpressionError`,
    :class:`~unicode_logic_kit.dl.UnsupportedDatatypeError`).
    """
    from .. import dl

    try:
        return _dl_abox_from_rows(concepts, roles, distinct, syntax, same,
                                  negative_roles, data, negative_data, datatypes)
    except (dl.RoleExpressionError, dl.UnsupportedDatatypeError) as exc:
        return None, _error(exc)


def _dl_abox_from_rows(concepts, roles, distinct, syntax, same, negative_roles,
                       data, negative_data, datatypes):
    """The body of :func:`_build_dl_abox`, which adds the one ``try`` around it."""
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
        concept, err = _parse_dl(text, syntax, f"concepts[{i}][1]", datatypes)
        if err is not None:
            return None, err
        abox.assert_concept(individual, concept)
    for i, triple in enumerate(roles or []):
        if not (isinstance(triple, list) and len(triple) == 3
                and all(isinstance(name, str) for name in triple)):
            return None, _error(ValueError(
                f"roles[{i}]: expected [a, b, role] (three strings), got {triple!r}"))
        a, b, role = triple
        abox.assert_role(a, b, role)
    for i, pair in enumerate(distinct or []):
        if not (isinstance(pair, list) and len(pair) == 2
                and all(isinstance(name, str) for name in pair)):
            return None, _error(ValueError(
                f"distinct[{i}]: expected [a, b] (two strings), got {pair!r}"))
        a, b = pair
        abox.assert_distinct(a, b)
    for i, pair in enumerate(same or []):
        if not (isinstance(pair, list) and len(pair) == 2
                and all(isinstance(name, str) for name in pair)):
            return None, _error(ValueError(
                f"same[{i}]: expected [a, b] (two strings), got {pair!r}"))
        a, b = pair
        abox.assert_same(a, b)
    for i, triple in enumerate(negative_roles or []):
        if not (isinstance(triple, list) and len(triple) == 3
                and all(isinstance(name, str) for name in triple)):
            return None, _error(ValueError(
                f"negative_roles[{i}]: expected [a, b, role] (three strings), "
                f"got {triple!r}"))
        a, b, role = triple
        abox.assert_negative_role(a, b, role)
    for field, rows, assert_ in (("data", data, abox.assert_data),
                                 ("negative_data", negative_data,
                                  abox.assert_negative_data)):
        for i, triple in enumerate(rows or []):
            if not (isinstance(triple, list) and len(triple) == 3
                    and isinstance(triple[0], str) and isinstance(triple[1], str)):
                return None, _error(ValueError(
                    f"{field}[{i}]: expected [individual, property, literal], "
                    f"got {triple!r}"))
            individual, prop, text = triple
            value, err = _parse_dl_literal(text, f"{field}[{i}][2]")
            if err is not None:
                return None, err
            assert_(individual, prop, value)
    return abox, None


@_answers_deep_input
def dl_concept_satisfiable(concept: str, tbox: Optional[List[dict]] = None,
                           syntax: str = "alc") -> dict:
    """Is ``concept`` satisfiable with respect to ``tbox`` (the ALCHQ tableau)?

    ``concept``/``tbox`` text and ``syntax`` follow this section's own header
    comment; ``tbox`` rows follow :func:`_build_dl_tbox`.

    Returns ``{"ok": True, "satisfiable": bool, "concept_unicode": str}``.
    """
    from .. import dl

    c, err = _parse_dl(concept, syntax, "concept", _dl_datatype_names(tbox))
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    texts, err = _unicode_texts(c)
    if err is not None:
        return err
    try:
        satisfiable = dl.concept_satisfiable(c, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "satisfiable": satisfiable, "concept_unicode": texts[0]}


@_answers_deep_input
def dl_subsumes(sub: str, sup: str, tbox: Optional[List[dict]] = None,
                syntax: str = "alc") -> dict:
    """Does ``tbox`` entail ``sub ⊑ sup`` (every model puts ``sub`` in ``sup``)?

    Returns ``{"ok": True, "subsumes": bool, "sub_unicode": str, "sup_unicode": str}``.
    """
    from .. import dl

    datatypes = _dl_datatype_names(tbox)
    sub_c, err = _parse_dl(sub, syntax, "sub", datatypes)
    if err is not None:
        return err
    sup_c, err = _parse_dl(sup, syntax, "sup", datatypes)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    texts, err = _unicode_texts(sub_c, sup_c)
    if err is not None:
        return err
    try:
        holds = dl.subsumes(sub_c, sup_c, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "subsumes": holds,
            "sub_unicode": texts[0], "sup_unicode": texts[1]}


@_answers_deep_input
def dl_equivalent(c: str, d: str, tbox: Optional[List[dict]] = None,
                  syntax: str = "alc") -> dict:
    """Does ``tbox`` entail ``c ≡ d`` (mutual subsumption)?

    Returns ``{"ok": True, "equivalent": bool, "c_unicode": str, "d_unicode": str}``.
    """
    from .. import dl

    datatypes = _dl_datatype_names(tbox)
    c_concept, err = _parse_dl(c, syntax, "c", datatypes)
    if err is not None:
        return err
    d_concept, err = _parse_dl(d, syntax, "d", datatypes)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    texts, err = _unicode_texts(c_concept, d_concept)
    if err is not None:
        return err
    try:
        holds = dl.equivalent(c_concept, d_concept, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "equivalent": holds,
            "c_unicode": texts[0], "d_unicode": texts[1]}


@_answers_deep_input
def dl_abox_consistent(concepts: List[List[str]],
                       roles: Optional[List[List[str]]] = None,
                       distinct: Optional[List[List[str]]] = None,
                       tbox: Optional[List[dict]] = None,
                       syntax: str = "alc",
                       same: Optional[List[List[str]]] = None,
                       negative_roles: Optional[List[List[str]]] = None,
                       data: Optional[List[List[str]]] = None,
                       negative_data: Optional[List[List[str]]] = None) -> dict:
    """Is the knowledge base ``(tbox, abox)`` consistent (does it have a model)?

    ``concepts``/``roles``/``distinct``/``same``/``negative_roles``/``data``/
    ``negative_data`` build the ABox — see :func:`_build_dl_abox`; ``tbox``
    follows :func:`_build_dl_tbox`. A knowledge base with DATA assertions or a
    data box is expressible here, but the in-house tableau REFUSES it by name
    (it has no data domain): the reply is then an ``{"error": ...}`` naming the
    refused kinds, never an answer about a weaker knowledge base.

    Returns ``{"ok": True, "consistent": bool}``.
    """
    from .. import dl

    err = _check_dl_syntax(syntax)
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax,
                               same, negative_roles, data, negative_data,
                               _dl_datatype_names(tbox))
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    try:
        consistent = dl.abox_consistent(abox, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "consistent": consistent}


@_answers_deep_input
def dl_instance_check(individual: str, concept: str,
                      concepts: List[List[str]],
                      roles: Optional[List[List[str]]] = None,
                      distinct: Optional[List[List[str]]] = None,
                      tbox: Optional[List[dict]] = None,
                      syntax: str = "alc",
                      same: Optional[List[List[str]]] = None,
                      negative_roles: Optional[List[List[str]]] = None,
                      data: Optional[List[List[str]]] = None,
                      negative_data: Optional[List[List[str]]] = None) -> dict:
    """Does the knowledge base entail ``individual : concept``?

    Open-world (:func:`~unicode_logic_kit.dl.instance_check`'s own contract):
    ``entailed=False`` means "not entailed", never "entailed to be false".
    ``concepts``/``roles``/``distinct``/``tbox`` build the KB exactly like
    :func:`dl_abox_consistent`; ``concept`` is the query, parsed the same way.

    Returns ``{"ok": True, "entailed": bool, "individual": str,
    "concept_unicode": str}``.
    """
    from .. import dl

    datatypes = _dl_datatype_names(tbox)
    query, err = _parse_dl(concept, syntax, "concept", datatypes)
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax,
                               same, negative_roles, data, negative_data,
                               datatypes)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    texts, err = _unicode_texts(query)
    if err is not None:
        return err
    try:
        entailed = dl.instance_check(abox, individual, query, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "entailed": entailed, "individual": individual,
            "concept_unicode": texts[0]}


@_answers_deep_input
def dl_instance_retrieval(concept: str, concepts: List[List[str]],
                          roles: Optional[List[List[str]]] = None,
                          distinct: Optional[List[List[str]]] = None,
                          tbox: Optional[List[dict]] = None,
                          syntax: str = "alc",
                          same: Optional[List[List[str]]] = None,
                          negative_roles: Optional[List[List[str]]] = None,
                          data: Optional[List[List[str]]] = None,
                          negative_data: Optional[List[List[str]]] = None) -> dict:
    """Every ABox individual the knowledge base entails is a ``concept``.

    Sweeps :func:`~unicode_logic_kit.dl.instance_check` over every individual
    named in the ABox — including one that appears only in a role assertion.
    Arguments as :func:`dl_instance_check`.

    Returns ``{"ok": True, "individuals": [str, ...], "concept_unicode": str}``
    (``individuals`` sorted, for a deterministic payload).
    """
    from .. import dl

    datatypes = _dl_datatype_names(tbox)
    query, err = _parse_dl(concept, syntax, "concept", datatypes)
    if err is not None:
        return err
    abox, err = _build_dl_abox(concepts, roles, distinct, syntax,
                               same, negative_roles, data, negative_data,
                               datatypes)
    if err is not None:
        return err
    tb, err = _build_dl_tbox(tbox, syntax)
    if err is not None:
        return err
    texts, err = _unicode_texts(query)
    if err is not None:
        return err
    try:
        individuals = dl.instance_retrieval(abox, query, tb)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True, "individuals": sorted(individuals),
            "concept_unicode": texts[0]}


@_answers_deep_input
def dl_classify(tbox: Optional[List[dict]] = None,
                concepts: Optional[List[str]] = None,
                syntax: str = "alc") -> dict:
    """Classify every named concept of ``tbox`` into a subsumption hierarchy.

    ``tbox`` follows :func:`_build_dl_tbox` (``None``/``[]`` classifies the
    empty TBox — every concept is then its own isolated node). ``concepts``
    is extra concept TEXT to bring names of interest into the vocabulary even
    when they never occur in a ``tbox`` axiom (see
    :func:`~unicode_logic_kit.dl.classify`'s own ``concepts`` parameter) —
    parsed under the same ``syntax``.

    Returns ``{"ok": True, "equivalents": {name: [str, ...]}, "parents":
    {name: [str, ...]}, "children": {name: [str, ...]}, "ancestors": {name:
    [str, ...]}}`` — :class:`~unicode_logic_kit.dl.Classification`'s frozensets
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
    datatypes = _dl_datatype_names(tbox)
    for i, text in enumerate(concepts or []):
        concept, err = _parse_dl(text, syntax, f"concepts[{i}]", datatypes)
        if err is not None:
            return err
        extra.append(concept)
    try:
        result = dl.classify(tb, extra or None)
    except _dl_errors() as exc:
        return _error(exc)
    return {"ok": True,
            "equivalents": {k: sorted(v) for k, v in result.equivalents.items()},
            "parents": {k: sorted(v) for k, v in result.parents.items()},
            "children": {k: sorted(v) for k, v in result.children.items()},
            "ancestors": {k: sorted(v) for k, v in result.ancestors.items()}}


def _role_axiom_payload(axiom) -> dict:
    """``dl.parse_manchester_role_axiom``'s tuple as a JSON payload.

    One function over its THREE tuple shapes, keyed by the TAG and read off the
    reader's own tables (``_BINARY_ROLE_FRAMES`` / ``_FILLER_ROLE_FRAMES`` /
    ``_CHARACTERISTIC_TAGS``), so a shape the reader gains cannot be named
    differently here.

    Until 0.30.0 this branch ended in ``_, role = axiom``, so every shape other
    than ``("subproperty", sub, sup)`` and a characteristic crashed the tool
    with ``ValueError: too many values to unpack`` — an ``InverseOf``,
    ``DisjointWith`` or ``EquivalentTo`` axiom the reader already read
    perfectly well. Deriving the tags means a reader shape with no payload here
    is reported as an error naming itself, not as a crash.
    """
    from ..dl import owl_manchester as _manchester

    pairs = {tag for tag, _spelling in _manchester._BINARY_ROLE_FRAMES.values()}
    fillers = {tag for tag, _spelling in _manchester._FILLER_ROLE_FRAMES.values()}
    characteristics = set(_manchester._CHARACTERISTIC_TAGS.values())
    tag = axiom[0]
    if tag in pairs and len(axiom) == 3:
        return {"ok": True, "kind": tag,
                "sub_role": axiom[1], "super_role": axiom[2]}
    if tag in fillers and len(axiom) == 3:
        texts, err = _unicode_texts(axiom[2])
        if err is not None:
            return err
        return {"ok": True, "kind": tag, "role": axiom[1],
                "concept_unicode": texts[0]}
    if tag in characteristics and len(axiom) == 2:
        return {"ok": True, "kind": tag, "role": axiom[1]}
    return _error(ValueError(
        f"dl_parse_manchester: dl.parse_manchester_role_axiom returned the "
        f"shape {axiom!r}, which this tool has no payload for — add one"))


@_answers_deep_input
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
    :mod:`unicode_logic_kit.dl.tableau`'s "Role hierarchies and transitive
    roles (RBox)").

    Returns, on success: ``{"ok": True, "concept_unicode": str, "manchester":
    str}`` (``kind="concept"``); ``{"ok": True, "kind": "subclass"|
    "equivalent", "sub_unicode": str, "sup_unicode": str}`` (``kind="axiom"``);
    and for ``kind="role_axiom"`` one of three shapes, by the axiom read (see
    :func:`_role_axiom_payload`): ``{"ok": True, "kind": "subproperty"|
    "equivalentproperty"|"inverse"|"disjoint", "sub_role": str, "super_role":
    str}``, ``{"ok": True, "kind": "domain"|"range", "role": str,
    "concept_unicode": str}``, or ``{"ok": True, "kind": "transitive"|…,
    "role": str}`` for a ``Characteristics:`` declaration.
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
        texts, err = _unicode_texts(concept)
        if err is not None:
            return err
        try:
            manchester = dl.to_manchester(concept)
        except ValueError as exc:       # a name parse_manchester could not read back
            return _error(exc)
        return {"ok": True, "concept_unicode": texts[0], "manchester": manchester}
    if kind == "axiom":
        try:
            label, sub, sup = dl.parse_manchester_axiom(text)
        except dl.ManchesterSyntaxError as exc:
            return {"ok": False, "argument": "text",
                    "errors": [{"dialect": "manchester", "message": str(exc)}],
                    "spec_topic": "description-logic"}
        texts, err = _unicode_texts(sub, sup)
        if err is not None:
            return err
        return {"ok": True, "kind": label,
                "sub_unicode": texts[0], "sup_unicode": texts[1]}
    if kind == "role_axiom":
        try:
            axiom = dl.parse_manchester_role_axiom(text)
        except dl.ManchesterSyntaxError as exc:
            return {"ok": False, "argument": "text",
                    "errors": [{"dialect": "manchester", "message": str(exc)}],
                    "spec_topic": "description-logic"}
        return _role_axiom_payload(axiom)
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
            "unicode_logic_kit.mcp needs the MCP SDK: "
            "pip install 'unicode-logic-kit[mcp]' (or: pip install 'mcp>=2.0')"
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
        server.tool()(_registered(fn))
    return server


def main() -> None:
    """Run the server on stdio (the transport MCP clients spawn)."""
    create_server().run("stdio")
