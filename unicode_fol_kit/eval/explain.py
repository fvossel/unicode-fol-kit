"""Plain-English rendering of a countermodel — the "why did this fail" gloss.

A countermodel proves *invalidity* by exhibiting a concrete structure, but a
raw :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`, a raw
:class:`~unicode_fol_kit.semantics.tarski.Structure`, or a Z3 assignment dict
is opaque to anyone who is not already reading this codebase.
:func:`explain_countermodel` turns any of those into a short, deterministic
English paragraph a human (or an LLM judge) can read directly.

Four input shapes are accepted — the ones that actually occur, either built by
hand/by a semantic search, or produced by the :mod:`unicode_fol_kit.atp.protocol`
Verdict layer as ``Verdict.countermodel`` / ``CountermodelResult.model``:

* :class:`~unicode_fol_kit.semantics.kripke.KripkeModel` — a possible-worlds
  countermodel. Reported: the number of worlds, the edges of every named
  accessibility relation, and the atoms true at each world. If ``formula`` is
  supplied and can actually be evaluated at world 0
  (:func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`), a closing
  sentence names whether it fails there — see the honesty note below.
* :class:`~unicode_fol_kit.semantics.tarski.Structure` — a finite first-order
  countermodel. Reported: the domain size and its elements, the denotation of
  every constant, and the extension of every predicate and function symbol.
* a bare ``dict`` with no ``"kind"`` key — a Z3-style assignment
  (``{name: value}``, exactly the shape ``Z3Backend.decide`` puts in
  ``Verdict.countermodel["assignment"]``). Reported: every assignment,
  enumerated.
* a **witness dict** carrying a ``"kind"`` key — the shape the Verdict layer
  actually stores at ``Verdict.countermodel`` / ``CountermodelResult.model``:
  ``{"kind": "z3_model", "assignment": {...}}`` (routed to the same Z3
  explanation as the bare-dict case above), or ``{"kind": "kripke" |
  "finite_structure" | "nitpick" | ..., "repr": "<python repr string>"}``.
  The repr-only shapes carry no structured data — only a Python ``repr()`` (or,
  for Isabelle's nitpick, its own textual countermodel) — so they are framed as
  an unparsed witness rather than reformatted as if they were structured; doing
  otherwise would mean inventing structure that was never actually recovered.

Honesty note (the same discipline the rest of the kit applies to proof search):
this function only ever states what it *computed*. The world-0 "fails" sentence
for a Kripke model is added only when ``satisfies_modal`` actually returns
``False`` — never inferred. Evaluation failures are treated as "not evaluable"
and the sentence is silently omitted rather than guessed: a
:class:`NotImplementedError` (the modal evaluator's own signal for an
out-of-fragment node, e.g. a quantifier, a fuzzy or lambda node) as well as a
:class:`ValueError` / :class:`KeyError` (a hybrid nominal with no assignment,
an unbound variable, a model with no object domains) all count, since none of
them yield a truth value to report.

Determinism: every enumeration (worlds, relation edges, atoms, domain
elements, constants, predicate/function extensions, Z3 assignments) is sorted
before rendering — falling back to a ``(type name, str value)`` key when the
raw values are not mutually orderable (e.g. mixed int/str worlds) — so calling
this function twice on the same input always returns byte-identical output.

Output shape: 2-6 short English sentences, plain text (no Markdown, no
line-art), joined with single spaces. ``max_sentences`` caps the sentence
count; content beyond the cap is dropped in the priority order documented on
each ``_explain_*`` helper below (never reordered, so raising the cap never
changes which sentences appear first — only how many spill over).

:func:`explain_proof` is the same idea for the other side of a
:class:`~unicode_fol_kit.atp.protocol.Verdict`: a proof of *validity* instead
of a countermodel of invalidity. See its own docstring for the shapes it
accepts.
"""

from itertools import product
from typing import Any, Dict, Iterable, List, Optional, Tuple

from ..atp.tableau import TableauProof
from ..atp.tstp import TstpDerivation
from ..atp.twee_entailment import TweeProof
from ..fol.nodes import Node
from ..semantics.kripke import KripkeModel, satisfies_modal
from ..semantics.tarski import Structure

__all__ = ["explain_countermodel", "explain_proof"]

#: Exceptions that mean "this evaluation attempt yielded no truth value" —
#: caught around the optional world-0 formula check so the missing sentence is
#: skipped instead of the whole explanation crashing. NotImplementedError is
#: satisfies_modal's own signal for an out-of-fragment node (quantifier, fuzzy,
#: lambda); ValueError/KeyError cover a hybrid nominal with no assignment, an
#: unknown quantifier type, or object quantifiers over a model without domains
#: — all genuine "not evaluable here", never a reason to guess a truth value.
_NOT_EVALUABLE = (NotImplementedError, ValueError, KeyError)

#: Cap on how many tuples a single predicate/function-extension sentence lists
#: verbatim before it switches to "... and N more" — keeps one enormous
#: extension from silently eating the whole sentence budget.
_TUPLE_LIST_LIMIT = 8

#: Cap on |domain|**arity before a callable function interpretation is
#: enumerated by brute-force calling — protects against paying an unbounded
#: number of calls (and their possible side effects) just to describe one.
_MAX_FUNCTION_ENUMERATION = 64


# ---------------------------------------------------------------------------
# Small deterministic-formatting helpers shared by every branch
# ---------------------------------------------------------------------------

def _s(value: Any) -> str:
    """Render ``value`` as a single-line string (collapses embedded newlines).

    Used for every value that ends up inside a sentence, including opaque
    ``repr()`` strings from a witness dict, so a stray newline in someone's
    ``__repr__`` can never break the "no line-art" output contract.
    """
    return str(value).replace("\r\n", " ").replace("\n", " ").replace("\r", " ")


def _safe_sorted(items: Iterable[Any]) -> List[Any]:
    """Sort ``items``, falling back to a ``(type name, str)`` key if unorderable.

    Kripke worlds and structure domain elements are typed as "any hashable
    value", so a mixed-type collection (e.g. some int worlds, some str worlds)
    can raise ``TypeError`` from a direct ``sorted()`` call. The fallback key
    is still total and deterministic — it just does not claim a "natural"
    ordering across incomparable types, only a reproducible one.
    """
    items = list(items)
    try:
        return sorted(items)
    except TypeError:
        return sorted(items, key=lambda x: (type(x).__name__, str(x)))


def _count_word(n: int, noun: str) -> str:
    """``"1 world"`` / ``"3 worlds"`` — regular pluralisation by appending 's'.

    Every noun this module counts with (world, edge, individual, assignment)
    pluralises regularly, so no irregular-plural table is needed.
    """
    return f"{n} {noun}" if n == 1 else f"{n} {noun}s"


def _format_tuple(value: Any) -> str:
    """Render an argument tuple as ``"(a, b)"``, or a bare value as-is."""
    if isinstance(value, tuple):
        return "(" + ", ".join(_s(e) for e in value) + ")"
    return _s(value)


def _format_tuple_list(tuples: List[Any], limit: int = _TUPLE_LIST_LIMIT) -> str:
    """Join formatted tuples with commas, truncating with an "and N more" tail.

    "entry"/"entries" is an irregular plural, so this is spelled out directly
    rather than routed through :func:`_count_word` (which only handles regular
    ``+s`` nouns).
    """
    shown = tuples[:limit]
    text = ", ".join(_format_tuple(t) for t in shown)
    remaining = len(tuples) - len(shown)
    if remaining == 1:
        text += ", and 1 more entry"
    elif remaining > 1:
        text += f", and {remaining} more entries"
    return text


# ---------------------------------------------------------------------------
# KripkeModel branch
# ---------------------------------------------------------------------------

def _explain_kripke(model: KripkeModel, formula: Optional[Node],
                    max_sentences: int) -> str:
    """Explain a possible-worlds countermodel.

    Sentence priority (highest first, so raising ``max_sentences`` only ever
    reveals more, never reorders what is already shown):

    1. World count.
    2. One sentence per named relation family with at least one edge (sorted
       by relation name), or a single "no accessibility edges" sentence if
       every relation is empty.
    3. One sentence per world (sorted) naming the atoms true there.
    4. If ``formula`` is given and ``satisfies_modal(formula, model, 0)``
       actually evaluates to ``False``, the fixed sentence
       "At world 0 the formula fails." — omitted (not guessed) whenever the
       evaluation is not evaluable at all (see ``_NOT_EVALUABLE``) or returns
       ``True``.
    """
    worlds = _safe_sorted(model.worlds)
    sentences: List[str] = [
        f"The countermodel has {_count_word(len(worlds), 'possible world')}."
    ]

    relation_sentences: List[str] = []
    for name in sorted(model.relations):
        edges = _safe_sorted(model.relations[name])
        if not edges:
            continue
        edges_str = ", ".join(f"{_s(a)} → {_s(b)}" for a, b in edges)
        relation_sentences.append(
            f'The "{name}" relation has {_count_word(len(edges), "edge")}: {edges_str}.'
        )
    if not relation_sentences:
        relation_sentences = ["There are no accessibility edges between worlds."]
    sentences += relation_sentences

    for w in worlds:
        atoms = sorted(model.atoms_true_at(w))
        if atoms:
            noun = "atom" if len(atoms) == 1 else "atoms"
            verb = "is" if len(atoms) == 1 else "are"
            sentences.append(
                f"At world {_s(w)}, the {noun} {', '.join(atoms)} {verb} true."
            )
        else:
            sentences.append(f"At world {_s(w)}, no atoms are true.")

    if formula is not None:
        try:
            value = satisfies_modal(formula, model, 0)
        except _NOT_EVALUABLE:
            value = None
        if value is False:
            sentences.append("At world 0 the formula fails.")

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Structure branch
# ---------------------------------------------------------------------------

def _resolve_function_mapping(interp: Any, domain: List[Any], arity: int
                              ) -> Optional[Dict[Tuple[Any, ...], Any]]:
    """Return ``{arg_tuple: value}`` for a function interpretation, or ``None``.

    ``None`` means "not enumerated" — either the interpretation is a callable
    over a domain too large to brute-force (see
    ``_MAX_FUNCTION_ENUMERATION``), or calling it raised. Both are reported
    honestly as "not enumerated" rather than silently omitted or guessed.
    """
    if isinstance(interp, dict):
        return dict(interp)
    if callable(interp):
        if len(domain) ** arity > _MAX_FUNCTION_ENUMERATION:
            return None
        mapping: Dict[Tuple[Any, ...], Any] = {}
        try:
            for args in product(domain, repeat=arity):
                mapping[args] = interp(*args)
        except Exception:
            return None
        return mapping
    return None


def _explain_structure(structure: Structure, max_sentences: int) -> str:
    """Explain a finite first-order countermodel.

    Sentence priority: domain size and elements; the denotation of every
    constant (one combined sentence); then one sentence per predicate and one
    per function (both sorted by ``(name, arity)``), each stating its
    extension.
    """
    domain = _safe_sorted(structure.domain)
    sentences: List[str] = [
        f"The domain has {_count_word(len(domain), 'individual')}: "
        f"{', '.join(_s(d) for d in domain)}."
    ]

    if structure.constants:
        parts = [f"{name} denotes {_s(structure.constants[name])}"
                 for name in sorted(structure.constants)]
        label = "constant" if len(parts) == 1 else "constants"
        sentences.append(f"The {label} {'; '.join(parts)}.")

    for key in sorted(structure.predicates):
        name, arity = key
        extension = structure.predicates[key]
        if arity == 0:
            truth = "true" if bool(extension) else "false"
            sentences.append(f"The nullary predicate {name} is {truth}.")
            continue
        tuples = _safe_sorted(extension)
        if not tuples:
            sentences.append(f"The predicate {name}/{arity} holds for no tuples.")
        else:
            sentences.append(
                f"The predicate {name}/{arity} holds for: {_format_tuple_list(tuples)}."
            )

    for key in sorted(structure.functions):
        name, arity = key
        mapping = _resolve_function_mapping(structure.functions[key], domain, arity)
        if mapping is None:
            sentences.append(
                f"The function {name}/{arity} is defined procedurally; "
                "its extension was not enumerated."
            )
        elif not mapping:
            sentences.append(f"The function {name}/{arity} has no defined values.")
        else:
            items = _safe_sorted(mapping.items())
            pairs = ", ".join(f"{_format_tuple(k)} → {_s(v)}" for k, v in items)
            sentences.append(f"The function {name}/{arity} maps {pairs}.")

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Z3-assignment branch (bare dict, or the "assignment" payload of a z3_model
# witness dict)
# ---------------------------------------------------------------------------

def _explain_z3_assignment(assignment: Dict[str, Any], max_sentences: int) -> str:
    """Explain a Z3-style ``{name: value}`` assignment."""
    if not assignment:
        return "Z3 produced a model, but it recorded no variable assignments."
    items = sorted(assignment.items(), key=lambda kv: str(kv[0]))
    assigned_str = ", ".join(f"{_s(k)} := {_s(v)}" for k, v in items)
    sentences = [
        f"Z3 found a model with {_count_word(len(items), 'assignment')}.",
        f"Under the assignment {assigned_str}, the two sides differ.",
    ]
    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Repr-only witness branch (Verdict-layer dicts carrying no structured payload)
# ---------------------------------------------------------------------------

def _explain_repr_witness(kind: Optional[str], repr_value: Any,
                          max_sentences: int) -> str:
    """Frame an opaque ``repr()`` string as an explicitly-unstructured witness.

    Deliberately does NOT attempt to parse or reformat ``repr_value`` — it is
    presented verbatim inside an explanatory sentence so the reader can see
    exactly, and only, what was actually recovered.
    """
    label = kind if kind else "unlabelled"
    sentences = [
        f'This countermodel was reported as a "{label}" witness carrying only '
        "its Python repr, not a structured payload.",
        f"The repr reads: {_s(repr_value)}",
    ]
    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def explain_countermodel(model: Any, formula: Optional[Node] = None, *,
                         max_sentences: int = 6) -> str:
    """Render a countermodel as 2-6 short, deterministic English sentences.

    Args:
        model: the countermodel to explain. One of:

            - a :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`;
            - a :class:`~unicode_fol_kit.semantics.tarski.Structure`;
            - a bare Z3-style assignment ``dict`` (``{name: value}``, no
              ``"kind"`` key — the shape of ``Verdict.countermodel["assignment"]``);
            - a Verdict-layer witness ``dict`` carrying a ``"kind"`` key:
              ``{"kind": "z3_model", "assignment": {...}}`` (routed to the same
              handling as the bare-dict case), or ``{"kind": ..., "repr": "..."}``
              (any other kind — ``"kripke"``, ``"finite_structure"``,
              ``"nitpick"``, or a future one — framed as an unparsed witness).
        formula: only consulted for a ``KripkeModel``, and only to decide
            whether to append the fixed sentence "At world 0 the formula
            fails." — see the module docstring's honesty note. Ignored for
            every other ``model`` shape.
        max_sentences: upper bound on the number of sentences returned (at
            least 1 is enforced). Content beyond the cap is dropped, not
            summarised — see each ``_explain_*`` helper for the priority order
            that decides what survives.

    Returns:
        A plain-text string: sentences separated by single spaces, no
        Markdown, no embedded newlines. Calling this twice on the same
        arguments always returns the identical string (see the module
        docstring's determinism note).

    Raises:
        ValueError: ``model`` is a witness ``dict`` whose ``"kind"`` is
            recognised as ``"z3_model"`` but has no usable ``"assignment"``
            sub-dict, and it also carries no ``"repr"`` fallback — i.e. there
            is nothing in it to explain.
        TypeError: ``model`` is not one of the four accepted shapes.
    """
    max_sentences = max(1, max_sentences)

    if isinstance(model, KripkeModel):
        return _explain_kripke(model, formula, max_sentences)

    if isinstance(model, Structure):
        return _explain_structure(model, max_sentences)

    if isinstance(model, dict):
        kind = model.get("kind")
        if kind is None:
            return _explain_z3_assignment(model, max_sentences)
        if kind == "z3_model":
            assignment = model.get("assignment")
            if isinstance(assignment, dict):
                return _explain_z3_assignment(assignment, max_sentences)
        if "repr" in model:
            return _explain_repr_witness(kind, model["repr"], max_sentences)
        raise ValueError(
            f"explain_countermodel: witness dict has kind={kind!r} but neither "
            "a usable 'assignment' dict (for kind='z3_model') nor a 'repr' "
            f"fallback to explain (keys present: {sorted(model)})."
        )

    raise TypeError(
        f"explain_countermodel: unsupported model type {type(model).__name__} — "
        "expected a KripkeModel, a Structure, a Z3 assignment dict, or a "
        "Verdict-layer witness dict with a 'kind' key."
    )


# ---------------------------------------------------------------------------
# explain_proof — the validity-side counterpart of explain_countermodel
# ---------------------------------------------------------------------------
#
# Five proof shapes actually reach ``Verdict.proof`` today (verified by
# grepping every ``proof=`` assignment in ``unicode_fol_kit/atp/``):
#
# * :class:`~unicode_fol_kit.atp.tableau.TableauProof` — ``TableauBackend``.
# * :class:`~unicode_fol_kit.atp.tstp.TstpDerivation` — ``VampireBackend`` and
#   ``EProverBackend`` (same shape, one renderer covers both).
# * :class:`~unicode_fol_kit.atp.twee_entailment.TweeProof` — ``TweeBackend``.
# * ``{"kind": "z3_unsat_core", "core": [...]}`` — ``Z3Backend``.
# * ``{"kind": "cvc5_alethe", "text": ..., "unsat_core": [...]}`` —
#   :class:`~unicode_fol_kit.atp.cvc5_backend.Cvc5Backend`.
#
# The first three also round-trip through ``.to_dict()`` (the shape
# ``Verdict.proof`` actually carries once a verdict has crossed the
# process-pool boundary — see ``atp.portfolio._verdict_from_dict``); the last
# two are ALWAYS plain dicts, since no richer dataclass wraps them. Every
# renderer below therefore accepts both the typed instance and its dict via
# the ``_field``/``_node_str`` helpers, and the five key sets are disjoint (a
# ``"kind"`` key picks the two Z3/cvc5 shapes; among the rest, only
# ``TableauProof`` carries ``"root_formulas"``/``"closures"``, only
# ``TweeProof`` carries ``"axioms"``/``"lemmas"``/``"goal"``, and a bare
# ``{"steps"}`` is ``TstpDerivation``) — see :func:`explain_proof`'s dispatch.
#
# Fitch ``Proof``/``Line``/``Justification`` chains (``atp.fitch_search``) are
# deliberately NOT covered: no ``ProverBackend`` currently attaches one to
# ``Verdict.proof``, so there is no live caller through the eval/atp protocol
# layer to explain today — a natural follow-up once/if one is registered.

def _field(obj: Any, key: str) -> Any:
    """Read ``key`` from ``obj``, whether it is a proof dataclass instance or
    the matching ``to_dict()``-shaped plain dict — both share field names, so
    this is the one place that bridges "typed object" and "Verdict.proof
    dict" for every renderer below."""
    return obj[key] if isinstance(obj, dict) else getattr(obj, key)


def _node_str(value: Any) -> str:
    """Render a formula field as Unicode text — ``value`` is a :class:`Node`
    when the caller passed typed proof objects, or a ``Node.to_dict()`` dict
    when it passed the plain ``Verdict.proof`` dict."""
    if isinstance(value, Node):
        return value.to_unicode_str()
    if isinstance(value, dict):
        return Node.from_dict(value).to_unicode_str()
    raise TypeError(
        f"explain_proof: expected a Node or a Node.to_dict() dict, got "
        f"{type(value).__name__}"
    )


# ---------------------------------------------------------------------------
# TableauProof branch
# ---------------------------------------------------------------------------

def _explain_tableau(proof: Any, max_sentences: int) -> str:
    """Explain a tableau refutation.

    Sentence priority (highest first):

    1. Step count.
    2. A sorted (by rule name) histogram of rule applications — omitted if
       there are no steps (a tableau that closes at the root needs none).
    3. Closed-branch count (``len(closures)``).
    4. One sentence per closure, sorted by ``leaf_id``, naming the two
       closing literals — or, for a self-closing branch (``literal`` is ⊥,
       ``complement`` is ``None`` per :class:`TableauClosure`'s own
       docstring), stating that directly rather than inventing a complement.
    """
    steps = list(_field(proof, "steps"))
    closures = list(_field(proof, "closures"))

    sentences: List[str] = [
        f"The tableau proof has {_count_word(len(steps), 'step')}."
    ]

    histogram: Dict[str, int] = {}
    for step in steps:
        rule = _field(step, "rule")
        histogram[rule] = histogram.get(rule, 0) + 1
    if histogram:
        parts = [f"{rule} ({count})" for rule, count in sorted(histogram.items())]
        sentences.append(f"Rule usage: {', '.join(parts)}.")

    branch_word = "closed branch" if len(closures) == 1 else "closed branches"
    sentences.append(f"The proof has {len(closures)} {branch_word}.")

    for closure in sorted(closures, key=lambda c: _field(c, "leaf_id")):
        leaf_id = _field(closure, "leaf_id")
        literal = _node_str(_field(closure, "literal"))
        complement = _field(closure, "complement")
        if complement is None:
            sentences.append(f"Branch closing at node {leaf_id} closes directly on {literal}.")
        else:
            sentences.append(
                f"Branch closing at node {leaf_id} closes {literal} against "
                f"{_node_str(complement)}."
            )

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# TstpDerivation branch (Vampire and E — same shape, same renderer)
# ---------------------------------------------------------------------------

def _explain_tstp(proof: Any, max_sentences: int) -> str:
    """Explain a TSTP derivation DAG.

    Sentence priority (highest first):

    1. Step count.
    2. The sorted set of roles present (``axiom``, ``negated_conjecture``, …).
    3. The final step's rule (or, if it names none, that it is an
       unjustified leaf) together with its ancestor trace: a backward
       breadth-first walk of the parent DAG rooted at the final step, listed
       layer by layer — so a multi-level derivation names every ancestor
       reached from the last step, not just one arbitrarily-chosen path.
       A cited parent name absent from this derivation's own steps (e.g. an
       external ``file(...)`` source never itself recorded) is left
       unexpanded rather than guessed at.
    """
    steps = list(_field(proof, "steps"))
    if not steps:
        raise ValueError("explain_proof: TstpDerivation has no steps to explain.")

    sentences: List[str] = [f"The derivation has {_count_word(len(steps), 'step')}."]

    roles = sorted({_field(s, "role") for s in steps})
    sentences.append(f"Roles present: {', '.join(roles)}.")

    by_name = {_field(s, "name"): s for s in steps}
    final = steps[-1]
    final_name = _field(final, "name")
    final_rule = _field(final, "rule")

    if final_rule is None:
        sentences.append(
            f"The final step {final_name} is a leaf with no inference rule recorded."
        )
    else:
        seen = {final_name}
        order: List[str] = []
        frontier = list(_field(final, "parents"))
        while frontier:
            next_frontier: List[str] = []
            for name in frontier:
                if name in seen:
                    continue
                seen.add(name)
                order.append(name)
                parent_step = by_name.get(name)
                if parent_step is not None:
                    next_frontier.extend(_field(parent_step, "parents"))
            frontier = next_frontier
        if order:
            sentences.append(
                f"The final step {final_name} applies {final_rule}, tracing "
                f"back through {', '.join(order)}."
            )
        else:
            sentences.append(
                f"The final step {final_name} applies {final_rule} with no "
                "recorded parents."
            )

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# TweeProof branch
# ---------------------------------------------------------------------------

def _format_twee_citation(citation: Any) -> str:
    """Render one ``{ by axiom N (name) [R->L] }`` / ``{ by lemma N [R->L] }``
    citation as ``"axiom N (name)"`` / ``"lemma N"``, with an " R->L" suffix
    when the citation applies its equation right-to-left."""
    kind = _field(citation, "kind")
    number = _field(citation, "number")
    name = _field(citation, "name")
    text = f"{kind} {number}" + (f" ({name})" if name else "")
    if _field(citation, "reversed"):
        text += " R->L"
    return text


def _explain_twee(proof: Any, max_sentences: int) -> str:
    """Explain a Twee equational proof.

    Sentence priority (highest first):

    1. Axiom and lemma counts.
    2. The goal's own equation, by name.
    3. The goal's rewrite chain, term by term.
    4. The chain's citations, in step order — or an explicit "no citations"
       sentence for the (degenerate, single-term) chain that has none.
    """
    axioms = list(_field(proof, "axioms"))
    lemmas = list(_field(proof, "lemmas"))
    goal = _field(proof, "goal")

    sentences: List[str] = [
        f"The proof uses {_count_word(len(axioms), 'axiom')} and "
        f"{_count_word(len(lemmas), 'lemma')}."
    ]

    goal_name = _field(goal, "name")
    equation = _field(goal, "equation")
    sentences.append(
        f"The goal ({goal_name}) states "
        f"{_node_str(_field(equation, 'lhs'))} = {_node_str(_field(equation, 'rhs'))}."
    )

    chain = _field(goal, "chain")
    terms = [_node_str(t) for t in _field(chain, "terms")]
    sentences.append(f"It rewrites {' → '.join(terms)}.")

    citations = list(_field(chain, "citations"))
    if citations:
        cite_strs = [_format_twee_citation(c) for c in citations]
        sentences.append(f"Citations: {', '.join(cite_strs)}.")
    else:
        sentences.append("No citations are recorded for this chain.")

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Z3Backend's unsat-core proof dict
# ---------------------------------------------------------------------------

def _explain_z3_unsat_core(proof: Dict[str, Any], max_sentences: int) -> str:
    """Explain ``{"kind": "z3_unsat_core", "core": [...]}``.

    ``core`` is a sound but not necessarily minimal unsat core (see
    ``Z3Backend.decide``'s own comment) — reported as exactly that, every
    tracked name listed in the order Z3/the backend already sorted them.
    """
    core = list(proof.get("core") or [])
    if not core:
        return "Z3 refutes the goal via an empty unsat core."
    sentences = [
        f"Z3 refutes the goal via an unsat core of "
        f"{_count_word(len(core), 'tracked term')}: {', '.join(_s(c) for c in core)}."
    ]
    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# CVC5Backend's Alethe proof dict
# ---------------------------------------------------------------------------

def _explain_cvc5_alethe(proof: Dict[str, Any], max_sentences: int) -> str:
    """Explain ``{"kind": "cvc5_alethe", "text": ..., "unsat_core": [...]}``.

    ``text`` (the Alethe proof, best-effort — see ``Cvc5Backend.decide``'s own
    comment) is summarised by its non-blank line count rather than quoted in
    full; ``unsat_core`` is the same "sound, not necessarily minimal" shape as
    Z3's. Either can be empty/``None`` without this being an error — both are
    reported honestly rather than guessed at.
    """
    text = proof.get("text")
    core = list(proof.get("unsat_core") or [])

    sentences: List[str] = []
    if text:
        line_count = len([ln for ln in text.splitlines() if ln.strip()])
        sentences.append(
            f"cvc5 refutes the goal with an Alethe proof of "
            f"{_count_word(line_count, 'line')}."
        )
    else:
        sentences.append("cvc5 refutes the goal; no Alethe proof text was recorded.")

    if core:
        sentences.append(
            f"Its unsat core cites {_count_word(len(core), 'term')}: "
            f"{', '.join(_s(c) for c in core)}."
        )
    else:
        sentences.append("Its unsat core is empty.")

    return " ".join(sentences[:max_sentences])


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def explain_proof(proof: Any, *, max_sentences: int = 6) -> str:
    """Render a proof as short, deterministic English sentences.

    The validity-side counterpart of :func:`explain_countermodel`: where that
    function explains why a formula is *not* valid (a witnessing structure),
    this one explains why it *is* (a proof search's own record of how it
    closed) — see the module docstring for the honesty/determinism
    discipline both share.

    Args:
        proof: the proof to explain. One of:

            - a :class:`~unicode_fol_kit.atp.tableau.TableauProof` (or its
              ``.to_dict()``) — from ``TableauBackend``;
            - a :class:`~unicode_fol_kit.atp.tstp.TstpDerivation` (or its
              ``.to_dict()``) — from ``VampireBackend``/``EProverBackend``;
            - a :class:`~unicode_fol_kit.atp.twee_entailment.TweeProof` (or
              its ``.to_dict()``) — from ``TweeBackend``;
            - ``{"kind": "z3_unsat_core", "core": [...]}`` — from
              ``Z3Backend``;
            - ``{"kind": "cvc5_alethe", "text": ..., "unsat_core": [...]}`` —
              from ``Cvc5Backend``.

            See the module-level comment above this section for how the five
            shapes are told apart unambiguously.
        max_sentences: upper bound on the number of sentences returned (at
            least 1 is enforced). Content beyond the cap is dropped, not
            summarised — see each ``_explain_*`` helper for the priority
            order that decides what survives.

    Returns:
        A plain-text string: sentences separated by single spaces, no
        Markdown, no embedded newlines (every value rendered into a sentence
        is either a :meth:`Node.to_unicode_str` result or a Python string
        already free of embedded newlines by construction). Calling this
        twice on the same argument always returns the identical string.

    Raises:
        ValueError: ``proof`` is a :class:`TstpDerivation` (or its dict) with
            no steps, or a dict carrying a ``"kind"`` this function does not
            recognise, or a dict whose keys match none of the five accepted
            shapes.
        TypeError: ``proof`` is not one of the five accepted shapes at all.
    """
    max_sentences = max(1, max_sentences)

    if isinstance(proof, TableauProof):
        return _explain_tableau(proof, max_sentences)
    if isinstance(proof, TstpDerivation):
        return _explain_tstp(proof, max_sentences)
    if isinstance(proof, TweeProof):
        return _explain_twee(proof, max_sentences)

    if isinstance(proof, dict):
        keys = set(proof)
        if "kind" in proof:
            kind = proof["kind"]
            if kind == "z3_unsat_core":
                return _explain_z3_unsat_core(proof, max_sentences)
            if kind == "cvc5_alethe":
                return _explain_cvc5_alethe(proof, max_sentences)
            raise ValueError(
                f"explain_proof: unrecognised proof dict kind={kind!r} — "
                "expected 'z3_unsat_core' or 'cvc5_alethe' "
                f"(keys present: {sorted(keys)})."
            )
        if {"root_formulas", "steps", "closures"} <= keys:
            return _explain_tableau(proof, max_sentences)
        if keys == {"steps"}:
            return _explain_tstp(proof, max_sentences)
        if {"axioms", "lemmas", "goal"} <= keys:
            return _explain_twee(proof, max_sentences)
        raise ValueError(
            "explain_proof: unrecognised proof dict shape — expected a "
            "TableauProof ({'root_formulas','steps','closures'}), a "
            "TstpDerivation ({'steps'}), a TweeProof "
            "({'axioms','lemmas','goal'}), or a 'kind'-tagged Verdict-layer "
            f"dict (keys present: {sorted(keys)})."
        )

    raise TypeError(
        f"explain_proof: unsupported proof type {type(proof).__name__} — "
        "expected a TableauProof, TstpDerivation, TweeProof, or one of the "
        "'kind'-tagged Verdict-layer proof dicts (z3_unsat_core, cvc5_alethe)."
    )
