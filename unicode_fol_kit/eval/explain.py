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
"""

from itertools import product
from typing import Any, Dict, Iterable, List, Optional, Tuple

from ..fol.nodes import Node
from ..semantics.kripke import KripkeModel, satisfies_modal
from ..semantics.tarski import Structure

__all__ = ["explain_countermodel"]

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
