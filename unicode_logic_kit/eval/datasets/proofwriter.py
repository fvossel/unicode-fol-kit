"""Adapter for the ProofWriter dataset (Tafjord, Dalvi Mishra, Clark,
"ProofWriter: Generating Implications, Proofs, and Abductive Statements over
Natural Language", Findings of ACL 2021, arXiv:2012.13048) — local JSONL
only, no network access.

Source and verified schema
---------------------------
The primary distribution named by the paper, https://allenai.org/data/proofwriter,
does NOT serve a metadata page: fetching it returns a bare HTTP 307 redirect
straight to ``proofwriter-dataset-V2020.12.3.zip`` (~214 MB) on
``aristo-data-public.s3.amazonaws.com``, with no separate page describing its
internal JSONL field names, and the current https://allenai.org/data catalog
no longer lists a ProofWriter entry at all (both checked directly,
2026-08-12). Downloading and unpacking a 214 MB archive was out of scope for
schema verification here, so — per this adapter's instructions, which allow
falling back to "the best-documented HF mirror" when the original
distribution's internal structure cannot be confirmed via the rows API — the
schema below was verified instead against
https://huggingface.co/datasets/tasksource/proofwriter (unauthenticated,
11,898+ downloads, the most-used ProofWriter mirror on the Hub), directly via
the Hugging Face ``datasets-server`` ``/first-rows``, ``/statistics``, and
``/search`` APIs across all three of its splits (``train`` — 585,552 rows,
``validation`` — 85,468 rows, ``test`` — 174,476 rows), 2026-08-12.
:func:`load_proofwriter` reads that verified schema, NOT the original
AllenAI ZIP's internal format (unverified here) — see "Honesty" below for
what this means in practice.

Each verified row is a flat JSON object with exactly these keys (confirmed
via the dataset's declared ``dataset_info.features`` and by inspecting many
real fetched rows):

* ``"id"``        — ``str``. NOT a per-row unique id (see "Id resolution"
  below) — it identifies one GENERATED THEORY, and every question asked
  against that theory (2-6 in the fetched sample) repeats the same ``"id"``.
  Its own substructure (e.g. ``"AttNeg-OWA-D0-1778"``) encodes, dash-separated:
  a generation-template family (``AttNeg``/``AttNoneg``/``RelNeg``/``RelNoneg``
  — attribute- or relation-typed facts, with or without negated facts), an
  open/closed-world tag (``OWA`` in every single row observed here — see
  "CWA vs OWA" below), a depth bucket (``D0`` etc., redundant with ``maxD``),
  and a generator seed/index. This adapter does not parse that substring; it
  is preserved verbatim in ``meta["theory_id"]``.
* ``"maxD"``      — ``int``, the maximum proof depth reachable from this
  theory's rule set (0 in every fetched sample row; the dataset overall
  ranges 0-10 per the mirror's column statistics).
* ``"NFact"``     — ``int``, number of atomic facts in ``"theory"``.
* ``"NRule"``     — ``int``, number of conditional rules in ``"theory"``.
* ``"theory"``    — ``str``, ALL of this theory's facts and rules concatenated
  into one string, one sentence per fact/rule, each ending in ``"."`` and
  separated by a single space — e.g. ``"Anne is smart. Dave is round. If
  someone is cold then they are blue."``. Verified: in every fetched row,
  ``NFact + NRule`` equals exactly the number of ``". "``-delimited sentences
  in ``"theory"`` (hand-checked below in the test suite), so this adapter's
  ``nl_premises`` sentence split (see "Field mapping") is not a guess.
* ``"question"``  — ``str``, one NL sentence being asked about (e.g. ``"Dave
  is round."`` or its negation ``"Dave is not round."``).
* ``"answer"``    — ``str``, one of exactly ``{"True", "False", "Unknown"}``
  (confirmed via the mirror's train-split column statistics: 158,805 /
  158,805 / 267,942 rows respectively — no fourth value exists in this
  mirror).
* ``"QDep"``      — ``int``, the depth of proof needed to answer this
  specific question (0 in every "directly stated fact" question observed).
* ``"QLen"``      — ``float`` or ``null``. In every row fetched here, ``null``
  exactly when ``"answer" == "Unknown"`` and ``1.0`` whenever the answer is
  ``"True"``/``"False"`` — an OBSERVED correlation from the sample fetched
  for this verification, not a guarantee re-derived from a spec, so it is
  not relied on by this loader beyond passing the raw value through in
  ``meta``.
* ``"allProofs"`` — ``str``, an opaque proof-forest annotation in the
  dataset's own ``triple``/``rule``-reference notation (e.g. ``"@0: Anne is
  smart.[(triple1)] ..."``), kept verbatim in ``meta`` — this adapter does
  not parse it (it is not FOL, and parsing its internal proof-tree grammar
  is out of scope here).
* ``"config"``    — ``str``, one of exactly 8 values confirmed via the
  mirror's train-split column statistics: ``"depth-0"``, ``"depth-1"``,
  ``"depth-2"``, ``"depth-3"``, ``"depth-3ext"``, ``"depth-3ext-NatLang"``,
  ``"depth-5"``, ``"NatLang"`` (the paper's D0-D5 depth staircase, plus the
  hand-authored "NatLang"/"birds-electricity"-style natural-language subsets
  described in the paper; note ``"depth-4"`` does not appear as a distinct
  ``config`` value in this mirror).

Honesty: what this adapter does NOT give you
----------------------------------------------
* **No FOL annotation exists.** ProofWriter's ``"theory"``/``"question"``
  are natural-language sentences ("If someone is red then they are kind.");
  there is no gold first-order-logic formula anywhere in the source data.
  Accordingly ``fol_premises`` is ALWAYS ``()`` and ``fol_conclusion`` is
  ALWAYS ``None`` for every example this loader yields — never guessed,
  never back-translated. A consequence: :func:`~unicode_logic_kit.eval.datasets.audit_examples`
  run over ProofWriter examples is VACUOUSLY ``ok=True`` for all of them (no
  FOL string means nothing to parse or fail ``check()`` on) — it is not a
  meaningful signal for this dataset and callers should not read "0 defects"
  as "ProofWriter's data is fine", only as "there is nothing here to audit".
* **CWA vs OWA, and why it is NOT classical FOL entailment.** ProofWriter
  was released in TWO reasoning-assumption variants per the paper: **CWA**
  (closed-world assumption — a fact not provable from the theory is assumed
  FALSE, i.e. negation-as-failure) and **OWA** (open-world assumption — a
  fact not provable either way is genuinely ``"Unknown"``, distinct from
  ``"False"``). The verified mirror used here contains **ONLY the OWA
  variant** — every single ``"id"`` in the fetched sample, and a full-text
  search for the substring ``"CWA"`` across the ENTIRE train split, returned
  zero matches (``num_rows_total: 0``, confirmed 2026-08-12) — so this
  adapter's field mapping and every claim above describes OWA data only. The
  presence of the three-valued ``answer`` (``"Unknown"`` as a genuine third
  value, not collapsed into ``"False"``) is itself the observable signature
  of OWA rather than CWA.

  How the two variants relate to classical FOL — stated precisely, because
  a sloppy version of this claim is easy to make and wrong: **CWA is
  ordinary two-valued FOL** — evaluation of the question in ONE canonical
  model, the closed (minimal) model, where exactly the derivable atoms hold
  and everything else is plainly false; there is no third value. **OWA's
  three-way label is the ENTAILMENT split** — ``True`` iff the theory
  entails the question, ``False`` iff it entails its negation, ``Unknown``
  otherwise — and "Unknown" is a statement ABOUT entailment, not an FOL
  truth value inside any model. Both are classical; they answer different
  questions ("true in the closed model?" vs "true in every model?"), and
  the labels visibly diverge exactly where a fact is underdetermined
  (closed model: false; entailment: unknown). For the STRUCTURED route
  below, both are decidable with any registered ATP:
  ``solve_structured_example(..., semantics="owa")`` runs the entailment
  cascade, ``semantics="cwa"`` runs closed-model checking with the ATP as
  the per-atom derivability oracle (exact for the definite, negation-free
  theories; a rule with negation in its body would mean
  negation-as-failure inside the theory and is refused). The FLAT
  tasksource mirror THIS loader reads carries no representations, so for
  it these labels remain data to report, not something this adapter
  recomputes.
* **Only one split's worth of assumption is covered.** This loader's field
  mapping was verified against OWA rows only (see above); if a caller
  obtains genuine CWA-variant ProofWriter data (e.g. from the original
  AllenAI ZIP, unverified here), the row shape is very likely structurally
  identical (same ``id`` substring convention, same field names) but that
  has NOT been independently confirmed by this adapter.
* **``"theory"`` is one blob string, not pre-split sentences.** ``nl_premises``
  below is DERIVED by this adapter (splitting on ``". "``), not a field that
  exists upstream — see "Field mapping".

License
-------
**UNVERIFIED** as of 2026-08-12. No ProofWriter-specific license text could
be confirmed from any live, unauthenticated source: the AllenAI dataset page
is a bare redirect straight to the ZIP with no accompanying license file
reachable without downloading it, the current AllenAI data catalog no longer
lists a ProofWriter entry to check, and the verified HF mirror
(tasksource/proofwriter)'s dataset card carries no ``license`` tag and reads
literally "More Information needed". The sibling AI2 RuleTaker CODE
repository (https://github.com/allenai/ruletaker, whose legacy JSONL example
format ProofWriter's ``theory``/``question`` sentences continue) is
Apache-2.0-licensed, but that governs that repository's CODE, not
ProofWriter's separately-hosted data ZIP, and is not treated here as a
substitute for a verified data license. Treat ProofWriter as all-rights-
reserved research data pending confirmation directly from the paper's
authors or AI2, and do not redistribute this loader's *inputs* (the JSONL
file itself) without resolving that.

Field mapping
--------------
ProofWriter has no premises/conclusion ENTAILMENT structure quite like
FOLIO's (no separate gold "this follows" formula), but its
theory-facts-and-rules / queried-question / True-False-Unknown shape maps
onto :class:`~unicode_logic_kit.eval.datasets.DatasetExample` as an entailment
example nonetheless:

* ``nl_premises`` — ``"theory"`` SPLIT into individual sentences on ``". "``
  (each fragment re-terminated with ``"."`` if the split ate it) by this
  module's :func:`_split_theory_sentences`. This is a LOCAL heuristic of
  this adapter, not part of the verified upstream schema (upstream gives you
  one string) — verified safe against every fetched sample row only insofar
  as none of them contain a sentence-internal period, abbreviation, or
  ellipsis (a synthetic, template-generated corpus, so this holds by
  construction for the OWA rows checked). The RAW, unsplit ``"theory"``
  string is ALSO kept verbatim in ``meta["theory"]`` so nothing is lost to
  the split.
* ``fol_premises`` — ALWAYS ``()`` (no FOL exists; see "Honesty" above).
* ``nl_conclusion`` — ``"question"`` verbatim.
* ``fol_conclusion`` — ALWAYS ``None`` (no FOL exists; see "Honesty" above).
* ``label`` — ``"answer"`` verbatim (``"True"``/``"False"``/``"Unknown"``).
* ``meta`` — every other record key (``maxD``, ``NFact``, ``NRule``, ``QDep``,
  ``QLen``, ``allProofs``, ``config``), PLUS the raw ``"theory"`` string,
  PLUS ``"theory_id"`` (renamed from the record's own ``"id"`` — see "Id
  resolution"), PLUS ``"line_no"``.

Id resolution
--------------
ProofWriter's own ``"id"`` field identifies a GENERATED THEORY, not a single
row — exactly the same shape of problem as FOLIO's ``"story-id"`` (see
``folio.py``'s docstring): several consecutive rows in the verified sample
share one ``"id"`` while asking different questions about the same theory,
so using it directly as this adapter's per-example id would collide. This
loader therefore ALWAYS uses the positional id ``f"proofwriter:{line_no}"``
(0-based line number in the local file) and preserves the original,
non-unique ``"id"`` value verbatim in ``meta["theory_id"]`` for anyone who
wants to group rows back into their source theory.

This module never downloads anything — obtain a local JSONL file yourself
(e.g. by exporting the verified ``tasksource/proofwriter`` split with
``datasets.load_dataset("tasksource/proofwriter", split="train").to_json(path, orient="records", lines=True)``,
or via the HF ``rows``/``first-rows`` API) and pass its local path to
:func:`load_proofwriter`.
"""

import itertools
import json
import re
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, Optional, Tuple, Union

from ...fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, substitute,
)
from ._base import DatasetExample, _register_dataset_info
from . import _proofwriter_proof as _proof

__all__ = [
    "load_proofwriter",
    "load_proofwriter_structured",
    "parse_proofwriter_representation",
    "solve_structured_example",
    "check_gold_proof",
]

_register_dataset_info(
    "proofwriter",
    license=(
        "UNVERIFIED as of 2026-08-12 -- no ProofWriter-specific license text "
        "could be confirmed from any live, unauthenticated source (AllenAI's "
        "dataset page redirects directly to a ZIP with no reachable license "
        "file; the verified HF mirror's dataset card has no license tag); "
        "treat as all-rights-reserved research data pending confirmation "
        "from the paper's authors or AI2 -- see module docstring"
    ),
    source_url="https://huggingface.co/datasets/tasksource/proofwriter",
    citation_hint=(
        "Tafjord, Oyvind, Bhavana Dalvi Mishra, and Peter Clark. \"ProofWriter: "
        "Generating Implications, Proofs, and Abductive Statements over Natural "
        "Language.\" Findings of the Association for Computational Linguistics: "
        "ACL-IJCNLP 2021. arXiv:2012.13048."
    ),
)


def _split_theory_sentences(theory: Optional[str]) -> Tuple[str, ...]:
    """Split a raw ``"theory"`` blob into individual NL fact/rule sentences.

    A LOCAL heuristic of this adapter (see the module docstring's "Field
    mapping" section for why this is safe over the verified sample but is
    not itself part of the upstream schema): splits on the literal
    substring ``". "``, then re-appends a trailing ``"."`` to any fragment
    the split consumed it from (every fragment except possibly the last).
    ``None`` or ``""`` (e.g. a record missing ``"theory"`` entirely) yields
    ``()`` rather than raising or fabricating a one-element tuple of empty
    string.
    """
    if not theory:
        return ()
    sentences = []
    for part in theory.strip().split(". "):
        part = part.strip()
        if not part:
            continue
        if not part.endswith("."):
            part = part + "."
        sentences.append(part)
    return tuple(sentences)


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    theory = record.get("theory")
    question = record.get("question")
    answer = record.get("answer")
    example_id = f"proofwriter:{line_no}"

    # Everything except question/answer stays in meta (including "theory"
    # itself, verbatim -- see module docstring: nl_premises below is a
    # DERIVED split, not a byte-identical copy). The record's own "id" is
    # renamed to "theory_id" here: see "Id resolution" in the module
    # docstring for why it is deliberately NOT used as this example's id.
    meta = {k: v for k, v in record.items() if k not in ("question", "answer")}
    meta["theory_id"] = meta.pop("id", None)
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=_split_theory_sentences(theory),
        fol_premises=(),
        nl_conclusion=question,
        fol_conclusion=None,
        label=answer,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_proofwriter(path: Union[str, Path], *,
                     known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_logic_kit.eval.datasets.DatasetExample` from a
    local ProofWriter JSONL file (verified ``tasksource/proofwriter`` schema
    -- see module docstring).

    Args:
        path: path to a local ``.jsonl`` file — one
            ``{"id", "maxD", "NFact", "NRule", "theory", "question",
            "answer", "QDep", "QLen", "allProofs", "config"}`` object per
            non-blank line (see module docstring for how to produce this
            from the verified HF mirror). NEVER downloaded by this function.
        known_bad_ids: ids (the positional ``f"proofwriter:{line_no}"`` form
            -- see "Id resolution" in the module docstring) whose ``answer``
            is known to be broken (e.g. from a prior human review). Every
            yielded example with a matching id gets ``known_bad=True``.
            Defaults to an empty set.

    Yields:
        One :class:`~unicode_logic_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order. ``fol_premises`` is always
        ``()`` and ``fol_conclusion`` is always ``None`` (ProofWriter has no
        FOL gold annotation -- see the module docstring's "Honesty"
        section). Fields missing from a record (e.g. no ``"theory"``, no
        ``"answer"``) map to ``()``/``None`` rather than raising -- this
        mirrors :mod:`~unicode_logic_kit.eval.datasets.folio`'s defensive
        ``dict.get`` style, documented, not an exception.

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON -- this is
            NOT swallowed; a malformed dataset file is a loud failure, not a
            silently-skipped row.
    """
    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            yield _example_from_record(record, line_no, known_bad_ids)


# --------------------------------------------------------------------------- #
# Structured OWA distribution: deterministic FOL GENERATION from the dataset's
# own triple/rule representations
#
# The AllenAI ProofWriter release (mirrored with all metadata intact at
# https://huggingface.co/datasets/hitachi-nlp/proofwriter_processed_OWA —
# configs depth-0/1/2/3/3ext/5, NatLang, birds-electricity; schema verified
# against real depth-2 rows on 2026-08-12) carries, next to every NL
# sentence, the ORIGINAL RuleTaker-style symbolic representation:
#
#   fact triple:  ("Anne" "is" "white" "+")          [attribute]
#                 ("bear" "chases" "dog" "+")        [relation]
#   rule:         ((("something" "is" "young" "+"))
#                    -> ("something" "is" "white" "+"))
#   question:     ("Charlie" "is" "cold" "-")        [negative polarity]
#
# Unlike the flat tasksource mirror load_proofwriter reads (NL text only —
# no FOL gold, as documented above), these representations admit a
# DETERMINISTIC, rule-based translation to FOL — no LLM, no heuristics on NL
# text. The convention implemented here (the standard reading of RuleTaker
# triples, Clark et al. 2020):
#
#   * an attribute triple (E "is" A pol) becomes A'(e) — predicate = the
#     attribute, capitalised (white → White); entity = a constant in kit
#     casing (Anne → anne, multi-word "bald eagle" → baldEagle);
#   * a relation triple (E V F pol) becomes V'(e, f) (chases → Chases);
#   * polarity "-" (or "~") wraps the atom in ¬;
#   * the placeholder words something/someone/somebody are RULE VARIABLES:
#     every rule quantifies universally over each distinct placeholder it
#     uses — ∀x (Young(x) → White(x)); a rule without placeholders stays a
#     ground implication;
#   * a rule ((c1 … cn) -> d) becomes (c1 ∧ … ∧ cn) → d under those
#     quantifiers.
#
# HONESTY: the resulting fol_premises/fol_conclusion are GENERATED BY THIS
# KIT from the dataset's own symbolic annotations — ProofWriter itself ships
# no FOL strings; meta["fol_generated"] marks every such example and meta
# keeps the verbatim source representations. The OWA labels are the
# classical ENTAILMENT split (True iff premises ⊨ q, False iff premises ⊨
# ¬q, Unknown otherwise) — solve_structured_example(semantics="owa") decides
# exactly that, verified 24/24 on the fixture. The CWA labels are ordinary
# two-valued truth in the CLOSED (minimal) model — plain FOL model checking,
# no third value — and solve_structured_example(semantics="cwa") decides
# that via per-atom derivability with the caller's chosen ATP (see its
# docstring for the exact fragment contract). The verified hitachi-nlp
# mirror ships only OWA data; CWA gold labels live in the original AllenAI
# zip (proofwriter-dataset-V2020.12.3.zip), whose per-question schema is
# identical — the CWA route was verified against it (2026-08-12): first 100
# theories of CWA/depth-2/meta-dev.jsonl = 1078/1078 questions correct
# (29 AttNoneg / 31 AttNeg / 19 RelNoneg / 21 RelNeg; z3 cross-check on the
# definite ones). Several of those theories NEED local stratification:
# their predicate graphs cycle through negation while their ground graphs
# do not — predicate-level stratification would refuse them.
# --------------------------------------------------------------------------- #

_REPR_TOKEN_RE = re.compile(r'\(|\)|->|"[^"]*"')

#: RuleTaker's rule-variable placeholder words (subject/object position of a
#: rule triple). Every DISTINCT placeholder in one rule gets its own
#: universally quantified variable, in order of first appearance: x, y, z.
_PLACEHOLDER_WORDS = ("something", "someone", "somebody")

_KIT_PRED_RE = re.compile(r"[A-Z][a-zA-Z0-9]*\Z")
_KIT_CONST_RE = re.compile(r"[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*\Z")


def _tokenise_representation(rep: str) -> List[str]:
    tokens = _REPR_TOKEN_RE.findall(rep)
    remainder = _REPR_TOKEN_RE.sub("", rep).strip()
    if remainder:
        raise ValueError(
            f"proofwriter: unrecognised material {remainder!r} in "
            f"representation {rep!r}")
    return tokens


def _parse_sexpr(tokens: List[str], pos: int):
    """One S-expression starting at ``pos`` → (parsed, next_pos).

    Strings stay strings (quotes stripped); ``(`` … ``)`` becomes a list;
    ``->`` stays the literal marker token.
    """
    token = tokens[pos]
    if token == "(":
        items = []
        pos += 1
        while pos < len(tokens) and tokens[pos] != ")":
            item, pos = _parse_sexpr(tokens, pos)
            items.append(item)
        if pos >= len(tokens):
            raise ValueError("proofwriter: unbalanced '(' in representation")
        return items, pos + 1
    if token == ")":
        raise ValueError("proofwriter: unbalanced ')' in representation")
    if token == "->":
        return "->", pos + 1
    return token[1:-1], pos + 1          # strip the quotes


def _camel(words: List[str]) -> str:
    return words[0] + "".join(w[0].upper() + w[1:] for w in words[1:] if w)


def _to_predicate_name(word: str) -> str:
    parts = [p for p in re.split(r"[\s\-]+", word.strip()) if p]
    if not parts:
        raise ValueError("proofwriter: empty predicate word")
    joined = _camel(parts)
    name = joined[0].upper() + joined[1:]
    if not _KIT_PRED_RE.match(name):
        raise ValueError(
            f"proofwriter: {word!r} does not map to a legal kit predicate "
            f"(got {name!r})")
    return name


def _to_constant_name(word: str) -> str:
    parts = [p for p in re.split(r"[\s\-]+", word.strip()) if p]
    if not parts:
        raise ValueError("proofwriter: empty entity word")
    joined = _camel(parts)
    name = joined[0].lower() + joined[1:]
    if not _KIT_CONST_RE.match(name):
        raise ValueError(
            f"proofwriter: entity {word!r} does not map to a legal kit "
            f"constant (got {name!r} — single-letter entities would lex as "
            "variables and are refused)")
    return name


def _term_for(word: str, variables: "Dict[str, Variable]") -> Node:
    lowered = word.strip().lower()
    if lowered in _PLACEHOLDER_WORDS:
        if lowered not in variables:
            if len(variables) >= 3:
                raise ValueError(
                    "proofwriter: more than three distinct placeholder "
                    "words in one rule — outside the documented convention")
            variables[lowered] = Variable("xyz"[len(variables)])
        return variables[lowered]
    return Constant(_to_constant_name(word))


def _triple_to_node(parsed, variables: "Dict[str, Variable]") -> Node:
    if (not isinstance(parsed, list) or len(parsed) != 4
            or any(not isinstance(p, str) for p in parsed)):
        raise ValueError(
            f"proofwriter: not a (subject predicate object polarity) triple: "
            f"{parsed!r}")
    subject, predicate, obj, polarity = parsed
    if polarity not in ("+", "-", "~"):
        raise ValueError(f"proofwriter: unknown polarity {polarity!r}")
    if predicate.strip().lower() == "is":
        atom = Atom(_to_predicate_name(obj), (_term_for(subject, variables),))
    else:
        atom = Atom(_to_predicate_name(predicate),
                    (_term_for(subject, variables), _term_for(obj, variables)))
    return Not(atom) if polarity in ("-", "~") else atom


def parse_proofwriter_representation(rep: str) -> Node:
    """One ProofWriter ``representation`` string → a closed kit formula.

    Accepts both shapes the OWA distribution uses: a bare triple (fact or
    question) and a rule ``((cond …) -> conclusion)``. See the comment block
    above for the exact translation convention; every distinct placeholder
    word in a rule is universally quantified, so the result is always closed.

    Raises:
        ValueError: the string is not a well-formed representation, or a
            name in it has no legal kit rendering.
    """
    tokens = _tokenise_representation(rep)
    if not tokens:
        raise ValueError("proofwriter: empty representation")
    parsed, next_pos = _parse_sexpr(tokens, 0)
    if next_pos != len(tokens):
        raise ValueError(
            f"proofwriter: trailing tokens after the representation: {rep!r}")

    variables: "Dict[str, Variable]" = {}
    if isinstance(parsed, list) and len(parsed) == 3 and parsed[1] == "->":
        conditions, _, conclusion = parsed
        if not isinstance(conditions, list) or not conditions:
            raise ValueError(
                f"proofwriter: rule without conditions: {rep!r}")
        cond_nodes = [_triple_to_node(c, variables) for c in conditions]
        body = cond_nodes[0]
        for extra in cond_nodes[1:]:
            body = And(body, extra)
        node: Node = Implies(body, _triple_to_node(conclusion, variables))
        for var in reversed(list(variables.values())):
            node = Quantifier("∀", var, node)
        return node
    return _triple_to_node(parsed, variables)


def _named_entries(section: Optional[dict], prefix: str) -> "List[Tuple[str, dict]]":
    """Non-null ``triple<N>``/``rule<N>``/``Q<N>`` entries in numeric order."""
    if not isinstance(section, dict):
        return []
    entries = []
    for key, value in section.items():
        if value is None or not isinstance(value, dict):
            continue
        match = re.fullmatch(re.escape(prefix) + r"(\d+)", key)
        order = int(match.group(1)) if match else float("inf")
        entries.append((order, key, value))
    entries.sort(key=lambda item: (item[0], item[1]))
    return [(key, value) for _, key, value in entries]


def load_proofwriter_structured(
        path: Union[str, Path], *,
        known_bad_ids: FrozenSet[str] = frozenset(),
        convert_fol: bool = True) -> Iterator[DatasetExample]:
    """Stream ONE example PER QUESTION from a structured-OWA JSONL file.

    Args:
        path: local ``.jsonl`` file with one theory record per line in the
            ``hitachi-nlp/proofwriter_processed_OWA`` schema (``id``,
            ``theory``, ``triples``, ``rules``, ``questions``, …; obtain it
            e.g. via ``load_dataset("hitachi-nlp/proofwriter_processed_OWA",
            "depth-2", split="train").to_json(...)``). NEVER downloaded here.
        known_bad_ids: example ids (``proofwriter:<row id>:<Qn>``) to flag
            ``known_bad=True``.
        convert_fol: with the default ``True``, ``fol_premises`` /
            ``fol_conclusion`` are GENERATED from the record's own symbolic
            representations via :func:`parse_proofwriter_representation`
            (``meta["fol_generated"]`` is set, the verbatim representations
            stay in ``meta``); a record whose representations cannot be
            converted yields its questions with empty FOL fields plus
            ``meta["fol_conversion_error"]``. ``False`` skips generation
            entirely (NL + label only, like :func:`load_proofwriter`).

    Yields:
        One :class:`DatasetExample` per non-null question, in file order and
        numeric question order; ``nl_premises`` are the fact/rule sentence
        texts, ``label`` is the OWA answer verbatim
        (``"True"``/``"False"``/``"Unknown"``). ``meta["proofs"]`` (the
        record's own, unparsed ``question["proofs"]`` string) and
        ``meta["strategy"]`` were already carried verbatim before this
        docstring was written; ``meta["premise_keys"]`` — the source
        record's ``"tripleN"``/``"ruleN"`` keys, parallel to
        ``meta["premise_representations"]`` — is additive, resolving those
        proof references back to a premise index for
        :func:`check_gold_proof`. Parse ``meta["proofs"]`` with
        :func:`~._proofwriter_proof.parse_question_proof` and verify it
        against this module's own forward-chaining fixpoint with
        :func:`check_gold_proof`.

    Raises:
        FileNotFoundError / json.JSONDecodeError: as in the other loaders —
        a missing or corrupt FILE fails loudly; per-record conversion
        problems are recorded per example instead.
    """
    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            row_id = record.get("id", f"pos{line_no}")

            triples = _named_entries(record.get("triples"), "triple")
            rules = _named_entries(record.get("rules"), "rule")
            premise_entries = triples + rules
            nl_premises = tuple(entry.get("text", "")
                                for _, entry in premise_entries)
            premise_reps = tuple(entry.get("representation", "")
                                 for _, entry in premise_entries)
            premise_keys = tuple(key for key, _ in premise_entries)

            fol_premises: "Tuple[str, ...]" = ()
            conversion_error: Optional[str] = None
            if convert_fol:
                try:
                    fol_premises = tuple(
                        parse_proofwriter_representation(rep).to_unicode_str()
                        for rep in premise_reps)
                except ValueError as exc:
                    conversion_error = f"{type(exc).__name__}: {exc}"

            for q_key, question in _named_entries(record.get("questions"), "Q"):
                example_id = f"proofwriter:{row_id}:{q_key}"
                q_rep = question.get("representation", "")
                fol_conclusion: Optional[str] = None
                q_error = conversion_error
                if convert_fol and q_error is None:
                    try:
                        fol_conclusion = parse_proofwriter_representation(
                            q_rep).to_unicode_str()
                    except ValueError as exc:
                        q_error = f"{type(exc).__name__}: {exc}"

                meta = {
                    "row_id": row_id,
                    "question_key": q_key,
                    "theory": record.get("theory"),
                    "premise_representations": list(premise_reps),
                    # Parallel to premise_representations/fol_premises: the
                    # source record's own "tripleN"/"ruleN" keys, in the SAME
                    # order -- added purely so a caller can resolve a
                    # question["proofs"] annotation's "tripleN"/"ruleN"
                    # references back to a premise index (see
                    # check_gold_proof). Every OTHER field here was already
                    # present before that addition; this key is new and
                    # purely additive, nothing existing was removed/renamed.
                    "premise_keys": list(premise_keys),
                    "question_representation": q_rep,
                    "QDep": question.get("QDep"),
                    "strategy": question.get("strategy"),
                    "proofs": question.get("proofs"),
                    "line_no": line_no,
                }
                if convert_fol and q_error is None:
                    meta["fol_generated"] = True
                if q_error is not None:
                    meta["fol_conversion_error"] = q_error

                yield DatasetExample(
                    id=example_id,
                    nl_premises=nl_premises,
                    fol_premises=fol_premises if q_error is None else (),
                    nl_conclusion=question.get("question"),
                    fol_conclusion=fol_conclusion,
                    label=question.get("answer"),
                    known_bad=example_id in known_bad_ids,
                    meta=meta,
                )


def _collect_constants(nodes) -> "List[Constant]":
    """Every distinct :class:`Constant` in ``nodes``, in a fixed name order."""
    by_name: "Dict[str, Constant]" = {}
    for node in nodes:
        for sub in node.walk():
            if isinstance(sub, Constant):
                by_name.setdefault(sub.name, sub)
    return [by_name[name] for name in sorted(by_name)]


def _as_literal(node: Node):
    """``(atom, positive)`` for a literal node, else ``ValueError``."""
    if isinstance(node, Atom):
        return node, True
    if isinstance(node, Not) and isinstance(node.formula, Atom):
        return node.formula, False
    raise ValueError(
        f"proofwriter: {node.to_unicode_str()!r} is not a literal — the CWA "
        "theory fragment is ground literals and (∀-quantified) rules "
        "'literal ∧ … ∧ literal → literal'.")


def _as_rule(premise: Node):
    """Decompose one premise into ``(variables, body_literals, head_literal)``.

    A ground literal comes back with an empty body (a fact). Anything outside
    the fact/rule shape raises ``ValueError``.
    """
    variables: "List[Variable]" = []
    node = premise
    while isinstance(node, Quantifier):
        if node.type not in ("∀", "forall"):
            raise ValueError(
                f"proofwriter: CWA premises must be universally quantified, "
                f"got {node.type!r} in {premise.to_unicode_str()!r}")
        variables.append(node.variable)
        node = node.formula
    if isinstance(node, Implies):
        body: "List[Node]" = []
        stack = [node.left]
        while stack:
            item = stack.pop()
            if isinstance(item, And):
                stack.append(item.right)
                stack.append(item.left)
            else:
                body.append(item)
        body_literals = [_as_literal(b) for b in body]
        head_literal = _as_literal(node.right)
        return variables, body_literals, head_literal
    if variables:
        raise ValueError(
            f"proofwriter: quantified premise without an implication is "
            f"outside the CWA fragment: {premise.to_unicode_str()!r}")
    return [], [], _as_literal(node)


def _ground_rule(rule, constants: "List[Constant]"):
    """One ``(variables, body, head)`` (see :func:`_as_rule`) → its list of
    GROUND ``(body, head)`` instances over ``constants`` (``[]`` if the rule
    is variable-free — a plain ground fact/implication grounds to itself)."""
    variables, body, head = rule
    if not variables:
        return [(body, head)]
    if not constants:
        return []
    groundings = []
    for values in itertools.product(constants, repeat=len(variables)):
        g_body = []
        for atom, positive in body:
            g_atom = atom
            for var, value in zip(variables, values):
                g_atom = substitute(g_atom, var, value)
            g_body.append((g_atom, positive))
        h_atom, h_positive = head
        for var, value in zip(variables, values):
            h_atom = substitute(h_atom, var, value)
        groundings.append((g_body, (h_atom, h_positive)))
    return groundings


def _closed_model(premises: "List[Node]", constants: "List[Constant]", *,
                  record_provenance: bool = False):
    """The theory's closed model, by STRATIFIED forward chaining.

    Returns ``(true_atoms, has_naf)`` — the set of ground-atom keys
    (``to_unicode_str``) true in the perfect model, and whether any rule
    body used negation (i.e. the theory is beyond the definite fragment, so
    membership is NOT classical entailment and must not be cross-checked
    against a classical prover). With ``record_provenance=True`` a THIRD
    element is returned, ``provenance`` (see below); with the default
    ``False`` the return shape is EXACTLY the 2-tuple above, unchanged —
    every existing caller (:func:`solve_structured_example`) is untouched.

    Semantics: negation in a rule body is NEGATION AS FAILURE, evaluated
    stratum by stratum over the GROUND dependency graph — LOCAL
    stratification: a ground atom that is tested negatively is fully
    fixpointed in a strictly LOWER stratum before any ground rule reading
    its absence may fire, which is exactly the perfect-model semantics of
    locally stratified logic programs. Stratifying ground atoms rather than
    predicate symbols is strictly more general and is required in practice:
    real ProofWriter theories contain rules like ``¬Likes(mouse, dog) →
    Likes(dog, rabbit)`` whose predicate graph has a negative self-loop but
    whose ground graph is acyclic. Only a GROUND cycle through negation
    (e.g. ``¬P(a) → P(a)``) has no local stratification (it would need
    well-founded/stable-model semantics) and raises ``ValueError``. A
    negative HEAD (a rule or fact concluding ``¬X``) derives no positive
    atom; it is evaluated once against the COMPLETED perfect model and
    tracked only for the final consistency check — a theory that derives
    some atom both positively and negatively is inconsistent under CWA and
    raises rather than answering arbitrarily.

    ``provenance`` (only computed when ``record_provenance=True``, for
    :func:`check_gold_proof`): ``{signed_key: [(premise_index,
    antecedent_keys), …]}`` — ``signed_key`` is the SIGNED rendering of a
    derived atom (``"Foo(a)"`` for a positive derivation, ``"¬Foo(a)"`` for
    a negative one, via a negative-headed rule or fact — real ProofWriter
    theories have both, see the module's ``check_gold_proof`` docstring);
    each ``premise_index`` is the position, in the ORIGINAL ``premises``
    list, of the fact/rule whose grounding fired; ``antecedent_keys`` is the
    ordered tuple of each required body literal's OWN SIGNED key (bare for a
    positive requirement, ``"¬"``-prefixed for a negation-as-failure one) —
    ``()`` for a fact. Real ProofWriter theories DO use negation-as-failure
    conditions (209 of 2401 real rules fetched from ``hitachi-nlp/
    proofwriter_processed_OWA`` — depths 0/1/2/3/3ext/3ext-NatLang/5/
    NatLang/birds-electricity — have one; ProofWriter's OWN grammar spells
    this ``"~"``, distinct from the ``"-"`` a FACT or rule HEAD uses for a
    flat negative assertion — see :func:`parse_proofwriter_representation`'s
    ``_triple_to_node``), and its own gold ``proofs`` annotation cites an
    EXPLICIT derivation of ``¬X`` for such a condition whenever the theory
    has one (rather than leaving it uncited as bare absence) — signing
    ``antecedent_keys`` is what lets :func:`check_gold_proof` look each one
    up as a recursive ``signed_key`` regardless of polarity. A
    ``signed_key`` can have SEVERAL entries (several grounded rules/facts
    derived it — the "OR-forest" a gold proof may cite any one branch of).
    Signing ``antecedent_keys`` does NOT change ``true_atoms``/``stratum``
    below: NAF satisfaction there is still checked by plain ABSENCE from
    ``true_atoms`` (``(atom.to_unicode_str() in true_atoms) == positive``),
    exactly ProofWriter's own stratified-fixpoint semantics; ``provenance``
    is a side record of what ALSO fired explicitly, not a different
    satisfaction rule.
    """
    parsed = [_as_rule(p) for p in premises]
    has_naf = any(not positive for _, body, _ in parsed
                  for _, positive in body)

    # Ground every rule over the finite constant set, remembering which
    # ORIGINAL premise (index into `premises`) each grounding came from --
    # needed only for `provenance`, but cheap enough to always compute.
    ground_rules: "List[Tuple[list, tuple]]" = []
    origin: "List[int]" = []
    for premise_index, rule in enumerate(parsed):
        for grounding in _ground_rule(rule, constants):
            ground_rules.append(grounding)
            origin.append(premise_index)

    # LOCAL stratification: strata live on GROUND ATOMS. A positive body
    # atom forces its head onto the same-or-higher stratum, a negated one
    # onto a strictly higher stratum. The iteration is Bellman-Ford-like:
    # each atom's stratum is bounded by #atoms on any locally stratifiable
    # program, so non-convergence within #atoms+1 rounds means a ground
    # cycle through negation. Negative-head rules derive nothing and are
    # left out of the graph (they are evaluated against the finished model
    # below).
    stratum: "Dict[str, int]" = {}
    for body, (head_atom, _) in ground_rules:
        stratum.setdefault(head_atom.to_unicode_str(), 0)
        for atom, _ in body:
            stratum.setdefault(atom.to_unicode_str(), 0)
    for _ in range(len(stratum) + 1):
        changed = False
        for body, (head_atom, head_positive) in ground_rules:
            if not head_positive:
                continue
            head_key = head_atom.to_unicode_str()
            for atom, positive in body:
                required = (stratum[atom.to_unicode_str()]
                            + (0 if positive else 1))
                if stratum[head_key] < required:
                    stratum[head_key] = required
                    changed = True
        if not changed:
            break
    else:
        raise ValueError(
            "proofwriter: the CWA theory has a GROUND cycle through negation "
            "(not even locally stratifiable) — its negation-as-failure "
            "semantics is not well-defined by stratified forward chaining; "
            "refusing rather than guessing (well-founded semantics is out of "
            "scope).")

    provenance: "Optional[Dict[str, set]]" = {} if record_provenance else None

    def _record(signed_key: str, gi: int, body) -> None:
        if provenance is None:
            return
        # SIGNED per literal (bare for a positive requirement, "¬"-prefixed
        # for a negation-as-failure one) -- a NAF antecedent's signed key is
        # what a gold proof cites when it names an EXPLICIT negative
        # derivation for it (see check_gold_proof's docstring on why real
        # ProofWriter proofs prefer a constructive ¬X derivation over silent
        # absence whenever one exists).
        ante_keys = tuple(
            atom.to_unicode_str() if positive else Not(atom).to_unicode_str()
            for atom, positive in body)
        provenance.setdefault(signed_key, set()).add((origin[gi], ante_keys))

    true_atoms: set = set()
    negative_atoms: set = set()
    positive_rules = [
        (gi, body, head) for gi, (body, head) in enumerate(ground_rules)
        if head[1]
    ]
    max_stratum = max(
        (stratum[head[0].to_unicode_str()] for _, _, head in positive_rules),
        default=0)
    for level in range(max_stratum + 1):
        level_rules = [
            (gi, body, head) for gi, body, head in positive_rules
            if stratum[head[0].to_unicode_str()] == level
        ]
        changed = True
        while changed:
            changed = False
            for gi, body, (head_atom, _) in level_rules:
                fires = all(
                    (atom.to_unicode_str() in true_atoms) == positive
                    for atom, positive in body
                )
                if not fires:
                    continue
                key = head_atom.to_unicode_str()
                _record(key, gi, body)
                if key not in true_atoms:
                    true_atoms.add(key)
                    changed = True

    # Negative heads read the COMPLETED model (previously they fired at
    # their head's level, silently missing body atoms derived later).
    for gi, (body, (head_atom, head_positive)) in enumerate(ground_rules):
        if head_positive:
            continue
        if all((atom.to_unicode_str() in true_atoms) == positive
               for atom, positive in body):
            negative_atoms.add(head_atom.to_unicode_str())
            _record(Not(head_atom).to_unicode_str(), gi, body)

    contradictions = sorted(true_atoms & negative_atoms)
    if contradictions:
        raise ValueError(
            f"proofwriter: the CWA theory derives {contradictions[0]!r} both "
            "positively and negatively — inconsistent under the closed-world "
            "reading; refusing rather than answering arbitrarily.")
    if record_provenance:
        ordered_provenance = {
            key: sorted(entries) for key, entries in provenance.items()
        }
        return frozenset(true_atoms), has_naf, ordered_provenance
    return frozenset(true_atoms), has_naf


def _cwa_holds(formula: Node, atom_oracle, constants) -> bool:
    """Two-valued truth of ``formula`` in the CLOSED model.

    The closed (minimal) model is represented by its atom valuation:
    ``atom_oracle(atom)`` answers "is this ground atom derivable from the
    premises?" — everything not derivable is FALSE, which is exactly the
    closed-world reading. Connectives are ordinary two-valued FOL on top of
    that valuation, and quantifiers range over the theory's (finite) set of
    constants — plain model checking, not entailment.
    """
    if isinstance(formula, Atom):
        return atom_oracle(formula)
    if isinstance(formula, Not):
        return not _cwa_holds(formula.formula, atom_oracle, constants)
    if isinstance(formula, And):
        return (_cwa_holds(formula.left, atom_oracle, constants)
                and _cwa_holds(formula.right, atom_oracle, constants))
    if isinstance(formula, Or):
        return (_cwa_holds(formula.left, atom_oracle, constants)
                or _cwa_holds(formula.right, atom_oracle, constants))
    if isinstance(formula, Xor):
        return (_cwa_holds(formula.left, atom_oracle, constants)
                != _cwa_holds(formula.right, atom_oracle, constants))
    if isinstance(formula, Implies):
        return ((not _cwa_holds(formula.left, atom_oracle, constants))
                or _cwa_holds(formula.right, atom_oracle, constants))
    if isinstance(formula, Iff):
        return (_cwa_holds(formula.left, atom_oracle, constants)
                == _cwa_holds(formula.right, atom_oracle, constants))
    if isinstance(formula, Quantifier):
        instances = (
            _cwa_holds(substitute(formula.formula, formula.variable, c),
                       atom_oracle, constants)
            for c in constants)
        if formula.type in ("∀", "forall"):
            return all(instances)
        if formula.type in ("∃", "exists"):
            return any(instances)
        raise ValueError(
            f"proofwriter: unknown quantifier {formula.type!r} in a CWA query")
    raise ValueError(
        f"proofwriter: node {type(formula).__name__} is outside the CWA "
        "query fragment (atoms, ¬ ∧ ∨ ⊕ → ↔, ∀/∃ over the constants)")


def solve_structured_example(example: DatasetExample, *,
                             semantics: str = "owa",
                             on_indefinite: str = "label",
                             **prove_kwargs) -> dict:
    """Decide one generated-FOL ProofWriter example against its gold label.

    The prover is the CALLER'S choice: every keyword in ``prove_kwargs`` goes
    verbatim to :func:`unicode_logic_kit.api.prove` — e.g.
    ``backends=["vampire"]`` or ``backends=["z3"], timeout=5000`` — so any
    registered ATP can drive either semantics.

    ``semantics="owa"`` (default) is the open-world three-way cascade over
    ENTAILMENT: premises ⊨ q → ``"True"``; else premises ⊨ ¬q → ``"False"``;
    else ``"Unknown"``. This maps the OWA labels exactly.

    ``on_indefinite`` controls how a NON-DEFINITIVE prover outcome (a
    ``Verdict`` with status ``unknown`` or ``error`` — timeouts, hit bounds,
    honest incompleteness; ``Verdict.is_definitive`` is the exact test) is
    interpreted when the OWA cascade reaches its third arm. The distinction
    it preserves: ``"Unknown"`` can be ESTABLISHED (both directions
    definitively REFUTED — the prover found countermodels both ways, so the
    question is provably underdetermined) or merely DEFAULTED to (some leg
    timed out / gave up — the prover failed to tell).

    - ``"label"`` (default): any not-proved outcome flows into the dataset's
      ``"Unknown"`` label — the pragmatic scoring mode, correct whenever the
      chosen prover is decisive on the fragment (z3 on these ground/Horn
      theories is).
    - ``"abstain"``: ``"Unknown"`` only when BOTH legs are definitively
      REFUTED; if any leg is indefinite, ``predicted`` is ``None`` — so
      evaluation numbers cannot silently credit a prover timeout as a
      correct "Unknown" prediction. The verdict dicts show which leg failed
      and why (``status``/``reason``, e.g. ``timeout``).
    - ``"raise"``: like ``"abstain"``, but an indefinite leg raises
      ``ValueError`` — for pipelines that must not contain holes.

    Under ``semantics="cwa"`` the fixpoint decides every atom, so
    ``on_indefinite`` has no effect there (the cross-check already records,
    and never alarms on, an indefinite prover verdict); the argument is
    still validated.

    ``semantics="cwa"`` is closed-world MODEL CHECKING — ordinary two-valued
    FOL evaluation in the closed model, which is COMPUTED exactly by
    stratified forward chaining over the grounded theory
    (:func:`_closed_model`): a ground atom is true iff it is in the perfect
    model, and negation/connectives/quantifiers in the QUERY are evaluated
    compositionally on top (¬q is true iff q is not in the model; ∀/∃ range
    over the theory's constants). There is no ``"Unknown"``: the result is
    ``"True"`` or ``"False"``. Rules with NEGATED BODY literals are
    supported with their standard negation-as-failure reading via LOCAL
    stratification over the ground dependency graph (the negatively-tested
    ground atom is fully fixpointed in a lower stratum first); only a
    GROUND cycle through negation (no local stratification exists) or a
    theory that derives an atom both positively and negatively
    (inconsistent under CWA) raises ``ValueError``. On
    DEFINITE theories (no negated bodies) the least model coincides with
    classical entailment, so every queried atom is additionally
    CROSS-CHECKED against the caller's chosen ATP — a definitive
    disagreement (prover proves an atom the fixpoint excludes, or refutes
    one it contains) raises a soundness alarm instead of returning either
    answer; an honest prover UNKNOWN is recorded, never alarmed on.

    Returns ``{"predicted": ..., "verdict": ..., "verdict_negated": ...}``;
    under ``"cwa"`` the two verdict slots are ``None`` and every per-atom
    oracle call is recorded in an additional ``"atom_calls"`` list
    (atom, derivable, full verdict dict). Requires an example produced with
    ``convert_fol=True`` and without a recorded conversion error; anything
    else raises ``ValueError``.
    """
    from ... import api

    if semantics not in ("owa", "cwa"):
        raise ValueError(
            f"proofwriter: semantics must be 'owa' or 'cwa', got {semantics!r}")
    if on_indefinite not in ("label", "abstain", "raise"):
        raise ValueError(
            f"proofwriter: on_indefinite must be 'label', 'abstain' or "
            f"'raise', got {on_indefinite!r}")
    if example.meta.get("fol_conversion_error"):
        raise ValueError(
            f"proofwriter: example {example.id} carries a conversion error "
            f"({example.meta['fol_conversion_error']}) — cannot solve it.")
    if example.fol_conclusion is None:
        raise ValueError(
            f"proofwriter: example {example.id} has no generated conclusion "
            "— was it loaded with convert_fol=False?")

    def _parse(text: str) -> Node:
        parsed = api.parse_any(text)
        if not parsed.ok:
            raise ValueError(
                f"proofwriter: example {example.id}: generated formula "
                f"{text!r} does not parse under the kit grammar")
        return parsed.formula

    premises = [_parse(p) for p in example.fol_premises]
    conclusion = _parse(example.fol_conclusion)

    if semantics == "owa":
        verdict = api.prove(conclusion, premises, **prove_kwargs)
        if verdict.status == "proved":
            return {"predicted": "True", "verdict": verdict.to_dict(),
                    "verdict_negated": None}
        negated = api.prove(Not(conclusion), premises, **prove_kwargs)
        if negated.status == "proved":
            predicted: "Optional[str]" = "False"
        elif on_indefinite == "label":
            predicted = "Unknown"
        elif verdict.status == "refuted" and negated.status == "refuted":
            # Underdetermination ESTABLISHED: countermodels exist against
            # both directions — "Unknown" is a definitive answer here, not
            # a fallback, so abstain/raise modes still label it.
            predicted = "Unknown"
        elif on_indefinite == "raise":
            raise ValueError(
                f"proofwriter: example {example.id}: indefinite prover "
                f"outcome (goal: {verdict.status}/{verdict.reason}, negated: "
                f"{negated.status}/{negated.reason}) with "
                "on_indefinite='raise' — the cascade cannot honestly assign "
                "a label.")
        else:                                    # "abstain"
            predicted = None
        return {"predicted": predicted, "verdict": verdict.to_dict(),
                "verdict_negated": negated.to_dict()}

    constants = _collect_constants(premises + [conclusion])
    model, has_naf = _closed_model(premises, constants)
    atom_calls: "List[dict]" = []
    cache: "Dict[str, bool]" = {}

    def atom_oracle(atom: Atom) -> bool:
        key = atom.to_unicode_str()
        if key not in cache:
            in_model = key in model
            record: dict = {"atom": key, "derivable": in_model}
            if not has_naf:
                # Definite theory: least model ⟺ classical entailment, so
                # the caller's ATP serves as an independent cross-check. Only
                # a DEFINITIVE disagreement is a soundness alarm; an honest
                # UNKNOWN (timeout, bound) is recorded, not alarmed on.
                verdict = api.prove(atom, premises, **prove_kwargs)
                record["verdict"] = verdict.to_dict()
                if ((verdict.status == "proved" and not in_model)
                        or (verdict.status == "refuted" and in_model)):
                    raise ValueError(
                        f"proofwriter: soundness alarm on {example.id}: the "
                        f"closed-model fixpoint says {key!r} is "
                        f"{'in' if in_model else 'NOT in'} the least model, "
                        f"but backend {verdict.backend!r} definitively says "
                        "the opposite — on a definite theory these must "
                        "coincide; refusing to answer.")
            cache[key] = in_model
            atom_calls.append(record)
        return cache[key]

    holds = _cwa_holds(conclusion, atom_oracle, constants)
    return {"predicted": "True" if holds else "False",
            "verdict": None, "verdict_negated": None,
            "atom_calls": atom_calls}


# --------------------------------------------------------------------------- #
# check_gold_proof: verify a structured-route example's OWN question["proofs"]
# annotation against the kit's own forward-chaining fixpoint — see
# _proofwriter_proof.py for the annotation grammar this parses.
# --------------------------------------------------------------------------- #

def _negate(node: Node) -> Node:
    """Logical negation WITHOUT double-negating: ``¬X`` → ``X``, else ``¬``."""
    return node.formula if isinstance(node, Not) else Not(node)


#: Every strategy tag observed across 390 real rows / 5452 questions fetched
#: from ``hitachi-nlp/proofwriter_processed_OWA`` (every published config)
#: plus the real AllenAI CWA fixture — see :func:`_target_for_strategy`.
_KNOWN_STRATEGIES = frozenset({
    "proof", "inv-proof", "rconc", "inv-rconc", "random", "inv-random",
})


def _target_for_strategy(conclusion: Node, strategy: "Optional[str]",
                         example_id: str) -> Node:
    """The literal a gold ``proofs`` annotation is ABOUT, given the
    question's own strategy tag.

    ProofWriter's ``"proof"``/``"rconc"``/``"random"`` strategies derive (or
    fail to derive) the question's conclusion EXACTLY as generated —
    whatever polarity the question itself has (a question can be phrased
    negatively, e.g. ``"The rabbit is not round."``, and be settled by
    directly citing a NEGATIVE fact — confirmed in real data: 96 of 1329
    real ``"proof"``-strategy questions fetched here are phrased negatively
    and their proof directly cites a negative-headed fact/rule). The
    ``"inv-*"`` strategies derive the OPPOSITE of the question instead
    (that is what makes the label ``"False"``/the "inv-" failure a
    not-entailed positive/negative pair) — never a double negation, since
    the question's own polarity is stripped, not added to.
    """
    if strategy not in _KNOWN_STRATEGIES:
        raise ValueError(
            f"proofwriter: example {example_id} has meta['strategy'] "
            f"{strategy!r}, not one of {sorted(_KNOWN_STRATEGIES)} — cannot "
            "tell which literal the gold proof is about")
    if strategy.startswith("inv-"):
        return _negate(conclusion)
    return conclusion


def _rule_body_holds(rule_node: Node, target_key: str,
                     true_atoms: "FrozenSet[str]",
                     constants: "List[Constant]") -> "Optional[bool]":
    """Is there SOME grounding of ``rule_node`` whose HEAD is ``target_key``
    (a SIGNED atom key — see :func:`_closed_model`'s ``provenance``) with a
    satisfied body?

    This is an EXISTENTIAL question over every grounding whose head matches
    (a rule with a variable that occurs in the body but not the head, or
    otherwise sharing its head atom across more than one grounding, can have
    several) — all matching groundings are checked, not just the first one
    ``itertools.product`` happens to visit, so a non-firing grounding never
    masks a later firing one.

    Returns ``None`` when no grounding of ``rule_node`` concludes
    ``target_key`` at all (the rule cannot structurally produce this atom,
    e.g. under any constant substitution its head is a different
    predicate/arguments) — a gold "deepest failure" witness naming such a
    rule cannot be confirmed or refuted this way, which
    :func:`check_gold_proof` surfaces rather than silently treating as
    either outcome.
    """
    rule = _as_rule(rule_node)
    matches = []
    for g_body, (g_head_atom, g_head_positive) in _ground_rule(rule, constants):
        signed = (g_head_atom.to_unicode_str() if g_head_positive
                  else Not(g_head_atom).to_unicode_str())
        if signed != target_key:
            continue
        matches.append(g_body)
    if not matches:
        return None
    return any(all((atom.to_unicode_str() in true_atoms) == positive
                    for atom, positive in g_body)
               for g_body in matches)


def _match_gold_derivation(node: "_proof.ProofNode", target_key: str,
                           key_to_index: "Dict[str, int]",
                           provenance: "Dict[str, list]") -> bool:
    """Does ``node`` (a :class:`~._proofwriter_proof.Leaf` /
    :class:`~._proofwriter_proof.Naf` / :class:`~._proofwriter_proof.Apply` /
    :class:`~._proofwriter_proof.Or`) explain how the fixpoint's OWN
    ``provenance`` derived ``target_key``?

    A :class:`~._proofwriter_proof.Leaf` matches iff the fact it cites fired
    with no antecedents for exactly ``target_key``; a
    :class:`~._proofwriter_proof.Naf` matches iff ``target_key`` is a
    NEGATIVE requirement (starts with ``"¬"``) whose bare positive form has
    NO provenance entry at all — genuine absence, matching negation-as-
    failure with no explicit ``¬X`` derivation to cite (see
    :class:`~._proofwriter_proof.Naf`); an :class:`~._proofwriter_proof.Apply`
    matches iff SOME provenance entry for ``target_key`` used the SAME rule
    with the SAME antecedent count, each antecedent recursively matching the
    corresponding gold sub-term (in order — see :func:`_closed_model`'s
    ``provenance`` docstring on why body order is preserved and safe to rely
    on positionally); an :class:`~._proofwriter_proof.Or` matches iff ANY
    alternative does (the OR-forest offers several valid supports —
    matching any one is enough).
    """
    if isinstance(node, _proof.Leaf):
        index = key_to_index.get(node.ref)
        if index is None:
            raise ValueError(
                f"proofwriter: gold proof cites unknown fact reference "
                f"{node.ref!r} — not among this example's premise_keys")
        return (index, ()) in provenance.get(target_key, ())
    if isinstance(node, _proof.Naf):
        if not target_key.startswith("¬"):
            raise ValueError(
                f"proofwriter: gold proof cites NAF (negation-as-failure) "
                f"for {target_key!r}, which is not itself a negative "
                "requirement — outside the documented grammar (NAF only "
                "ever justifies a '~'-polarity body condition)")
        return target_key[1:] not in provenance
    if isinstance(node, _proof.Or):
        return any(_match_gold_derivation(alt, target_key, key_to_index,
                                          provenance)
                   for alt in node.alts)
    if isinstance(node, _proof.Apply):
        index = key_to_index.get(node.rule)
        if index is None:
            raise ValueError(
                f"proofwriter: gold proof cites unknown rule reference "
                f"{node.rule!r} — not among this example's premise_keys")
        parts = node.args.parts
        for origin_index, ante_keys in provenance.get(target_key, ()):
            if origin_index != index or len(ante_keys) != len(parts):
                continue
            if all(_match_gold_derivation(sub, ante_keys[i], key_to_index,
                                          provenance)
                   for i, sub in enumerate(parts)):
                return True
        return False
    raise ValueError(
        f"proofwriter: gold proof node {type(node).__name__} is not a "
        "derivation node (Leaf/Naf/Apply/Or) — a FailWitness at this "
        "position is handled separately by check_gold_proof, never "
        "recursed into")


def check_gold_proof(example: DatasetExample) -> dict:
    """Verify a structured-route example's gold ``question["proofs"]``
    against the kit's OWN forward-chaining fixpoint (:func:`_closed_model`
    with ``record_provenance=True``) — a genuine "same derivation" check,
    because ProofWriter's own generator and this fixpoint are both doing
    forward chaining over the SAME ground theory (see the module docstring's
    CWA section). Unlike :func:`solve_structured_example`, no ATP is
    invoked — the whole point is a SECOND, independent route to the same
    ground theory's derivable atoms, so this takes no ``prove_kwargs``.
    Requires an ``example`` produced by :func:`load_proofwriter_structured`
    with ``convert_fol=True`` (so ``meta["premise_keys"]``/
    ``meta["proofs"]``/``meta["strategy"]`` and the generated FOL are all
    present) and without a recorded conversion error.

    Known, narrow disagreement (report, do not repair — see this module's
    "Independent verification" contract): a real rule body's ``"~"``
    (negation-as-failure) condition and a fact/rule head's ``"-"`` (strong
    negation) both lower to the SAME kit ``Not()`` in the generated FOL (see
    :func:`parse_proofwriter_representation`'s ``_triple_to_node`` —
    pre-existing, unrelated to this function), so when a ``"~"`` condition
    is genuinely UNDETERMINED under ProofWriter's own open-world reading
    (never asserted true OR false) rather than absent-under-closed-world,
    :func:`_closed_model`'s NAF-as-absence semantics (pre-existing,
    unrelated to this function, verified 1078/1078 against genuinely
    CWA-labelled data) can let a rule fire that ProofWriter's own OWA-
    consistent annotation says should not. Confirmed on 7 of 4550
    checkable real questions fetched here (0.15%) — every one traced to a
    rule using ``"~"``; :func:`check_gold_proof` correctly reports these as
    ``ok=False`` rather than silently agreeing, which is the intended
    behaviour, not a bug in the parser or this checker.

    Two shapes, per :mod:`._proofwriter_proof`'s grammar:

    * A DERIVATION (``strategy`` ``"proof"``/``"inv-proof"``/``"rconc"``/
      ``"random"``/``"inv-rconc"``/``"inv-random"`` whose ``proofs`` parses
      to a :class:`~._proofwriter_proof.Leaf`/:class:`~._proofwriter_proof.Apply`/
      :class:`~._proofwriter_proof.Or`): the target literal (see
      :func:`_target_for_strategy`) must be among the atoms the fixpoint's
      own provenance says were derived by exactly that named chain of
      facts/rules (:func:`_match_gold_derivation`).
    * A :class:`~._proofwriter_proof.FailWitness` (``"Unknown"`` answers):
      confirms the target literal is genuinely NOT derivable (absent from
      ``provenance``), and — when the witness names a first candidate rule
      (``rule_chain[0]``) — that THAT rule's own grounding for this target
      has an unsatisfied body in the fixpoint's COMPLETED perfect model
      (:func:`_rule_body_holds`). ``true_atoms`` IS the theory's perfect
      model already (:func:`_closed_model` fully stratifies before
      returning), so this is the exact ground truth regardless of whether
      the rule's own body has a negation-as-failure condition — there is no
      "which round" ambiguity to approximate. **Explicitly NOT verified**:
      deeper links of a multi-rule failure chain (``rule_chain[1:]`` — real
      witnesses go up to 5 links deep, see
      :class:`~._proofwriter_proof.FailWitness`); only the first, named
      "could this have produced the target" candidate is checked.

    Returns a dict with ``"kind"`` (``"derivation"`` or ``"fail_witness"``),
    ``"ok"`` (bool), ``"atom"`` (the target's signed key) and ``"gold"``
    (the parsed :data:`~._proofwriter_proof.ProofNode`); a
    ``"fail_witness"`` result additionally carries ``"derivable"`` and
    ``"rule_body_holds"`` (``None`` when ``rule_chain`` is empty or its
    first rule cannot structurally conclude the target atom).

    Raises:
        ValueError: the example is missing generated FOL, its
            ``meta["proofs"]``/``meta["premise_keys"]``/``meta["strategy"]``
            (i.e. it was not produced by :func:`load_proofwriter_structured`
            with ``convert_fol=True``), the generated conclusion is not a
            (possibly negated) atom, or the gold annotation cites a
            ``tripleN``/``ruleN`` reference outside this example's own
            premises — never silently ignored or guessed at.
    """
    from ... import api

    if example.meta.get("fol_conversion_error"):
        raise ValueError(
            f"proofwriter: example {example.id} carries a conversion error "
            f"({example.meta['fol_conversion_error']}) — cannot check its "
            "proof.")
    if example.fol_conclusion is None:
        raise ValueError(
            f"proofwriter: example {example.id} has no generated conclusion "
            "— was it loaded with convert_fol=False?")
    proofs_text = example.meta.get("proofs")
    if not proofs_text:
        raise ValueError(
            f"proofwriter: example {example.id} has no recorded "
            "meta['proofs'] annotation to check.")
    premise_keys = example.meta.get("premise_keys")
    if not premise_keys:
        raise ValueError(
            f"proofwriter: example {example.id} has no meta['premise_keys'] "
            "— only load_proofwriter_structured's output names its "
            "triples/rules.")

    def _parse(text: str) -> Node:
        parsed = api.parse_any(text)
        if not parsed.ok:
            raise ValueError(
                f"proofwriter: example {example.id}: generated formula "
                f"{text!r} does not parse under the kit grammar")
        return parsed.formula

    premises = [_parse(p) for p in example.fol_premises]
    conclusion = _parse(example.fol_conclusion)
    target = _target_for_strategy(conclusion, example.meta.get("strategy"),
                                  example.id)
    target_atom = target.formula if isinstance(target, Not) else target
    if not isinstance(target_atom, Atom):
        raise ValueError(
            f"proofwriter: example {example.id}: target "
            f"{target.to_unicode_str()!r} is not a (possibly negated) atom "
            "— cannot check its proof against a ground fixpoint")
    target_key = target.to_unicode_str()

    constants = _collect_constants(premises + [conclusion])
    true_atoms, _has_naf, provenance = _closed_model(
        premises, constants, record_provenance=True)
    key_to_index = {key: i for i, key in enumerate(premise_keys)}
    gold = _proof.parse_question_proof(proofs_text)

    if isinstance(gold, _proof.FailWitness):
        derivable = target_key in provenance
        rule_body_holds: "Optional[bool]" = None
        if gold.rule_chain:
            rule_ref = gold.rule_chain[0]
            rule_index = key_to_index.get(rule_ref)
            if rule_index is None:
                raise ValueError(
                    f"proofwriter: gold failure witness cites unknown rule "
                    f"reference {rule_ref!r} — not among this example's "
                    "premise_keys")
            rule_body_holds = _rule_body_holds(
                premises[rule_index], target_key, true_atoms, constants)
        ok = (not derivable) and (rule_body_holds is not True)
        return {"kind": "fail_witness", "ok": ok, "atom": target_key,
                "gold": gold, "derivable": derivable,
                "rule_body_holds": rule_body_holds}

    ok = _match_gold_derivation(gold, target_key, key_to_index, provenance)
    return {"kind": "derivation", "ok": ok, "atom": target_key, "gold": gold}
