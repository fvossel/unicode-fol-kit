"""Adapter for the ProverQA dataset (Qi et al., "Large Language Models Meet
Symbolic Provers for Logical Reasoning Evaluation", ICLR 2025; dataset built
by the ProverGen framework) — local JSONL only, no network access.

Source and verified schema
---------------------------
Source verified 2026-08-12 directly against
https://huggingface.co/datasets/opendatalab/ProverQA (repo file listing via
``https://huggingface.co/api/datasets/opendatalab/ProverQA``, record schema
via the raw files fetched from
``https://huggingface.co/datasets/opendatalab/ProverQA/resolve/main/<path>``,
cross-checked against the field descriptions and JSON example in the
repository's own ``README.md``). Code for the generation pipeline (not
consulted for this loader, provided for context only):
https://github.com/opendatalab/ProverGen.

The repository has exactly four data files, in TWO INCOMPATIBLE shapes:

* ``dev/easy.json``, ``dev/medium.json``, ``dev/hard.json`` — the paper's
  1,500-instance evaluation benchmark (500 per difficulty tier: easy = 1-2
  reasoning steps, medium = 3-5, hard = 6-9), each a JSON ARRAY of flat
  objects. Verified by downloading and inspecting all 1,500 rows: every
  single row has EXACTLY these 8 keys, no more, no fewer —

  * ``"id"``            — ``int``, 0-based, unique WITHIN one tier file
    (0..499 in each of the three files) but NOT globally unique — the same
    id appears in all three tiers. A caller loading more than one tier must
    pass a distinguishing ``tier`` to :func:`load_proverqa` (see below) or
    the resulting ids collide.
  * ``"options"``        — ``list[str]``, always exactly 3 entries in every
    verified row: ``["A) True", "B) False", "C) Uncertain"]`` verbatim
    (letter-and-text order never varies across the 1,500 rows checked).
  * ``"answer"``         — ``str``, one of ``"A"``/``"B"``/``"C"``; verified
    for all 1,500 rows that ``options[ord(answer) - ord("A")]`` starts with
    ``f"{answer})"`` — the letter always indexes its own option correctly.
  * ``"question"``       — ``str``, the FULL interrogative prompt, e.g.
    ``"Based on the above information, is the following statement true,
    false, or uncertain? Brecken has never experienced heartbreak."`` —
    UNLIKE FOLIO's ``conclusion`` field, this is NOT a bare declarative
    sentence; the bare statement is not separately provided upstream, and
    this adapter does not attempt to extract it with a regex heuristic (that
    would be an invented field, not a verified one).
  * ``"reasoning"``      — ``str``, a free-text chain-of-thought trace.
  * ``"context"``        — ``str``, the natural-language premises,
    concatenated. Verified equal to ``" ".join(nl2fol.keys())`` for 1,497 of
    the 1,500 rows; the 3 exceptions (e.g. ``dev/easy.json`` id 361) have a
    premise sentence repeated VERBATIM TWICE in ``context`` but only once in
    ``nl2fol`` — ``nl2fol`` is a JSON object keyed by sentence text, so a
    literal duplicate premise silently collapses to one entry. This is an
    upstream data quirk (verified present in the raw file), not introduced
    by this adapter; it means ``fol_premises`` can have fewer entries than
    ``context`` has sentences for a handful of rows.
  * ``"nl2fol"``         — ``dict[str, str]``, NL premise sentence -> its
    gold FOL translation, insertion-ordered (Python/JSON preserve object key
    order, and ``dict.keys()``/``dict.values()`` iterate in matched,
    corresponding order for the same dict) — this is the exact
    ``nl_premises``/``fol_premises`` pairing this adapter uses.
  * ``"conclusion_fol"`` — ``str``, the gold FOL for the statement embedded
    in ``question``.

* ``train/provergen-5000.json`` — the paper's 5,000-instance fine-tuning
  split, a JSON array of flat objects. Verified by downloading and
  inspecting all 5,000 rows: every row has EXACTLY 4 keys —
  ``"system"``/``"instruction"``/``"input"``/``"output"``, an
  instruction-tuning prompt/response pair (the context, question, and
  options are embedded as free NATURAL-LANGUAGE TEXT inside ``instruction``,
  and the gold reasoning/answer letter as free text inside ``output``, as a
  JSON-in-a-string). It carries **NO** structured ``id``/``nl2fol``/
  ``conclusion_fol``/``answer``/``options`` fields at all — no FOL
  annotation of any kind is recoverable from this file without re-parsing
  free text. **This loader does NOT support the train split** — only
  ``dev/easy.json``/``dev/medium.json``/``dev/hard.json`` carry the
  structured FOL fields :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
  needs.

CRITICAL notation finding (parse rate is 0%, verified, not a bug)
-------------------------------------------------------------------
Every one of the 17,342 real FOL strings in the three ``dev/*.json`` files
(every ``nl2fol`` value plus every ``conclusion_fol``, across all 1,500 rows)
was run through :func:`unicode_fol_kit.api.parse_any` as part of verifying
this adapter. **0 of 17,342 parsed** under any dialect. The cause is a
NOTATION mismatch, not a data-quality defect in ProverQA: ProverQA's gold
FOL uses lower-case ``snake_case`` predicate identifiers with underscores
(e.g. ``has_experienced_heartbreak``) and Capitalized proper-noun constants
(e.g. ``Brecken``) — the OPPOSITE convention from this kit's own grammar
(``unicode_fol_kit/fol/grammars/terminals.lark``: ``PREDICATE`` must start
uppercase with no underscore, e.g. ``Cat``; the constant/function ``NAME``
terminal must start lowercase with no underscore, e.g. ``tom`` — the
convention FOLIO's and MALLS's gold data already happen to follow, which is
WHY those two adapters' fixtures mostly parse and this one's does not).
ProverQA's own README states its FOL was "validated through automated
symbolic provers (Prover9)" — a different tool with a different accepted
surface syntax than this kit's parser.

This adapter resolves the mismatch with a DEDICATED IMPORT-TIME GRAMMAR
rather than a lexical rewrite: :data:`_PROVERQA_GRAMMAR` parses the dataset's
own notation (operators verified against the real corpus), and the resulting
tree is converted into kit nodes with identifiers renamed into the kit's
convention (:class:`_NameConverter` — injective per namespace, constants
that would become variables refused; see the dialect comment block above the
grammar). With the default ``convert_fol=True``, ``fol_premises`` /
``fol_conclusion`` therefore hold KIT-notation strings that parse under
``api.parse_any``, while ``meta`` keeps the verbatim upstream strings
(``original_fol_premises``/``original_fol_conclusion``) and the
changed-names mapping (``fol_name_mapping``) — the gold data remains fully
recoverable and every rename is on the record. ``convert_fol=False``
restores the raw pass-through, whose 0% kit-parse rate is pinned by
``tests/test_datasets_proverqa.py``. :func:`solve_example` then decides a
converted example end-to-end (premises ⊨ conclusion → ``"A"``, premises ⊨
¬conclusion → ``"B"``, else ``"C"``) against the gold ``answer``.

Also observed, and left as-is (not fixed): ``dev/easy.json`` row ``id=7``
uses the predicate ``resolves_conflict_peacefully`` (singular "conflict") in
one ``nl2fol`` rule but ``resolves_conflicts_peacefully`` (plural
"conflicts") in ``conclusion_fol`` — an internal predicate-name
inconsistency verified present in the raw upstream file itself, not
introduced by this adapter. It is exactly the kind of defect
:func:`~unicode_fol_kit.eval.datasets.audit_examples` exists to surface (as
an ``arity_conflict``/mismatched-signature symptom) IF the formulas parsed
at all — here it is masked by the notation mismatch above, since neither
formula parses in the first place.

Upstream distribution format and this loader
-----------------------------------------------
Each ``dev/<tier>.json`` file is a JSON ARRAY (like MALLS's upstream
distribution), NOT JSONL. This loader, like
:func:`~unicode_fol_kit.eval.datasets.folio.load_folio` and
:func:`~unicode_fol_kit.eval.datasets.malls.load_malls`, reads local JSONL
(one JSON object per line) for a uniform, streaming-friendly adapter surface
across this subpackage — convert an upstream ``dev/<tier>.json`` file to
JSONL first (e.g. ``jq -c '.[]' dev/easy.json > proverqa_easy.jsonl``) before
calling :func:`load_proverqa`.

Because the tier (easy/medium/hard) is which FILE a row came from, not a
field inside the row, :func:`load_proverqa` takes an optional ``tier``
keyword purely so the loader can (a) namespace ids so multiple tiers can be
loaded into one corpus without id collisions (see the ``"id"`` bullet
above), and (b) record the tier in ``meta``. It is caller-supplied, not
inferred from the file content — passing the wrong ``tier`` for a given file
is a caller error this loader cannot detect.

Field mapping onto :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
(a deliberate design choice for the fields the source has no direct
equivalent for, exactly like :mod:`~unicode_fol_kit.eval.datasets.malls`
documents its own mapping choices):

* ``id``: ``f"proverqa:{tier}:{record['id']}"`` when ``tier`` is given,
  else ``f"proverqa:{record['id']}"`` (see the id-collision note above).
  Falls back to a positional ``f"proverqa:{tier or 'untiered'}:pos{line_no}"``
  ONLY if the record has no ``"id"`` key at all (defensive; never observed
  in verified real data — every one of the 1,500 rows has it).
* ``nl_premises`` / ``fol_premises``: ``tuple(nl2fol.keys())`` /
  ``tuple(nl2fol.values())`` — see the ``"nl2fol"`` bullet above for why
  this pairing is safe. ``()`` if ``"nl2fol"`` is absent or not a mapping.
* ``nl_conclusion``: the verbatim ``"question"`` string (the interrogative
  prompt, NOT a bare declarative — see the ``"question"`` bullet above).
* ``fol_conclusion``: the verbatim ``"conclusion_fol"`` string.
* ``label``: the verbatim ``"answer"`` letter (``"A"``/``"B"``/``"C"``) —
  kept as the dataset's own raw vocabulary rather than resolved to
  ``"True"``/``"False"``/``"Uncertain"`` text, so nothing is synthesised
  that is not literally the ``"answer"`` field; a caller who wants the
  semantic text can resolve it themselves from ``meta["options"]``.
* ``meta``: every other record key verbatim (``"options"``, ``"context"``,
  ``"reasoning"``, and any future/unrecognised key), plus ``"line_no"`` and
  (when given) ``"tier"``.

License
-------
**UNSPECIFIED** by the authors — verified against both the Hugging Face
dataset card's metadata (``cardData`` has no ``license`` key at all) and the
README's own "License and Ethics" section, which states only that the
INPUT SOURCES used to build the dataset comply with their own licenses
("MIT for names, WordNet for keywords") — that is a statement about the
dataset's INGREDIENTS, not a license grant for the ProverQA data itself. No
CC/MIT/Apache/etc. license is declared for the dataset artifact. Treat as
all-rights-reserved / contact the authors before any redistribution beyond
the kind of small local research fixture this module's own test fixture is.
This loader itself never downloads or redistributes ProverQA data — it only
reads a LOCAL file the caller already obtained.

Citation (from the repository's ``README.md``)::

    @inproceedings{qi2025large,
      title={Large Language Models Meet Symbolic Provers for Logical
             Reasoning Evaluation},
      author={Chengwen Qi and Ren Ma and Bowen Li and He Du and
              Binyuan Hui and Jinwang Wu and Yuanjun Laili and Conghui He},
      booktitle={The Thirteenth International Conference on Learning
                 Representations},
      year={2025},
      url={https://openreview.net/forum?id=C25SgeXWjE}
    }

This module never downloads anything — obtain and convert the data yourself
and pass its local JSONL path to :func:`load_proverqa`.
"""

import json
import re
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, Optional, Sequence, Tuple, Union

from lark import Lark, Transformer
from lark.exceptions import LarkError, VisitError

from ...fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, free_variables,
)
from ._base import DatasetExample, _register_dataset_info

__all__ = [
    "load_proverqa",
    "parse_proverqa_formula", "convert_proverqa_formulas",
    "solve_example",
]

_VALID_TIERS = ("easy", "medium", "hard")

_register_dataset_info(
    "proverqa",
    license=(
        "UNSPECIFIED by the authors (no license key in the HF dataset card; "
        "the README's 'License and Ethics' section only states that the "
        "dataset's INPUT SOURCES — names/keywords — comply with their own "
        "licenses, which is not a license grant for the ProverQA data "
        "itself). Treat as all-rights-reserved until the authors clarify."
    ),
    source_url="https://huggingface.co/datasets/opendatalab/ProverQA",
    citation_hint=(
        "Qi, Chengwen, et al. \"Large Language Models Meet Symbolic Provers "
        "for Logical Reasoning Evaluation.\" ICLR 2025. "
        "https://openreview.net/forum?id=C25SgeXWjE"
    ),
)


# --------------------------------------------------------------------------- #
# The ProverQA FOL dialect: an import-time grammar + conversion to kit ASTs
#
# ProverQA's gold FOL is honest first-order logic in a NOTATION this kit's own
# grammar refuses (snake_case predicates, Capitalized constants — see the
# module docstring's "CRITICAL notation finding"). Instead of lexically
# rewriting the strings, the loader parses them with THIS dedicated grammar
# (operators verified against the real corpus: ¬ ∧ ∨ ⊕ → ↔ ∀ ∃, standard
# precedence ¬ > ∧ > ∨ > ⊕ > → (right-assoc) > ↔; ProverQA parenthesises
# mixed nesting anyway) and converts the resulting tree into kit nodes,
# renaming identifiers into the kit's convention along the way:
#
#   * predicate ``has_experienced_heartbreak`` → ``HasExperiencedHeartbreak``
#     (underscore parts joined, each part's FIRST letter upcased, interior
#     capitalisation preserved — minimal change, not a re-styling),
#   * constant ``Brecken`` → ``brecken`` (first letter downcased; snake_case
#     constants fold the same way with camelCase joints),
#   * a term that lexes as a kit VARIABLE (``[a-z][0-9]*``) stays a variable.
#
# Two hard refusals keep the conversion honest: a constant whose converted
# form would lex as a VARIABLE (e.g. the constant ``A`` → ``a``) raises
# instead of silently changing quantification semantics, and the mapping is
# INJECTIVE per namespace across one whole example — two source names that
# would collapse onto one target (``p_a`` and ``pA`` → ``PA``) raise rather
# than merging distinct symbols. The loader stores the original strings and
# the (changed-entries-only) mapping in ``meta``, so nothing is hidden.
# --------------------------------------------------------------------------- #

_PROVERQA_GRAMMAR = r"""
?start: formula
?formula: iff
?iff: implies ("↔" implies)*
?implies: xor "→" implies        -> implies
        | xor
?xor: disj ("⊕" disj)*
?disj: conj ("∨" conj)*
?conj: unary ("∧" unary)*
?unary: "¬" unary                -> neg
      | "∀" IDENT unary          -> forall
      | "∃" IDENT unary          -> exists
      | atom
      | "(" formula ")"
atom: IDENT "(" IDENT ("," IDENT)* ")"
IDENT: /[A-Za-z][A-Za-z0-9_]*/
%import common.WS
%ignore WS
"""

_KIT_PREDICATE_RE = re.compile(r"[A-Z][a-zA-Z0-9]*\Z")
_KIT_CONSTANT_RE = re.compile(r"[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*\Z")
_KIT_VARIABLE_RE = re.compile(r"[a-z][0-9]*\Z")


class _NameConverter:
    """Kit-convention renaming with a per-namespace injectivity guarantee.

    One instance spans ONE example (all premises + the conclusion), so a
    predicate keeps the same converted name everywhere it occurs and two
    distinct source names can never collapse onto one target. ``pred_map`` /
    ``const_map`` hold only the names that actually changed — exactly what
    the loader records in ``meta["fol_name_mapping"]``.
    """

    def __init__(self) -> None:
        self.pred_map: Dict[str, str] = {}
        self.const_map: Dict[str, str] = {}
        self._final: Dict[str, Dict[str, str]] = {"predicate": {}, "constant": {}}

    def _claim(self, namespace: str, source: str, target: str) -> str:
        owner = self._final[namespace].setdefault(target, source)
        if owner != source:
            raise ValueError(
                f"proverqa: {namespace} names {owner!r} and {source!r} would "
                f"both convert to {target!r} — the renaming must stay "
                "injective, so this example cannot be converted.")
        return target

    def predicate(self, name: str) -> str:
        if _KIT_PREDICATE_RE.match(name):
            return self._claim("predicate", name, name)
        parts = [p for p in name.split("_") if p]
        if not parts:
            raise ValueError(f"proverqa: predicate {name!r} is underscores only.")
        target = "".join(p[0].upper() + p[1:] for p in parts)
        if not _KIT_PREDICATE_RE.match(target):
            raise ValueError(
                f"proverqa: predicate {name!r} does not convert to a legal "
                f"kit predicate (got {target!r}).")
        self._claim("predicate", name, target)
        self.pred_map[name] = target
        return target

    def constant(self, name: str) -> str:
        if _KIT_CONSTANT_RE.match(name):
            return self._claim("constant", name, name)
        parts = [p for p in name.split("_") if p]
        if not parts:
            raise ValueError(f"proverqa: constant {name!r} is underscores only.")
        head = parts[0][0].lower() + parts[0][1:]
        target = head + "".join(p[0].upper() + p[1:] for p in parts[1:])
        if _KIT_VARIABLE_RE.match(target):
            raise ValueError(
                f"proverqa: constant {name!r} would convert to {target!r}, "
                "which this kit lexes as a VARIABLE — refusing the silent "
                "semantics change.")
        if not _KIT_CONSTANT_RE.match(target):
            raise ValueError(
                f"proverqa: constant {name!r} does not convert to a legal "
                f"kit constant (got {target!r}).")
        self._claim("constant", name, target)
        self.const_map[name] = target
        return target

    def mapping(self) -> Dict[str, Dict[str, str]]:
        return {"predicates": dict(self.pred_map), "constants": dict(self.const_map)}


class _ProverQATransformer(Transformer):
    """Lark tree → kit :class:`~unicode_fol_kit.fol.nodes.Node`."""

    def __init__(self, converter: _NameConverter) -> None:
        super().__init__()
        self._conv = converter

    def _term(self, token) -> Node:
        name = str(token)
        if _KIT_VARIABLE_RE.match(name):
            return Variable(name)
        return Constant(self._conv.constant(name))

    def _binder(self, token) -> Variable:
        name = str(token)
        if not _KIT_VARIABLE_RE.match(name):
            raise ValueError(
                f"proverqa: quantified variable {name!r} is not a kit "
                "variable token ([a-z][0-9]*) — refusing to guess a rename "
                "for a BOUND name.")
        return Variable(name)

    def atom(self, children) -> Node:
        pred = self._conv.predicate(str(children[0]))
        return Atom(pred, tuple(self._term(t) for t in children[1:]))

    def neg(self, children) -> Node:
        return Not(children[0])

    def forall(self, children) -> Node:
        return Quantifier("∀", self._binder(children[0]), children[1])

    def exists(self, children) -> Node:
        return Quantifier("∃", self._binder(children[0]), children[1])

    def _fold(self, children, cls) -> Node:
        node = children[0]
        for right in children[1:]:
            node = cls(node, right)
        return node

    def conj(self, children) -> Node:
        return self._fold(children, And)

    def disj(self, children) -> Node:
        return self._fold(children, Or)

    def xor(self, children) -> Node:
        return self._fold(children, Xor)

    def implies(self, children) -> Node:
        if len(children) == 1:
            return children[0]
        return Implies(children[0], children[1])

    def iff(self, children) -> Node:
        return self._fold(children, Iff)


_proverqa_parser = Lark(_PROVERQA_GRAMMAR, parser="lalr")


def parse_proverqa_formula(text: str, *,
                           converter: Optional[_NameConverter] = None) -> Node:
    """Parse ONE formula in ProverQA's FOL notation into a kit AST.

    Identifiers are converted into this kit's naming convention (see the
    dialect comment block above). Pass a shared ``converter`` to keep the
    renaming consistent and injective across several formulas of one example
    — :func:`convert_proverqa_formulas` does exactly that.

    Raises:
        lark.exceptions.LarkError: ``text`` is not in the dialect.
        ValueError: an identifier cannot be converted without a collision or
            a constant→variable semantics change.
    """
    conv = converter if converter is not None else _NameConverter()
    tree = _proverqa_parser.parse(text)
    try:
        return _ProverQATransformer(conv).transform(tree)
    except VisitError as exc:
        # Lark wraps transformer exceptions; surface the converter's own
        # ValueError unchanged so the documented error contract holds.
        if isinstance(exc.orig_exc, ValueError):
            raise exc.orig_exc from None
        raise


def convert_proverqa_formulas(
        texts: Sequence[str]) -> Tuple[Tuple[Node, ...], Dict[str, Dict[str, str]]]:
    """Convert several ProverQA formulas with ONE shared, injective renaming.

    Returns ``(nodes, mapping)`` where ``mapping`` is
    ``{"predicates": {original: new}, "constants": {original: new}}`` holding
    only the names that actually changed. Every returned node must be CLOSED
    — a free variable (e.g. from a mis-scoped quantifier reading) raises
    rather than yielding a silently defective formula.
    """
    conv = _NameConverter()
    nodes: List[Node] = []
    for text in texts:
        node = parse_proverqa_formula(text, converter=conv)
        free = free_variables(node)
        if free:
            raise ValueError(
                f"proverqa: converted formula has free variable(s) "
                f"{sorted(free)!r} — refusing (source: {text!r}).")
        nodes.append(node)
    return tuple(nodes), conv.mapping()


def solve_example(example: DatasetExample, *, on_indefinite: str = "label",
                  **prove_kwargs) -> dict:
    """Decide one converted ProverQA example end-to-end via ``api.prove``.

    ProverQA's three-way gold label maps onto classical entailment exactly:
    ``"A"`` (True) iff premises ⊨ conclusion, ``"B"`` (False) iff premises ⊨
    ¬conclusion, ``"C"`` (Uncertain) otherwise. This helper proves the
    positive direction first and the negated one only when needed, and
    returns ``{"predicted": letter, "verdict": ..., "verdict_negated": ...}``
    (verdicts as dicts; ``verdict_negated`` is ``None`` when the positive
    direction already settled it). Extra ``prove_kwargs`` go verbatim to
    :func:`unicode_fol_kit.api.prove`, so the ATP is the caller's choice
    (``backends=["vampire"]``, ``timeout=…``). It requires an example whose
    formulas are in KIT notation — i.e. loaded with the default
    ``convert_fol=True`` and without a recorded
    ``meta["fol_conversion_error"]``; anything else raises ``ValueError``
    rather than silently scoring garbage.

    ``on_indefinite`` controls how a NON-DEFINITIVE prover outcome (status
    ``unknown``/``error`` — timeout, hit bound, honest incompleteness) is
    interpreted when neither direction was proved:

    - ``"label"`` (default): predict ``"C"`` — correct whenever the chosen
      prover is decisive on the fragment (z3 on ProverQA's dev tiers is).
    - ``"abstain"``: ``"C"`` only when BOTH directions are definitively
      REFUTED (underdetermination ESTABLISHED by countermodels); any
      indefinite leg yields ``predicted=None``, so a prover timeout can
      never be silently scored as a correct "Uncertain".
    - ``"raise"``: like ``"abstain"`` but an indefinite leg raises
      ``ValueError``.
    """
    from ... import api

    if on_indefinite not in ("label", "abstain", "raise"):
        raise ValueError(
            f"proverqa: on_indefinite must be 'label', 'abstain' or 'raise', "
            f"got {on_indefinite!r}")
    if example.meta.get("fol_conversion_error"):
        raise ValueError(
            f"proverqa: example {example.id} carries a conversion error "
            f"({example.meta['fol_conversion_error']}) — cannot solve it.")
    if example.fol_conclusion is None:
        raise ValueError(f"proverqa: example {example.id} has no conclusion.")

    def _parse(text: str) -> Node:
        parsed = api.parse_any(text)
        if not parsed.ok:
            raise ValueError(
                f"proverqa: example {example.id}: {text!r} does not parse "
                "under the kit grammar — was the example loaded with "
                "convert_fol=False?")
        return parsed.formula

    premises = [_parse(p) for p in example.fol_premises]
    conclusion = _parse(example.fol_conclusion)

    verdict = api.prove(conclusion, premises, **prove_kwargs)
    if verdict.status == "proved":
        return {"predicted": "A", "verdict": verdict.to_dict(),
                "verdict_negated": None}
    negated = api.prove(Not(conclusion), premises, **prove_kwargs)
    if negated.status == "proved":
        predicted: Optional[str] = "B"
    elif on_indefinite == "label":
        predicted = "C"
    elif verdict.status == "refuted" and negated.status == "refuted":
        # Underdetermination ESTABLISHED (countermodels both ways): "C" is a
        # definitive answer here, so abstain/raise modes still label it.
        predicted = "C"
    elif on_indefinite == "raise":
        raise ValueError(
            f"proverqa: example {example.id}: indefinite prover outcome "
            f"(goal: {verdict.status}/{verdict.reason}, negated: "
            f"{negated.status}/{negated.reason}) with on_indefinite='raise'.")
    else:                                        # "abstain"
        predicted = None
    return {"predicted": predicted, "verdict": verdict.to_dict(),
            "verdict_negated": negated.to_dict()}


def _resolve_id(record: dict, line_no: int, tier: Optional[str]) -> str:
    """The record's own ``"id"`` when present (namespaced by ``tier`` if
    given, to avoid the cross-tier collision documented in the module
    docstring), else a positional fallback.

    The positional fallback never fires against verified real data (every
    one of the 1,500 checked rows carries ``"id"``); it exists only so a
    malformed/hand-edited record still yields an addressable example instead
    of crashing on a missing key.
    """
    raw_id = record.get("id")
    if raw_id is None:
        raw_id = f"pos{line_no}"
    if tier is not None:
        return f"proverqa:{tier}:{raw_id}"
    return f"proverqa:{raw_id}"


def _example_from_record(record: dict, line_no: int, tier: Optional[str],
                         known_bad_ids: FrozenSet[str],
                         convert_fol: bool) -> DatasetExample:
    nl2fol = record.get("nl2fol") or {}
    nl_premises = tuple(nl2fol.keys())
    fol_premises = tuple(nl2fol.values())
    question = record.get("question")
    conclusion_fol = record.get("conclusion_fol")
    answer = record.get("answer")
    example_id = _resolve_id(record, line_no, tier)

    meta = {
        k: v for k, v in record.items()
        if k not in ("id", "nl2fol", "conclusion_fol", "question", "answer")
    }
    meta["line_no"] = line_no
    if tier is not None:
        meta["tier"] = tier

    if convert_fol:
        texts = list(fol_premises)
        if conclusion_fol is not None:
            texts.append(conclusion_fol)
        try:
            nodes, mapping = convert_proverqa_formulas(texts)
        except (LarkError, ValueError) as exc:
            # Honest per-example fallback: the verbatim upstream strings stay
            # in place and the failure is recorded, never swallowed.
            meta["fol_conversion_error"] = f"{type(exc).__name__}: {exc}"
        else:
            meta["original_fol_premises"] = list(fol_premises)
            meta["original_fol_conclusion"] = conclusion_fol
            meta["fol_name_mapping"] = mapping
            rendered = tuple(node.to_unicode_str() for node in nodes)
            if conclusion_fol is not None:
                fol_premises = rendered[:-1]
                conclusion_fol = rendered[-1]
            else:
                fol_premises = rendered

    return DatasetExample(
        id=example_id,
        nl_premises=nl_premises,
        fol_premises=fol_premises,
        nl_conclusion=question,
        fol_conclusion=conclusion_fol,
        label=answer,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_proverqa(path: Union[str, Path], *, tier: Optional[str] = None,
                  known_bad_ids: FrozenSet[str] = frozenset(),
                  convert_fol: bool = True) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local ProverQA ``dev/<tier>.json``-derived JSONL file.

    Args:
        path: path to a local ``.jsonl`` file — one ``dev/<tier>.json``
            record object per non-blank line (see module docstring for
            converting the upstream JSON-array distribution to this format).
            NEVER downloaded by this function. The upstream train split
            (``train/provergen-5000.json``) is NOT supported — it carries no
            structured FOL fields at all (see module docstring).
        tier: ``"easy"``, ``"medium"``, ``"hard"``, or ``None`` (default).
            Purely caller-supplied metadata (the source file itself does not
            self-report which tier a row belongs to) used to namespace ids
            (see module docstring for why that matters across tiers) and
            recorded verbatim in ``meta["tier"]`` when given.
        known_bad_ids: ids (see :func:`_resolve_id`) whose gold FOL is known
            to be broken beyond the notation mismatch documented in the
            module docstring (e.g. a curated finding on top of that). Every
            yielded example with a matching id gets ``known_bad=True``.
            Defaults to an empty set.
        convert_fol: with the default ``True``, every example's gold FOL is
            parsed with the dedicated ProverQA dialect grammar and re-emitted
            in KIT notation (``fol_premises``/``fol_conclusion`` then parse
            under ``api.parse_any``); the verbatim upstream strings and the
            injective name mapping land in ``meta["original_fol_premises"]``
            / ``meta["original_fol_conclusion"]`` /
            ``meta["fol_name_mapping"]``, and a per-example conversion
            failure is recorded in ``meta["fol_conversion_error"]`` with the
            verbatim strings kept in place — never swallowed, never a crash
            of the whole load. ``False`` restores the raw pass-through
            (0% kit-parse rate, see module docstring).

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order.

    Raises:
        ValueError: ``tier`` is given but is not one of ``"easy"``,
            ``"medium"``, ``"hard"``.
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON — this is
            NOT swallowed; a malformed dataset file is a loud failure, not a
            silently-skipped row.
    """
    if tier is not None and tier not in _VALID_TIERS:
        raise ValueError(f"tier must be one of {_VALID_TIERS!r} or None, got {tier!r}")

    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            yield _example_from_record(record, line_no, tier, known_bad_ids,
                                       convert_fol)
