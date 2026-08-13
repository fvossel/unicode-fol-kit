"""Adapter for LogicNLI (Tian, Li, Chen, Xiao, He, and Jin, "Diagnosing the
First-Order Logical Reasoning Ability Through LogicNLI", EMNLP 2021) — local
JSONL only, no network access.

Two sources were checked, not assumed
--------------------------------------
The task brief for this adapter asked specifically whether the Hugging Face
mirror carries the same first-order structure as the GitHub original. It
does not, and the difference drives every design choice below.

**Hugging Face mirror** — https://huggingface.co/datasets/tasksource/LogicNLI
(unauthenticated; verified 2026-08-12 via the ``datasets-server``
``/splits`` and ``/first-rows`` APIs). Three splits under config
``"default"``: ``train`` (16000 rows), ``validation`` (2000 rows), ``test``
(2000 rows) — 20000 rows total. Every row is a flat object with EXACTLY
three keys, all ``dtype: string``:

* ``"premise"``    — ONE string: every fact sentence, ``"\\n"``-joined,
  directly followed by every rule sentence, also ``"\\n"``-joined, but with
  **no separator at all between the last fact and the first rule** (verified
  directly in the fetched sample: ``"...Nathalie is not accurate.If there is
  someone..."`` — the period is followed immediately by ``"If"``, no space or
  newline). This is a lossy blob: individual premise sentences cannot be
  recovered from it without a fact/rule-boundary heuristic this adapter
  declines to guess.
* ``"hypothesis"`` — ``str``, the statement being judged.
* ``"label"``      — ``str``. The **verified label vocabulary**, read
  directly off real rows (not the paper's prose), is exactly four values:
  ``"entailment"``, ``"contradiction"``, ``"neutral"``, ``"self_contradiction"``.
  Note this explicitly: the fourth class is **not** called ``"paradox"``
  anywhere in the data — that was only ever an informal guess.

There is NO first-order-logic column of any kind on the HF mirror — no field
resembling FOLIO's ``premises-FOL``/``conclusion-FOL`` exists here at all.

**GitHub original** — https://github.com/omnilabNLP/LogicNLI (verified
2026-08-12 via the GitHub Contents API and by downloading and unzipping the
repo's one data artifact, ``dataset/LogicNLI_sim.zip``, 856136 bytes per the
Contents API). The archive contains six files, ``{train,dev,test}_language.json``
and ``{train,dev,test}_logic.json``, each a JSON object keyed by a "story id"
string. Counts were verified exhaustively (every story in every split, not a
sample): every single story has EXACTLY 12 facts, 12 rules, and 20 statements
— 800 stories in ``train`` (16000 statements), 100 in ``dev`` (2000), 100 in
``test`` (2000). These totals match the HF mirror's split sizes exactly
(16000/2000/2000), confirming both are the same underlying benchmark (``dev``
here vs. ``validation`` there is just a naming difference) — though row order
does not obviously align 1:1 (HF row 0 uses different character names than
GitHub story ``"0"``), so treat them as two independently-obtained copies,
not index-aligned mirrors of each other.

Critically, ``*_logic.json`` DOES carry a logical annotation the HF mirror
lacks — but it is a bespoke STRUCTURED SYMBOLIC form, not an FOL formula
string of the kind FOLIO's ``premises-FOL`` provides. Confirmed directly by
loading and inspecting real story records (``dev_logic.json``/
``dev_language.json``, stories ``"0"`` and ``"1"``, cross-checked sentence by
sentence against the paired ``*_language.json`` English text):

* A **fact** is a 4-element list ``[subject, attribute, polarity, tag]``,
  e.g. ``["Eli", "soft", "-", "fact 0"]`` for "Eli is not soft." — always a
  NAMED entity (``subject`` is never a quantifier marker; verified over all
  12000 facts across all three splits: 100% ``const``-subject).
  ``polarity`` is ``"+"`` (asserted) or ``"-"`` (negated).
  A **statement** (the hypothesis being labelled) has the same 4-element
  shape and the same 100%-named-subject property (verified over all 20000
  statements), plus a fourth element that is a human-unreadable PROVENANCE
  trace of which facts/rules the label was derived from (e.g.
  ``"[[fact 2-->6]-->3]"``), not a sentence.
* A **rule** is ``{"p": {"fact": [...], "conj": ...}, "q": {"fact": [...],
  "conj": ...}, "type": "imp"|"equ", "reasoning": <code>, "class": <int>}``.
  ``p``/``q`` are the antecedent/consequent, each a list of 1-2 fact-triples
  ``[subject_or_quantifier, attribute, polarity]`` (no tag) combined by
  ``conj`` (``"none"`` for a singleton, else ``"and"``/``"or"``); ``type``
  is ``"imp"`` (material implication, p occurring first) or ``"equ"``
  (biconditional). ``subject_or_quantifier`` is one of a NAMED entity,
  ``"all"``, or ``"exist"`` — verified EXHAUSTIVELY over all 12000 rules
  across all three splits that within one ``p``/``q`` group the subject kind
  is always homogeneous (never a named entity mixed with a quantifier
  marker in the same group), and that only four ``(p_kind, q_kind)``
  combinations ever occur: ``(all, all)`` — 4980, ``(const, const)`` — 3890,
  ``(exist, const)`` — 2783, ``(all, const)`` — 347 (of which ALL 347 are
  ``"imp"``, never ``"equ"``). No ``(exist, exist)``, ``(exist, all)``, or
  ``(const, *quantifier*)`` combination occurs at all. ``"reasoning"``/
  ``"class"`` are the paper's own internal category codes for its
  robustness/traceability evaluation; this adapter does not interpret them.

What this adapter deliberately does NOT do
-------------------------------------------
Turning the structured ``rules`` annotation above into an actual FOL formula
string is possible in principle (the exhaustive combo analysis above is
enough to fix a translation scheme unambiguously) but it is a NEW,
kit-authored INTERPRETATION of the data, not something the dataset's authors
themselves published as a formula — the closest they publish is the
human-readable ``*_language.json`` sentence. Shipping a from-scratch compiler
here would (a) silently present an unreviewed, unverified rendering as if it
were "the dataset's FOL", which is exactly the kind of quiet reshaping this
adapter subpackage's docstrings elsewhere warn against, and (b) make
:func:`~unicode_fol_kit.eval.datasets.audit_examples` report on formulas THIS
adapter invented rather than ones the dataset ships — a meaningless "clean"
signal. So, per this task's own documented fallback: **``fol_premises`` is
always ``()`` and ``fol_conclusion`` is always ``None`` for every LogicNLI
example.** The raw structured annotation is not discarded, though — it is
preserved VERBATIM in ``meta["premises_logic"]`` / ``meta["hypothesis_logic"]``
(see the loader schema below) for any downstream user who wants to write
their own translation.

This adapter's own JSONL schema (NOT a verbatim upstream format)
------------------------------------------------------------------
Neither upstream source is naturally "one JSON object per example": the HF
mirror gives ONE flat row per example but with the two fatal issues above
(no split-out premise sentences, no logic annotation at all); the GitHub
original groups 20 examples under one shared story (12 facts + 12 rules) and
splits that across TWO separate files (language / logic) that must be joined
by story id. So, exactly like :mod:`~unicode_fol_kit.eval.datasets.malls`
asks the caller to convert an upstream JSON array to JSONL first, this loader
defines its OWN per-example JSONL row shape and expects the caller to
produce it from the GitHub archive (a story's facts+rules is repeated
verbatim across every example/line drawn from that story — the same "several
consecutive rows share identical premises" situation FOLIO's docstring
already documents for its own story grouping):

* ``"premises_nl"``    — ``list[str]``: that story's ``facts`` (language)
  followed by its ``rules`` (language), in source order.
* ``"premises_logic"`` — ``list``, the SAME length/order as ``premises_nl``:
  each fact position holds its raw ``[subject, attribute, polarity, tag]``
  list, each rule position holds its raw ``{"p": ..., "q": ..., "type":
  ..., "conj": ..., "reasoning": ..., "class": ...}`` dict (see above) —
  copied verbatim from ``*_logic.json``, uninterpreted.
* ``"hypothesis_nl"``    — ``str``, the statement's language text.
* ``"hypothesis_logic"`` — the statement's raw ``[subject, attribute,
  polarity, provenance]`` list, copied verbatim.
* ``"label"``          — ``str``, one of the four verified values above.
* ``"story_id"`` / ``"statement_id"`` / ``"split"`` — optional provenance
  strings (the upstream story key, the upstream per-statement key within
  that story, and which of ``train``/``dev``/``test`` it came from) used for
  id construction when present (see :func:`_resolve_id`); a caller merging
  multiple splits into one file should keep ``"split"`` so ids stay unique
  across splits sharing the same numeric ``story_id``.
* ``"id"``             — optional explicit override, honoured before any of
  the above (same defensive stance as every other adapter in this
  subpackage).

A short recipe to produce this from the downloaded GitHub archive (adjust
paths/split as needed)::

    import json
    with open("dev_language.json", encoding="utf-8") as f: lang = json.load(f)
    with open("dev_logic.json", encoding="utf-8") as f: logic = json.load(f)
    with open("logicnli_dev.jsonl", "w", encoding="utf-8") as out:
        for story_id, story in logic.items():
            slang = lang[story_id]
            premises_nl = list(slang["facts"]) + list(slang["rules"])
            premises_logic = ([story["facts"][str(i)] for i in range(len(slang["facts"]))]
                              + [story["rules"][str(i)] for i in range(len(slang["rules"]))])
            for sid, label in story["labels"].items():
                row = {
                    "story_id": story_id, "statement_id": sid, "split": "dev",
                    "premises_nl": premises_nl, "premises_logic": premises_logic,
                    "hypothesis_nl": slang["statements"][int(sid)],
                    "hypothesis_logic": story["statements"][sid],
                    "label": label,
                }
                out.write(json.dumps(row, ensure_ascii=False) + "\\n")

License — not stated by the authors, flagged rather than guessed
-------------------------------------------------------------------
Neither source declares a machine-readable license (verified 2026-08-12): the
GitHub repository has no ``LICENSE`` file (the GitHub Licenses API returns
404 for it) and no license section in its ``README.md``; the Hugging Face
dataset card's metadata (fetched via the HF datasets API and the raw
``README.md``) carries no ``license`` tag and no licensing prose — only the
paper's BibTeX entry. :data:`DATASET_INFO`'s ``license`` field for
``"logicnli"`` records exactly this absence rather than guessing a permissive
or restrictive default; confirm terms with the authors before redistributing.

This module never downloads anything — obtain and convert the data yourself
(see the recipe above) and pass its local JSONL path to :func:`load_logicnli`.
"""

import json
from pathlib import Path
from typing import FrozenSet, Iterator, Union

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_logicnli"]

_register_dataset_info(
    "logicnli",
    license=(
        "Not stated by the authors as of verification (2026-08-12): the "
        "GitHub repository (omnilabNLP/LogicNLI) has no LICENSE file (GitHub "
        "Licenses API returns 404) and no licensing section in its README; "
        "the Hugging Face mirror (tasksource/LogicNLI) has no license tag or "
        "licensing prose on its dataset card either. Confirm terms with the "
        "authors before redistributing."
    ),
    source_url="https://github.com/omnilabNLP/LogicNLI",
    citation_hint=(
        "Tian, Jidong, et al. \"Diagnosing the First-Order Logical Reasoning "
        "Ability Through LogicNLI.\" Proceedings of the 2021 Conference on "
        "Empirical Methods in Natural Language Processing (EMNLP 2021), "
        "pages 3738-3747. https://doi.org/10.18653/v1/2021.emnlp-main.303"
    ),
)

_RECORD_KEYS = (
    "premises_nl", "premises_logic", "hypothesis_nl", "hypothesis_logic",
    "label", "story_id", "statement_id", "split", "id",
)


def _resolve_id(record: dict, line_no: int) -> str:
    """An explicit ``"id"`` if present; else a story/statement-derived id
    (optionally split-qualified) built from ``"story_id"``/``"statement_id"``
    (present in this adapter's own JSONL schema, see module docstring); else
    a positional fallback — every example is addressable either way.
    """
    explicit = record.get("id")
    if explicit is not None:
        return str(explicit)

    story_id = record.get("story_id")
    statement_id = record.get("statement_id")
    if story_id is not None and statement_id is not None:
        split = record.get("split")
        if split is not None:
            return f"logicnli:{split}:{story_id}:{statement_id}"
        return f"logicnli:{story_id}:{statement_id}"

    return f"logicnli:{line_no}"


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    premises_nl = tuple(record.get("premises_nl") or ())
    hypothesis_nl = record.get("hypothesis_nl")
    label = record.get("label")
    example_id = _resolve_id(record, line_no)

    meta = {k: v for k, v in record.items() if k not in _RECORD_KEYS}
    meta["premises_logic"] = record.get("premises_logic")
    meta["hypothesis_logic"] = record.get("hypothesis_logic")
    meta["story_id"] = record.get("story_id")
    meta["statement_id"] = record.get("statement_id")
    meta["split"] = record.get("split")
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=premises_nl,
        fol_premises=(),           # see module docstring: never compiled
        nl_conclusion=hypothesis_nl,
        fol_conclusion=None,       # see module docstring: never compiled
        label=label,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_logicnli(path: Union[str, Path], *,
                  known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local LogicNLI JSONL file in THIS ADAPTER's OWN schema (see module
    docstring for the field list and the recipe to produce it from the
    downloaded GitHub original).

    Args:
        path: path to a local ``.jsonl`` file — one row per LogicNLI
            statement/hypothesis, in this adapter's own schema (module
            docstring). NEVER downloaded by this function; obtain and
            convert the data yourself from
            https://github.com/omnilabNLP/LogicNLI.
        known_bad_ids: ids (see :func:`_resolve_id`) whose annotation is
            known to be broken. Every yielded example with a matching id
            gets ``known_bad=True``; everything else gets ``known_bad=False``.
            Defaults to an empty set.

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order. ``fol_premises`` is always
        ``()`` and ``fol_conclusion`` is always ``None`` — this dataset has
        no ready-made FOL formula strings, only a structured symbolic
        annotation this adapter deliberately does not compile into one (see
        module docstring); that raw annotation survives, uninterpreted, in
        ``meta["premises_logic"]``/``meta["hypothesis_logic"]``. A record
        missing an expected key yields ``None``/``()`` for that field rather
        than raising — the same "missing key -> default, not exception"
        convention :func:`~unicode_fol_kit.eval.datasets.folio.load_folio`
        documents.

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON — raised,
            not swallowed (a malformed dataset file must fail loudly).
    """
    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            yield _example_from_record(record, line_no, known_bad_ids)
