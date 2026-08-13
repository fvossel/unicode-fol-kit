"""Adapter for the GROVES dataset (Vossel, "Groves" dataset card,
https://huggingface.co/datasets/fvossel/groves) — local JSONL only, no
network access.

Source and verified schema
---------------------------
Source: https://huggingface.co/datasets/fvossel/groves (unauthenticated;
verified 2026-08-12 directly via the Hugging Face datasets-server
``/splits``, ``/first-rows``, and ``/size`` APIs, and cross-checked against
the raw upstream ``train.json`` file via ``huggingface.co/.../resolve/main/``).
Config ``default`` has three splits — ``train`` (35910 rows), ``validation``
(3989 rows), ``test`` (9971 rows) — each row a flat JSON object with exactly
two keys:

* ``"NL"``  — ``str``, one natural-language statement.
* ``"FOL"`` — ``str``, its FOL translation, already written in THIS KIT'S OWN
  unicode surface syntax (``∀``/``∃``/``∧``/``∨``/``¬``/``→``/``↔``/``⊕``/
  ``≠``/``=`` all appear in the 100-row verified sample and ALL parse under
  this kit's default ``fol`` mode via :func:`unicode_fol_kit.api.parse_any` —
  confirmed directly, not assumed, by parsing and :func:`~unicode_fol_kit.api.check`-
  ing a 26-row spot sample spanning every connective/quantifier combination
  seen in the sample, all of which came back ``ok=True``/``is_closed=True``/
  ``arity_consistent=True``/``has_lambdas=False``). GROVES is the only
  adapter in this subpackage whose FOL column needs no dialect coaxing at
  all — it was generated directly in this kit's notation.

GROVES has NO id field, NO premises/conclusion structure, and NO entailment
label — the SAME flat (NL, FOL) translation-pair shape as
:mod:`~unicode_fol_kit.eval.datasets.malls`, mapped onto
:class:`~unicode_fol_kit.eval.datasets.DatasetExample` the same way (see
``malls.py``'s docstring for the field-mapping rationale, reused verbatim
here):

* ``nl_conclusion`` / ``fol_conclusion`` carry ``"NL"`` / ``"FOL"``.
* ``nl_premises`` / ``fol_premises`` are always ``()``.
* ``label`` is always ``None``.

Provenance (per the dataset card's "Description"/"Licensing" sections,
verified 2026-08-12): GROVES's natural-language inputs are drawn from
WillowNLtoFOL (https://huggingface.co/datasets/iedeveci/WillowNLtoFOL,
originally CC BY-NC-ND 4.0, "included with permission from the original
authors" per the card) and MALLS-v0
(https://huggingface.co/datasets/yuan-yang/MALLS-v0, CC BY-NC 4.0); the FOL
expressions themselves were newly generated for GROVES and the dataset was
"subsequently filtered" — the card gives no further detail on that
generation/filtering pipeline, and this adapter does not invent any (no
independent semantic re-verification of the FOL against the NL is claimed
here beyond "it parses and is well-formed under this kit").

Upstream GROVES is distributed as JSON ARRAY files (``train.json`` /
``val.json`` / ``test.json`` — one big ``[...]`` list per split, confirmed
directly from the raw file's first bytes), NOT as JSONL. Like
:mod:`~unicode_fol_kit.eval.datasets.malls`, this loader reads local JSONL
(one JSON object per line) for a uniform streaming adapter surface; convert
an upstream split file first (e.g. ``jq -c '.[]' train.json >
groves_train.jsonl``) before calling :func:`load_groves`.

License: **CC-BY-NC-4.0** (non-commercial), per the dataset card's ``license``
front-matter and its "Licensing" section — which additionally requires
downstream users to also comply with the licenses of the two datasets GROVES
is built from (WillowNLtoFOL, CC BY-NC-ND 4.0; MALLS-v0, CC BY-NC 4.0). This
loader itself has no license implications beyond reading a local file the
caller already obtained; it never downloads or redistributes GROVES data.

Citation: as of 2026-08-12 the dataset card's "Notes" section states only
that "[f]urther details about dataset construction and evaluation will be
provided in a forthcoming publication" — it does NOT name a paper. A
plausible companion paper, matching both topic (NL-to-FOL formalization with
fine-tuned LLMs) and authorship (the dataset's Hugging Face account is
``fvossel``): Vossel, Felix, Till Mossakowski, and Bjoern Gehrke. "Advancing
Natural Language Formalization to First Order Logic with Fine-tuned LLMs."
arXiv:2509.22338. This link is NOT asserted by the dataset card itself —
:data:`DATASET_INFO`'s ``citation_hint`` for ``"groves"`` flags it as
plausible-but-unconfirmed rather than presenting it as settled.

What GROVES does NOT have (spelled out so nothing here is silently assumed):
no premises/entailment structure (a straight translation-pair dataset, like
MALLS, unlike FOLIO); no entailment label; no id field of any kind; no
train/validation/test SPLIT FILE bundling — each split is its own upstream
JSON array file, and this loader (like ``load_malls``) takes exactly one
already-converted local JSONL path per call, so loading multiple splits
means calling :func:`load_groves` once per split file; no independent
human/semantic verification of the FOL column beyond "the dataset was
filtered" per the card — this adapter's own :func:`~unicode_fol_kit.eval.datasets.audit_examples`
only checks parseability and well-formedness (closed, arity-consistent,
lambda-free), never whether a given FOL formula is a *correct* translation
of its NL sentence.

This module never downloads anything — obtain and convert the data yourself
and pass its local JSONL path to :func:`load_groves`.
"""

import json
from pathlib import Path
from typing import FrozenSet, Iterator, Union

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_groves"]

_register_dataset_info(
    "groves",
    license=(
        "CC-BY-NC-4.0 (non-commercial); GROVES is built from WillowNLtoFOL "
        "(CC BY-NC-ND 4.0, used with permission from its original authors "
        "per the GROVES dataset card) and MALLS-v0 (CC BY-NC 4.0) "
        "natural-language inputs, so downstream use must also honour both "
        "of those source licenses per the dataset card's Licensing section"
    ),
    source_url="https://huggingface.co/datasets/fvossel/groves",
    citation_hint=(
        "Vossel, Felix. \"Groves\" (dataset card, Hugging Face, "
        "https://huggingface.co/datasets/fvossel/groves) — the card states "
        "only that \"further details ... will be provided in a forthcoming "
        "publication\" and names no paper. Plausible (topic- and "
        "author-matched, but NOT card-confirmed) companion paper: Vossel, "
        "Felix, Till Mossakowski, and Bjoern Gehrke. \"Advancing Natural "
        "Language Formalization to First Order Logic with Fine-tuned "
        "LLMs.\" arXiv:2509.22338."
    ),
)


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    nl = record.get("NL")
    fol = record.get("FOL")
    # GROVES has no native id field (see module docstring): every verified
    # row is exactly {"NL": ..., "FOL": ...}. Mirrors malls.py's stance —
    # honour an "id" key opportunistically should some downstream re-export
    # add one, otherwise fall back to a positional id.
    raw_id = record.get("id")
    example_id = str(raw_id) if raw_id is not None else f"groves:{line_no}"

    meta = {k: v for k, v in record.items() if k not in ("NL", "FOL", "id")}
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=(),
        fol_premises=(),
        nl_conclusion=nl,
        fol_conclusion=fol,
        label=None,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_groves(path: Union[str, Path], *,
                known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local GROVES JSONL file (one already-converted split — see module
    docstring for converting the upstream JSON-array split files).

    Args:
        path: path to a local ``.jsonl`` file — one ``{"NL": ..., "FOL": ...}``
            object per non-blank line. NEVER downloaded by this function;
            obtain and convert the split file yourself from
            https://huggingface.co/datasets/fvossel/groves.
        known_bad_ids: ids (the record's own ``"id"`` if present, else the
            positional fallback ``f"groves:{line_no}"``) whose ``"FOL"``
            translation is known to be broken. Every yielded example with a
            matching id gets ``known_bad=True``. Defaults to an empty set.

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order, with ``nl_conclusion``/
        ``fol_conclusion`` set from ``"NL"``/``"FOL"`` and
        ``nl_premises``/``fol_premises`` empty (see module docstring for why).
        A record missing ``"NL"`` and/or ``"FOL"`` yields an example with
        ``None`` in the corresponding field rather than raising — the same
        documented "missing key -> None/() default" behaviour as
        :func:`~unicode_fol_kit.eval.datasets.folio.load_folio` and
        :func:`~unicode_fol_kit.eval.datasets.malls.load_malls` (a structurally
        malformed FILE is a loud failure, see below; a single record missing
        an optional-looking key is not).

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
