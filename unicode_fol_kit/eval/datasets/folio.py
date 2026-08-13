"""Adapter for the FOLIO dataset (Han et al., "FOLIO: Natural Language
Reasoning with First-Order Logic") — local JSONL only, no network access.

Source and verified schema
---------------------------
Canonical, unauthenticated source: https://github.com/Yale-LILY/FOLIO
(``data/v0.0/folio-train.jsonl`` / ``data/v0.0/folio-validation.jsonl``). A
mirror also exists at https://huggingface.co/datasets/yale-nlp/FOLIO, but
that mirror is access-gated (requires a Hugging Face login to download), so
it was NOT used to verify the schema below — everything here was verified
directly against the raw GitHub JSONL content.

Each verified ``v0.0`` JSONL line is a flat JSON object with exactly these
keys (confirmed by fetching and inspecting real rows of
``folio-validation.jsonl``):

* ``"premises"``       — ``list[str]``, the natural-language premises.
* ``"premises-FOL"``   — ``list[str]``, the SAME LENGTH and ORDER as
  ``"premises"``; each entry is that premise's gold FOL annotation, written
  in this kit's own unicode surface syntax (``∀``/``∃``/``∧``/``∨``/``¬``/
  ``→``/``⊕`` etc. all appear in the verified sample and all parse under this
  kit's default ``fol`` mode).
* ``"conclusion"``     — ``str``, the natural-language conclusion.
* ``"conclusion-FOL"`` — ``str``, its gold FOL annotation.
* ``"label"``          — ``str``, the gold entailment label. The verified
  sample showed ``"True"`` and ``"Uncertain"``; the paper and repository
  README additionally document ``"False"`` as the third value (NOT directly
  observed in the two rows fetched for this verification — flagged here
  rather than silently assumed).

The verified ``v0.0`` rows carry NO id field at all (no ``example-id``,
``story-id``, or ``source`` key was present in the fetched sample, contrary
to a fields description on the Hugging Face mirror's README, which this
adapter could not reach past the login gate to cross-check). This loader is
defensive rather than assuming either shape is final: it uses an
``"example-id"``/``"example_id"`` key WHEN PRESENT, and otherwise falls back
to a positional id ``f"folio:{line_no}"`` (0-based line number within the
file) so every example is still addressable. Deliberately NOT used for id
resolution: ``"story-id"``/``"story_id"`` — the verified sample shows several
consecutive rows sharing identical ``premises``/``premises-FOL`` (one story,
several conclusions), so a story id identifies a GROUP of examples, not one
example, and using it alone as an id would collide across that group. It is
still preserved (like every other unrecognised key) in ``meta`` when present.

License: **CC-BY-SA-4.0**, per the ``LICENSE`` file at the repository root
(https://github.com/Yale-LILY/FOLIO/blob/main/LICENSE, verified directly).
Share-alike: adaptations/redistributions of the data itself must carry a
compatible license and attribution — this loader only reads a LOCAL file the
caller already obtained, it does not redistribute or embed any FOLIO data.

This module never downloads anything — obtain the JSONL file yourself from
one of the sources above and pass its local path to :func:`load_folio`.
"""

import json
from pathlib import Path
from typing import FrozenSet, Iterator, Union

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_folio"]

_register_dataset_info(
    "folio",
    license="CC-BY-SA-4.0",
    source_url="https://github.com/Yale-LILY/FOLIO",
    citation_hint=(
        "Han, Simin, et al. \"FOLIO: Natural Language Reasoning with "
        "First-Order Logic.\" arXiv:2209.00840."
    ),
)


def _resolve_id(record: dict, line_no: int) -> str:
    """The record's own per-example id field if present, else a positional
    fallback.

    Tries both the hyphenated spelling documented in the field-description
    text and the underscore spelling a JSON-key-safe re-export might use;
    verified real data has neither (see module docstring), so the fallback
    path is what actually fires against the canonical GitHub JSONL today.
    Deliberately does NOT consult ``"story-id"``/``"story_id"`` — see the
    module docstring for why that would not be a safe per-example id.
    """
    for key in ("example-id", "example_id"):
        value = record.get(key)
        if value is not None:
            return str(value)
    return f"folio:{line_no}"


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    premises = tuple(record.get("premises") or ())
    premises_fol = tuple(record.get("premises-FOL") or ())
    conclusion = record.get("conclusion")
    conclusion_fol = record.get("conclusion-FOL")
    label = record.get("label")
    example_id = _resolve_id(record, line_no)

    meta = {
        k: v for k, v in record.items()
        if k not in ("premises", "premises-FOL", "conclusion",
                    "conclusion-FOL", "label")
    }
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=premises,
        fol_premises=premises_fol,
        nl_conclusion=conclusion,
        fol_conclusion=conclusion_fol,
        label=label,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_folio(path: Union[str, Path], *,
               known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local FOLIO JSONL file.

    Args:
        path: path to a local ``.jsonl`` file in the verified FOLIO schema
            (see module docstring) — one JSON object per non-blank line.
            NEVER downloaded by this function; obtain the file from
            https://github.com/Yale-LILY/FOLIO yourself.
        known_bad_ids: ids (see :func:`_resolve_id`) whose gold annotation is
            known to be broken (e.g. from a prior human review or an
            :func:`~unicode_fol_kit.eval.datasets.audit_examples` pass on an
            earlier load). Every yielded example with a matching id gets
            ``known_bad=True``; everything else gets ``known_bad=False``.
            Defaults to an empty set (nothing pre-flagged).

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order. ``premises``/``premises-FOL``
        (mapped to ``nl_premises``/``fol_premises``) are guaranteed to be the
        same length only insofar as the source file guarantees it — this
        loader does not enforce or re-check that pairing (a length mismatch
        would show up as a defect during evaluation, not silently here).

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON — this is
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
