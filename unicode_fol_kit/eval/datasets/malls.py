"""Adapter for the MALLS dataset (Yang et al., "Harnessing the Power of Large
Language Models for Natural Language to First-Order Logic Translation") —
local JSONL only, no network access.

Source and verified schema
---------------------------
Source: https://huggingface.co/datasets/yuan-yang/MALLS-v0 (unauthenticated;
verified directly via the Hugging Face datasets-server rows API). Each record
is a flat JSON object with exactly two keys:

* ``"NL"``  — ``str``, one natural-language statement.
* ``"FOL"`` — ``str``, its FOL translation (GPT-4-generated, then a subset
  auto/human-verified — see the paper for the verification pipeline; MALLS
  is a straight NL-to-FOL TRANSLATION pair, not a premise/conclusion
  entailment example the way FOLIO is).

MALLS has NO id field, NO premises/conclusion structure, and NO entailment
label — it is a flat bag of (statement, formula) pairs. This adapter maps
that onto :class:`~unicode_fol_kit.eval.datasets.DatasetExample` as follows,
a deliberate design choice (not something verified from the source, since
the source has no such structure to verify against):

* ``nl_conclusion`` / ``fol_conclusion`` carry the ``"NL"`` / ``"FOL"``
  values — "conclusion" here means "the target formula the translation task
  is producing", which is the natural reading for a single-sentence
  translation pair (as opposed to ``nl_premises``/``fol_premises``, which
  would imply an entailment structure MALLS does not have).
* ``nl_premises`` / ``fol_premises`` are always ``()`` (empty tuples).
* ``label`` is always ``None`` (MALLS carries no entailment label).

Upstream MALLS is distributed as JSON ARRAY files (e.g.
``MALLS-v0.1-train.json``, ``MALLS-v0.json`` — one big ``[...]`` list), NOT
as JSONL. This loader, like :func:`~unicode_fol_kit.eval.datasets.folio.load_folio`,
reads local JSONL (one JSON object per line) for a uniform, streaming-friendly
adapter surface across both datasets in this subpackage — convert an upstream
MALLS file to JSONL first (e.g. ``jq -c '.[]' MALLS-v0.1-train.json >
malls.jsonl``) before calling :func:`load_malls`.

License: **CC-BY-NC-4.0** (non-commercial), per the dataset card. Because the
FOL annotations were generated with GPT-4, the dataset card also states it
"abides by the policy of OpenAI" (https://openai.com/policies/terms-of-use)
— both the license's non-commercial clause and that usage-policy pointer
apply to any use of the actual MALLS data (this loader itself has no
license implications beyond reading a local file the caller already
obtained; it never downloads or redistributes MALLS data).

This module never downloads anything — obtain and convert the data yourself
and pass its local JSONL path to :func:`load_malls`.
"""

import json
from pathlib import Path
from typing import FrozenSet, Iterator, Union

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_malls"]

_register_dataset_info(
    "malls",
    license=(
        "CC-BY-NC-4.0 (non-commercial); data is GPT-4-generated, so usage is "
        "additionally subject to OpenAI's usage policies, "
        "https://openai.com/policies/terms-of-use"
    ),
    source_url="https://huggingface.co/datasets/yuan-yang/MALLS-v0",
    citation_hint=(
        "Yang, Yuan, et al. \"Harnessing the Power of Large Language Models "
        "for Natural Language to First-Order Logic Translation.\" "
        "arXiv:2305.15541."
    ),
)


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    nl = record.get("NL")
    fol = record.get("FOL")
    # MALLS has no native id field (see module docstring); some downstream
    # re-exports might add one, so honour it opportunistically before
    # falling back to a positional id.
    raw_id = record.get("id")
    example_id = str(raw_id) if raw_id is not None else f"malls:{line_no}"

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


def load_malls(path: Union[str, Path], *,
               known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local MALLS JSONL file.

    Args:
        path: path to a local ``.jsonl`` file — one ``{"NL": ..., "FOL": ...}``
            object per non-blank line (see module docstring for converting
            the upstream JSON-array distribution to this format). NEVER
            downloaded by this function.
        known_bad_ids: ids (the record's own ``"id"`` if present, else the
            positional fallback ``f"malls:{line_no}"``) whose ``"FOL"``
            translation is known to be broken. Every yielded example with a
            matching id gets ``known_bad=True``. Defaults to an empty set.

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order, with ``nl_conclusion``/
        ``fol_conclusion`` set from ``"NL"``/``"FOL"`` and
        ``nl_premises``/``fol_premises`` empty (see module docstring for why).

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
