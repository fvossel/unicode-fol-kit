"""Adapter for LogicBench (Parmar, Patel, Varshney, Nakamura, Luo, Mashetty,
Mitra, Baral, "Towards Systematic Evaluation of Logical Reasoning Ability of
Large Language Models", 2024, arXiv:2404.15522) — natural-language
question-answering over 25 single-inference-rule reasoning patterns spanning
propositional, first-order and non-monotonic logic. Modeled directly on
:mod:`~unicode_logic_kit.eval.datasets.fracas`, since LogicBench ships NO gold
FOL either: every row is natural-language context plus a question and a
yes/no or multiple-choice answer, nothing more — so, exactly as for FraCaS,
the translation step lives OUTSIDE this library (:func:`solve_example`'s
``translate``) and this package only decides.

Source and verified schema
---------------------------
Verified 2026-09-17 directly against a local clone of the repository the
paper names, ``https://github.com/Mihir3009/LogicBench``. ``data/`` holds
two releases:

* **LogicBench(Eval)** — the human-verified evaluation set this adapter
  reads, split into ``BQA`` (Binary Question-Answering) and ``MCQA``
  (Multiple-Choice Question-Answering), each further split by
  ``propositional_logic`` / ``first_order_logic`` / ``nm_logic`` and then by
  one JSON file per inference rule ("axiom"), e.g.
  ``BQA/propositional_logic/modus_tollens/data_instances.json``.
* **LogicBench(Aug)** — a synthetically augmented TRAINING split with a
  DIFFERENT schema (top-level key ``"data_samples"`` instead of
  ``"samples"``, no per-row ``"id"``, and 4 ``qa_pairs`` per row — both
  polarities of both directions — instead of 2). Inspected while verifying
  this adapter's schema, but NOT read by it: the build spec this module
  implements only covers ``LogicBench(Eval)``, and Aug's different shape
  would need its own field mapping, not this one.

One **Eval** JSON file — :func:`load_logicbench` reads exactly one, like
every other loader in this package; nothing here downloads anything — has
the shape ``{"type": str, "axiom": str, "samples": [...]}``:

* ``"type"`` — the file's own logic-type label, kept VERBATIM in
  ``meta["logic_type"]``. Confirmed by reading every real Eval file: it is
  ``"propositional_logic"`` / ``"first_order_logic"`` under those two
  directories (matching the directory name), but ``"non_monotonic_logic"``
  under the ``nm_logic`` DIRECTORY — never the literal string
  ``"nm_logic"``. :func:`solve_example` routes on the ACTUAL file value
  (``"non_monotonic_logic"``, :data:`NM_LOGIC_TYPE`), not on the directory
  name a caller happened to read the file from.
* ``"axiom"`` — the inference-rule name (e.g. ``"modus_tollens"``), kept
  verbatim in ``meta["axiom"]``.
* ``"samples"`` — a list of ``{"id": int, "context": str, ...}``. ``id`` is
  1-based WITHIN THIS ONE FILE, not globally unique (kept verbatim in
  ``meta["sample_id"]``); ``context`` is one NL paragraph, never pre-split
  into sentences the way FraCaS's ``<p>`` elements are, so it maps to the
  single-element ``nl_premises = (context,)`` — a caller's ``translate``
  sees the whole paragraph at once and is free to return a single
  conjunctive formula for it.

  * **BQA** (``split="BQA"``): each sample additionally carries
    ``"qa_pairs": [{"question": str, "answer": "yes"|"no"}, ...]`` — 2 to 4
    pairs per sample in every real Eval BQA file (every ``answer`` verified
    to be exactly the lowercase string ``"yes"`` or ``"no"``, nothing else).
    A sample with N qa_pairs yields N separate :class:`DatasetExample`\\ s
    (one per question, all sharing the same ``nl_premises``), since each
    pair asks about a DIFFERENT proposition with its OWN gold answer —
    collapsing them into one example would silently keep only one label.
    ``meta["qa_index"]`` (0-based, within the sample) makes the split point
    reconstructable, and the synthetic id embeds it too.
  * **MCQA** (``split="MCQA"``): each sample instead carries
    ``"question": str`` (a FIXED meta-question, e.g. "What would be the most
    appropriate conclusion based on the given context?" — not itself a
    provable proposition; see :func:`solve_example`), ``"choices": dict``
    (``"choice_1"``, … — 4 or 5 entries depending on the file, verified) and
    ``"answer": str`` (verified, in every real Eval MCQA file, to always be
    a key of that SAME sample's ``choices``). One :class:`DatasetExample`
    per sample. ``choices`` survives verbatim in ``meta["choices"]``.

Field mapping (either split): ``nl_premises = (context,)``, ``nl_conclusion``
= the question text, ``label`` = the answer — ``"yes"``/``"no"`` verbatim
for BQA, the chosen ``"choice_N"`` key verbatim for MCQA. Kept AS-IS, not
smoothed into FraCaS's yes/no/unknown three-way scale: a binary
question-answering task and a 4-or-5-way multiple choice are different task
shapes, and forcing one vocabulary onto both would invent structure that is
not in the data. ``fol_premises = ()`` and ``fol_conclusion = None``
always — see "Honest limitations".

Honest limitations
-------------------
* No gold FOL anywhere in the source, so — exactly as for
  :mod:`~unicode_logic_kit.eval.datasets.fracas` —
  :func:`~unicode_logic_kit.eval.datasets.audit_examples` is vacuous on every
  LogicBench example (nothing to audit), and deciding one needs an
  externally injected translation.
* **MCQA rows are not decided by this module at all.** ``"question"`` in an
  MCQA sample is a generic meta-question ("What would be the most
  appropriate conclusion...?"), not a standalone proposition — there is
  nothing there for a prover to prove or refute. :func:`solve_example`
  refuses every MCQA row by name rather than silently running
  ``api.prove`` on a sentence that was never meant to be one; a caller who
  wants to score MCQA has to translate one of ``example.meta["choices"]``
  itself and decide it directly. Consequently the DISTRACTOR choices are
  never logic-checked by this adapter at all, chosen or not.
* **The non-monotonic route is a real, narrow fragment, not a general
  solver.** :mod:`~unicode_logic_kit.semantics.nonmonotonic`'s
  ``minimal_models``/``minimal_entails`` implement circumscription with
  every predicate either CIRCUMSCRIBED (minimised) or FIXED — there is no
  third "varied" category (that module's own ``circumscription_formula``
  explicitly leaves it unimplemented). A translation that leaves an
  "abnormality" predicate free for some individual (rather than pinning it
  with an explicit ground fact, positive or negative) will generally admit
  several incomparable minimal models that DISAGREE on the goal.
  :func:`solve_example` does **not** detect that disagreement and does
  **not** refuse it: ``minimal_entails`` only ever returns a bool, with no
  way to report that its minimal models disagree, so the route falls
  through to that bool's own SKEPTICAL reading — "yes" iff the goal holds
  in *every* minimal model found, "no" otherwise — and reports it exactly
  like any other answer, with no flag that several readings were possible.
  That skeptical bool is a real, well-defined answer to a real, precisely
  bounded question (minimal-model entailment up to ``max_size``), not a
  guess or an approximation of one — but it is only as trustworthy as the
  translation's discipline in pinning every abnormality predicate with an
  explicit ground fact for every named individual; a translation that
  skips one gets a confident-looking "yes"/"no" out of this route with no
  signal that the question was underspecified. The ONE case this route
  does detect and refuse is the *empty* minimal-model set (see
  :func:`solve_example`'s own docstring) — genuinely unsatisfiable
  premises, or a search bound that is simply too small.

License
-------
The roadmap build spec that requested this adapter named CC BY 4.0. That is
WRONG for this repository: the cloned ``LogicBench`` repository's
``LICENSE`` file is the plain MIT License (``Copyright (c) 2024 Mihir``),
and its ``README.md`` states "**Licence:** MIT License" directly under its
"Data Release" heading — both read directly, 2026-09-17.
:data:`~unicode_logic_kit.eval.datasets.DATASET_INFO` records MIT, not the
spec's CC BY 4.0.
"""

import json
from pathlib import Path
from typing import Callable, FrozenSet, Iterator, Optional, Set, Union

from ._base import DatasetExample, _register_dataset_info
from ...semantics.modelfinder import MAX_CANDIDATES

__all__ = ["load_logicbench", "solve_example", "LOGIC_TYPES", "NM_LOGIC_TYPE"]


#: The three ``"type"`` values a real LogicBench(Eval) file carries — see the
#: module docstring for why the non-monotonic one is NOT the string
#: ``"nm_logic"`` despite that being the directory name upstream.
LOGIC_TYPES = ("propositional_logic", "first_order_logic", "non_monotonic_logic")

#: The ``"type"`` value :func:`solve_example` routes through
#: :mod:`~unicode_logic_kit.semantics.nonmonotonic` instead of ``api.prove``.
NM_LOGIC_TYPE = "non_monotonic_logic"

_CLASSICAL_LOGIC_TYPES = frozenset(LOGIC_TYPES) - {NM_LOGIC_TYPE}
_SPLITS = ("BQA", "MCQA")
_BQA_ANSWERS = frozenset({"yes", "no"})


_register_dataset_info(
    "logicbench",
    license=("MIT License (the repository's own LICENSE file and its "
             "README's 'Licence: MIT License' agree; verified 2026-09-17 — "
             "NOT CC BY 4.0, which is what an earlier, unverified roadmap "
             "entry for this adapter had assumed)"),
    source_url="https://github.com/Mihir3009/LogicBench",
    citation_hint=('Parmar, Patel, Varshney, Nakamura, Luo, Mashetty, Mitra, '
                   'Baral, "Towards Systematic Evaluation of Logical '
                   'Reasoning Ability of Large Language Models", 2024, '
                   'arXiv:2404.15522.'),
)


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------

def load_logicbench(path: Union[str, Path], *, split: str,
                    known_bad_ids: FrozenSet[str] = frozenset(),
                    ) -> Iterator[DatasetExample]:
    """Read one LogicBench(Eval) ``data_instances.json`` into
    :class:`DatasetExample` objects, in file order.

    See the module docstring for the field mapping and the BQA
    qa_pairs-flattening this loader does. ``split`` must be ``"BQA"`` or
    ``"MCQA"`` and must match the file's ACTUAL sample shape — a BQA sample
    without ``qa_pairs`` (or an MCQA sample without ``question``/``choices``)
    is refused by name rather than silently misread, so passing the wrong
    ``split`` for a file cannot produce garbage examples.

    Args:
        path: the local ``data_instances.json`` (one axiom, one logic type,
            one of BQA/MCQA).
        split: ``"BQA"`` or ``"MCQA"`` — which of LogicBench(Eval)'s two
            task shapes this file holds.
        known_bad_ids: ids (in this adapter's own prefixed form, e.g.
            ``"logicbench:BQA:propositional_logic:modus_tollens:1:0"``) to
            flag as ``known_bad`` — the same caller-curated mechanic every
            adapter has.

    Raises:
        ValueError: ``split`` is not one of ``"BQA"``/``"MCQA"``, the file
            is missing ``type``/``axiom``/``samples``, ``type`` is outside
            :data:`LOGIC_TYPES`, a sample id repeats, a BQA sample has no
            ``qa_pairs`` (or an answer outside ``{"yes", "no"}``), or an
            MCQA sample has no ``question``/``choices`` (or an ``answer``
            that is not itself a key of its own ``choices``) — every
            malformed-input case is named, never worked around.
    """
    if split not in _SPLITS:
        raise ValueError(
            f"logicbench: split must be one of {_SPLITS}, got {split!r}")

    with open(path, encoding="utf-8") as f:
        data = json.load(f)

    if not isinstance(data, dict) or not {"type", "axiom", "samples"} <= data.keys():
        raise ValueError(
            f"logicbench: {path} is missing 'type'/'axiom'/'samples' — is "
            "this a LogicBench(Eval) data_instances.json?")

    logic_type = data["type"]
    if logic_type not in LOGIC_TYPES:
        raise ValueError(
            f"logicbench: {path} has type={logic_type!r}, outside "
            f"{list(LOGIC_TYPES)}")
    axiom = data["axiom"]
    if not axiom:
        raise ValueError(f"logicbench: {path} has an empty 'axiom'")

    samples = data["samples"]
    if not isinstance(samples, list):
        raise ValueError(f"logicbench: {path}: 'samples' is not a list")

    seen_sample_ids: Set = set()
    for sample in samples:
        sample_id = sample.get("id")
        if sample_id is None:
            raise ValueError(f"logicbench: {path}: a sample has no 'id'")
        if sample_id in seen_sample_ids:
            raise ValueError(
                f"logicbench: {path}: duplicate sample id {sample_id!r}")
        seen_sample_ids.add(sample_id)

        context = sample.get("context")
        if not context:
            raise ValueError(
                f"logicbench: {path}: sample {sample_id} has an empty "
                "'context'")

        base_meta = {"axiom": axiom, "logic_type": logic_type, "task": split,
                    "sample_id": sample_id}

        if split == "BQA":
            qa_pairs = sample.get("qa_pairs")
            if not qa_pairs:
                raise ValueError(
                    f"logicbench: {path}: sample {sample_id} has no "
                    "'qa_pairs' — is split='BQA' correct for this file?")
            for qa_index, qa in enumerate(qa_pairs):
                question = qa.get("question")
                answer = qa.get("answer")
                if not question:
                    raise ValueError(
                        f"logicbench: {path}: sample {sample_id} "
                        f"qa_pairs[{qa_index}] has no 'question'")
                if answer not in _BQA_ANSWERS:
                    raise ValueError(
                        f"logicbench: {path}: sample {sample_id} "
                        f"qa_pairs[{qa_index}] has answer={answer!r}, "
                        f"outside {sorted(_BQA_ANSWERS)}")
                example_id = (f"logicbench:BQA:{logic_type}:{axiom}:"
                             f"{sample_id}:{qa_index}")
                yield DatasetExample(
                    id=example_id,
                    nl_premises=(context,),
                    fol_premises=(),
                    nl_conclusion=question,
                    fol_conclusion=None,
                    label=answer,
                    known_bad=example_id in known_bad_ids,
                    meta=dict(base_meta, qa_index=qa_index),
                )
        else:                                        # "MCQA"
            question = sample.get("question")
            choices = sample.get("choices")
            answer = sample.get("answer")
            if not question:
                raise ValueError(
                    f"logicbench: {path}: sample {sample_id} has no "
                    "'question' — is split='MCQA' correct for this file?")
            if not isinstance(choices, dict) or not choices:
                raise ValueError(
                    f"logicbench: {path}: sample {sample_id} has no "
                    "'choices' dict")
            if answer not in choices:
                raise ValueError(
                    f"logicbench: {path}: sample {sample_id} has "
                    f"answer={answer!r}, not a key of its own 'choices' "
                    f"{sorted(choices)}")
            example_id = f"logicbench:MCQA:{logic_type}:{axiom}:{sample_id}"
            yield DatasetExample(
                id=example_id,
                nl_premises=(context,),
                fol_premises=(),
                nl_conclusion=question,
                fol_conclusion=None,
                label=answer,
                known_bad=example_id in known_bad_ids,
                meta=dict(base_meta, choices=dict(choices)),
            )


# ---------------------------------------------------------------------------
# Deciding — with the translation injected by the caller
# ---------------------------------------------------------------------------

def solve_example(example: DatasetExample, *, translate: Callable[[str], object],
                  circumscribed: Optional[Set] = None,
                  max_size: int = 4, max_candidates: int = MAX_CANDIDATES,
                  **prove_kwargs) -> dict:
    """Decide one LogicBench BQA row end-to-end — the translation is YOURS.

    LogicBench ships no formulas, so this helper takes ``translate``: a
    callable mapping one natural-language sentence to either a formula
    string (parsed with :func:`unicode_logic_kit.api.parse_any`) or an
    already-built kit node — the same seam
    :func:`~unicode_logic_kit.eval.datasets.fracas.solve_example` uses. This
    package calls no LLM and no external system itself.

    Routing is on ``example.meta["logic_type"]``:

    * :data:`NM_LOGIC_TYPE` (``"non_monotonic_logic"``): decided via
      :func:`unicode_logic_kit.semantics.nonmonotonic.minimal_entails` —
      ``circumscribed`` (``None`` minimises every predicate in the
      translated theory, matching that module's own default reading),
      ``max_size`` and ``max_candidates`` reach it verbatim. Before trusting
      the answer, this function ALSO calls
      :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models`
      directly and checks it is non-empty: ``minimal_entails`` returns
      ``True`` VACUOUSLY when no minimal model exists within the bound
      (nothing to check the conclusion against — for-loop over an empty
      list), which would silently misreport either genuinely unsatisfiable
      premises or a search bound that is simply too small as a confident
      "yes". Finding no minimal model raises instead, naming the reason,
      rather than ever returning that vacuous "yes". This is the ONLY
      case this route detects and refuses: a translation that leaves an
      abnormality predicate's value free for some individual (instead of
      pinning it, positive or negative, with an explicit ground fact) will
      typically produce several incomparable minimal models that DISAGREE
      on the goal rather than an empty set, so it is NOT caught here —
      :func:`minimal_entails` only ever returns a bool, with no way to
      report that its minimal models disagree, so this function silently
      reports that bool's own skeptical reading ("yes" iff the goal holds
      in every minimal model found) with no signal that several readings
      were possible. See the module docstring's "Honest limitations"
      section for the discipline a translation needs (an explicit ground
      fact for every abnormality predicate application) to avoid that
      silent case.
    * :data:`~unicode_logic_kit.eval.datasets.logicbench.LOGIC_TYPES`'s other
      two values (``"propositional_logic"``, ``"first_order_logic"``):
      decided via :func:`unicode_logic_kit.api.prove` — ``"yes"`` iff PROVED,
      ``"no"`` iff REFUTED (a genuine countermodel, not merely "could not
      prove"), and ``predicted=None`` on an inconclusive UNKNOWN verdict:
      LogicBench's label vocabulary is only ``{"yes", "no"}``, so — unlike
      FraCaS, whose own three-way scale has an ``"unknown"`` label to fall
      back on — forcing an indefinite prover outcome into either binary
      label would invent an answer LogicBench never asked for. Extra
      ``prove_kwargs`` reach :func:`unicode_logic_kit.api.prove` verbatim (and
      are IGNORED on a non-monotonic-logic row — that route takes
      ``circumscribed``/``max_size``/``max_candidates`` instead).

    Only decides BQA rows. An MCQA row's ``nl_conclusion`` is a generic
    meta-question, not a standalone proposition (see the module docstring),
    so this function refuses it by name instead of running a prover on a
    sentence that was never meant to be one.

    Returns a dict with ``predicted`` (``"yes"``/``"no"``/``None``),
    ``label`` (the gold answer, untouched — scoring against it is the
    caller's decision), ``route`` (``"classical"``/``"nonmonotonic"``), the
    translated ``premises``/``hypothesis`` in kit notation (so a wrong
    prediction can be traced back to the translation that caused it), and
    either ``verdict`` (the classical route's full
    :class:`~unicode_logic_kit.atp.protocol.Verdict` dict) or
    ``minimal_model_count`` (the non-monotonic route's model count).

    Raises:
        ValueError: ``example`` is an MCQA row, its ``logic_type`` is
            outside :data:`LOGIC_TYPES`, a translated string does not parse,
            or (non-monotonic route only) no minimal model of the
            translated premises was found within ``max_size``.
    """
    from ... import api
    from ...fol.nodes import Node
    from ...semantics.nonmonotonic import minimal_entails, minimal_models

    if example.meta.get("task") != "BQA":
        raise ValueError(
            f"logicbench: example {example.id}: solve_example only decides "
            "BQA rows — an MCQA row's 'question' field is a generic "
            "meta-question ('What would be the most appropriate "
            "conclusion...?'), not a standalone provable proposition; "
            "translate one of example.meta['choices'] yourself and decide "
            "it directly instead.")

    def _formula(sentence: str) -> "Node":
        produced = translate(sentence)
        if isinstance(produced, Node):
            return produced
        if not isinstance(produced, str):
            raise ValueError(
                f"logicbench: example {example.id}: translate({sentence!r}) "
                f"returned {type(produced).__name__}, expected a formula "
                "string or a kit node")
        parsed = api.parse_any(produced)
        if not parsed.ok:
            raise ValueError(
                f"logicbench: example {example.id}: the translation "
                f"{produced!r} of {sentence!r} does not parse")
        return parsed.formula

    premises = [_formula(sentence) for sentence in example.nl_premises]
    hypothesis = _formula(example.nl_conclusion)

    result = {
        "label": example.label,
        "premises": [p.to_unicode_str() for p in premises],
        "hypothesis": hypothesis.to_unicode_str(),
    }

    logic_type = example.meta.get("logic_type")
    if logic_type == NM_LOGIC_TYPE:
        found = minimal_models(premises, circumscribed, max_size=max_size,
                               max_candidates=max_candidates,
                               extra_signature=[hypothesis])
        if not found:
            raise ValueError(
                f"logicbench: example {example.id}: "
                "semantics.nonmonotonic found NO minimal model of the "
                f"translated premises within max_size={max_size} — this "
                "route refuses rather than trust minimal_entails's vacuous "
                "'True' for an empty model set (which could mean the "
                "premises are unsatisfiable, or just that the bound is too "
                "small to tell). Widen max_size, or check the translation.")
        entailed = minimal_entails(premises, hypothesis, circumscribed,
                                   max_size=max_size,
                                   max_candidates=max_candidates)
        result.update(predicted=("yes" if entailed else "no"),
                     route="nonmonotonic", minimal_model_count=len(found))
        return result

    if logic_type not in _CLASSICAL_LOGIC_TYPES:
        raise ValueError(
            f"logicbench: example {example.id}: unsupported "
            f"logic_type {logic_type!r} — solve_example decides "
            f"{sorted(_CLASSICAL_LOGIC_TYPES)} via api.prove and "
            f"{NM_LOGIC_TYPE!r} via semantics.nonmonotonic, nothing else.")

    verdict = api.prove(hypothesis, premises, **prove_kwargs)
    if verdict.status == "proved":
        predicted: Optional[str] = "yes"
    elif verdict.status == "refuted":
        predicted = "no"
    else:                                            # "unknown"
        predicted = None
    result.update(predicted=predicted, route="classical",
                  verdict=verdict.to_dict())
    return result
