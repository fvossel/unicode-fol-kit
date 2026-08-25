"""Adapter for the FraCaS textual-inference problem set — pure NLI, no FOL.

Every other adapter in this package carries gold FOL (or generates it from a
structured source). FraCaS carries NONE, by construction: its problems are
natural-language premises plus a hypothesis and a three-valued answer, and
there is no logic field anywhere in its DTD. That is exactly why it earns a
place here — the kit's entailment verdict is three-valued too, so FraCaS's
``yes``/``no``/``unknown`` maps onto ``premises ⊨ h`` / ``premises ⊨ ¬h`` /
neither WITHOUT any interpretive glue, which makes it a reference target for
an NL→logic pipeline whose translation step lives OUTSIDE this library (see
:func:`solve_example`: the translation is an injected callable, never a
model this package calls).

Source and verified schema
---------------------------
Verified 2026-08-19 directly against the canonical machine-readable edition,
``https://nlp.stanford.edu/~wcmac/downloads/fracas.xml`` (XML conversion by
Bill MacCartney of the FraCaS Consortium's 1996 deliverable "Using the
Framework", Cooper et al.). Like every loader in this package it reads a
LOCAL file the caller already obtained — nothing here downloads anything.

The file's own header documents the representation; the numbers below are
this adapter's independent re-measurement of the file it parses:

* **346 problems**, ids ``"001"`` … ``"346"``, unique, zero-padded to three
  digits (this adapter prefixes them: ``"fracas:001"``).
* **536 premises**, as ``<p idx="n">`` children — verified contiguous and
  1-based in every problem (192 problems have one premise, 122 two, 29
  three, 2 four, 1 five). Read in ``idx`` order, not document order.
* ``<q>`` the original question, ``<h>`` the declarative hypothesis, ``<a>``
  the source document's answer text (``"Yes"``, ``"Don't know"``, but also
  qualified phrases like ``"Not many"``), optional ``<why>`` (110) and
  ``<note>`` (33).
* ``fracas_answer`` ∈ ``yes`` (203) / ``unknown`` (98) / ``no`` (33) /
  ``undef`` (12) — the canonicalisation of ``<a>``; this is the ``label``.
* ``fracas_nonstandard="true"`` on the 41 problems whose ``<a>`` is not one
  of the three canonical answers.
* Sections are NOT attributes: they are ``<comment class="section">`` /
  ``"subsection"`` / ``"subsubsection"`` markers between problems (9 / 47 /
  10 of them), so section membership is DOCUMENT ORDER. This adapter tracks
  them as it walks and resets the finer levels whenever a coarser one
  changes — a problem can therefore never inherit a stale subsection from
  the previous section.

Honest limitations
-------------------
* **Four problems (276, 305, 309, 310) have an EMPTY ``<q>`` and ``<h>``** —
  the source document has no question for them. They load (nothing is
  dropped silently) with ``nl_conclusion=None`` and are refused by
  :func:`solve_example` with a named error rather than scored against an
  absent hypothesis. All four are also ``undef``.
* **``undef`` is not a fourth answer class**, it marks a problem whose
  source answer is not canonicalisable at all. Such examples load with
  ``label="undef"``; :func:`solve_example` will still PREDICT for the eight
  of them that have a hypothesis (predicting is not scoring), and the caller
  is expected to exclude them from any accuracy figure.
* ``fol_premises`` is always empty and ``fol_conclusion`` always ``None``:
  there is no gold FOL to audit, so
  :func:`~unicode_fol_kit.eval.datasets.audit_examples` reports these
  examples as ``ok`` VACUOUSLY. That is not a claim about the data.
* The answer text in ``<a>`` is kept verbatim in ``meta["answer_text"]``,
  including the qualified ones — canonicalising them further would be this
  adapter inventing gold labels.
"""

import re
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import (
    Callable, Dict, FrozenSet, Iterable, Iterator, List, Optional, Union,
)

from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_fracas", "solve_example", "ace_census", "FRACAS_ANSWERS"]


#: The canonical values of the ``fracas_answer`` attribute. ``undef`` is a
#: "no canonical answer exists" marker, not a fourth answer — see the module
#: docstring.
FRACAS_ANSWERS = ("yes", "no", "unknown", "undef")

_SECTION_LEVELS = ("section", "subsection", "subsubsection")
_HEADING_RE = re.compile(r"^([\d.]+)\s+(.*)$", re.DOTALL)


_register_dataset_info(
    "fracas",
    license=("no explicit licence statement in the source file; the XML "
             "edition asks for credit for the conversion, and the problems "
             "derive from the FraCaS Consortium's 1996 deliverable"),
    source_url="https://nlp.stanford.edu/~wcmac/downloads/fracas.xml",
    citation_hint=('FraCaS Consortium (Cooper et al.), "Using the '
                   'Framework", 1996; XML edition by Bill MacCartney.'),
)


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------

def _text(element: Optional[ET.Element]) -> Optional[str]:
    """Element text with XML indentation collapsed — ``None`` when absent or
    empty (the four question-less problems), never the empty string."""
    if element is None or element.text is None:
        return None
    collapsed = " ".join(element.text.split())
    return collapsed or None


def _heading(raw: Optional[str]) -> Dict[str, Optional[str]]:
    """``"1.2 Monotonicity (…)"`` → number and title, kept separate so a
    caller filters on the STABLE number rather than on prose."""
    if raw is None:
        return {"number": None, "title": None}
    match = _HEADING_RE.match(raw)
    if match is None:
        return {"number": None, "title": raw}
    return {"number": match.group(1), "title": " ".join(match.group(2).split())}


def _premises(problem: ET.Element) -> List[str]:
    """The ``<p>`` texts in ``idx`` order, with the ordering CHECKED: the
    file's indices are contiguous and 1-based throughout, so anything else
    is a corrupted input and says so instead of being silently reordered."""
    numbered = []
    for element in problem.findall("p"):
        raw_idx = element.get("idx")
        if raw_idx is None or not raw_idx.isdigit():
            raise ValueError(
                f"fracas: problem {problem.get('id')!r} has a <p> without a "
                f"numeric idx (got {raw_idx!r})")
        text = _text(element)
        if text is None:
            raise ValueError(
                f"fracas: problem {problem.get('id')!r} has an empty premise "
                f"at idx {raw_idx}")
        numbered.append((int(raw_idx), text))
    numbered.sort()
    if [i for i, _ in numbered] != list(range(1, len(numbered) + 1)):
        raise ValueError(
            f"fracas: problem {problem.get('id')!r} has non-contiguous "
            f"premise indices {[i for i, _ in numbered]}")
    return [text for _, text in numbered]


def load_fracas(path: Union[str, Path], *,
                sections: Optional[Iterable[str]] = None,
                answers: Optional[Iterable[str]] = None,
                known_bad_ids: FrozenSet[str] = frozenset(),
                ) -> Iterator[DatasetExample]:
    """Read the FraCaS XML into :class:`DatasetExample` objects, in file order.

    Field mapping (see the module docstring for what each source element is):
    ``nl_premises`` = the ``<p>`` texts in ``idx`` order, ``nl_conclusion`` =
    ``<h>`` (``None`` for the four question-less problems), ``label`` =
    ``fracas_answer``, and ``fol_premises``/``fol_conclusion`` stay empty —
    FraCaS has no logic annotation. Everything else from the record survives
    in ``meta``: ``question``, ``answer_text``, ``why``, ``note``,
    ``nonstandard``, ``premise_count``, and the section / subsection /
    subsubsection numbers and titles.

    Args:
        path: the local ``fracas.xml``.
        sections: keep only problems in these SECTION NUMBERS (``{"1", "3"}``
            — the stable identifier, matched against the top-level section,
            so ``"1"`` keeps all of ``1.x``). ``None`` keeps everything.
        answers: keep only these ``fracas_answer`` values (e.g.
            ``{"yes", "no", "unknown"}`` to drop the twelve ``undef``
            problems). ``None`` keeps everything, ``undef`` included — this
            loader never drops them on its own.
        known_bad_ids: ids (in the prefixed ``"fracas:001"`` form) to flag as
            ``known_bad``; the same caller-curated mechanic every adapter has.

    Raises:
        ValueError: the file is not a FraCaS problem set, a problem lacks its
            id or ``fracas_answer``, an answer is outside
            :data:`FRACAS_ANSWERS`, ids repeat, or premise indices are not
            contiguous — a malformed input is named, never worked around.
    """
    wanted_sections = None if sections is None else {str(s) for s in sections}
    wanted_answers = None if answers is None else {str(a) for a in answers}
    if wanted_answers is not None:
        unknown = wanted_answers - set(FRACAS_ANSWERS)
        if unknown:
            raise ValueError(
                f"fracas: answers={sorted(unknown)} is outside "
                f"{list(FRACAS_ANSWERS)}")

    root = ET.parse(str(path)).getroot()
    if root.tag != "fracas-problems":
        raise ValueError(
            f"fracas: {path} has root element {root.tag!r}, expected "
            "'fracas-problems' — is this the FraCaS XML?")

    headings: Dict[str, Dict[str, Optional[str]]] = {
        level: _heading(None) for level in _SECTION_LEVELS}
    seen = set()

    for element in root:
        if element.tag == "comment":
            level = element.get("class")
            if level in _SECTION_LEVELS:
                headings[level] = _heading(_text(element))
                # A coarser heading invalidates every finer one, so a
                # problem can never inherit a stale subsection.
                for finer in _SECTION_LEVELS[_SECTION_LEVELS.index(level) + 1:]:
                    headings[finer] = _heading(None)
            continue
        if element.tag != "problem":
            continue

        raw_id = element.get("id")
        if not raw_id:
            raise ValueError("fracas: a <problem> element has no id")
        example_id = f"fracas:{raw_id}"
        if example_id in seen:
            raise ValueError(f"fracas: duplicate problem id {raw_id!r}")
        seen.add(example_id)

        answer = element.get("fracas_answer")
        if answer is None:
            raise ValueError(
                f"fracas: problem {raw_id!r} has no fracas_answer attribute")
        if answer not in FRACAS_ANSWERS:
            raise ValueError(
                f"fracas: problem {raw_id!r} has fracas_answer {answer!r}, "
                f"outside {list(FRACAS_ANSWERS)}")

        if (wanted_sections is not None
                and headings["section"]["number"] not in wanted_sections):
            continue
        if wanted_answers is not None and answer not in wanted_answers:
            continue

        premises = _premises(element)
        meta = {
            "question": _text(element.find("q")),
            "answer_text": _text(element.find("a")),
            "why": _text(element.find("why")),
            "note": _text(element.find("note")),
            "nonstandard": element.get("fracas_nonstandard") == "true",
            "premise_count": len(premises),
        }
        for level in _SECTION_LEVELS:
            meta[level] = headings[level]["number"]
            meta[f"{level}_title"] = headings[level]["title"]

        yield DatasetExample(
            id=example_id,
            nl_premises=tuple(premises),
            fol_premises=(),
            nl_conclusion=_text(element.find("h")),
            fol_conclusion=None,
            label=answer,
            known_bad=example_id in known_bad_ids,
            meta=meta,
        )


# ---------------------------------------------------------------------------
# Deciding — with the translation injected by the caller
# ---------------------------------------------------------------------------

def solve_example(example: DatasetExample, *,
                  translate: Callable[[str], object],
                  on_indefinite: str = "label", **prove_kwargs) -> dict:
    """Decide one FraCaS problem end-to-end — the translation is YOURS.

    FraCaS ships no formulas, so this helper takes ``translate``: a callable
    mapping one natural-language sentence to either a formula string (parsed
    with :func:`unicode_fol_kit.api.parse_any`) or an already-built kit node.
    That is the seam where an external system — a semantic parser, a
    hand-written table, a language model driven by the caller — plugs in;
    this package deliberately calls no such system itself.

    The rest is the same three-valued cascade the other adapters use, and it
    matches FraCaS's own answer semantics exactly: ``"yes"`` iff premises ⊨
    hypothesis, ``"no"`` iff premises ⊨ ¬hypothesis, ``"unknown"`` otherwise.
    Extra ``prove_kwargs`` reach :func:`unicode_fol_kit.api.prove` verbatim,
    so the prover is the caller's choice.

    ``on_indefinite`` handles a NON-DEFINITIVE prover outcome (timeout, hit
    bound, honest incompleteness) when neither direction was proved:

    - ``"label"`` (default): predict ``"unknown"``.
    - ``"abstain"``: ``"unknown"`` only when BOTH directions came back
      definitively refuted (underdetermination established by countermodels);
      any indefinite leg yields ``predicted=None``, so a timeout can never be
      scored as a correct "unknown".
    - ``"raise"``: like ``"abstain"`` but raises instead.

    Returns a dict with ``predicted`` (``"yes"``/``"no"``/``"unknown"``/
    ``None``), ``label`` (the gold answer, ``"undef"`` included — scoring
    against it is the caller's decision), ``verdict``/``verdict_negated``
    (verdict dicts; the negated one is ``None`` when the positive direction
    already settled it), and the translated ``premises``/``hypothesis`` in
    kit notation, so a wrong prediction can be traced back to the
    translation that caused it.

    Raises:
        ValueError: the example has no hypothesis (the four question-less
            problems), ``on_indefinite`` is not one of the three modes, or a
            translated string does not parse.
    """
    from ... import api
    from ...fol.nodes import Node, Not

    if on_indefinite not in ("label", "abstain", "raise"):
        raise ValueError(
            f"fracas: on_indefinite must be 'label', 'abstain' or 'raise', "
            f"got {on_indefinite!r}")
    if example.nl_conclusion is None:
        raise ValueError(
            f"fracas: example {example.id} has no hypothesis (the source "
            "document has no question for it) — nothing to decide.")

    def _formula(sentence: str) -> "Node":
        produced = translate(sentence)
        if isinstance(produced, Node):
            return produced
        if not isinstance(produced, str):
            raise ValueError(
                f"fracas: example {example.id}: translate({sentence!r}) "
                f"returned {type(produced).__name__}, expected a formula "
                "string or a kit node")
        parsed = api.parse_any(produced)
        if not parsed.ok:
            raise ValueError(
                f"fracas: example {example.id}: the translation "
                f"{produced!r} of {sentence!r} does not parse")
        return parsed.formula

    premises = [_formula(sentence) for sentence in example.nl_premises]
    hypothesis = _formula(example.nl_conclusion)

    result = {
        "label": example.label,
        "premises": [p.to_unicode_str() for p in premises],
        "hypothesis": hypothesis.to_unicode_str(),
    }
    verdict = api.prove(hypothesis, premises, **prove_kwargs)
    if verdict.status == "proved":
        result.update(predicted="yes", verdict=verdict.to_dict(),
                      verdict_negated=None)
        return result

    negated = api.prove(Not(hypothesis), premises, **prove_kwargs)
    if negated.status == "proved":
        predicted: Optional[str] = "no"
    elif on_indefinite == "label":
        predicted = "unknown"
    elif verdict.status == "refuted" and negated.status == "refuted":
        # Underdetermination ESTABLISHED both ways: "unknown" is a definitive
        # answer here, so even abstain/raise report it.
        predicted = "unknown"
    elif on_indefinite == "raise":
        raise ValueError(
            f"fracas: example {example.id}: indefinite prover outcome "
            f"(goal: {verdict.status}/{verdict.reason}, negated: "
            f"{negated.status}/{negated.reason}) with on_indefinite='raise'.")
    else:                                        # "abstain"
        predicted = None

    result.update(predicted=predicted, verdict=verdict.to_dict(),
                  verdict_negated=negated.to_dict())
    return result


# ---------------------------------------------------------------------------
# How much of it is controlled English?
# ---------------------------------------------------------------------------

def ace_census(examples: Iterable[DatasetExample], *,
               ulex: Optional[str] = None, timeout: float = 30.0,
               ) -> List[dict]:
    """Per-SENTENCE report: which FraCaS sentences does APE accept as ACE?

    A measurement, not a score. FraCaS is short, deliberately plain English,
    so it is the natural corpus for asking how far Attempto Controlled
    English reaches as a target notation — and the answer comes per
    sentence, with APE's own diagnosis attached, never as a single aggregate
    this function decides for you (group the rows by ``section`` yourself).

    Needs a reachable APE binary
    (:func:`unicode_fol_kit.ace.ape_available`); ``ulex`` is passed through
    as APE's user lexicon, which matters because APE's built-in lexicon is
    small and a missing word is reported as "not ACE" like any other
    refusal.

    Returns one dict per sentence, in example order: ``id``, ``section``,
    ``role`` (``"premise"``/``"hypothesis"``), ``index`` (position within the
    premises, ``None`` for the hypothesis), ``sentence``, ``status``
    (:class:`~unicode_fol_kit.ace.runner.CoverageRow`'s vocabulary:
    ``ok``/``tptp_unsupported``/``tptp_unread``/``not_ace``/``infra``) and
    ``detail``.
    """
    from ...ace import ace_coverage

    rows: List[dict] = []
    for example in examples:
        sentences = [("premise", i, s)
                     for i, s in enumerate(example.nl_premises)]
        if example.nl_conclusion is not None:
            sentences.append(("hypothesis", None, example.nl_conclusion))
        coverage = ace_coverage([s for _, _, s in sentences],
                                ulex=ulex, timeout=timeout)
        for (role, index, sentence), row in zip(sentences, coverage):
            rows.append({
                "id": example.id,
                "section": example.meta.get("section"),
                "role": role,
                "index": index,
                "sentence": sentence,
                "status": row.status,
                "detail": row.detail,
            })
    return rows
