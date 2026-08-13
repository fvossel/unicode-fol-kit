"""Shared infrastructure for NL/FOL dataset adapters (:mod:`folio`, :mod:`malls`).

This module defines the one example shape every dataset adapter normalises
into (:class:`DatasetExample`), a small provenance registry
(:data:`DATASET_INFO`), and the self-audit mechanic (:func:`audit_examples`)
that a caller uses to find defective *gold* formulas in a dataset BEFORE
trusting them as an evaluation reference — an LLM-authored or crowd-annotated
FOL string can itself be unparseable or ill-formed, and treating it as ground
truth without checking would silently corrupt every metric computed against
it.

Design notes:

* :class:`DatasetExample` is deliberately dataset-agnostic: FOLIO's
  premises/conclusion/label entailment shape and MALLS's single
  NL-statement/FOL-formula translation pairs both fit the same fields (see
  each adapter module's docstring for its exact field mapping).
* Parsing is LAZY and never raises: :meth:`DatasetExample.parse_premises` /
  :meth:`DatasetExample.parse_conclusion` call
  :func:`unicode_fol_kit.api.parse_any` only when invoked (loading a dataset
  of thousands of examples must not eagerly parse every one), and return
  :class:`~unicode_fol_kit.api.ParseResult` objects — a parse failure is
  reported, never swallowed or turned into an exception.
* ``known_bad`` is a CURATED flag an adapter sets from a caller-supplied
  ``known_bad_ids`` set (e.g. IDs a human or a prior audit run identified as
  having a broken gold annotation). It is independent of
  :func:`audit_examples`, which is the AUTOMATED detector: the two are meant
  to be cross-checked against each other, not conflated.
"""

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Dict, Iterable, List, Optional, Tuple

if TYPE_CHECKING:                                   # pragma: no cover - typing only
    from ...api import CheckResult, ParseResult

__all__ = ["DatasetExample", "DATASET_INFO", "audit_examples"]


# ---------------------------------------------------------------------------
# DatasetExample
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DatasetExample:
    """One normalised NL/FOL example from any adapter in this subpackage.

    Fields:
        id: a stable identifier. Adapters use the dataset's own ID field when
            the source data provides one, otherwise a positional fallback
            (documented per adapter) — never ``None``, so examples are always
            addressable (e.g. for ``known_bad_ids``).
        nl_premises: natural-language premise sentences, in source order.
            Empty for datasets with no premise/conclusion structure (e.g.
            MALLS — see its adapter module for the field-mapping rationale).
        fol_premises: the gold FOL premise strings, in the SAME order as
            ``nl_premises`` (index ``i`` of one corresponds to index ``i`` of
            the other). Left as raw strings, not parsed, until
            :meth:`parse_premises` is called.
        nl_conclusion / fol_conclusion: the natural-language / FOL conclusion
            (entailment datasets), or the single NL statement / FOL formula
            being translated (translation-pair datasets). ``None`` when the
            dataset has no conclusion slot at all.
        label: the gold entailment label (dataset-specific vocabulary, e.g.
            FOLIO's ``"True"``/``"False"``/``"Uncertain"``), or ``None`` for
            datasets without one (e.g. MALLS).
        known_bad: True iff this example's ``id`` was passed in the loader's
            ``known_bad_ids`` — a caller-curated "do not trust this gold
            annotation" flag, set at load time and never inferred here.
        meta: adapter-specific leftover fields from the source record (e.g.
            FOLIO's ``source``/``story-id``, or a synthetic-fixture marker),
            kept as a plain JSON-compatible dict so nothing from the original
            record is silently discarded.
    """

    id: str
    nl_premises: Tuple[str, ...]
    fol_premises: Tuple[str, ...]
    nl_conclusion: Optional[str]
    fol_conclusion: Optional[str]
    label: Optional[str]
    known_bad: bool
    meta: dict = field(default_factory=dict)

    def parse_premises(self) -> Tuple["ParseResult", ...]:
        """Parse every ``fol_premises`` string, lazily, in order.

        Uses :func:`unicode_fol_kit.api.parse_any` (dialect auto-detection);
        each element of the returned tuple is that call's
        :class:`~unicode_fol_kit.api.ParseResult` UNCHANGED — a parse failure
        shows up as ``ok=False`` with its ``errors``, never as an exception
        and never silently dropped.
        """
        from ... import api           # lazy: avoid import-time cost/cycles

        return tuple(api.parse_any(p) for p in self.fol_premises)

    def parse_conclusion(self) -> Optional["ParseResult"]:
        """Parse ``fol_conclusion``, lazily — ``None`` iff there is none.

        Returns the raw :class:`~unicode_fol_kit.api.ParseResult` (so a parse
        failure is visible via ``ok=False``/``errors``), or ``None`` when this
        example carries no conclusion/target formula at all (a different
        thing from a formula that failed to parse).
        """
        if self.fol_conclusion is None:
            return None
        from ... import api           # lazy: avoid import-time cost/cycles

        return api.parse_any(self.fol_conclusion)

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (all fields, names as keys)."""
        return {
            "id": self.id,
            "nl_premises": list(self.nl_premises),
            "fol_premises": list(self.fol_premises),
            "nl_conclusion": self.nl_conclusion,
            "fol_conclusion": self.fol_conclusion,
            "label": self.label,
            "known_bad": self.known_bad,
            "meta": self.meta,
        }


# ---------------------------------------------------------------------------
# Provenance registry
# ---------------------------------------------------------------------------

#: Dataset name -> provenance dict (``license``, ``source_url``,
#: ``citation_hint``). Populated by each adapter module at import time via
#: :func:`_register_dataset_info` so this dict never drifts from the loader
#: that actually claims to implement it. Verified against the primary sources
#: named in each adapter's module docstring — nothing here is guessed.
DATASET_INFO: Dict[str, dict] = {}


def _register_dataset_info(name: str, *, license: str, source_url: str,
                           citation_hint: str) -> None:
    """Record ``name``'s provenance in :data:`DATASET_INFO` (adapter-internal)."""
    DATASET_INFO[name] = {
        "license": license,
        "source_url": source_url,
        "citation_hint": citation_hint,
    }


# ---------------------------------------------------------------------------
# audit_examples — the self-audit mechanic
# ---------------------------------------------------------------------------

def _check_result_defects(check_result: "CheckResult", field_name: str,
                          index: Optional[int]) -> List[dict]:
    """Expand one failing :class:`~unicode_fol_kit.api.CheckResult` into
    per-aspect defect dicts (a formula can fail more than one aspect at once,
    e.g. an unbound variable AND an arity conflict, so this can return more
    than one entry for a single formula).
    """
    defects: List[dict] = []
    if not check_result.is_closed:
        defects.append({
            "kind": "free_variables", "field": field_name, "index": index,
            "detail": list(check_result.free_variables),
        })
    if not check_result.arity_consistent:
        defects.append({
            "kind": "arity_conflict", "field": field_name, "index": index,
            "detail": list(check_result.arity_conflicts),
        })
    if check_result.has_lambdas:
        defects.append({
            "kind": "residual_lambda", "field": field_name, "index": index,
            "detail": None,
        })
    return defects


def audit_examples(examples: Iterable[DatasetExample], *,
                   max_examples: Optional[int] = None) -> List[dict]:
    """Self-audit a batch of examples: which gold FOL strings are broken?

    This is the mechanic for finding defective gold annotations WITHOUT any
    external reference — it only requires that a gold formula (a) parses and
    (b) is well-formed (closed, arity-consistent, lambda-free), both of which
    :func:`unicode_fol_kit.api.parse_any` / :func:`unicode_fol_kit.api.check`
    can decide on their own. It does NOT check the entailment ``label``
    itself (that would need a prover run over the whole premise set, a
    heavier and separately-scoped operation).

    Args:
        examples: any iterable of :class:`DatasetExample` (a generator from a
            loader is fine — nothing here requires a materialised list).
        max_examples: stop after auditing this many examples (``None`` audits
            everything). Useful for a quick pass over a large dataset.

    Returns:
        A ``list[dict]``, one entry per audited example, in input order, each
        JSON-compatible:

        * ``id`` / ``known_bad``: copied from the example, for cross-checking
          the automated finding against any curated flag.
        * ``all_parsed``: True iff every ``fol_premises`` string and (if
          present) ``fol_conclusion`` parsed successfully — answers "parsen
          alle FOL-Strings?".
        * ``all_checked``: True iff every formula that DID parse also passed
          :func:`~unicode_fol_kit.api.check` (``check().ok``); vacuously True
          if nothing parsed. Independent of ``all_parsed`` — a formula that
          fails to parse contributes nothing here, only to ``all_parsed``.
        * ``ok``: ``all_parsed and all_checked`` — no defect of any kind.
        * ``defects``: the collected defect classes, each
          ``{"kind": ..., "field": "premises"|"conclusion", "index": int|None,
          "detail": ...}``. ``kind`` is one of ``"unparseable"``,
          ``"free_variables"``, ``"arity_conflict"``, ``"residual_lambda"``.
          ``index`` is the position within ``fol_premises`` for that field, or
          ``None`` for the (singular) conclusion.
    """
    from ... import api           # lazy: avoid import-time cost/cycles

    reports: List[dict] = []
    for i, example in enumerate(examples):
        if max_examples is not None and i >= max_examples:
            break

        defects: List[dict] = []
        all_parsed = True
        all_checked = True

        premise_results = example.parse_premises()
        for idx, pr in enumerate(premise_results):
            if not pr.ok:
                all_parsed = False
                message = pr.errors[-1]["message"] if pr.errors else "unparseable"
                defects.append({"kind": "unparseable", "field": "premises",
                                "index": idx, "detail": message})
                continue
            cr = api.check(pr.formula)
            if not cr.ok:
                all_checked = False
                defects.extend(_check_result_defects(cr, "premises", idx))

        conclusion_result = example.parse_conclusion()
        if conclusion_result is not None:
            if not conclusion_result.ok:
                all_parsed = False
                message = (conclusion_result.errors[-1]["message"]
                          if conclusion_result.errors else "unparseable")
                defects.append({"kind": "unparseable", "field": "conclusion",
                                "index": None, "detail": message})
            else:
                cr = api.check(conclusion_result.formula)
                if not cr.ok:
                    all_checked = False
                    defects.extend(_check_result_defects(cr, "conclusion", None))

        reports.append({
            "id": example.id,
            "known_bad": example.known_bad,
            "all_parsed": all_parsed,
            "all_checked": all_checked,
            "ok": all_parsed and all_checked,
            "defects": defects,
        })
    return reports
