"""Adapter for C3PO (CHEBI Chemical Classification Program Ontology
Benchmark, Mungall, Malik, Korn, Reese, O'Boyle & Hastings, "Chemical
classification program synthesis using generative artificial intelligence",
Journal of Cheminformatics, 2025, DOI 10.1186/s13321-025-01092-3) — local
JSONL only, no network access.

C3PO pairs each CHEBI class with its natural-language definition plus the
SMILES of molecules known to be members -- the shape any FOL formalisation
of chemical classes has to be evaluated against. Unlike every other adapter
in this subpackage, C3PO's gold is NOT a reference FOL formula to compare a
prediction against by parsing/structural-equality (there is no gold FOL
here at all — see "Honesty" below); it is an EXECUTABLE membership decision:
a molecule either is or is not in the class, decidable by MODEL CHECKING a
candidate FOL definition against the molecule as a
:class:`~unicode_fol_kit.semantics.structures.FiniteStructure`
(:func:`unicode_fol_kit.chem.mol_to_structure`). This module accordingly
ships two things: :func:`load_c3po` (the usual streaming loader) and
:func:`score_definition`, which runs that model-checking evaluation over a
positive/negative SMILES split and reports precision/recall/F1 — WITHOUT
silently folding a failed evaluation into "negative" (see its own docstring).

Source and verified schema
---------------------------
Source: https://huggingface.co/datasets/MonarchInit/C3PO (unauthenticated,
CC0-1.0). Verified directly, 2026-08-13:

* The HF dataset-viewer's queryable ``"default"``/``"train"`` config (via the
  ``datasets-server`` ``/first-rows`` API) exposes exactly the CLASSES table,
  9 flat fields, confirmed against real fetched rows (CHEBI:10036 "wax
  ester", CHEBI:131565 "steroid aldehyde") AND cross-checked against the
  ``ChemicalClass`` Pydantic model in the benchmark's own generator source,
  https://github.com/cmungall/c3p (``c3p/datamodel.py``, fetched directly),
  which agrees field-for-field:

  * ``"id"``                          -- ``str``, a CHEBI curie (e.g.
    ``"CHEBI:10036"``) -- globally unique, unlike FOLIO's/ProofWriter's
    grouping ids (see their modules' "Id resolution" notes) -- so this
    loader uses it directly as :attr:`DatasetExample.id`, no positional
    fallback scheme needed for the common case.
  * ``"name"``                        -- ``str``, the class's ``rdfs:label``.
  * ``"definition"``                  -- ``str``, the natural-language
    definition an FOL-formalisation system (an LLM, or a human) is
    asked to translate. THIS is what :func:`load_c3po` maps onto
    ``nl_conclusion`` -- see "Field mapping" below.
  * ``"parents"``                     -- list of parent-class CHEBI curies.
  * ``"xrefs"``                       -- list of cross-references to other
    databases (KEGG, MetaCyc, ...); absent for most classes (confirmed via
    the mirror's own column statistics: only 367 of 1364 classes carry any).
  * ``"all_positive_examples"``       -- list of SMILES strings: molecules
    CHEBI records as members of this class. THE gold used by
    :func:`score_definition`'s ``positives=`` argument.
  * ``"parents_count"`` / ``"xrefs_count"`` / ``"all_positive_examples_count"``
    -- ``int``/``float``/``int`` -- redundant with the length of the
    corresponding list field (kept verbatim, not recomputed, in case a real
    export ever has them drift).

  Note for anyone working from prose descriptions of this benchmark rather
  than the verified schema: there is NO "number of transitive subclasses" field
  anywhere in this table -- ``parents_count`` counts DIRECT PARENTS, the
  opposite direction. Whatever prior description mentioned a transitive-
  subclass count was not corroborated by the live schema and this loader
  does not invent one.

* **``structures.csv``** (every CHEBI structure with its SMILES and its
  class memberships, referenced by the README as containing "a flag ... [for
  the] validation split") is a REAL sibling file in the same HF repo but
  could NOT be verified at the row level: it is a 38.5 MB Git-LFS blob, over
  this environment's fetch size limit, is not exposed through the
  ``datasets-server`` rows API (only the classes table is), and the repo has
  no successful parquet auto-conversion to sample instead (checked: the
  ``/parquet`` endpoint reports a failed conversion). The upstream Pydantic
  model (``c3p/datamodel.py``'s ``ChemicalStructure``) declares only
  ``name``/``smiles``; the validation-split flag the README describes is not
  visible on that model at all, so its ACTUAL column name in the exported
  CSV is unverified. Recorded honestly rather than glossed over: **this
  adapter does not parse ``structures.csv``** rather than guess a column
  name that could silently mislabel every molecule's split. This is not a
  functional gap for the documented use: :func:`score_definition` takes its
  ``positives``/``negatives`` SMILES directly from the CALLER (typically
  ``example.meta["positive_smiles"]`` for positives, plus whatever negative
  pool the caller assembles) rather than reading a structures table itself.

License: **CC0-1.0** (public-domain dedication), per the repo's own
``cardData``/tags -- verified directly, not inferred. Unlike FOLIO
(CC-BY-SA-4.0, share-alike) or MALLS (CC-BY-NC-4.0, non-commercial), C3PO
carries no redistribution restriction at all; this loader still never
downloads or embeds the real data (see below), simply because there is no
license reason it would need to.

Field mapping
--------------
C3PO has no premise/conclusion entailment structure (like MALLS, not like
FOLIO) AND no gold FOL of any kind (like ProofWriter's flat NL split, not
like FOLIO/MALLS) -- see "Honesty" above. Mapped onto
:class:`~unicode_fol_kit.eval.datasets.DatasetExample`:

* ``id`` -- the record's own ``"id"`` (a CHEBI curie) verbatim, or the
  positional fallback ``f"c3po:{line_no}"`` for a record with none.
* ``nl_premises`` / ``fol_premises`` -- always ``()`` (no premise structure).
* ``nl_conclusion`` -- ``"definition"`` verbatim (the NL text a
  formalisation system is asked to translate).
* ``fol_conclusion`` -- always ``None`` (C3PO ships no FOL gold at all;
  consequently :func:`~unicode_fol_kit.eval.datasets.audit_examples` run over
  C3PO examples is VACUOUSLY ``ok=True`` for every one of them -- exactly the
  same caveat as :mod:`~unicode_fol_kit.eval.datasets.proofwriter`'s
  "Honesty" section, for the identical reason: nothing to parse means
  nothing can fail to parse).
* ``label`` -- always ``None``. C3PO's "gold" is not a single categorical
  label per example (unlike FOLIO's True/False/Uncertain) -- it is the
  per-MOLECULE membership decision :func:`score_definition` computes, which
  does not fit this dataclass's one-label-per-example slot.
* ``meta`` -- ``"chebi_id"`` (same value as ``id``, kept explicit alongside
  it), ``"name"``, ``"positive_smiles"`` (tuple, from
  ``"all_positive_examples"`` -- the field :func:`score_definition`'s
  ``positives=`` argument is meant to be filled from), ``"parents"``,
  ``"parents_count"``, ``"xrefs"``, ``"xrefs_count"``,
  ``"all_positive_examples_count"``, ``"line_no"``, plus any other key the
  record happens to carry (forward-compatibility, mirroring every other
  adapter in this subpackage).

This module never downloads anything. The real C3PO ``classes.csv`` is a
CSV with (per the verified schema above) LIST-valued cells for
``parents``/``xrefs``/``all_positive_examples``, whose exact upstream
serialisation delimiter could not itself be verified (the raw CSV bytes were
unreachable -- see "structures.csv" above for why); rather than guess a
delimiter that might silently mis-split a SMILES string containing the wrong
character, :func:`load_c3po` reads local JSONL with the SAME COLUMN NAMES
and plain JSON list values for those three fields -- trivially produced from
a real download with, e.g.::

    import ast, json, pandas as pd
    df = pd.read_csv("classes.csv")
    for col in ("parents", "xrefs", "all_positive_examples"):
        df[col] = df[col].apply(lambda v: ast.literal_eval(v) if isinstance(v, str) else v)
    df.to_json("classes.jsonl", orient="records", lines=True)

(swap ``ast.literal_eval`` for ``json.loads`` if a real download turns out to
already use JSON-list syntax in its cells -- unverified either way here).
"""

import json
from pathlib import Path
from typing import (
    FrozenSet, Iterable, Iterator, List, MutableMapping, Optional,
    Tuple, Union,
)

from dataclasses import dataclass

from ...fol.nodes import Node
from ...fol.tptp_input import TptpParsingError
from ...chem import mol_to_structure, parse_chemlog_tptp, to_chemlog_names
from ...chem.cache import StructureBuildError
from ...semantics.model_eval import (
    evaluate_detailed, UninterpretedSymbol, UnsupportedNode,
)
from ...semantics.structures import FiniteStructure
from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_c3po", "DefinitionScore", "score_definition"]

_register_dataset_info(
    "c3po",
    license="CC0-1.0",
    source_url="https://huggingface.co/datasets/MonarchInit/C3PO",
    citation_hint=(
        "Mungall, Christopher J., Adnan Malik, Daniel R. Korn, Justin T. "
        "Reese, Noel M. O'Boyle, and Janna Hastings. \"Chemical "
        "classification program synthesis using generative artificial "
        "intelligence.\" Journal of Cheminformatics (2025). "
        "DOI:10.1186/s13321-025-01092-3."
    ),
)

# The verified classes.csv/first-rows column set (see module docstring).
_KNOWN_KEYS = frozenset({
    "id", "name", "definition", "parents", "xrefs", "all_positive_examples",
    "parents_count", "xrefs_count", "all_positive_examples_count",
})


# ---------------------------------------------------------------------------
# load_c3po
# ---------------------------------------------------------------------------

def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    chebi_id = record.get("id")
    example_id = str(chebi_id) if chebi_id is not None else f"c3po:{line_no}"
    definition = record.get("definition")
    positive_smiles = tuple(record.get("all_positive_examples") or ())

    meta = {
        "chebi_id": chebi_id,
        "name": record.get("name"),
        "positive_smiles": positive_smiles,
        "parents": tuple(record.get("parents") or ()),
        "parents_count": record.get("parents_count"),
        "xrefs": tuple(record.get("xrefs") or ()),
        "xrefs_count": record.get("xrefs_count"),
        "all_positive_examples_count": record.get("all_positive_examples_count"),
    }
    # Forward-compatibility: preserve any key this record carries beyond the
    # verified schema, same convention as every other adapter here.
    for key, value in record.items():
        if key not in _KNOWN_KEYS:
            meta.setdefault(key, value)
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=(),
        fol_premises=(),
        nl_conclusion=definition,
        fol_conclusion=None,
        label=None,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_c3po(path: Union[str, Path], *,
              known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local C3PO classes JSONL file (verified schema -- see module docstring).

    Args:
        path: path to a local ``.jsonl`` file -- one ``{"id", "name",
            "definition", "parents", "xrefs", "all_positive_examples",
            "parents_count", "xrefs_count", "all_positive_examples_count"}``
            object per non-blank line (see module docstring for producing
            this from a real ``classes.csv`` download). NEVER downloaded by
            this function.
        known_bad_ids: ids (the record's own CHEBI curie, or the positional
            fallback ``f"c3po:{line_no}"`` for a record with none) whose
            ``all_positive_examples`` is known to be broken (e.g. a SMILES
            that fails to parse, found by a prior audit). Every yielded
            example with a matching id gets ``known_bad=True``.

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order -- see module docstring's "Field
        mapping" for exactly what goes where. ``fol_premises`` is always
        ``()`` and ``fol_conclusion`` is always ``None`` (C3PO has no FOL
        gold of any kind).

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON -- raised,
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


# ---------------------------------------------------------------------------
# score_definition -- model-checking a candidate FOL definition
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DefinitionScore:
    """Outcome of :func:`score_definition`: a confusion matrix PLUS two
    honest failure categories that are never folded into it.

    ``tp``/``fp``/``fn``/``tn`` count only molecules the evaluator reached a
    DEFINITE two-valued verdict on. ``n_errors`` (with per-item detail in
    ``errors``) counts molecules where building the structure or evaluating
    the formula raised one of the documented, expected exceptions (an
    unparseable/invalid SMILES; a formula predicate/constant the structure
    does not interpret; a formula outside the evaluator's supported
    fragment; a free variable) -- these are NEITHER a positive NOR a
    negative prediction, so they must never silently become one. Likewise
    ``n_exhausted`` (``exhausted``) counts molecules where the evaluator's
    step ``budget`` ran out before a definite answer -- an honest UNKNOWN,
    not a guessed ``False``. ``n_positives``/``n_negatives`` are the raw
    input counts, so ``tp + fn + (errors/exhausted tagged "positive") ==
    n_positives`` always holds (and symmetrically for negatives) -- every
    input molecule is accounted for exactly once, in exactly one bucket.

    ``precision``/``recall``/``f1`` are ``None`` when their denominator would
    be zero (e.g. ``precision`` needs at least one of ``tp``/``fp``) --
    never silently reported as ``0.0``, which would misrepresent "no data"
    as "definitely wrong". When both ``precision`` and ``recall`` ARE
    defined but sum to zero (both exactly 0.0), ``f1`` is reported as
    ``0.0`` by the standard convention (the ``2pr/(p+r)`` formula's own
    removable singularity at the origin), not ``None``.
    """

    tp: int
    fp: int
    fn: int
    tn: int
    n_positives: int
    n_negatives: int
    precision: Optional[float]
    recall: Optional[float]
    f1: Optional[float]
    n_errors: int
    n_exhausted: int
    errors: Tuple[dict, ...] = ()
    exhausted: Tuple[dict, ...] = ()

    def to_dict(self) -> dict:
        return {
            "tp": self.tp, "fp": self.fp, "fn": self.fn, "tn": self.tn,
            "n_positives": self.n_positives, "n_negatives": self.n_negatives,
            "precision": self.precision, "recall": self.recall, "f1": self.f1,
            "n_errors": self.n_errors, "n_exhausted": self.n_exhausted,
            "errors": list(self.errors), "exhausted": list(self.exhausted),
        }


#: Sentinel cached in place of a :class:`FiniteStructure` when
#: :func:`unicode_fol_kit.chem.mol_to_structure` refused a SMILES (invalid
#: syntax, unsupported element/bond, ...) -- see :func:`_structure_for`.
#: Caching the failure too (not just successes) means a SMILES that fails once
#: is never re-run through RDKit on a later call sharing the same
#: ``structure_cache``, the same cost argument the module docstring makes for
#: successes.
#:
#: ALIASED, not redefined: a campaign shares one
#: :class:`~unicode_fol_kit.chem.cache.StructureCache` between this module and
#: :mod:`unicode_fol_kit.eval.chem_batch`, and two structurally identical
#: sentinel classes would make each module's ``isinstance`` check silently
#: miss the other's cached failures -- reporting them as structures and
#: crashing in the evaluator instead.
_StructureBuildError = StructureBuildError


#: :func:`_structure_for`'s cache key -- see that function's own docstring
#: for why it is NOT just the bare SMILES string. Identical to
#: :data:`unicode_fol_kit.chem.cache.CacheKey`, so a
#: :class:`~unicode_fol_kit.chem.cache.StructureCache` can be handed straight
#: to :func:`score_definition`'s ``structure_cache``.
_CacheKey = Tuple[str, str, bool, bool]


def _structure_for(
    smiles: str, cache: MutableMapping[_CacheKey, object], *,
    naming: str = "chemlog", aromatic: bool, computed: bool,
) -> Union[FiniteStructure, _StructureBuildError]:
    """``cache[(smiles, naming, aromatic, computed)]``, building and inserting
    it first if absent.

    The cache key is the FULL triple, not the bare SMILES string, because
    ``aromatic``/``computed`` are STRUCTURE-DETERMINING parameters, not
    incidental ones: :func:`unicode_fol_kit.chem.mol_to_structure` builds a
    genuinely different :class:`FiniteStructure` for the same SMILES
    depending on either (``aromatic=False`` Kekulizes the bond typing
    instead of keeping ``bAROMATIC``; ``computed=False`` omits the five
    ring/aromaticity/connectivity predicates entirely -- see that
    function's own module docstring). Keying on the bare SMILES alone would
    let one call's ``aromatic=True`` structure silently answer a LATER
    call's ``aromatic=False`` request for the identical molecule whenever
    the two calls share a ``structure_cache`` -- a real, reproduced bug:
    two :func:`score_definition` calls sharing one cache, one with
    ``aromatic=True`` (checking ``bAROMATIC`` on benzene, correctly True)
    and a second with ``aromatic=False`` on the same SMILES (which should
    make ``bAROMATIC`` empty -- Kekulized bond typing has none), returned
    the FIRST call's stale ``aromatic=True`` structure to the second before
    this fix, silently reporting the wrong verdict rather than raising or
    rebuilding.

    ``naming`` is the third structure-determining parameter and is in the key
    for the same reason, even though this module always passes
    ``"chemlog"``: every formula path here ends up in ChemLog spelling
    (:func:`unicode_fol_kit.chem.parse_chemlog_tptp` renames back to it, and
    the ``dialect="unicode"`` path applies
    :func:`unicode_fol_kit.chem.to_chemlog_names` explicitly -- see
    :func:`_resolve_formula`), so the structure side has no reason to diverge
    from it here. It is in the key anyway because the cache is no longer
    private to this module: :class:`unicode_fol_kit.chem.cache.StructureCache`
    is shared across a whole campaign, and other entry points DO expose
    ``naming`` (``mcp.chem_tools.molecule_to_structure``). Leaving naming out
    kept this module correct only by an invariant nothing enforced -- the
    moment one cache serves both, a ``naming="paper"`` request would be
    answered with a ChemLog-spelled structure and every predicate would come
    back uninterpreted.

    Only :class:`ValueError` from ``mol_to_structure`` (a bad/unsupported
    molecule) is caught and turned into a cached
    :class:`_StructureBuildError` -- :class:`ImportError` (RDKit not
    installed) and :class:`TypeError` (a caller passing something that is
    not even a string) are environment/caller bugs, not a per-molecule data
    problem, and are left to propagate immediately rather than being
    reported as one identical "error" per molecule in the corpus.
    """
    key: _CacheKey = (smiles, naming, aromatic, computed)
    if key in cache:
        return cache[key]
    try:
        structure = mol_to_structure(
            smiles, naming=naming, aromatic=aromatic, computed=computed)
    except ValueError as exc:
        result: Union[FiniteStructure, _StructureBuildError] = (
            _StructureBuildError(f"{type(exc).__name__}: {exc}"))
    else:
        result = structure
    cache[key] = result
    return result


def _resolve_formula(formula: Union[Node, str], dialect: str) -> Node:
    """``formula`` as a :class:`Node`, in ChemLog predicate spelling.

    ``formula`` already a :class:`Node` is returned UNCHANGED -- this
    function trusts the caller to have it in the right vocabulary already
    (typically because it came from :func:`unicode_fol_kit.chem.
    parse_chemlog_tptp` itself, or from :func:`_resolve_formula`'s own
    ``dialect="unicode"`` branch on an earlier call).

    ``dialect="tptp"`` (the default -- this is the format an LLM asked for
    FOL emits, and the format ChemLog's own axiom files use):
    parsed via :func:`unicode_fol_kit.chem.parse_chemlog_tptp`, which
    already renames the chemical vocabulary back to ChemLog's lower-case
    spelling (bare TPTP capitalises every predicate on import -- see that
    function's own docstring) and applies the LLM-syntax repair layer.

    ``dialect="unicode"``: parsed via :func:`unicode_fol_kit.api.parse_any`
    (this kit's own ∃/∧/... surface syntax, predicates conventionally
    CAPITALISED, e.g. ``"∃x (C(x) ∧ O(x))"``), then explicitly renamed to
    ChemLog spelling with :func:`unicode_fol_kit.chem.to_chemlog_names` --
    without that second step a kit-syntax formula's ``C(x)``/``O(x)`` would
    never match a structure's stored ``c``/``o`` predicates and every
    molecule would fail with :class:`~unicode_fol_kit.semantics.model_eval.
    UninterpretedSymbol`, which is a genuinely different failure than "this
    formula does not actually hold" and would be a confusing default.

    Raises:
        TypeError: ``formula`` is neither a :class:`Node` nor a ``str``.
        ValueError: ``dialect`` is neither ``"tptp"`` nor ``"unicode"``; OR
            the text does not parse AT ALL under the chosen dialect -- this
            is a HARD, IMMEDIATE failure (there is nothing any molecule
            could be evaluated against), deliberately NOT reported as a
            per-molecule error the way an :class:`~unicode_fol_kit.
            semantics.model_eval.UninterpretedSymbol` (formula parses fine,
            just does not match this structure's vocabulary) is -- see
            :func:`score_definition`'s docstring for that distinction. Note:
            :func:`unicode_fol_kit.chem.parse_chemlog_tptp` itself actually
            raises :class:`~unicode_fol_kit.fol.tptp_input.TptpParsingError`
            for a genuine syntax error (its own docstring's ``ValueError``
            claim does not match this kit version's actual behaviour, verified
            directly here) -- caught and re-raised as ``ValueError`` below so
            this function keeps ONE stable exception contract regardless of
            which dialect the caller chose.
    """
    if isinstance(formula, Node):
        return formula
    if not isinstance(formula, str):
        raise TypeError(
            "c3po.score_definition: formula must be a Node or str, got "
            f"{type(formula).__name__}")

    if dialect == "tptp":
        try:
            return parse_chemlog_tptp(formula)
        except (TptpParsingError, ValueError) as exc:
            raise ValueError(
                "c3po.score_definition: formula did not parse under "
                f"dialect='tptp': {exc}") from exc

    if dialect == "unicode":
        from ... import api                          # lazy: avoid import cycle

        parsed = api.parse_any(formula)
        if not parsed.ok:
            detail = parsed.errors[-1]["message"] if parsed.errors else "unparseable"
            raise ValueError(
                "c3po.score_definition: formula did not parse under "
                f"dialect='unicode' ({detail}): {formula!r}")
        return to_chemlog_names(parsed.formula)

    raise ValueError(
        f"c3po.score_definition: dialect must be 'tptp' or 'unicode', got "
        f"{dialect!r}")


def _classify(
    smiles_list: Iterable[str], split_name: str, formula: Node, *,
    all_different: bool, budget: Optional[int], aromatic: bool, computed: bool,
    structure_cache: MutableMapping[_CacheKey, object],
    errors: List[dict], exhausted: List[dict],
) -> Tuple[int, int]:
    """Evaluate ``formula`` against every molecule in ``smiles_list``.

    Returns ``(n_holds, n_fails)`` -- how many molecules ``formula`` held /
    did not hold on, EXCLUDING anything routed into ``errors``/``exhausted``
    (appended to in place). The caller reinterprets ``(n_holds, n_fails)``
    as ``(tp, fn)`` for the positive split or ``(fp, tn)`` for the negative
    one -- see :func:`score_definition`.
    """
    n_holds = 0
    n_fails = 0
    for smiles in smiles_list:
        structure = _structure_for(
            smiles, structure_cache, aromatic=aromatic, computed=computed)
        if isinstance(structure, _StructureBuildError):
            errors.append({
                "smiles": smiles, "split": split_name, "stage": "structure",
                "kind": "StructureBuildError", "message": structure.message,
            })
            continue
        try:
            result = evaluate_detailed(
                formula, structure, all_different=all_different, budget=budget)
        except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
            errors.append({
                "smiles": smiles, "split": split_name, "stage": "evaluate",
                "kind": type(exc).__name__, "message": str(exc),
            })
            continue
        if result.exhausted:
            exhausted.append({
                "smiles": smiles, "split": split_name, "steps": result.steps,
            })
            continue
        if result.holds:
            n_holds += 1
        else:
            n_fails += 1
    return n_holds, n_fails


def _safe_div(numerator: int, denominator: int) -> Optional[float]:
    return None if denominator == 0 else numerator / denominator


def _f1_of(precision: Optional[float], recall: Optional[float]) -> Optional[float]:
    if precision is None or recall is None:
        return None
    if precision + recall == 0:
        return 0.0
    return 2 * precision * recall / (precision + recall)


def score_definition(
    formula: Union[Node, str],
    positives: Iterable[str],
    negatives: Iterable[str],
    *,
    dialect: str = "tptp",
    all_different: bool = True,
    budget: Optional[int] = None,
    aromatic: bool = True,
    computed: bool = True,
    structure_cache: Optional[MutableMapping[_CacheKey, object]] = None,
) -> DefinitionScore:
    """Model-check ``formula`` against a positive/negative SMILES split.

    This is C3PO-style evaluation: ``formula`` is a CLOSED FOL sentence over
    the ChemLog vocabulary (typically the right-hand side of a ChEBI class's
    ``<=>`` definition -- e.g. the ``?[A1,A2,A3]: (...)`` half of a
    ``carboxylicAcid`` definition, NOT the biconditional itself: the
    left-hand class name is a bare 0-ary atom this module's structures do
    not interpret, so evaluating the whole biconditional would raise
    :class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol` on
    every molecule). It is evaluated ONCE PER MOLECULE, each against its OWN
    :func:`~unicode_fol_kit.chem.mol_to_structure` structure -- there is no
    cross-molecule comparison; "classifying" a molecule means deciding
    whether ``formula`` is true in that ONE molecule's structure.

    Args:
        formula: a parsed :class:`~unicode_fol_kit.fol.nodes.Node`, or TPTP/
            kit-unicode text (see ``dialect=``) -- resolved ONCE, before the
            per-molecule loop (see :func:`_resolve_formula`).
        positives: SMILES of molecules that SHOULD satisfy ``formula`` (the
            gold-positive set -- typically a C3PO example's
            ``meta["positive_smiles"]``).
        negatives: SMILES of molecules that should NOT (the gold-negative
            set -- this module does not source it for you; see the module
            docstring's ``structures.csv`` note for why).
        dialect: ``"tptp"`` (default) or ``"unicode"`` -- see
            :func:`_resolve_formula`. Ignored if ``formula`` is already a
            :class:`Node`.
        all_different: forwarded to
            :func:`~unicode_fol_kit.semantics.model_eval.evaluate_detailed`.
            Defaults to ``True`` -- NOT this evaluator's own library default
            (which is ``False``, plain FOL semantics) -- because ChemLog's
            own TPTP convention (documented in ``model_eval``'s module
            docstring) is that separately-quantified existentials denote
            PAIRWISE DISTINCT individuals with no explicit ``≠`` ever
            written, and ``dialect="tptp"`` formulas are exactly that
            convention's own output. Pass ``all_different=False`` explicitly
            for a formula that does NOT follow it (e.g. a hand-written
            ``dialect="unicode"`` formula using genuine plain-FOL semantics).
        budget: forwarded to ``evaluate_detailed`` as its per-molecule step
            budget. ``None`` (default) means unlimited -- ``exhausted`` will
            then always be empty.
        aromatic / computed: forwarded to
            :func:`~unicode_fol_kit.chem.mol_to_structure` for every
            molecule this call builds a structure for.
        structure_cache: a caller-owned, mutable
            ``{(smiles, aromatic, computed): structure}`` dict, extended IN
            PLACE -- the key is the FULL triple, not the bare SMILES, because
            ``aromatic``/``computed`` are structure-determining parameters
            (see :func:`_structure_for`'s own docstring): a SMILES cached
            under one ``aromatic=``/``computed=`` combination is never
            returned for a call using a DIFFERENT combination, even when both
            calls share this same dict, so passing one shared cache to calls
            that deliberately vary ``aromatic=``/``computed=`` is always
            safe. Pass the SAME dict across multiple :func:`score_definition`
            calls that share (even partially overlapping) molecule sets AND
            the same ``aromatic=``/``computed=`` choice -- e.g. scoring
            several candidate definitions against one C3PO class's
            positives, or scoring one definition against many classes that
            share common negatives -- to build each distinct SMILES's
            structure ONCE, not once per call (RDKit parsing + the
            ring/fragment computed-predicate pass is the dominant
            per-molecule cost). ``None`` (default) creates a fresh,
            call-local dict -- structures are still deduplicated WITHIN one
            call (e.g. a SMILES appearing in both ``positives`` and
            ``negatives``, or repeated in one list), just not reused across
            separate calls.

    Returns:
        A :class:`DefinitionScore`. See its docstring for exactly how the
        four confusion-matrix cells, the two honest failure categories, and
        the derived precision/recall/F1 relate.

    Raises:
        TypeError: ``formula`` is neither a :class:`Node` nor ``str``.
        ValueError: ``dialect`` is invalid, or ``formula`` (as text) fails to
            parse AT ALL -- see :func:`_resolve_formula`. This is the ONE
            failure mode NOT absorbed into ``DefinitionScore.errors``: a
            formula that never became a valid AST cannot meaningfully be
            "scored" as 0-for-everything, so this raises immediately instead
            of manufacturing a degenerate result the caller might not
            scrutinise. A formula that DOES parse but names a predicate this
            vocabulary does not have (e.g. a typo, or a genuinely unknown
            predicate) is different: it fails identically on every molecule,
            but via the ordinary per-molecule ``UninterpretedSymbol`` path,
            so it shows up as ``n_errors == n_positives + n_negatives`` in an
            otherwise normally-returned score -- exactly the distinction
            that matters here: an unusable vocabulary is reported as its own
            error category, never as "everything came out negative".
        ImportError: RDKit is not installed (propagated from the first
            :func:`~unicode_fol_kit.chem.mol_to_structure` call).
    """
    resolved = _resolve_formula(formula, dialect)
    cache: MutableMapping[_CacheKey, object] = (
        {} if structure_cache is None else structure_cache)

    positives_list = list(positives)
    negatives_list = list(negatives)

    errors: List[dict] = []
    exhausted: List[dict] = []

    tp, fn = _classify(
        positives_list, "positive", resolved,
        all_different=all_different, budget=budget,
        aromatic=aromatic, computed=computed,
        structure_cache=cache, errors=errors, exhausted=exhausted,
    )
    fp, tn = _classify(
        negatives_list, "negative", resolved,
        all_different=all_different, budget=budget,
        aromatic=aromatic, computed=computed,
        structure_cache=cache, errors=errors, exhausted=exhausted,
    )

    precision = _safe_div(tp, tp + fp)
    recall = _safe_div(tp, tp + fn)
    f1 = _f1_of(precision, recall)

    return DefinitionScore(
        tp=tp, fp=fp, fn=fn, tn=tn,
        n_positives=len(positives_list), n_negatives=len(negatives_list),
        precision=precision, recall=recall, f1=f1,
        n_errors=len(errors), n_exhausted=len(exhausted),
        errors=tuple(errors), exhausted=tuple(exhausted),
    )
