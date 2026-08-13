"""Campaign-scale checking of chemical class definitions against molecules.

:func:`~unicode_fol_kit.eval.datasets.c3po.score_definition` answers "how good
is THIS definition" and returns a confusion matrix. This module answers the
other question a campaign asks — "run these K definitions over these N
molecules and write down everything that happened" — and its contract is
shaped by the two ways such a run fails in practice.

**A run never stops because of data.** One unparseable SMILES in a set of
200 000, or one definition mentioning a predicate no structure interprets,
must not cost the other 199 999 rows. Every such failure becomes a ROW with a
``status``, never an exception. The dividing line is exactly: is this a
property of the input data (row) or of the configuration (raise, immediately,
before the first molecule)? RDKit not installed, an unknown ``naming``, an
unwritable results path — those are configuration, and they fail loudly up
front rather than as 200 000 identical error rows.

**Partial results survive an interrupt.** Rows are flushed to JSONL after each
DEFINITION rather than at the end, so a run killed at 90 % keeps 90 %. With
``resume=True`` a re-run reads back what is already there and skips those
``(definition, molecule)`` pairs — the campaign's own restart mechanism, not
an afterthought.

**The structure is built once per molecule, not once per check.** That is what
:class:`~unicode_fol_kit.chem.cache.StructureCache` is for, and why this
module loops definition-outer/molecule-inner: the inner loop hits the cache.
Measured speed-up on this kit: 1.6× to 59× depending on how fast the formula
short-circuits, around 3–8× for a realistic mix (see the cache module's own
docstring for the numbers and the method).

Statuses a row can carry:

``ok``
    The formula was evaluated; ``holds`` is ``True``/``False``.
``exhausted``
    The evaluation budget ran out. ``holds`` is ``None`` — NEVER ``False``.
    A separate status because counting an undecided check as a negative is
    how an evaluation quietly flatters itself.
``structure_error``
    RDKit refused the SMILES. Cached, so it costs one attempt per molecule
    for the whole run, not one per definition.
``parse_error`` / ``eval_error``
    The definition did not parse (recorded ONCE, on a synthetic row with
    ``smiles=None``, and the definition is then skipped), or the evaluator
    refused this structure/formula pair (per row — typically an
    :class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol` for a
    class predicate that only exists in another definition).
"""

import io
import json
import os
import time
from dataclasses import dataclass, field
from typing import (
    Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple,
    Union,
)

from ..chem.cache import StructureBuildError, StructureCache
from ..fol.nodes import Atom, Node
from ..semantics.model_eval import (
    evaluate_detailed, UninterpretedSymbol, UnsupportedNode,
)

__all__ = ["ChemBatchResult", "check_definitions"]

_STATUSES = ("ok", "exhausted", "structure_error", "parse_error", "eval_error")


@dataclass(frozen=True)
class ChemBatchResult:
    """Outcome of :func:`check_definitions`.

    ``rows`` is every row produced BY THIS CALL — rows skipped because a
    resume found them already written are not re-reported, so ``counts`` and
    ``rows`` describe the work this call did, while the JSONL file describes
    the run as a whole. ``skipped`` says how many pairs the resume passed
    over, so the difference is never silent.
    """

    rows: Tuple[dict, ...]
    counts: Dict[str, int]
    cache_stats: Dict[str, Any]
    seconds: float
    skipped: int = 0

    def to_dict(self) -> dict:
        return {"rows": list(self.rows), "counts": dict(self.counts),
                "cache_stats": dict(self.cache_stats),
                "seconds": self.seconds, "skipped": self.skipped}


def _resolve(formula: Union[Node, str], dialect: str) -> Node:
    """Definition text -> a ChemLog-spelled :class:`Node`.

    Delegates to :func:`unicode_fol_kit.eval.datasets.c3po._resolve_formula`
    rather than reimplementing the dialect routing and the ChemLog rename:
    two implementations of "which parser, then which rename" is exactly how
    the unicode path silently stopped matching structures once before.
    """
    from .datasets.c3po import _resolve_formula

    return _resolve_formula(formula, dialect)


def _unknown_predicates(formula: Node, structure) -> List[str]:
    """Predicates the formula uses that this structure does not interpret.

    Informational, never fatal. A ChEBI class definition legitimately names
    OTHER class predicates (``carboxylicAcid``, ``lipid``) that no molecule
    structure can decide — they have to be unfolded first — and refusing the
    definition for it would reject most of a real corpus. Reporting them once
    per definition turns a wall of identical per-row ``eval_error``s into one
    actionable line.
    """
    unknown = set()
    for part in formula.walk():
        if isinstance(part, Atom) and part.predicate not in ("=", "≠"):
            if not structure.interprets(part.predicate, len(part.args)):
                unknown.add(f"{part.predicate}/{len(part.args)}")
    return sorted(unknown)


def _existing_pairs(path: str) -> set:
    """``(def_id, smiles)`` pairs already in the results file.

    A truncated final line (the normal shape of an interrupted run) is
    ignored rather than raising: the pair it described simply gets redone.
    """
    pairs = set()
    if not os.path.exists(path):
        return pairs
    with io.open(path, encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except ValueError:
                continue
            pairs.add((row.get("def_id"), row.get("smiles")))
    return pairs


def check_definitions(
    definitions: Iterable[Mapping[str, Any]],
    molecules: Sequence[str],
    *,
    results_path: Optional[str] = None,
    dialect: str = "tptp",
    naming: str = "chemlog",
    aromatic: bool = True,
    computed: bool = True,
    all_different: bool = True,
    budget: Optional[int] = None,
    cache: Optional[StructureCache] = None,
    resume: bool = True,
    progress: Optional[Callable[[str, int, int], None]] = None,
) -> ChemBatchResult:
    """Evaluate every definition against every molecule.

    Args:
        definitions: mappings with ``"id"`` and ``"formula"`` (text in
            ``dialect``, or an already-parsed
            :class:`~unicode_fol_kit.fol.nodes.Node`). Validated up front —
            a missing key is a caller bug, not data, and raises.
        molecules: SMILES strings. Only strings: an already-parsed
            ``rdkit.Chem.Mol`` cannot be a cache key (object identity would
            defeat the cache and the key would be mutable).
        results_path: JSONL to append to, flushed after each definition.
            ``None`` keeps everything in memory only.
        dialect: ``"tptp"`` (the ChemLog format) or ``"unicode"``.
        naming / aromatic / computed: structure-building options, forwarded to
            :func:`~unicode_fol_kit.chem.mol_to_structure` AND part of the
            cache key — see :mod:`unicode_fol_kit.chem.cache`.
        all_different: ChemLog's convention that separately introduced
            existential variables denote distinct individuals. Defaults to
            ``True`` here, matching every other chemical entry point in the
            kit (and unlike the underlying evaluator's plain-FOL default).
        budget: evaluation step budget per check. ``None`` is unbounded; a
            campaign should set one, and an exhausted check is reported as
            ``status="exhausted"`` with ``holds=None``.
        cache: a shared :class:`~unicode_fol_kit.chem.cache.StructureCache`.
            One is created if omitted; pass your own to share it across calls
            (that is where the speed-up lives).
        resume: skip ``(def_id, smiles)`` pairs already present in
            ``results_path``.
        progress: called as ``(def_id, index, total)`` after each definition.

    Returns:
        A :class:`ChemBatchResult`.

    Raises:
        ValueError: a definition without ``id``/``formula``, a non-string
            SMILES, an unknown ``naming``/``dialect``, or an unwritable
            ``results_path`` — all configuration, all detected before the
            first molecule is built.
        ImportError: RDKit is not installed.
    """
    started = time.perf_counter()
    if naming not in ("chemlog", "paper"):
        raise ValueError(f"check_definitions: unknown naming={naming!r}")
    if dialect not in ("tptp", "unicode"):
        raise ValueError(f"check_definitions: unknown dialect={dialect!r}")

    prepared: List[Tuple[str, Any]] = []
    for entry in definitions:
        if "id" not in entry or "formula" not in entry:
            raise ValueError(
                "check_definitions: every definition needs 'id' and 'formula'; "
                f"got keys {sorted(entry)}")
        prepared.append((str(entry["id"]), entry["formula"]))
    for smiles in molecules:
        if not isinstance(smiles, str):
            raise ValueError(
                "check_definitions: molecules must be SMILES strings, got "
                f"{type(smiles).__name__}")

    if results_path:
        directory = os.path.dirname(os.path.abspath(results_path))
        if directory and not os.path.isdir(directory):
            raise ValueError(
                f"check_definitions: results_path directory does not exist: "
                f"{directory}")

    cache = cache if cache is not None else StructureCache()
    # Fail on a missing RDKit here, once, rather than per molecule: it is the
    # environment, not the data. Deliberately NOT through the cache — a
    # pre-warm would count as a hit on the first row and make the reported
    # hit rate flatter than the run actually achieved, which is the one
    # number M2 exists to measure.
    if molecules:
        from ..chem import mol_to_structure

        try:
            mol_to_structure(molecules[0], naming=naming, aromatic=aromatic,
                             computed=computed)
        except ValueError:
            pass    # a bad FIRST molecule is data; it gets its own row below

    done = _existing_pairs(results_path) if (resume and results_path) else set()
    rows: List[dict] = []
    counts: Dict[str, int] = {status: 0 for status in _STATUSES}
    skipped = 0

    def record(row: dict) -> None:
        rows.append(row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1

    for index, (def_id, raw_formula) in enumerate(prepared, 1):
        slab: List[dict] = []
        try:
            formula = _resolve(raw_formula, dialect)
        except Exception as exc:   # noqa: BLE001 — every parser has its own
            row = {"def_id": def_id, "smiles": None, "status": "parse_error",
                   "holds": None, "steps": None, "exhausted": None,
                   "witness": None, "error_kind": type(exc).__name__,
                   "error_msg": str(exc)[:400], "ms": None, "cached": None}
            record(row)
            slab.append(row)
            _flush(results_path, slab)
            if progress:
                progress(def_id, index, len(prepared))
            continue

        reported_unknown = False
        for smiles in molecules:
            if (def_id, smiles) in done:
                skipped += 1
                continue
            cell_started = time.perf_counter()
            before = cache.misses
            structure = cache.structure_for(smiles, naming=naming,
                                            aromatic=aromatic, computed=computed)
            was_cached = cache.misses == before
            row = {"def_id": def_id, "smiles": smiles, "status": "ok",
                   "holds": None, "steps": None, "exhausted": False,
                   "witness": None, "error_kind": None, "error_msg": None,
                   "ms": None, "cached": was_cached}

            if isinstance(structure, StructureBuildError):
                row.update(status="structure_error", exhausted=None,
                           error_kind="StructureBuildError",
                           error_msg=structure.message)
            else:
                if not reported_unknown:
                    unknown = _unknown_predicates(formula, structure)
                    reported_unknown = True
                    if unknown:
                        row["unknown_predicates"] = unknown
                try:
                    result = evaluate_detailed(
                        formula, structure, all_different=all_different,
                        budget=budget)
                except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
                    row.update(status="eval_error", exhausted=None,
                               error_kind=type(exc).__name__,
                               error_msg=str(exc)[:400])
                else:
                    row["steps"] = result.steps
                    row["exhausted"] = result.exhausted
                    if result.exhausted:
                        row["status"] = "exhausted"
                    else:
                        row["holds"] = result.holds
                        row["witness"] = (dict(result.witness)
                                          if result.witness else None)
            row["ms"] = round((time.perf_counter() - cell_started) * 1000, 4)
            record(row)
            slab.append(row)

        _flush(results_path, slab)
        if progress:
            progress(def_id, index, len(prepared))

    return ChemBatchResult(
        rows=tuple(rows), counts=counts, cache_stats=cache.stats(),
        seconds=round(time.perf_counter() - started, 3), skipped=skipped)


def _flush(results_path: Optional[str], slab: List[dict]) -> None:
    """Append one definition's rows and fsync-free close.

    Append mode, one open/close per definition: a campaign run is minutes to
    hours long, and holding one handle open for its whole duration means an
    interrupt loses whatever the OS had buffered.
    """
    if not results_path or not slab:
        return
    with io.open(results_path, "a", encoding="utf-8", newline="\n") as handle:
        for row in slab:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
