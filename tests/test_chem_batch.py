"""Tests for the campaign batch layer — :mod:`unicode_fol_kit.chem.cache` and
:mod:`unicode_fol_kit.eval.chem_batch`.

Every expected verdict is hand-derived from the molecule, not copied from a
run. The pattern used throughout is the kit's own amide-bond example
(``docs/guide/mcp.md``): "some carbon double-bonded to an oxygen and singly
bonded to a nitrogen".

* **glycylglycine** ``NCC(=O)NCC(=O)O`` — the peptide bond IS a
  ``-C(=O)-N-``, so the pattern holds.
* **ethanol** ``CCO`` — no nitrogen at all, so ``n(N)`` can never be
  satisfied and the pattern fails whatever the bonds do.
* **acetic acid** ``CC(=O)O`` — has the carbonyl but no nitrogen: fails the
  amide pattern, satisfies the carboxylic-acid one.
"""

import json
import os

import pytest

from unicode_fol_kit.chem.cache import StructureBuildError, StructureCache
from unicode_fol_kit.eval.chem_batch import check_definitions

pytest.importorskip("rdkit", reason="chem_batch builds structures with RDKit")

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
ACID = "?[C,O1,O2]: (c(C) & o(O1) & o(O2) & bDOUBLE(C,O1) & bSINGLE(C,O2))"

GLYCYLGLYCINE = "NCC(=O)NCC(=O)O"
ETHANOL = "CCO"
ACETIC_ACID = "CC(=O)O"


class TestStructureCache:
    def test_the_options_are_part_of_the_key_not_just_the_smiles(self):
        """The bug this key exists to prevent: one call's structure answering
        another call's question. ``computed=False`` omits the five
        ring/aromaticity predicates entirely, so the two structures for ONE
        molecule are genuinely different objects and must not share a slot."""
        cache = StructureCache()
        full = cache.structure_for(ETHANOL, computed=True)
        lean = cache.structure_for(ETHANOL, computed=False)

        assert full is not lean
        assert len(cache) == 2
        assert full.interprets("in_ring", 1)
        assert not lean.interprets("in_ring", 1)

    def test_naming_is_part_of_the_key(self):
        """The one that was only correct by an unenforced invariant: c3po
        hardcoded ``naming="chemlog"`` and left naming out of the key, which
        held until a cache is SHARED with an entry point that exposes it.
        'paper' spells the single bond ``singleBond``, 'chemlog' ``bSINGLE`` —
        a formula checked against the wrong one fails on every molecule."""
        cache = StructureCache()
        chemlog = cache.structure_for(ETHANOL, naming="chemlog")
        paper = cache.structure_for(ETHANOL, naming="paper")

        assert chemlog is not paper
        assert len(cache) == 2
        assert chemlog.interprets("bSINGLE", 2)
        assert not paper.interprets("bSINGLE", 2)

    def test_a_second_lookup_is_a_hit_and_returns_the_same_object(self):
        cache = StructureCache()
        first = cache.structure_for(ETHANOL)
        second = cache.structure_for(ETHANOL)

        assert first is second
        assert (cache.hits, cache.misses) == (1, 1)
        assert cache.hit_rate == 0.5

    def test_hit_rate_is_none_before_the_first_lookup(self):
        """Never a fabricated 0.0 for a cache nobody has asked anything."""
        assert StructureCache().hit_rate is None

    def test_a_refused_smiles_is_cached_as_an_error_not_retried(self):
        """The failure is deterministic, so paying RDKit for it twice buys
        nothing — and it must come back as a VALUE, not an exception, or a
        hit and a miss would behave differently at the call site."""
        cache = StructureCache()
        first = cache.structure_for("not-a-molecule(((")
        second = cache.structure_for("not-a-molecule(((")

        assert isinstance(first, StructureBuildError)
        assert first is second
        assert cache.misses == 1

    def test_eviction_is_least_recently_used_and_bounded(self):
        """A campaign revisits the same molecules across definitions, so
        recency is the right predictor — and unbounded growth is not an
        option over hundreds of thousands of molecules."""
        cache = StructureCache(max_entries=2)
        cache.structure_for(ETHANOL)
        cache.structure_for(ACETIC_ACID)
        cache.structure_for(ETHANOL)          # refreshes ethanol
        cache.structure_for(GLYCYLGLYCINE)    # evicts acetic acid, not ethanol

        assert cache.evictions == 1
        assert ("CCO", "chemlog", True, True) in cache
        assert ("CC(=O)O", "chemlog", True, True) not in cache


class TestCheckDefinitions:
    def test_verdicts_match_the_hand_derived_chemistry(self):
        result = check_definitions(
            [{"id": "amide", "formula": AMIDE}, {"id": "acid", "formula": ACID}],
            [GLYCYLGLYCINE, ETHANOL, ACETIC_ACID])

        holds = {(r["def_id"], r["smiles"]): r["holds"] for r in result.rows}
        assert holds[("amide", GLYCYLGLYCINE)] is True
        assert holds[("amide", ETHANOL)] is False
        assert holds[("amide", ACETIC_ACID)] is False     # carbonyl, no N
        assert holds[("acid", ACETIC_ACID)] is True
        assert holds[("acid", GLYCYLGLYCINE)] is True     # its C-terminal COOH
        assert holds[("acid", ETHANOL)] is False
        assert result.counts["ok"] == 6

    def test_one_bad_molecule_never_stops_the_run(self):
        """The whole point of the layer: 199 999 rows must not be lost to one
        SMILES RDKit refuses."""
        result = check_definitions(
            [{"id": "amide", "formula": AMIDE}],
            [GLYCYLGLYCINE, "not-a-molecule(((", ETHANOL])

        by_status = [r["status"] for r in result.rows]
        assert by_status.count("ok") == 2
        assert by_status.count("structure_error") == 1
        bad = next(r for r in result.rows if r["status"] == "structure_error")
        assert bad["holds"] is None
        assert "StructureBuildError" == bad["error_kind"]

    def test_an_unparseable_definition_is_recorded_once_not_per_molecule(self):
        """A broken formula is one fact about the definition, not N facts
        about the molecules — reporting it N times would bury the run."""
        result = check_definitions(
            [{"id": "broken", "formula": "?[X]: (c(X) &"}],
            [GLYCYLGLYCINE, ETHANOL, ACETIC_ACID])

        assert result.counts["parse_error"] == 1
        assert len(result.rows) == 1
        assert result.rows[0]["smiles"] is None

    def test_the_cache_is_what_makes_the_second_definition_cheap(self):
        """K definitions over N molecules build N structures, not K·N."""
        cache = StructureCache()
        check_definitions(
            [{"id": "amide", "formula": AMIDE}, {"id": "acid", "formula": ACID}],
            [GLYCYLGLYCINE, ETHANOL, ACETIC_ACID], cache=cache)

        assert cache.misses == 3          # three molecules, built once each
        assert cache.hits == 3            # the second definition hits all three

    def test_an_unknown_predicate_is_reported_but_does_not_stop_anything(self):
        """A ChEBI definition legitimately names OTHER class predicates that
        no molecule structure can decide — they have to be unfolded first.
        Refusing the definition for it would reject most of a real corpus.

        Reported as ``Lipid/1``, not ``lipid/1``: the TPTP importer
        capitalises every parsed predicate, and ``to_chemlog_names`` renames
        back only the 35 symbols of ChemLog's own vocabulary — a class
        predicate has no ChemLog spelling to restore, so it keeps the kit's
        (see ``chem.interop``'s module docstring). The report names the symbol
        as the EVALUATOR saw it, which is the one a caller has to go and
        define.
        """
        result = check_definitions(
            [{"id": "delegating", "formula": "?[X]: (c(X) & lipid(X))"}],
            [ETHANOL])

        row = result.rows[0]
        assert row["status"] == "eval_error"
        assert row["unknown_predicates"] == ["Lipid/1"]

    def test_rows_are_written_per_definition_and_a_rerun_resumes(self, tmp_path):
        """A run killed at 90 % keeps 90 %, and re-running finishes the rest
        instead of redoing it."""
        path = str(tmp_path / "rows.jsonl")
        first = check_definitions(
            [{"id": "amide", "formula": AMIDE}],
            [GLYCYLGLYCINE, ETHANOL], results_path=path)
        assert len(first.rows) == 2

        written = [json.loads(line)
                   for line in open(path, encoding="utf-8") if line.strip()]
        assert len(written) == 2

        second = check_definitions(
            [{"id": "amide", "formula": AMIDE}],
            [GLYCYLGLYCINE, ETHANOL], results_path=path)
        assert second.rows == ()
        assert second.skipped == 2

    def test_a_configuration_mistake_raises_instead_of_becoming_rows(self):
        """The dividing line the module is built on: data becomes a row,
        configuration fails loudly before the first molecule."""
        with pytest.raises(ValueError, match="naming"):
            check_definitions([{"id": "a", "formula": AMIDE}], [ETHANOL],
                              naming="nonsense")
        with pytest.raises(ValueError, match="'id' and 'formula'"):
            check_definitions([{"formula": AMIDE}], [ETHANOL])
        with pytest.raises(ValueError, match="SMILES strings"):
            check_definitions([{"id": "a", "formula": AMIDE}], [42])

    def test_an_exhausted_budget_is_its_own_status_never_a_false(self):
        """Counting an undecided check as a negative is how an evaluation
        quietly flatters itself."""
        result = check_definitions(
            [{"id": "amide", "formula": AMIDE}], [GLYCYLGLYCINE], budget=1)

        row = result.rows[0]
        assert row["status"] == "exhausted"
        assert row["holds"] is None
        assert row["exhausted"] is True
