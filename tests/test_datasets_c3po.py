"""Tests for unicode_fol_kit.eval.datasets.c3po (C3PO adapter).

Fixture provenance (``tests/fixtures/c3po_mini.jsonl``): 8 hand-written
SYNTHETIC classes in the verified upstream ``classes.csv`` field format (see
``c3po.py``'s module docstring for how that schema was verified against the
real ``MonarchInit/C3PO`` HF dataset) — NOT copied from real CHEBI/C3PO data
(the ids ``CHEBI:900001``..``CHEBI:900008`` are deliberately out of any real
CHEBI id range), only shaped like it, for the same license-hygiene reason
every other fixture in this subpackage documents. Every SMILES in the
fixture was parsed with RDKit directly (see the module-level sanity run this
test suite's author performed before writing it) and every hand-derived
atom/bond/hydrogen-count claim below matches ``Chem.MolFromSmiles(...);
Chem.RemoveHs(...)`` exactly — none of it is copied from a first run of the
code under test.

Skipped entirely (module-level ``importorskip``) on a machine without
RDKit — :func:`~unicode_fol_kit.eval.datasets.c3po.load_c3po` itself needs no
chemistry at all (it only reads JSON), but essentially every meaningful test
here exercises :func:`~unicode_fol_kit.eval.datasets.c3po.score_definition`,
which does.
"""

from pathlib import Path

import pytest

rdkit = pytest.importorskip("rdkit")

import json

from unicode_fol_kit.eval.datasets import DatasetExample, DATASET_INFO, audit_examples
from unicode_fol_kit.eval.datasets.c3po import load_c3po, score_definition, DefinitionScore

_FIXTURES = Path(__file__).parent / "fixtures"
_C3PO_FIXTURE = _FIXTURES / "c3po_mini.jsonl"

# The definition under test throughout this file: "the molecule carries a
# free carboxylic-acid group" -- a carbon (A1) double-bonded to an oxygen
# (A2) and singly bonded to a SECOND, distinct oxygen (A3) that itself
# carries exactly one hydrogen. Written directly in ChemLog/bare-TPTP
# syntax, the format :func:`score_definition`'s default dialect="tptp"
# expects (and the format an LLM asked for a chemical class definition
# emits — one existential block of atom-type, hydrogen-count and bond
# literals, whose shape this formula deliberately mirrors).
_CARBOXY_FORMULA = (
    "?[A1,A2,A3]: (c(A1) & o(A2) & o(A3) & has_1_hs(A3) "
    "& bDOUBLE(A1,A2) & bSINGLE(A1,A3))"
)


# ---------------------------------------------------------------------------
# load_c3po: field mapping
# ---------------------------------------------------------------------------

def test_load_c3po_yields_one_example_per_line():
    """8 non-blank JSONL lines in the fixture -> 8 examples, in file order."""
    examples = list(load_c3po(_C3PO_FIXTURE))
    assert len(examples) == 8
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_load_c3po_field_mapping_first_example():
    """Row 1 (CHEBI:900001, the carboxylic-acid fixture class): id is the
    CHEBI curie verbatim, definition maps to nl_conclusion, fol_conclusion
    and label are always None (C3PO has neither), and meta carries the
    positive SMILES plus every other verified classes.csv column."""
    example = next(load_c3po(_C3PO_FIXTURE))
    assert example.id == "CHEBI:900001"
    assert example.nl_premises == ()
    assert example.fol_premises == ()
    assert example.nl_conclusion.startswith("A molecule that carries at least one carboxy group")
    assert example.fol_conclusion is None
    assert example.label is None
    assert example.known_bad is False

    assert example.meta["chebi_id"] == "CHEBI:900001"
    assert example.meta["name"] == "carboxylic acid (fixture)"
    assert example.meta["positive_smiles"] == ("CC(=O)O", "c1ccccc1C(=O)O", "CCC(=O)O")
    assert example.meta["parents"] == ("CHEBI:900100",)
    assert example.meta["parents_count"] == 1
    assert example.meta["xrefs"] == ("KEGG:C00033",)
    assert example.meta["xrefs_count"] == 1.0
    assert example.meta["all_positive_examples_count"] == 3
    assert example.meta["line_no"] == 0


def test_load_c3po_null_xrefs_count_maps_to_none():
    """Row 2 (primary alcohol) has no xrefs in the fixture -> xrefs_count is
    JSON null, which must arrive as Python None, not 0 or NaN."""
    examples = list(load_c3po(_C3PO_FIXTURE))
    second = examples[1]
    assert second.id == "CHEBI:900002"
    assert second.meta["xrefs"] == ()
    assert second.meta["xrefs_count"] is None


def test_load_c3po_all_eight_ids_and_counts():
    examples = list(load_c3po(_C3PO_FIXTURE))
    ids = [e.id for e in examples]
    assert ids == [
        "CHEBI:900001", "CHEBI:900002", "CHEBI:900003", "CHEBI:900004",
        "CHEBI:900005", "CHEBI:900006", "CHEBI:900007", "CHEBI:900008",
    ]
    counts = [e.meta["all_positive_examples_count"] for e in examples]
    assert counts == [3, 3, 3, 3, 2, 2, 2, 2]
    # every declared count matches the actual length of positive_smiles
    for example in examples:
        assert len(example.meta["positive_smiles"]) == example.meta["all_positive_examples_count"]


def test_load_c3po_known_bad_flag():
    examples = list(load_c3po(_C3PO_FIXTURE, known_bad_ids=frozenset({"CHEBI:900005"})))
    flags = {e.id: e.known_bad for e in examples}
    assert flags["CHEBI:900005"] is True
    assert sum(flags.values()) == 1


def test_load_c3po_positional_id_fallback_for_id_less_row():
    """A record with no 'id' field falls back to f"c3po:{line_no}"."""
    from unicode_fol_kit.eval.datasets.c3po import _example_from_record
    example = _example_from_record({"definition": "no id here"}, 42, frozenset())
    assert example.id == "c3po:42"
    assert example.meta["chebi_id"] is None
    assert example.meta["positive_smiles"] == ()


def test_load_c3po_missing_file_raises_file_not_found():
    with pytest.raises(FileNotFoundError):
        list(load_c3po(_FIXTURES / "does_not_exist_c3po.jsonl"))


def test_load_c3po_malformed_json_line_raises_not_silently_skipped():
    bad_path = _FIXTURES / "_tmp_malformed_c3po.jsonl"
    bad_path.write_text('{"id": "CHEBI:1", "definition": "ok"}\nnot json\n', encoding="utf-8")
    try:
        with pytest.raises(json.JSONDecodeError):
            list(load_c3po(bad_path))
    finally:
        bad_path.unlink()


def test_dataset_example_to_dict_is_json_compatible():
    example = next(load_c3po(_C3PO_FIXTURE))
    payload = example.to_dict()
    text = json.dumps(payload)
    round_tripped = json.loads(text)
    assert round_tripped["id"] == "CHEBI:900001"
    assert round_tripped["fol_premises"] == []
    assert round_tripped["fol_conclusion"] is None


# ---------------------------------------------------------------------------
# audit_examples: C3PO carries no FOL at all -> vacuously ok=True
# ---------------------------------------------------------------------------

def test_audit_examples_is_vacuously_ok_for_c3po():
    """C3PO has no fol_premises/fol_conclusion (see module docstring's
    Honesty section) -- audit_examples has nothing to parse or check, so
    every example reports ok=True with no defects. This is NOT a claim that
    the definitions are fine, only that there is nothing here to audit."""
    examples = list(load_c3po(_C3PO_FIXTURE))
    report = audit_examples(examples)
    assert len(report) == 8
    assert all(r["ok"] and r["all_parsed"] and r["all_checked"] and not r["defects"]
               for r in report)


# ---------------------------------------------------------------------------
# DATASET_INFO
# ---------------------------------------------------------------------------

def test_dataset_info_registry_has_verified_provenance_for_c3po():
    assert "c3po" in DATASET_INFO
    info = DATASET_INFO["c3po"]
    assert info["license"] == "CC0-1.0"
    assert info["source_url"] == "https://huggingface.co/datasets/MonarchInit/C3PO"
    assert "Mungall" in info["citation_hint"]
    assert "Cheminformatics" in info["citation_hint"]


# ---------------------------------------------------------------------------
# score_definition: the mandatory hand-computed confusion matrix
# ---------------------------------------------------------------------------
#
# Hand derivation (cross-checked against a direct RDKit atom/bond dump before
# this test was written -- see this module's docstring):
#
# Positives (gold: "has a carboxylic-acid group"):
#   P1 acetic acid     "CC(=O)O"     -- c2(=O)(OH): O=O has 0 H, O-H has 1 H
#                                        -> formula TRUE  => TP
#   P2 benzoic acid    "c1ccccc1C(=O)O" -- same exocyclic -C(=O)OH group
#                                        -> formula TRUE  => TP
#   P3 acetate anion   "CC(=O)[O-]"  -- the singly-bonded O carries charge
#                                        -1 and ZERO hydrogens (RDKit:
#                                        GetTotalNumHs()==0), so has_1_hs
#                                        fails on every oxygen
#                                        -> formula FALSE => FN
#
# Negatives (gold: "does not have a carboxylic-acid group"):
#   N1 ethanol         "CCO"         -- no C=O bond at all (bDOUBLE empty)
#                                        -> formula FALSE => TN
#   N2 methyl acetate  "CC(=O)OC"    -- the ester's singly-bonded O is
#                                        bonded to TWO carbons, 0 hydrogens
#                                        -> formula FALSE => TN
#   N3 methylamine     "CN"          -- no oxygen atom at all (o/1 empty)
#                                        -> formula FALSE => TN
#
# => tp=2, fp=0, fn=1, tn=3
#    precision = tp/(tp+fp) = 2/2       = 1.0
#    recall    = tp/(tp+fn) = 2/3       = 0.6666...
#    f1        = 2*P*R/(P+R) = (4/3)/(5/3) = 4/5 = 0.8

_POSITIVES = ["CC(=O)O", "c1ccccc1C(=O)O", "CC(=O)[O-]"]
_NEGATIVES = ["CCO", "CC(=O)OC", "CN"]


def test_score_definition_hand_computed_confusion_matrix():
    score = score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES)
    assert isinstance(score, DefinitionScore)
    assert (score.tp, score.fp, score.fn, score.tn) == (2, 0, 1, 3)
    assert score.n_positives == 3
    assert score.n_negatives == 3
    assert score.n_errors == 0
    assert score.n_exhausted == 0
    assert score.precision == pytest.approx(1.0)
    assert score.recall == pytest.approx(2 / 3)
    assert score.f1 == pytest.approx(0.8)


def test_score_definition_from_a_pre_parsed_node_gives_the_same_result():
    """Passing an already-parsed Node (as chem.parse_chemlog_tptp would
    produce) must be equivalent to passing the raw TPTP text -- dialect is
    then irrelevant (and ignored)."""
    from unicode_fol_kit.chem import parse_chemlog_tptp
    node = parse_chemlog_tptp(_CARBOXY_FORMULA)
    score = score_definition(node, _POSITIVES, _NEGATIVES)
    assert (score.tp, score.fp, score.fn, score.tn) == (2, 0, 1, 3)


def test_score_definition_every_input_molecule_is_accounted_for_exactly_once():
    score = score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES)
    pos_errors = sum(1 for e in score.errors if e["split"] == "positive")
    pos_exhausted = sum(1 for e in score.exhausted if e["split"] == "positive")
    neg_errors = sum(1 for e in score.errors if e["split"] == "negative")
    neg_exhausted = sum(1 for e in score.exhausted if e["split"] == "negative")
    assert score.tp + score.fn + pos_errors + pos_exhausted == score.n_positives
    assert score.fp + score.tn + neg_errors + neg_exhausted == score.n_negatives


# ---------------------------------------------------------------------------
# score_definition: honest failure categories -- never folded into "negative"
# ---------------------------------------------------------------------------

def test_score_definition_unknown_predicate_is_an_error_category_not_all_negative():
    """A formula naming a predicate the ChemLog vocabulary does not have
    must fail EVERY molecule via UninterpretedSymbol -- and must be reported
    as n_errors, NOT as tn/fn (which would misrepresent 'we could not
    evaluate this' as 'this definitely does not hold')."""
    score = score_definition(
        "?[A1]: totallyMadeUpPredicate(A1)", ["CC(=O)O"], ["CCO"])
    assert (score.tp, score.fp, score.fn, score.tn) == (0, 0, 0, 0)
    assert score.n_errors == 2
    assert score.n_exhausted == 0
    assert score.precision is None
    assert score.recall is None
    assert score.f1 is None
    assert [e["kind"] for e in score.errors] == ["UninterpretedSymbol", "UninterpretedSymbol"]
    assert {e["split"] for e in score.errors} == {"positive", "negative"}
    assert all("TotallyMadeUpPredicate" in e["message"] for e in score.errors)


def test_score_definition_invalid_smiles_is_a_structure_error_not_all_negative():
    """A syntactically invalid SMILES must be caught at the structure-build
    stage, not silently treated as a negative classification."""
    score = score_definition(_CARBOXY_FORMULA, ["not a smiles at all####"], ["CCO"])
    assert score.n_errors == 1
    assert score.errors[0]["stage"] == "structure"
    assert score.errors[0]["split"] == "positive"
    assert score.errors[0]["kind"] == "StructureBuildError"
    # the one clean negative is still scored normally
    assert (score.tp, score.fp, score.fn, score.tn) == (0, 0, 0, 1)


def test_score_definition_budget_exhaustion_is_its_own_category():
    """budget=1 exhausts every one of the 6 hand-derivation molecules after
    exactly 2 evaluator steps (verified directly against evaluate_detailed
    before writing this test: each needs >=2 steps just to enter the
    existential search, so a budget of 1 always exhausts, never decides).
    None of the 6 may show up as tp/fp/fn/tn or as an error."""
    score = score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES, budget=1)
    assert (score.tp, score.fp, score.fn, score.tn) == (0, 0, 0, 0)
    assert score.n_errors == 0
    assert score.n_exhausted == 6
    assert score.precision is None
    assert score.recall is None
    assert score.f1 is None
    assert all(item["steps"] >= 1 for item in score.exhausted)
    assert {item["smiles"] for item in score.exhausted} == set(_POSITIVES) | set(_NEGATIVES)


# ---------------------------------------------------------------------------
# score_definition: structure_cache reuse (the documented cost optimisation)
# ---------------------------------------------------------------------------

def test_score_definition_structure_cache_is_reused_across_calls():
    """Passing the SAME structure_cache dict to two calls (with the SAME
    aromatic=/computed= choice -- the default for both calls here) must
    build each distinct SMILES's FiniteStructure exactly once -- verified
    by identity (the second call's cached objects are the literal SAME
    Python objects the first call inserted, not rebuilt equivalents).

    The cache key is ``(smiles, naming, aromatic, computed)``, not the bare
    SMILES -- see ``test_score_definition_structure_cache_keyed_by_aromatic_
    and_computed_too`` below for why that extra key material matters."""
    cache = {}
    score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES, structure_cache=cache)
    populated_after_first = dict(cache)
    assert set(populated_after_first) == {
        (smiles, "chemlog", True, True)
        for smiles in set(_POSITIVES) | set(_NEGATIVES)}

    score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES, structure_cache=cache)
    for key, structure in populated_after_first.items():
        assert cache[key] is structure                  # same object, not rebuilt


def test_score_definition_structure_cache_keyed_by_aromatic_and_computed_too():
    """Regression test for the cache-staleness bug: before the fix,
    ``_structure_for``'s cache was keyed by the bare SMILES string alone, so
    two ``score_definition`` calls sharing one ``structure_cache`` but
    passing DIFFERENT ``aromatic=``/``computed=`` for the SAME molecule
    silently returned each other's structure instead of each building its
    own -- a genuinely wrong verdict, not merely a missed cache hit.

    Benzene "c1ccccc1", formula "exists a bAROMATIC-bonded pair": with the
    default ``aromatic=True`` every ring bond is typed ``bAROMATIC`` (never
    ``bSINGLE``/``bDOUBLE`` -- see test_chem.py's own benzene test), so the
    formula holds; with ``aromatic=False`` the SAME molecule is Kekulized
    instead (alternating ``bSINGLE``/``bDOUBLE``, ``bAROMATIC`` empty), so
    the IDENTICAL formula must NOT hold. Before the fix, the second call
    (sharing the first call's cache) found the bare SMILES already cached
    and returned the first call's ``aromatic=True`` structure verbatim, so
    the formula incorrectly kept holding under ``aromatic=False`` too.
    """
    cache = {}
    formula = "?[X,Y]: bAROMATIC(X,Y)"

    aromatic_score = score_definition(
        formula, ["c1ccccc1"], [], all_different=False, structure_cache=cache)
    assert (aromatic_score.tp, aromatic_score.fn) == (1, 0)

    kekulized_score = score_definition(
        formula, ["c1ccccc1"], [], all_different=False, aromatic=False,
        structure_cache=cache)
    assert (kekulized_score.tp, kekulized_score.fn) == (0, 1)

    # both structures were actually built and kept, under distinct keys --
    # the second call did not just silently reuse (or overwrite) the first.
    # The key carries naming too (always "chemlog" from this module, but the
    # cache is shared with entry points that expose it -- see _structure_for).
    assert set(cache) == {("c1ccccc1", "chemlog", True, True),
                          ("c1ccccc1", "chemlog", False, True)}


def test_score_definition_without_a_cache_still_dedupes_within_one_call():
    """A SMILES repeated across positives/negatives within ONE call is still
    only built once -- default structure_cache=None just means the dedup
    dict is call-local rather than caller-shared."""
    score = score_definition(_CARBOXY_FORMULA, ["CC(=O)O", "CC(=O)O"], ["CCO"])
    assert score.n_positives == 2
    assert (score.tp, score.fn) == (2, 0)     # both duplicate entries scored


# ---------------------------------------------------------------------------
# score_definition: dialect="unicode"
# ---------------------------------------------------------------------------

def test_score_definition_unicode_dialect_renames_to_chemlog_spelling():
    """A formula written in the kit's own unicode syntax with CAPITALISED
    (kit-convention) chemical predicate names must be renamed back to
    ChemLog's lower-case spelling before evaluation -- 'exists an oxygen
    atom' correctly distinguishes ethanol (has one) from ethane (has none)."""
    score = score_definition(
        "∃x O(x)", ["CCO"], ["CC"], dialect="unicode", all_different=False)
    assert (score.tp, score.fp, score.fn, score.tn) == (1, 0, 0, 1)
    assert score.precision == pytest.approx(1.0)
    assert score.recall == pytest.approx(1.0)
    assert score.f1 == pytest.approx(1.0)


# ---------------------------------------------------------------------------
# score_definition: error contract for a formula that never becomes an AST
# ---------------------------------------------------------------------------

def test_score_definition_rejects_non_node_non_str_formula():
    with pytest.raises(TypeError):
        score_definition(12345, ["CCO"], ["CC"])


def test_score_definition_rejects_unknown_dialect():
    with pytest.raises(ValueError, match="dialect"):
        score_definition("c(A1)", ["CCO"], ["CC"], dialect="bogus")


def test_score_definition_unparseable_tptp_text_raises_immediately():
    """A formula that never becomes a valid AST cannot be 'scored' -- this
    must raise ValueError immediately, NOT return a DefinitionScore with
    every molecule dumped into n_errors."""
    with pytest.raises(ValueError):
        score_definition("?[A1]: (c(A1) &", ["CCO"], ["CC"])


def test_score_definition_unparseable_unicode_text_raises_immediately():
    with pytest.raises(ValueError):
        score_definition("∃x (Gizmo(x", ["CCO"], ["CC"], dialect="unicode")


# ---------------------------------------------------------------------------
# DefinitionScore.to_dict()
# ---------------------------------------------------------------------------

def test_definition_score_to_dict_is_json_compatible():
    score = score_definition(_CARBOXY_FORMULA, _POSITIVES, _NEGATIVES)
    payload = score.to_dict()
    text = json.dumps(payload)
    round_tripped = json.loads(text)
    assert round_tripped["tp"] == 2
    assert round_tripped["fn"] == 1
    assert isinstance(round_tripped["errors"], list)
    assert isinstance(round_tripped["exhausted"], list)
