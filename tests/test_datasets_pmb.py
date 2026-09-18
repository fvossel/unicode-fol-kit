"""Tests for the PMB adapter (unicode_fol_kit.eval.datasets.pmb).

Tier 1 (below, always runs): SYNTHETIC fixtures under ``tests/fixtures/pmb/``, hand-
written in PMB's own ``p<NN>/d<NNNN>/<lang>.drs.sbn`` release layout (PMB's raw texts
carry no single licence statement this repository could safely redistribute under —
see ``pmb.py``'s module docstring — so nothing real is checked in). These drive
ordinary :class:`~unicode_fol_kit.eval.datasets.DatasetExample` field-mapping checks,
the same way ``test_datasets_groves.py``/``test_datasets_malls.py`` do for their own
adapters. Every expected ``fol_conclusion`` string below was independently confirmed
by running the actual fixture text through ``parse_sbn``/``drs_to_fol`` and reading off
the result (see the docstring of each test) — not derived from the loader itself.

Tier 2, opt-in (bottom of the file): a ROBUSTNESS/coverage differential against a real,
locally-extracted PMB gold release, skipped unless ``$UFK_PMB_SBN_DIR`` points at one —
the same "skip without a real file/binary" precedent ``test_datasets_fracas.py`` and the
0.24.0 APE live tests already set. It is a robustness differential, not a translation-
ACCURACY one: PMB ships no independent gold FOL to compare against, so "correct" here
means "parses under parse_sbn's own documented subset and round-trips", never "matches
an external answer" (see ``unicode_fol_kit/eval/datasets/pmb.py``'s module docstring for
the measured numbers this differential reproduces).
"""

import os
from pathlib import Path

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.drt.export import drs_to_fol
from unicode_fol_kit.drt.parser import SBNSyntaxError, parse_sbn
from unicode_fol_kit.eval.datasets import DATASET_INFO
from unicode_fol_kit.eval.datasets.pmb import load_pmb

_FIXTURES = Path(__file__).parent / "fixtures" / "pmb"


def _by_id(examples):
    return {e.id: e for e in examples}


# =============================================================================
# Tier 1 — synthetic fixtures (tests/fixtures/pmb), always runs.
# =============================================================================

def test_load_pmb_walks_a_directory_and_finds_every_document():
    examples = list(load_pmb(_FIXTURES))
    assert {e.id for e in examples} == {
        "p00/d0001", "p00/d0002", "p00/d0003", "p01/d0099"}


def test_field_mapping_for_a_successful_flat_document():
    # tests/fixtures/pmb/p00/d0001/en.drs.sbn: "dog.n.01\nbark.v.01 Agent -1" (plus a
    # %%% header and %-comments, both discarded). Hand-derived exactly as the module
    # docstring's grammar specifies: dog.n.01 -> referent e1, predicate DogN01;
    # bark.v.01 -> referent e2, predicate BarkV01; "Agent -1" on line 2 (content-line
    # index 2) points back one line to index 1 -> Agent(e2, e1). No NEGATION anywhere,
    # so both existentials close directly over the flat conjunction — confirmed by
    # running the fixture text through parse_sbn/drs_to_fol directly.
    e = _by_id(load_pmb(_FIXTURES))["p00/d0001"]
    assert e.nl_premises == ()
    assert e.fol_premises == ()
    assert e.nl_conclusion == "A dog barks."
    assert e.fol_conclusion == "∃e1 ∃e2 (DogN01(e1) ∧ BarkV01(e2) ∧ Agent(e2, e1))"
    assert e.label is None
    assert e.known_bad is False
    assert e.meta == {
        "part": "p00", "doc": "d0001", "lang": "en", "parse_error": None,
        "sbn_mapping": {
            "predicates": {"dog.n.01": "DogN01", "bark.v.01": "BarkV01"},
            "constants": {},
        },
    }
    # Independent second route: audit_examples' own oracle (parse + well-formedness)
    # agrees the emitted formula is clean.
    parsed = e.parse_conclusion()
    assert parsed.ok is True
    assert api.check(parsed.formula).ok is True


def test_field_mapping_for_a_negated_document_via_the_connector_dialect():
    # p00/d0002/en.drs.sbn uses the real release's own CONNECTOR dialect ("  NEGATION
    # <1", space-indented — pure cosmetic alignment in this dialect, see
    # unicode_fol_kit.drt.parser's module docstring): dog.n.01 (concept 1, e1);
    # NEGATION <1 attaches Neg to context (1-1)=0, the root; bark.v.01 (concept 2, e2)
    # inside it, Agent -1 counting back one CONCEPT (not content line) to e1.
    e = _by_id(load_pmb(_FIXTURES))["p00/d0002"]
    assert e.nl_conclusion == "The dog does not bark."
    assert e.fol_conclusion == "∃e1 (DogN01(e1) ∧ ¬∃e2 (BarkV01(e2) ∧ Agent(e2, e1)))"
    assert e.meta["parse_error"] is None
    assert e.meta["sbn_mapping"]["predicates"] == {
        "dog.n.01": "DogN01", "bark.v.01": "BarkV01"}


def test_a_document_outside_the_sbn_subset_is_surfaced_not_dropped():
    # p00/d0003 uses POSSIBILITY, which this SBN subset refuses by name (see
    # unicode_fol_kit.drt.parser). load_pmb must not drop the document: it still
    # yields a DatasetExample, with the refusal recorded in meta rather than raised.
    e = _by_id(load_pmb(_FIXTURES))["p00/d0003"]
    assert e.fol_conclusion is None
    assert e.meta["sbn_mapping"] is None
    assert "POSSIBILITY" in e.meta["parse_error"]
    assert "not supported" in e.meta["parse_error"]
    # This fixture ships no sibling en.raw on purpose: best-effort, not an error.
    assert e.nl_conclusion is None


def test_known_bad_ids_is_independent_of_parse_success():
    examples = _by_id(load_pmb(_FIXTURES, known_bad_ids={"p01/d0099"}))
    assert examples["p01/d0099"].known_bad is True
    assert examples["p00/d0001"].known_bad is False
    # p00/d0003 failed to parse but was never asked to be known_bad — the two
    # mechanisms (curated vs. this adapter's own refusal) stay independent.
    assert examples["p00/d0003"].known_bad is False


def test_load_pmb_accepts_an_explicit_iterable_of_file_paths():
    one = _FIXTURES / "p00" / "d0001" / "en.drs.sbn"
    examples = list(load_pmb([one]))
    assert [e.id for e in examples] == ["p00/d0001"]


def test_load_pmb_refuses_a_single_path_that_is_not_a_directory():
    one = _FIXTURES / "p00" / "d0001" / "en.drs.sbn"
    with pytest.raises(ValueError, match="not a directory"):
        list(load_pmb(one))


def test_load_pmb_refuses_duplicate_document_ids():
    one = _FIXTURES / "p00" / "d0001" / "en.drs.sbn"
    with pytest.raises(ValueError, match="duplicate document id"):
        list(load_pmb([one, one]))


def test_dataset_info_registers_pmb_with_its_two_layer_license():
    info = DATASET_INFO["pmb"]
    assert "ODC-BY" in info["license"]
    assert "NOT" in info["license"]
    assert info["source_url"] == "https://pmb.let.rug.nl/data.php"
    assert "Abzianidze" in info["citation_hint"]


# =============================================================================
# Tier 2 — a real PMB gold release, opt-in.
# =============================================================================

_REAL = os.environ.get("UFK_PMB_SBN_DIR")
real_release = pytest.mark.skipif(
    not (_REAL and Path(_REAL).is_dir()),
    reason="set $UFK_PMB_SBN_DIR to a local PMB gold release directory "
           "(e.g. a pmb-x.y.z release's data/en/gold)")


@real_release
def test_real_pmb_release_is_a_robustness_coverage_differential():
    """Every real ``.drs.sbn`` file either (a) parses and round-trips byte-identically
    through ``drs_to_fol -> to_unicode_str -> api.parse_any -> to_unicode_str``, or
    (b) raises exactly :class:`SBNSyntaxError` naming an out-of-scope construct. ANY
    OTHER exception is a HARD FAILURE — this is the robustness/coverage differential
    the roadmap asked for (PMB ships no independent gold FOL to check translation
    ACCURACY against), and it is exactly the class of bug 2-3 hand fixtures cannot
    surface. No numeric floor is asserted (it would drift with whichever PMB release
    the caller points this at); the accept/refuse counts are printed for a human to
    read, the same style as ``ace_coverage``."""
    files = sorted(Path(_REAL).rglob("*.drs.sbn"))
    assert files, f"no *.drs.sbn files found under {_REAL}"

    accepted = 0
    refused = 0
    hard_failures = []
    for path in files:
        text = path.read_text(encoding="utf-8")
        try:
            drs, _mapping = parse_sbn(text)
        except SBNSyntaxError:
            refused += 1
            continue
        except Exception as e:                        # the point of this test
            hard_failures.append((path, repr(e)))
            continue
        try:
            s1 = drs_to_fol(drs).to_unicode_str()
            parsed_back = api.parse_any(s1)
            if not parsed_back.ok or parsed_back.formula.to_unicode_str() != s1:
                hard_failures.append((path, f"round-trip mismatch: {s1!r}"))
                continue
        except Exception as e:                        # ditto
            hard_failures.append((path, repr(e)))
            continue
        accepted += 1

    total = accepted + refused + len(hard_failures)
    print(f"\nPMB SBN coverage over {total} real document(s): {accepted} "
          f"accepted/round-tripped, {refused} refused (SBNSyntaxError), "
          f"{len(hard_failures)} hard failure(s).")
    if hard_failures:
        detail = "\n".join(f"  {p}: {msg}" for p, msg in hard_failures[:10])
        pytest.fail(f"{len(hard_failures)} document(s) raised something other than "
                    f"SBNSyntaxError, or failed to round-trip:\n{detail}")
    assert accepted > 0
    assert refused >= 0


@real_release
def test_load_pmb_over_the_real_release_never_drops_a_document():
    """load_pmb's own contract end-to-end: exactly one DatasetExample per real
    ``.drs.sbn`` file, every refusal surfaced in ``meta`` rather than silently
    skipped, and every successful ``fol_conclusion`` re-parses cleanly."""
    files = list(Path(_REAL).rglob("*.drs.sbn"))
    examples = list(load_pmb(_REAL))
    assert len(examples) == len(files)
    n_parsed = 0
    for e in examples:
        if e.meta["parse_error"] is None:
            assert e.fol_conclusion is not None
            assert e.meta["sbn_mapping"] is not None
            assert api.parse_any(e.fol_conclusion).ok is True
            n_parsed += 1
        else:
            assert e.fol_conclusion is None
            assert e.meta["sbn_mapping"] is None
    assert n_parsed > 0
