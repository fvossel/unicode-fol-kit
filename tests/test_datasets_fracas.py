"""Tests for the FraCaS adapter (unicode_fol_kit.eval.datasets.fracas).

The fixture (``tests/fixtures/fracas_mini.xml``) is SYNTHETIC — sentences
written for this suite, in the real file's XML shape — for two reasons: the
source problem set carries no licence statement, so it is not committed
here, and the structural cases that matter for a reader (heading resets,
premise idx against document order, whitespace across source lines, XML
entities, a problem with no question at all) can be put side by side in six
problems instead of hunted across 346.

That the reader also matches the REAL file is pinned separately by
``test_the_real_problem_set_reads_as_measured``, which skips unless
``$UFK_FRACAS_XML`` points at a local copy; its expected numbers are the
ones the adapter's module docstring documents.

Every expectation below was read off the fixture (or, for the solver, hand-
derived and then confirmed against the prover) — nothing here is invented.
"""

import os
from pathlib import Path

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.eval.datasets import (
    DATASET_INFO, DatasetExample, audit_examples,
)
from unicode_fol_kit.eval.datasets.fracas import (
    FRACAS_ANSWERS, ace_census, load_fracas, solve_example,
)

_FIXTURES = Path(__file__).parent / "fixtures"
_FIXTURE = _FIXTURES / "fracas_mini.xml"


def _examples(**kwargs):
    return list(load_fracas(_FIXTURE, **kwargs))


def _by_id(examples):
    return {e.id: e for e in examples}


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------

def test_the_fixture_loads_in_file_order_with_prefixed_ids():
    examples = _examples()
    assert [e.id for e in examples] == [
        "fracas:000", "fracas:001", "fracas:002", "fracas:003",
        "fracas:004", "fracas:005",
    ]
    assert all(isinstance(e, DatasetExample) for e in examples)


def test_premises_come_in_idx_order_not_document_order():
    # Problem 002 writes idx=2 first: the reader must sort by idx, so the
    # "first premise" sentence has to come out first.
    example = _by_id(_examples())["fracas:002"]
    assert example.nl_premises[0].startswith("The first premise")
    assert example.meta["premise_count"] == 2


def test_source_line_breaks_and_entities_are_normalised():
    examples = _by_id(_examples())
    # A premise split across two indented source lines becomes one line.
    assert examples["fracas:002"].nl_premises[1] == (
        "The second premise spans two source lines.")
    # XML entities are decoded, not passed through as escapes.
    assert examples["fracas:002"].meta["answer_text"] == "Don't know"
    assert examples["fracas:005"].nl_premises == (
        "A premise stands alone, and 1 < 2.",)


def test_headings_track_document_order_and_reset_finer_levels():
    examples = _by_id(_examples())
    # Before any section marker: no heading is invented.
    first = examples["fracas:000"]
    assert (first.meta["section"], first.meta["subsection"]) == (None, None)
    assert first.meta["section_title"] is None
    # Number and title are kept apart, so a caller filters on the number.
    assert examples["fracas:001"].meta["section"] == "1"
    assert examples["fracas:001"].meta["section_title"] == "FIRST TOPIC"
    assert examples["fracas:001"].meta["subsection_title"] == "Plain Problems"
    # The subsubsection applies where it is declared ...
    assert examples["fracas:003"].meta["subsubsection"] == "1.2.1"
    # ... and a NEW section clears both finer levels: 004 must not inherit
    # 1.2.1, and its own subsection is 2.1.
    assert examples["fracas:004"].meta["section"] == "2"
    assert examples["fracas:004"].meta["subsection"] == "2.1"
    assert examples["fracas:004"].meta["subsubsection"] is None


def test_every_answer_value_survives_including_undef():
    labels = [e.label for e in _examples()]
    assert labels == ["yes", "yes", "unknown", "no", "undef", "undef"]
    assert set(labels) <= set(FRACAS_ANSWERS)


def test_the_remaining_source_fields_land_in_meta():
    examples = _by_id(_examples())
    assert examples["fracas:001"].meta["why"] == (
        "Trivially, from the premise itself.")
    assert examples["fracas:003"].meta["note"] == "Both premises are needed here."
    assert examples["fracas:004"].meta["nonstandard"] is True
    assert examples["fracas:003"].meta["nonstandard"] is False
    assert examples["fracas:001"].meta["question"] == (
        "Does every reader parse a file?")


def test_a_problem_without_a_question_loads_with_none_not_an_empty_string():
    # Empty <q>/<h>/<a> must not become "" — absent and empty-string are
    # different things for a caller deciding whether it can score it.
    example = _by_id(_examples())["fracas:005"]
    assert example.nl_conclusion is None
    assert example.meta["question"] is None
    assert example.meta["answer_text"] is None
    assert example.nl_premises  # the premises are still there


# ---------------------------------------------------------------------------
# Filters
# ---------------------------------------------------------------------------

def test_the_section_filter_keeps_a_whole_top_level_section():
    kept = _examples(sections={"1"})
    assert [e.id for e in kept] == ["fracas:001", "fracas:002", "fracas:003"]
    assert not _examples(sections={"9"})


def test_the_answer_filter_is_how_undef_gets_dropped():
    # The loader never drops undef on its own — the caller asks for it.
    kept = _examples(answers={"yes", "no", "unknown"})
    assert [e.label for e in kept] == ["yes", "yes", "unknown", "no"]
    assert len(_examples()) == 6


def test_an_answer_filter_outside_the_vocabulary_is_refused():
    with pytest.raises(ValueError, match="outside"):
        _examples(answers={"maybe"})


def test_known_bad_ids_flag_the_prefixed_id():
    examples = _by_id(_examples(known_bad_ids=frozenset({"fracas:003"})))
    assert examples["fracas:003"].known_bad is True
    assert examples["fracas:001"].known_bad is False


# ---------------------------------------------------------------------------
# The no-FOL contract
# ---------------------------------------------------------------------------

def test_no_example_carries_gold_fol_and_the_audit_says_so_vacuously():
    examples = _examples()
    assert all(e.fol_premises == () for e in examples)
    assert all(e.fol_conclusion is None for e in examples)
    assert all(e.parse_premises() == () for e in examples)
    assert all(e.parse_conclusion() is None for e in examples)
    # audit_examples reports ok because there is nothing to audit — pinned
    # so the vacuity is a documented property, not a surprise later.
    report = audit_examples(examples)
    assert all(row["ok"] and not row["defects"] for row in report)


def test_the_provenance_is_registered():
    info = DATASET_INFO["fracas"]
    assert info["source_url"].endswith("fracas.xml")
    assert "licence" in info["license"] or "license" in info["license"]
    assert "FraCaS" in info["citation_hint"]


# ---------------------------------------------------------------------------
# Malformed inputs are named
# ---------------------------------------------------------------------------

_HEAD = '<?xml version="1.0" encoding="UTF-8"?>\n'


def _write(tmp_path, body, name="bad.xml"):
    path = tmp_path / name
    path.write_text(_HEAD + body, encoding="utf-8")
    return path


@pytest.mark.parametrize("body,fragment", [
    ("<other-root><problem id='1' fracas_answer='yes'/></other-root>",
     "root element"),
    ("<fracas-problems><problem fracas_answer='yes'>"
     "<p idx='1'>A.</p></problem></fracas-problems>", "no id"),
    ("<fracas-problems><problem id='001'>"
     "<p idx='1'>A.</p></problem></fracas-problems>", "no fracas_answer"),
    ("<fracas-problems><problem id='001' fracas_answer='perhaps'>"
     "<p idx='1'>A.</p></problem></fracas-problems>", "outside"),
    ("<fracas-problems>"
     "<problem id='001' fracas_answer='yes'><p idx='1'>A.</p></problem>"
     "<problem id='001' fracas_answer='no'><p idx='1'>B.</p></problem>"
     "</fracas-problems>", "duplicate"),
    ("<fracas-problems><problem id='001' fracas_answer='yes'>"
     "<p idx='1'>A.</p><p idx='3'>B.</p></problem></fracas-problems>",
     "non-contiguous"),
    ("<fracas-problems><problem id='001' fracas_answer='yes'>"
     "<p>A.</p></problem></fracas-problems>", "numeric idx"),
    ("<fracas-problems><problem id='001' fracas_answer='yes'>"
     "<p idx='1'>  </p></problem></fracas-problems>", "empty premise"),
])
def test_a_malformed_file_is_refused_by_name(tmp_path, body, fragment):
    with pytest.raises(ValueError, match=fragment):
        list(load_fracas(_write(tmp_path, body)))


# ---------------------------------------------------------------------------
# solve_example — the translation is injected
# ---------------------------------------------------------------------------

#: Hand-written formulas for the fixture's sentences. This IS the seam the
#: adapter documents: a caller's translator sits here, and the kit only
#: decides. Hand-derived, then confirmed against the prover.
_TRANSLATION = {
    "Every reader parses a file.": "∀x (Reader(x) → Parses(x))",
    "No fixture is a corpus.": "∀x (Fixture(x) → ¬Corpus(x))",
    "This file is a fixture.": "Fixture(f)",
    "This file is a corpus.": "Corpus(f)",
    "Some checks are strict.": "∃x (Check(x) ∧ Strict(x))",
    "All checks are strict.": "∀x (Check(x) → Strict(x))",
}


def _translate(sentence):
    return _TRANSLATION[sentence]


def test_an_entailed_hypothesis_is_yes():
    example = _by_id(_examples())["fracas:001"]
    result = solve_example(example, translate=_translate)
    assert result["predicted"] == "yes"
    assert result["label"] == "yes"
    assert result["verdict"]["status"] == "proved"
    assert result["verdict_negated"] is None
    # The translations travel with the result, so a wrong prediction can be
    # traced back to the translation that caused it.
    assert result["premises"] == ["∀x (Reader(x) → Parses(x))"]
    assert result["hypothesis"] == "∀x (Reader(x) → Parses(x))"


def test_a_contradicted_hypothesis_is_no():
    # "No fixture is a corpus." + "This file is a fixture." ⊨ ¬Corpus(f).
    result = solve_example(_by_id(_examples())["fracas:003"],
                           translate=_translate)
    assert result["predicted"] == "no"
    assert result["label"] == "no"
    assert result["verdict_negated"]["status"] == "proved"


def test_an_underdetermined_hypothesis_is_unknown():
    # "Some checks are strict." settles neither direction of "All checks
    # are strict." — and the gold label here is undef, which the result
    # reports untouched: predicting is not scoring.
    result = solve_example(_by_id(_examples())["fracas:004"],
                           translate=_translate)
    assert result["predicted"] == "unknown"
    assert result["label"] == "undef"


def test_a_translator_may_return_a_node_instead_of_a_string():
    parser = MSFLParser()
    result = solve_example(
        _by_id(_examples())["fracas:001"],
        translate=lambda s: parser.parse(_TRANSLATION[s]))
    assert result["predicted"] == "yes"


def test_on_indefinite_separates_established_unknown_from_prover_failure():
    """With z3 both legs of the underdetermined problem come back definitively
    REFUTED, so "unknown" is ESTABLISHED and even 'abstain' labels it. With
    the resolution backend alone both legs are indefinite (it cannot refute),
    so 'abstain' yields None and 'raise' raises: a prover that merely gave up
    must never be credited with a correct "unknown"."""
    example = _by_id(_examples())["fracas:004"]

    established = solve_example(example, translate=_translate,
                                on_indefinite="abstain")
    assert established["predicted"] == "unknown"
    assert established["verdict"]["status"] == "refuted"
    assert established["verdict_negated"]["status"] == "refuted"

    abstained = solve_example(example, translate=_translate,
                              backends=["resolution"], on_indefinite="abstain")
    assert abstained["predicted"] is None
    assert abstained["verdict"]["status"] == "unknown"

    with pytest.raises(ValueError, match="indefinite"):
        solve_example(example, translate=_translate, backends=["resolution"],
                      on_indefinite="raise")


@pytest.mark.parametrize("kwargs,fragment", [
    ({"on_indefinite": "guess"}, "on_indefinite"),
    ({"translate": lambda s: "∀x ("}, "does not parse"),
    ({"translate": lambda s: 17}, "expected a formula"),
])
def test_solve_example_refuses_what_it_cannot_decide(kwargs, fragment):
    example = _by_id(_examples())["fracas:001"]
    call = {"translate": _translate}
    call.update(kwargs)
    with pytest.raises(ValueError, match=fragment):
        solve_example(example, **call)


def test_a_problem_without_a_hypothesis_cannot_be_decided():
    example = _by_id(_examples())["fracas:005"]
    with pytest.raises(ValueError, match="no hypothesis"):
        solve_example(example, translate=_translate)


# ---------------------------------------------------------------------------
# The real file, and the ACE census — both opt-in
# ---------------------------------------------------------------------------

_REAL = os.environ.get("UFK_FRACAS_XML")
real_file = pytest.mark.skipif(
    not (_REAL and Path(_REAL).is_file()),
    reason="set $UFK_FRACAS_XML to a local fracas.xml")


@real_file
def test_the_real_problem_set_reads_as_measured():
    """The adapter's documented numbers, re-measured through the loader."""
    from collections import Counter

    examples = list(load_fracas(_REAL))
    assert len(examples) == 346
    assert sum(len(e.nl_premises) for e in examples) == 536
    assert Counter(e.label for e in examples) == {
        "yes": 203, "unknown": 98, "no": 33, "undef": 12}
    assert sum(e.meta["nonstandard"] for e in examples) == 41
    assert [e.id for e in examples if e.nl_conclusion is None] == [
        "fracas:276", "fracas:305", "fracas:309", "fracas:310"]
    # Nine sections, and none of them leaks a subsection from the previous.
    sections = {e.meta["section"] for e in examples}
    assert sections == {str(n) for n in range(1, 10)}
    for section in sorted(sections):
        first = next(e for e in examples if e.meta["section"] == section)
        assert first.meta["subsection"] == f"{section}.1"


@pytest.mark.skipif(
    not __import__("unicode_fol_kit.ace", fromlist=["x"]).ape_available(),
    reason="no APE binary reachable")
def test_the_ace_census_reports_one_row_per_sentence():
    """A measurement helper, so what is pinned is its SHAPE and honesty: one
    row per sentence, statuses from the coverage vocabulary, nothing
    aggregated away. (The fixture's sentences use words outside APE's small
    built-in lexicon, so most rows are `not_ace` — that is a fact about the
    lexicon, not a defect, and exactly why the helper reports per sentence
    with APE's own diagnosis attached.)"""
    examples = _examples()
    rows = ace_census(examples)
    expected = sum(len(e.nl_premises) + (e.nl_conclusion is not None)
                   for e in examples)
    assert len(rows) == expected
    assert {r["role"] for r in rows} == {"premise", "hypothesis"}
    assert all(r["status"] in
               ("ok", "tptp_unsupported", "tptp_unread", "not_ace", "infra")
               for r in rows)
    first = rows[0]
    assert first["id"] == "fracas:000"
    assert first["index"] == 0
    assert first["sentence"] == "A tester writes a fixture."
    # The hypothesis row carries no premise index.
    assert all(r["index"] is None for r in rows if r["role"] == "hypothesis")
