"""Tests for :mod:`unicode_fol_kit.ace` — the APE runner and the TPTP route.

Two layers, mirroring the E-prover tests' structure:

- **Offline** (the bulk): everything derivable from the RECORDED fixture
  ``ape_5f4d535_corpus_v1.json`` — APE's raw output for every sentence of the
  hand-written corpus ``ace_corpus_v1.tsv``, captured at the pinned APE commit
  named in the filename. The classification tests re-derive statuses from the
  raw recorded output through the CURRENT code, so a routing change fails here
  without APE installed. Eight sentences additionally carry HAND-CHECKED
  expected formulas written literally in this file, independent of how the
  fixture was generated (the fixture's own ``kit_formulas`` are a regression
  pin, not a correctness argument — these eight are the correctness argument).
- **Live** (skips without an APE binary): a handful of fresh APE calls
  compared byte-for-byte against the fixture's ``drs``/``tptp`` — the drift
  alarm for an APE or lexicon change. stderr reasons are deliberately NOT
  compared verbatim: they embed SWI-Prolog variable numbers (``_3930``) that
  are not stable across SWI versions; live assertions check the condition
  NAME instead.

The corpus is hand-written for this kit (no third-party texts). Fixture and
corpus pin each other: same sentences, same order, and the recorded status
counts are asserted exactly, so a silently changed corpus row fails loudly.
"""

import json
import os
from pathlib import Path

import pytest

from unicode_fol_kit.ace import (
    AceParseError, AceTptpUnreadError, AceTptpUnsupportedError, ApeResult,
    ace_coverage, ace_to_fol, ape_available, run_ape,
)
from unicode_fol_kit.ace import runner as ace_runner
from unicode_fol_kit.fol.tptp_input import TptpParsingError, parse_tptp

FIXTURES = Path(__file__).parent / "fixtures"

live = pytest.mark.skipif(not ape_available(),
                          reason="no APE binary (env/PATH/WSL) — offline "
                                 "fixture tests still cover the routing")


def load_corpus():
    rows = []
    for line in (FIXTURES / "ace_corpus_v1.tsv").read_text(
            encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            tag, sentence = line.split("\t", 1)
            rows.append((tag, sentence))
    return rows


def load_fixture():
    return json.loads(
        (FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(encoding="utf-8"))


CORPUS = load_corpus()
FIXTURE = load_fixture()
BY_TAG = {row["tag"]: row for row in FIXTURE}


# ---------------------------------------------------------------------------
# Corpus/fixture integrity — the two files pin each other.
# ---------------------------------------------------------------------------

def test_fixture_covers_the_corpus_exactly_in_order():
    assert [(r["tag"], r["sentence"]) for r in FIXTURE] == CORPUS


def test_the_recorded_status_census():
    """38 ok / 11 tptp_unsupported / 1 tptp_unread / 5 not_ace, and no other
    status. Exact on purpose: a corpus edit must re-record the fixture, and a
    routing change that reclassifies anything must be a conscious act.
    (ACE-4 added card-greater and re-recorded: 37 ok became 38.)"""
    census = {}
    for row in FIXTURE:
        census[row["status"]] = census.get(row["status"], 0) + 1
    assert census == {"ok": 38, "tptp_unsupported": 11,
                      "tptp_unread": 1, "not_ace": 5}


def test_every_not_ace_row_recorded_an_error_message():
    for row in FIXTURE:
        if row["status"] == "not_ace":
            assert any(m["importance"] == "error" for m in row["messages"]), \
                row["tag"]


# ---------------------------------------------------------------------------
# Hand-checked formulas — the correctness argument for the TPTP route.
# Each expected string was derived by hand from the sentence's unique ACE
# reading and checked against the recorded TPTP, not copied from the code's
# output history. Event referents are explicit (neo-Davidsonian), and the
# donkey sentence gets the universal reading of its indefinite.
# ---------------------------------------------------------------------------

HAND_CHECKED = {
    "svo-intransitive": ["∃a Predicate1(a, wait, John)"],
    "universal": ["∀a (Man(a) → ∃b Predicate1(b, wait, a))"],
    "donkey": ["∀a ∀b ∀c (Farmer(a) ∧ (Donkey(b) ∧ Predicate2(c, own, a, b))"
               " → ∃d Predicate2(d, beat, a, b))"],
    "negation-verb": ["¬∃a Predicate1(a, wait, John)"],
    "if-then": ["∀a ∀b ∀c (Man(a) ∧ (Dog(b) ∧ Predicate2(c, see, a, b))"
                " → ∃d Predicate1(d, wait, a))"],
    "or-sentences": ["∃a (Predicate1(a, wait, John)"
                     " ∨ ∃b Predicate1(b, wait, Mary))"],
    "card-geq": ["∃a ∃b (Predicate1(a, wait, b)"
                 " ∧ Object(b, man, countable, na, geq, 3))"],
    "collective": ["∃a ∃b ∃c (Object(a, na, countable, na, eq, 2)"
                   " ∧ (Has_part(a, Mary) ∧ (Predicate2(b, lift, a, c)"
                   " ∧ (Table(c) ∧ Has_part(a, John)))))"],
}


@pytest.mark.parametrize("tag", sorted(HAND_CHECKED))
def test_hand_checked_formula_from_recorded_tptp(tag):
    """Recorded raw TPTP → repair → kit reader → exactly the hand-derived
    formula. Runs the CURRENT translation code on the PINNED input."""
    row = BY_TAG[tag]
    result = ApeResult(drs=row["drs"], tptp=row["tptp"], messages=(),
                       stderr="")
    formulas, _repaired = ace_runner._formulas_from(result)
    assert [f.to_unicode_str() for f in formulas] == HAND_CHECKED[tag]


def test_every_ok_row_rederives_its_recorded_formulas():
    """Regression net over ALL 37 ok rows: the current code turns the
    recorded raw TPTP into the recorded formulas. Not a correctness proof
    (the recording used the same code) — the eight hand-checked rows above
    are that — but any translation change surfaces here row by row."""
    for row in FIXTURE:
        if row["status"] != "ok":
            continue
        result = ApeResult(drs=row["drs"], tptp=row["tptp"], messages=(),
                           stderr="")
        formulas, repaired = ace_runner._formulas_from(result)
        assert [f.to_unicode_str() for f in formulas] == row["kit_formulas"], \
            row["tag"]
        assert repaired == row["tptp_repaired"], row["tag"]


# ---------------------------------------------------------------------------
# The upstream juxtaposed-atom bug and its repair.
# ---------------------------------------------------------------------------

def test_the_collective_tptp_is_malformed_and_the_repair_heals_it():
    """APE really does print ``(table C)``: the raw recorded text must FAIL
    the kit reader (otherwise the repair guards nothing), and the repaired
    text must parse. Pins both halves so an upstream fix — the raw text
    starting to parse — shows up as a failure here and retires the repair."""
    raw = BY_TAG["collective"]["tptp"]
    assert "(table C)" in raw
    with pytest.raises(TptpParsingError):
        parse_tptp(raw)
    fixed, n = ace_runner._repair_ape_tptp(raw)
    assert n == 1
    parse_tptp(fixed)  # must not raise


def test_the_repair_is_a_no_op_on_every_other_recorded_output():
    """The safety property that justifies auto-repair: the pattern matches
    ONLY the malformation. Across every other recorded TPTP text — 47 rows
    of legal output — the regex must fire zero times."""
    for row in FIXTURE:
        if row["tag"] == "collective" or not row["tptp"]:
            continue
        _fixed, n = ace_runner._repair_ape_tptp(row["tptp"])
        assert n == 0, row["tag"]


# ---------------------------------------------------------------------------
# Routing — statuses re-derived from recorded raw output by current code.
# ---------------------------------------------------------------------------

def test_modal_naf_query_command_rows_are_all_tptp_unsupported():
    expected_condition = {
        "modal-must": "must", "modal-can": "can", "modal-should": "should",
        "modal-may": "may", "modal-universal": "must", "naf": "~",
        "question-who": "query", "command": "command",
    }
    for tag, condition in expected_condition.items():
        row = BY_TAG[tag]
        assert row["status"] == "tptp_unsupported", tag
        assert condition in row["detail"], tag
        # and the DRS carries the construct, which is what ACE-3 will read:
        assert row["drs"] != "drs([],[])", tag


def test_the_yesno_question_is_refused_for_its_conjecture_role():
    """'Does John wait?' survives APE's TPTP route AS A CONJECTURE — the one
    case where flattening roles would silently turn a question into the
    assertion that John waits. The guard must catch it offline."""
    row = BY_TAG["question-yesno"]
    assert row["status"] == "tptp_unsupported"
    assert "conjecture" in row["detail"]
    result = ApeResult(drs=row["drs"], tptp=row["tptp"], messages=(),
                       stderr="")
    with pytest.raises(AceTptpUnsupportedError, match="conjecture"):
        ace_runner._formulas_from(result)


def test_arithmetic_is_tptp_unread_not_silently_dropped():
    """'1 + 2 = 3.' — APE emits infix arithmetic outside both standard FOF
    and the kit reader's fragment; the status says so and the raw TPTP is
    preserved for ACE-4."""
    row = BY_TAG["arithmetic"]
    assert row["status"] == "tptp_unread"
    assert "1+2=3" in row["tptp"].replace(" ", "")
    result = ApeResult(drs=row["drs"], tptp=row["tptp"], messages=(),
                       stderr="")
    with pytest.raises(AceTptpUnreadError) as excinfo:
        ace_runner._formulas_from(result)
    assert excinfo.value.tptp == row["tptp"]


def test_reified_cardinality_flags_exactly_the_recorded_set():
    flagged = {row["tag"] for row in FIXTURE
               if row.get("reified_cardinality")}
    assert flagged == {"card-geq", "card-plain", "card-greater",
                       "collective", "distributive-each-of", "mass-noun"}
    # Re-derive one from raw output so the flag is code, not archive:
    row = BY_TAG["mass-noun"]
    result = ApeResult(drs=row["drs"], tptp=row["tptp"], messages=(),
                       stderr="")
    formulas, _ = ace_runner._formulas_from(result)
    assert ace_runner._has_reified_object(formulas)


def test_documented_conventions_in_the_not_ace_rows():
    """possessive-unbound and lexicon-gap are corpus rows on purpose: the
    first pins ACE's binding convention (bare 'his' cannot take the same
    sentence's subject; 'his own' can — see possessive-own being ok), the
    second pins that the SMALL BUILT-IN LEXICON, not ACE's grammar, rejects
    a real English word."""
    assert BY_TAG["possessive-own"]["status"] == "ok"
    unbound = BY_TAG["possessive-unbound"]
    assert unbound["status"] == "not_ace"
    assert any("his" in m["value"] for m in unbound["messages"])
    gap = BY_TAG["lexicon-gap"]
    assert gap["status"] == "not_ace"
    assert any(m["value"] == "whistles" for m in gap["messages"])


# ---------------------------------------------------------------------------
# XML parsing and discovery — pure unit tests.
# ---------------------------------------------------------------------------

def test_ape_xml_parsing_extracts_messages_with_positions():
    xml = """<?xml version="1.0" encoding="UTF-8"?>
<apeResult>
  <duration tokenizer="0.001" parser="0.001" refres="0.000"/>
  <drs>drs([],[])</drs>
  <tptp></tptp>
  <messages>
    <message importance="error" type="word" sentence="1" token=""
             value="waitz" repair="wait"/>
    <message importance="error" type="sentence" sentence="1" token="3"
             value="Every man &lt;&gt; waitz." repair="hint"/>
  </messages>
</apeResult>"""
    drs, tptp, messages = ace_runner._parse_ape_xml(xml)
    assert drs == "drs([],[])" and tptp == ""
    assert [m.token for m in messages] == [None, 3]
    assert messages[0].repair == "wait"
    assert messages[0].is_error


def test_non_xml_output_is_an_infrastructure_error():
    with pytest.raises(RuntimeError, match="not the expected"):
        ace_runner._parse_ape_xml("Segmentation fault")


def test_env_override_forces_the_wsl_route(monkeypatch):
    monkeypatch.setenv("UFK_APE_CMD", "wsl:/opt/APE/ape.exe")
    assert ace_runner._discover() == (["wsl.exe", "-e", "/opt/APE/ape.exe"],
                                      True)
    monkeypatch.setenv("UFK_APE_CMD", r"C:\tools\ape.exe")
    assert ace_runner._discover() == ([r"C:\tools\ape.exe"], False)


def test_discovery_miss_raises_the_documented_error(monkeypatch):
    monkeypatch.setattr(ace_runner, "_discover", lambda: None)
    with pytest.raises(ace_runner.ApeUnavailableError, match="UFK_APE_CMD"):
        run_ape("John waits.")


def test_coverage_classifies_from_stubbed_results(monkeypatch):
    """ace_coverage end to end with APE stubbed out — one row per status,
    exercised through the SAME branch structure live calls take."""
    canned = {
        "ok.": ApeResult("drs([A],[predicate(A,wait,named('John'))-1/1])",
                         "fof(f1, axiom, (? [A] : "
                         "(predicate1(A,wait,'John')))).", (), ""),
        "modal.": ApeResult("drs([],[must(drs([A],[predicate(A,wait,"
                            "named('John'))-1/3]))])", "", (), "ERROR: must"),
        "bad.": ApeResult("drs([],[])", "", (ace_runner.ApeMessage(
            "error", "word", 1, None, "waitz", "wait"),), ""),
    }
    monkeypatch.setattr(ace_runner, "run_ape",
                        lambda text, **kw: canned[text])
    rows = ace_coverage(["ok.", "modal.", "bad."])
    assert [r.status for r in rows] == ["ok", "tptp_unsupported", "not_ace"]
    assert rows[0].formulas and not rows[0].reified_cardinality
    assert rows[1].detail == "ERROR: must"
    assert "waitz" in rows[2].detail


# ---------------------------------------------------------------------------
# Live — drift alarm against the pinned fixture, plus the ulex mechanism.
# ---------------------------------------------------------------------------

@live
@pytest.mark.parametrize("tag", ["donkey", "collective", "modal-must",
                                 "unknown-word"])
def test_live_ape_still_matches_the_recorded_fixture(tag):
    """Fresh APE output must equal the recording byte for byte (drs + tptp).
    Failing here means the local APE differs from the pinned commit — bump
    the pin and re-record, or fix the installation. stderr is deliberately
    not compared (SWI variable numbers are version-dependent)."""
    row = BY_TAG[tag]
    result = run_ape(row["sentence"])
    assert result.drs == row["drs"], tag
    assert result.tptp == row["tptp"], tag


@live
def test_live_the_tptp_route_end_to_end():
    formulas = ace_to_fol("Every farmer who owns a donkey beats it.")
    assert [f.to_unicode_str() for f in formulas] == HAND_CHECKED["donkey"]
    assert ace_to_fol("") == []


@live
def test_live_a_question_raises_not_asserts():
    with pytest.raises(AceTptpUnsupportedError, match="conjecture"):
        ace_to_fol("Does John wait?")


@live
def test_live_the_ulex_remedies_the_lexicon_gap():
    """The documented remedy for the small built-in lexicon, demonstrated on
    the exact corpus sentence it rejects."""
    with pytest.raises(AceParseError):
        ace_to_fol("A man whistles.")
    formulas = ace_to_fol("A man whistles.",
                          ulex="iv_finsg(whistles, whistle).")
    assert [f.to_unicode_str() for f in formulas] == \
        ["∃a ∃b (Predicate1(a, whistle, b) ∧ Man(b))"]


@live
def test_live_not_ace_carries_the_repair_hint():
    with pytest.raises(AceParseError) as excinfo:
        ace_to_fol("Every man waitz.")
    first = excinfo.value.messages[0]
    assert (first.value, first.repair) == ("waitz", "wait")
