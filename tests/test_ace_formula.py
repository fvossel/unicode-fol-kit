"""The ACE formula route: modality, questions, counting, arithmetic — and
the three-way agreement.

Offline except two live smoke tests: the route is a pure function on DRS
terms, and the terms are recorded. Hand-checked expectations first, then
the structural pins (every modal formula re-parses IDENTICALLY through the
kit's own modal parser — the loop ACE → APE → kit node → unicode syntax →
parser → same node, closed), then the three-way differential that welds
this route to the DRS route (which the mapping tests weld to Attempto's
reference TPTP — so all three implementations agree pairwise).
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit import Box, Diamond, MSFLParser, Obligatory, Permitted
from unicode_fol_kit.ace import (
    AceUnsupportedError, ace_drs_to_formula, ace_to_formula, ape_available,
    map_ace_drs, parse_ape_drs,
)
from unicode_fol_kit.drt import drs_to_fol
from unicode_fol_kit.eval.equivalence import equivalent

live = pytest.mark.skipif(not ape_available(),
                          reason="no APE binary reachable")

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
BY_TAG = {r["tag"]: r for r in ROWS}


def _formula(tag):
    return ace_drs_to_formula(parse_ape_drs(BY_TAG[tag]["drs"]))


# ---------------------------------------------------------------------------
# The four modal boxes, hand-checked
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,node_type,rendered", [
    ("modal-must", Box, "□∃e1 Wait(e1, john)"),
    ("modal-can", Diamond, "◇∃e1 Wait(e1, john)"),
    ("modal-should", Obligatory, "Ⓞ∃e1 Wait(e1, john)"),
    ("modal-may", Permitted, "Ⓟ∃e1 Wait(e1, john)"),
])
def test_each_modal_box_lands_on_its_documented_operator(tag, node_type,
                                                         rendered):
    result = _formula(tag)
    assert isinstance(result.formula, node_type)
    assert result.formula.to_unicode_str() == rendered
    assert result.kind == "assertion"
    assert result.modalities == (tag.split("-")[1],)


def test_modality_under_a_universal_nests_correctly():
    # "Every man must wait." — the universal OUTSIDE, the box INSIDE:
    # ∀x(Man(x) → □∃e Wait(e,x)), not □∀x(...). APE's DRS fixes that scope
    # (the => box contains the must box) and the translation must keep it.
    result = _formula("modal-universal")
    assert result.formula.to_unicode_str() == "∀x1 (Man(x1) → □∃e1 Wait(e1, x1))"
    assert result.modalities == ("must",)


MODAL_TAGS = ["modal-must", "modal-can", "modal-should", "modal-may",
              "modal-universal"]


@pytest.mark.parametrize("tag", MODAL_TAGS)
def test_every_modal_formula_reparses_identically(tag):
    formula = _formula(tag).formula
    assert MSFLParser(modal=True).parse(formula.to_unicode_str()) == formula


# ---------------------------------------------------------------------------
# Questions
# ---------------------------------------------------------------------------

def test_a_wh_question_is_an_open_formula():
    result = _formula("question-who")
    assert result.kind == "wh_question"
    assert result.query_variables == (("x1", "who"),)
    # x1 stays FREE: answering is model finding, not proof.
    assert result.formula.to_unicode_str() == "∃e1 Wait(e1, x1)"
    from unicode_fol_kit import free_variables
    assert {v.name for v in free_variables(result.formula)} == {"x1"}


def test_a_yesno_question_is_closed_but_keeps_its_force():
    result = _formula("question-yesno")
    assert result.kind == "yesno_question"
    assert result.query_variables == ()
    from unicode_fol_kit import free_variables
    assert not free_variables(result.formula)
    # Same content as the assertion "John waits." — the difference lives
    # in kind, which is exactly the bit ace_to_fol could not carry.
    assert result.formula.to_unicode_str() == "∃e1 Wait(e1, john)"


def test_a_question_mixed_with_assertions_refuses():
    mixed = parse_ape_drs(
        "drs([A,B],[object(A,man,countable,na,eq,1)-1/2,"
        "predicate(B,wait,A)-1/4,"
        "question(drs([C],[query(C,who)-2/1,predicate(C,sleep,A)-2/2]))])")
    with pytest.raises(AceUnsupportedError, match="split the text"):
        ace_drs_to_formula(mixed)


# ---------------------------------------------------------------------------
# Cardinality and arithmetic (ACE-4) — the constructs only THIS route carries
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,rendered", [
    # The [...] maximality of exactly/at most becomes a counting
    # quantifier over the whole scope — the DISTRIBUTIVE reading
    # ("exactly 2 dogs bark" = exactly two individual barkers; collective
    # maximality is not FO-expressible), documented at box_with_lists.
    ("card-exact", "∃=2 g1 ∃e1 (Dog(g1) ∧ Bark(e1, g1))"),
    ("card-leq", "∃≤5 g1 ∃e1 (Man(g1) ∧ Wait(e1, g1))"),
    # Plain cardinalities take the same collective group shape as the
    # DRS route (the three-way differential below pins the equivalence).
    ("card-geq", "∃g1 ∃e1 (∃≥3 p1 Part_of(p1, g1) ∧ "
                 "∀x1 (Part_of(x1, g1) → Man(x1)) ∧ Wait(e1, g1))"),
    ("collective", "∃x1 ∃e1 ∃g1 (Part_of(john, g1) ∧ Table(x1) ∧ "
                   "Lift(e1, g1, x1) ∧ Part_of(mary, g1) ∧ "
                   "∃=2 p1 Part_of(p1, g1))"),
    ("distributive-each-of", "∃g1 (Part_of(john, g1) ∧ "
                             "∀x1 (Part_of(x1, g1) → ∃e1 Wait(e1, x1)) ∧ "
                             "Part_of(mary, g1) ∧ ∃=2 p1 Part_of(p1, g1))"),
])
def test_each_counting_sentence_lands_on_its_hand_checked_formula(tag,
                                                                  rendered):
    result = _formula(tag)
    assert result.formula.to_unicode_str() == rendered
    assert result.kind == "assertion"
    # Count formulas are first-class kit syntax: the loop closes.
    assert MSFLParser().parse(rendered) == result.formula


def test_arithmetic_translates_and_the_arith_route_decides_it():
    formula = _formula("arithmetic").formula
    assert formula.to_unicode_str() == "1 + 2 = 3"
    # The DEFAULT z3 route reads + uninterpreted (measured; documented at
    # translate.arithmetic) — deciding the fragment is is_valid_arith's
    # job, and it must prove the truth and refute a falsehood.
    from unicode_fol_kit.atp.z3_arith import is_valid_arith
    assert is_valid_arith(formula, sort="int") is True
    assert is_valid_arith(MSFLParser().parse("1 + 2 = 4"), sort="int") is False


# ---------------------------------------------------------------------------
# Refusals — what stays undecided on BOTH routes
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,fragment", [
    ("naf", "negation as failure"),
    ("command", "imperative"),
])
def test_what_neither_route_carries_raises_here_too(tag, fragment):
    with pytest.raises(AceUnsupportedError) as exc_info:
        _formula(tag)
    assert fragment in str(exc_info.value)


# ---------------------------------------------------------------------------
# The three-way agreement
# ---------------------------------------------------------------------------

PURE_ROWS = [r for r in ROWS if r["status"] != "not_ace"
             and map_ace_drs(parse_ape_drs(r["drs"])).complete]


@pytest.mark.parametrize("row", PURE_ROWS, ids=[r["tag"] for r in PURE_ROWS])
def test_formula_route_agrees_with_the_drs_route(row):
    """On the shared fragment the two translations are independent code
    paths (this route's compositional translator vs drt.export's standard
    translation) over one shared atomic-condition table — Z3 must find
    them equivalent. The mapping tests weld the DRS route to Attempto's
    TPTP, so all three agree pairwise."""
    via_formula = ace_drs_to_formula(parse_ape_drs(row["drs"])).formula
    via_drs = drs_to_fol(map_ace_drs(parse_ape_drs(row["drs"])).drs)
    assert equivalent(via_formula, via_drs).equivalent, row["tag"]


def test_the_three_way_slice_is_not_vacuous():
    # 38 of the 55 corpus sentences since ACE-4/5 (the five plural tags
    # joined the complete set); a floor so growth doesn't churn this file.
    assert len(PURE_ROWS) >= 35


# ---------------------------------------------------------------------------
# Live
# ---------------------------------------------------------------------------

@live
def test_ace_to_formula_live_matches_the_recorded_route():
    live_result = ace_to_formula("Every man must wait.")
    assert live_result == _formula("modal-universal")


@live
def test_a_live_modal_formula_reaches_the_kits_modal_backends():
    from unicode_fol_kit.fol.qml import qml_is_valid

    # □φ → ◇φ holds on any SERIAL frame (D); "must wait" entails "can
    # wait" there. A smoke test that the produced nodes are first-class
    # citizens of the kit's modal machinery, not just printable.
    from unicode_fol_kit import Implies
    must = ace_to_formula("John must wait.").formula
    can = ace_to_formula("John can wait.").formula
    assert qml_is_valid(Implies(must, can), frame="KD") is True
