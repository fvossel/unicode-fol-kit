"""``fol_to_drs``: the standard translation, run backwards, pinned hard.

The strong claim is the inverse-on-image property: for every DRS ``d`` the
kit can build, ``drs_to_fol(fol_to_drs(drs_to_fol(d))) == drs_to_fol(d)``
NODE-identically — export, import, export is a fixed point. That is
checked over every mappable corpus DRS (real APE output, all condition
shapes) and over hand-built boxes covering the two documented
canonicalizations (strict Card bounds return shifted, ``Part_of`` atoms
return as typed ``Part``). Refusals are the other half of the contract:
everything outside the export's image must raise ``FolToDrsError`` with a
reason, never come back approximated.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.ace import map_ace_drs, parse_ape_drs
from unicode_fol_kit.drt import (
    Card, FolToDrsError, drs_to_fol, fol_to_drs, parse_drs,
)

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
MAPPABLE = [r for r in ROWS if r["status"] != "not_ace"
            and map_ace_drs(parse_ape_drs(r["drs"])).complete]


# ---------------------------------------------------------------------------
# Inverse on the image
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("row", MAPPABLE, ids=[r["tag"] for r in MAPPABLE])
def test_export_import_export_is_a_fixed_point_on_the_corpus(row):
    exported = drs_to_fol(map_ace_drs(parse_ape_drs(row["drs"])).drs)
    assert drs_to_fol(fol_to_drs(exported)) == exported


@pytest.mark.parametrize("box", [
    "[x1, e1 | Man(x1), Wait(e1, x1)]",
    "[ | [x1 | Man(x1)] -> [e1 | Wait(e1, x1)]]",
    "[x1 | Man(x1), ~[e1 | Wait(e1, x1)]]",
    "[ | [x1, e1 | Man(x1), Wait(e1, x1)] ∨ [x2, e2 | Dog(x2), Bark(e2, x2)]]",
    "[g1, e1 | Card(g1, >=, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)],"
    " Wait(e1, g1)]",
    "[g1 | Card(g1, =, 2), Part_of(john, g1), Part_of(mary, g1)]",
    "[x1 | Number(x1), x1 = c_30]",
    # Nested: a negation inside a duplex consequent.
    "[ | [x1 | Man(x1)] -> [ | ~[e1 | Wait(e1, x1)]]]",
])
def test_export_import_export_is_a_fixed_point_on_hand_boxes(box):
    exported = drs_to_fol(parse_drs(box))
    assert drs_to_fol(fol_to_drs(exported)) == exported


def test_a_round_tripped_box_is_node_identical_when_no_canonicalization_fires():
    drs = parse_drs("[x1, e1 | Man(x1), Wait(e1, x1), ~[e2 | Sleep(e2, x1)]]")
    assert fol_to_drs(drs_to_fol(drs)) == drs


def test_the_strict_card_bound_returns_in_shifted_form():
    # Card(g, >, 2) exports as ∃≥3 — the same claim over natural counts —
    # and reads back canonically as Card(g, >=, 3). Documented, and the
    # formula level is where the identity holds (the fixed-point tests).
    drs = parse_drs("[g1 | Card(g1, >, 2), [x1 | Part_of(x1, g1)] -> [ | Man(x1)]]")
    back = fol_to_drs(drs_to_fol(drs))
    assert Card("g1", ">=", 3) in back.conditions


def test_a_parser_built_formula_lands_on_its_hand_written_box():
    formula = MSFLParser().parse(
        "∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2)"
        " → ∃e2 Beat(e2, x1, x2))")
    assert fol_to_drs(formula) == parse_drs(
        "[ | [x1, x2, e1 | Farmer(x1), Donkey(x2), Own(e1, x1, x2)]"
        " -> [e2 | Beat(e2, x1, x2)]]")


# ---------------------------------------------------------------------------
# Refusals, by name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text,modal,fragment", [
    ("□∃e1 Wait(e1, john)", True, "no classical DRS condition"),
    ("Ⓞ∃e1 Wait(e1, john)", True, "no classical DRS condition"),
    ("∀x1 Man(x1)", False, "without an implication body"),
    ("∀x1 (Man(x1) ↔ Human(x1))", False, "without an implication body"),
    # The formula-level counting reading is strictly stronger than Card.
    ("∃=2 x1 (Dog(x1) ∧ Bark(x1))", False, "FORMULA-level counting"),
    ("1 + 2 = 3", False, "term in argument position"),
    # A free variable becomes an undeclared referent.
    ("∃e1 Wait(e1, x1)", False, "free variable"),
])
def test_what_the_image_does_not_contain_is_refused_by_name(text, modal,
                                                            fragment):
    formula = MSFLParser(modal=modal).parse(text)
    with pytest.raises(FolToDrsError, match=fragment):
        fol_to_drs(formula)


def test_the_error_is_a_value_error_for_plain_callers():
    assert issubclass(FolToDrsError, ValueError)
