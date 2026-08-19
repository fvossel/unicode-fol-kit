"""The plural-DRT pair Card/Part: construction, parsing, export, verdicts.

Every expectation here is hand-derived first and only then pinned: the
strict-op shifts are arithmetic on paper (`> 2` IS `>= 3` over natural
counts, `< 3` IS `<= 2`), the no-capture case is the one fresh-name bug a
counter seeded from the box referents must not have, and the entailment
pair (>=3 proves >=2, >=2 refutes >=3) is the smallest non-trivial claim
whose BOTH directions Z3 can decide — a one-direction check would also
pass on an export that dropped the count entirely.
"""

import pytest

from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.drt import (
    CARD_OPS, Card, DRSSyntaxError, Part, drs_to_fol, parse_drs,
)
from unicode_fol_kit.drt.nodes import DRS, Pred


# ---------------------------------------------------------------------------
# Construction: what a Card/Part refuses to be
# ---------------------------------------------------------------------------

def test_card_ops_is_the_pinned_five():
    assert CARD_OPS == ("=", ">=", "<=", ">", "<")


@pytest.mark.parametrize("build,fragment", [
    (lambda: Card("g", "==", 3), "op '=='"),
    (lambda: Card("g", ">=", -1), "non-negative"),
    (lambda: Card("g", ">=", True), "non-negative int"),
    (lambda: Card("g", "<", 0), "unsatisfiable by spelling"),
    (lambda: Card("3bad", ">=", 2), "'3bad'"),
    (lambda: Part("m", "3bad"), "'3bad'"),
    (lambda: Part("_x", "g"), "'_x'"),
])
def test_malformed_cards_and_parts_raise_at_construction(build, fragment):
    with pytest.raises((ValueError, TypeError), match=fragment):
        build()


def test_card_zero_is_legal_where_satisfiable():
    # "= 0" and "<= 0" are meaningful (an empty group); only "< 0" is not.
    assert Card("g", "=", 0).n == 0
    assert Card("g", "<=", 0).n == 0


# ---------------------------------------------------------------------------
# Box notation: render, parse, round-trip
# ---------------------------------------------------------------------------

def test_box_notation_round_trips_through_the_drs_parser():
    drs = parse_drs("[g, m | Card(g, >=, 3), Part_of(m, g)]")
    assert drs.conditions == (Card("g", ">=", 3), Part("m", "g"))
    assert drs.to_box_notation() == "[g, m | Card(g, >=, 3), Part_of(m, g)]"
    assert parse_drs(drs.to_box_notation()) == drs


def test_a_pred_merely_named_card_stays_a_pred():
    # Disambiguation is by the comparison operator, not the name: term
    # arguments mean the user genuinely has a predicate called Card.
    drs = parse_drs("[x, y | Card(x, y)]")
    assert drs.conditions == (Pred("Card", ("x", "y")),)


def test_part_of_with_the_wrong_arity_is_a_parse_error():
    with pytest.raises(DRSSyntaxError, match="exactly two arguments"):
        parse_drs("[x, y, z | Part_of(x, y, z)]")


def test_serialization_carries_all_fields():
    assert Card("g", ">=", 3).to_dict() == {
        "_type": "Card", "ref": "g", "op": ">=", "n": 3}
    assert Part("m", "g").to_dict() == {
        "_type": "Part", "member": "m", "group": "g"}


# ---------------------------------------------------------------------------
# Accessibility
# ---------------------------------------------------------------------------

def test_a_card_over_an_undeclared_referent_fails_validation():
    with pytest.raises(ValueError, match="not access"):
        DRS((), (Card("g", ">=", 2),)).validate()


def test_a_part_reaches_referents_of_the_enclosing_box():
    # Standard DRT accessibility: the inner box may use the outer's g.
    parse_drs("[g | Card(g, =, 2), [m | Part_of(m, g)] -> [ | Man(m)]]"
              ).validate()


# ---------------------------------------------------------------------------
# Export: the counting quantifier, with the strict-op shifts
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("op,n,rendered", [
    ("=", 3, "∃g ∃=3 p1 Part_of(p1, g)"),
    (">=", 3, "∃g ∃≥3 p1 Part_of(p1, g)"),
    ("<=", 5, "∃g ∃≤5 p1 Part_of(p1, g)"),
    # Count carries only =/>=/<=; the strict ops shift by one, which is
    # exact over natural counts: > 2 IS >= 3, < 3 IS <= 2.
    (">", 2, "∃g ∃≥3 p1 Part_of(p1, g)"),
    ("<", 3, "∃g ∃≤2 p1 Part_of(p1, g)"),
])
def test_each_card_op_lowers_to_its_hand_computed_count(op, n, rendered):
    fol = drs_to_fol(DRS(("g",), (Card("g", op, n),)))
    assert fol.to_unicode_str() == rendered
    # And the produced Count formula is first-class kit syntax.
    assert MSFLParser().parse(rendered) == fol


def test_the_fresh_counting_variable_dodges_a_declared_p1():
    fol = drs_to_fol(DRS(("p1",), (Card("p1", ">=", 2),)))
    assert fol.to_unicode_str() == "∃p1 ∃≥2 p2 Part_of(p2, p1)"


def test_part_exports_as_the_binary_part_of_atom():
    fol = drs_to_fol(parse_drs("[g | Part_of(john, g)]"))
    assert fol.to_unicode_str() == "∃g Part_of(john, g)"


# ---------------------------------------------------------------------------
# Verdicts: the counting force is real, in both directions
# ---------------------------------------------------------------------------

def test_at_least_three_proves_at_least_two_but_not_conversely():
    three = drs_to_fol(DRS(("g",), (Card("g", ">=", 3),)))
    two = drs_to_fol(DRS(("g",), (Card("g", ">=", 2),)))
    assert api.prove(two, premises=[three]).status == "proved"
    assert api.prove(three, premises=[two]).status == "refuted"
