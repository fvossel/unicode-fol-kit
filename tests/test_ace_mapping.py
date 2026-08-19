"""ACE-DRS → kit DRS: hand-checked mappings, honest refusals, and THE
differential — the kit route against Attempto's own reference translation.

Offline throughout: the corpus DRSs and TPTP outputs are recorded fixtures,
Z3 runs locally. The differential is the correctness argument for the whole
mapping: for every sentence BOTH routes cover, drs_to_fol over our mapped
DRS must be Z3-equivalent to APE's own TPTP read by the kit — two
implementations, one written in Zurich and one here, agreeing formula by
formula. The vocabulary alignment (`ace._align`) that makes the comparison
possible is itself part of the claim: a wrong alignment rule makes
sentences INequivalent and this file loud, never quietly green.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.ace import (
    AceUnsupportedError, ace_to_drs, ape_available, condition_statistics,
    map_ace_drs, parse_ape_drs,
)
from unicode_fol_kit.ace._align import align_ape_tptp_formula, conjoin
from unicode_fol_kit.ace.mapping import _named_constant
from unicode_fol_kit.ace.runner import _repair_ape_tptp
from unicode_fol_kit.drt import drs_to_fol, is_predicate_name, parse_drs
from unicode_fol_kit.drt.nodes import Card, Eq, Part, Pred
from unicode_fol_kit.eval.equivalence import equivalent
from unicode_fol_kit.fol.tptp_input import parse_tptp

live = pytest.mark.skipif(not ape_available(),
                          reason="no APE binary reachable")

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
BY_TAG = {r["tag"]: r for r in ROWS}
ACE_ROWS = [r for r in ROWS if r["status"] != "not_ace"]

#: Which corpus sentences the classical DRS core carries COMPLETELY —
#: pinned as an exact set, so both a silently shrinking and a silently
#: growing mapping fail here (growth must arrive together with the
#: milestone that justifies it, and with this list's edit).
COMPLETE_TAGS = {
    "svo-intransitive", "svo-transitive", "svo-ditransitive", "universal",
    "universal-transitive", "no-quantifier", "negation-verb",
    "negation-sentence", "if-then", "or-sentences", "vp-conjunction",
    "vp-disjunction", "donkey", "relative-clause", "anaphora-pronoun",
    "anaphora-definite", "anaphora-variable", "adjective",
    "copula-adjective", "copula-identity", "genitive", "of-relation",
    "pp-modifier", "adverb", "adverb-pp-combined", "there-is",
    "transitive-pp", "possessive-own", "two-sentences", "comparative",
    "number-copula", "mass-noun", "string-value",
    # ACE-4/5 growth: since Card/Part entered the DRS core, plurals and
    # cardinalities map — collectively (the group stays the verb's term).
    "card-geq", "card-plain", "card-greater", "collective",
    "distributive-each-of",
}


def _mapping(tag):
    return map_ace_drs(parse_ape_drs(BY_TAG[tag]["drs"]))


# ---------------------------------------------------------------------------
# Verdicts over the whole corpus
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("row", ACE_ROWS, ids=[r["tag"] for r in ACE_ROWS])
def test_the_complete_set_is_exactly_the_pinned_one(row):
    mapping = map_ace_drs(parse_ape_drs(row["drs"]))
    assert mapping.complete == (row["tag"] in COMPLETE_TAGS), row["tag"]
    if mapping.complete:
        # map_ace_drs validates internally; do it again HERE so a future
        # refactor that drops the internal call still meets the invariant.
        mapping.drs.validate()
        assert not mapping.unsupported
    else:
        assert mapping.drs is None, "a partial DRS must never be returned"
        assert mapping.unsupported, "incomplete but nothing reported"


def test_milestones_point_where_the_plan_says():
    # card-geq and collective left this list when ACE-4/5 landed: they map
    # now (see COMPLETE_TAGS). What remains unsupported HERE is exactly
    # what lives at formula level (the [...] maximality of exactly/at most,
    # arithmetic) plus the two honest "undecided" refusals.
    milestones = {tag: {r.milestone for r in _mapping(tag).unsupported}
                  for tag in ("modal-must", "question-who", "card-exact",
                              "card-leq", "arithmetic", "naf", "command")}
    assert milestones["modal-must"] == {"ACE-3"}
    assert "ACE-3" in milestones["question-who"]
    assert milestones["card-exact"] == {"ACE-4"}
    assert milestones["card-leq"] == {"ACE-4"}
    assert milestones["arithmetic"] == {"ACE-4"}
    # No milestone promised for naf and commands — an empty marker is the
    # honest "undecided", not a forgotten label.
    assert milestones["naf"] == {""}
    assert milestones["command"] == {""}


def test_the_formula_level_refusals_name_their_carrier():
    # The DRS route must not just refuse the maximality list and
    # arithmetic — it must point at ace_to_formula, which carries both.
    for tag in ("card-exact", "arithmetic"):
        reasons = " ".join(r.reason for r in _mapping(tag).unsupported)
        assert "ace_to_formula" in reasons, tag


def test_statistics_carry_functor_and_arity():
    stats = condition_statistics(
        map_ace_drs(parse_ape_drs(r["drs"])) for r in ACE_ROWS)
    assert stats[("object/6", "mapped", "")] >= 35
    assert stats[("predicate/3", "mapped", "")] >= 20
    # has_part crossed from unsupported/ACE-5 to mapped when Part landed.
    assert stats[("has_part/2", "mapped", "")] >= 5
    assert ("has_part/2", "unsupported", "ACE-5") not in stats
    assert stats[("must", "unsupported", "ACE-3")] >= 2
    assert stats[("[…]", "unsupported", "ACE-4")] == 2  # exactly / at most


# ---------------------------------------------------------------------------
# Hand-checked mappings
# ---------------------------------------------------------------------------

def test_transitive_sentence_by_hand():
    drs = _mapping("svo-transitive").drs
    assert drs.referents == ("x1", "e1")
    assert drs.conditions == (Pred("Dog", ("x1",)),
                              Pred("See", ("e1", "mary", "x1")))


def test_the_donkey_sentence_matches_the_hand_written_box_notation():
    ours = _mapping("donkey").drs
    reference = parse_drs(
        "[ | [x1, x2, e1 | Farmer(x1), Donkey(x2), Own(e1, x1, x2)]"
        " -> [e2 | Beat(e2, x1, x2)] ]")
    assert drs_to_fol(ours) == drs_to_fol(reference)


def test_the_copula_becomes_equality_and_the_event_is_gone():
    drs = _mapping("copula-adjective").drs
    assert Eq("john", "x1") in drs.conditions
    # The be-event referent was dropped: only the property's x1 remains.
    assert drs.referents == ("x1",)


def test_ditransitive_argument_order_is_subject_direct_indirect():
    # "John gives Mary a book." — A is the book (direct), Mary indirect.
    drs = _mapping("svo-ditransitive").drs
    assert Pred("Give", ("e1", "john", "x1", "mary")) in drs.conditions


def test_values_become_c_constants():
    assert Eq("x1", "c_30") in _mapping("number-copula").drs.conditions
    assert Eq("x1", "c_Johnny") in _mapping("string-value").drs.conditions


def test_a_proper_name_never_lands_in_the_referent_namespace():
    # "E1" would collide with an event referent name; the rule must take
    # the explicit constant form instead.
    assert _named_constant("John") == "john"
    assert _named_constant("E1") == "c_E1"
    assert _named_constant("X") == "c_X"


# ---------------------------------------------------------------------------
# Hand-checked plural mappings (ACE-4/5)
# ---------------------------------------------------------------------------

def test_a_counted_plural_maps_to_card_plus_the_membership_duplex():
    # "At least 3 men wait." — collectively: ONE waiting event whose
    # subject is the group, |group| >= 3, every member a man. NOT three
    # individual waits (that reading belongs to "each of").
    drs = _mapping("card-geq").drs
    assert drs.referents == ("g1", "e1")
    membership = parse_drs("[ | [x1 | Part_of(x1, g1)] -> [ | Man(x1)]]"
                           ).conditions[0]
    assert drs.conditions == (Card("g1", ">=", 3), membership,
                              Pred("Wait", ("e1", "g1")))


def test_the_strict_op_survives_the_mapping_untranslated():
    # "More than 2 men wait." — the mapping records what APE said (>, 2);
    # the one-off shift to the counting quantifier is the EXPORT's job
    # (pinned in test_drt_card_part), not the mapping's.
    assert Card("g1", ">", 2) in _mapping("card-greater").drs.conditions


def test_more_than_two_and_at_least_three_are_the_same_claim():
    # ...and after export the shift makes them Z3-equivalent — two
    # different ACE sentences, two different Card ops, one meaning.
    geq = drs_to_fol(_mapping("card-geq").drs)
    greater = drs_to_fol(_mapping("card-greater").drs)
    assert equivalent(geq, greater).equivalent
    # Non-vacuity for the counting force: "3 men" (=) is NOT "at least 3".
    plain = drs_to_fol(_mapping("card-plain").drs)
    assert not equivalent(plain, geq).equivalent


def test_a_coordination_maps_to_a_closed_group():
    # "John and Mary lift a table." — both Part_of atoms name constants,
    # the cardinality closes the group at exactly 2, and the lift-event
    # takes the GROUP as its subject: the table is lifted together.
    conditions = _mapping("collective").drs.conditions
    assert Part("john", "g1") in conditions
    assert Part("mary", "g1") in conditions
    assert Card("g1", "=", 2) in conditions
    assert Pred("Lift", ("e1", "g1", "x1")) in conditions


def test_each_of_distributes_through_the_duplex_not_an_operator():
    # "Each of John and Mary waits." — APE compiles the distribution into
    # an ordinary => box over the members; no Dist operator needed, which
    # is exactly why the core extension stayed at Card/Part.
    drs = _mapping("distributive-each-of").drs
    duplex = parse_drs("[ | [x1 | Part_of(x1, g1)] -> [e1 | Wait(e1, x1)]]"
                       ).conditions[0]
    assert duplex in drs.conditions
    # And z3 draws the distributed consequence: John himself waits.
    from unicode_fol_kit import MSFLParser, api
    verdict = api.prove(MSFLParser().parse("∃e1 Wait(e1, john)"),
                        premises=[drs_to_fol(drs)])
    assert verdict.status == "proved"


def test_the_error_object_separates_unsupported_from_mapped_rows():
    # modal-must: the must-shell is refused, its inner predicate still
    # gets a mapped row — the report keeps both kinds side by side.
    mapping = map_ace_drs(parse_ape_drs(BY_TAG["modal-must"]["drs"]))
    error = AceUnsupportedError("probe", mapping.rows)
    assert error.unsupported
    assert all(r.verdict == "unsupported" for r in error.unsupported)
    # The full report is on .rows: mapped rows too, for context.
    assert len(error.unsupported) < len(error.rows)


# ---------------------------------------------------------------------------
# The differential: our route vs Attempto's reference translation
# ---------------------------------------------------------------------------

#: Sentences whose reference translation is itself UNDER-translated:
#: Attempto's TPTP keeps the counted ``object/6`` (and ``has_part``)
#: reified — one witness plus an inert annotation, no counting force.
#: Since ACE-4/5 the kit route DOES carry that force (Card → Count), so
#: demanding Z3-equivalence here would demand our translation be wrong.
#: mass-noun is flagged ``reified_cardinality`` too but stays in: its
#: reified object carries op ``na`` — nothing was lost, and its
#: differential row keeps proving the alignment handles inert objects.
UNDER_TRANSLATED_TAGS = {
    "card-geq", "card-plain", "card-greater", "collective",
    "distributive-each-of",
}

DIFF_ROWS = [r for r in ROWS
             if r["status"] == "ok" and r["tag"] in COMPLETE_TAGS
             and r["tag"] not in UNDER_TRANSLATED_TAGS]


def test_the_exclusion_list_tracks_the_fixtures_own_honesty_flag():
    # The recording pipeline flags reified TPTP itself; the exclusion set
    # must be exactly those flags minus the documented mass-noun exception
    # — so a re-recorded corpus that reifies MORE (or less) forces this
    # file to take a position rather than silently shrinking the diff.
    flagged = {r["tag"] for r in ROWS if r.get("reified_cardinality")}
    assert UNDER_TRANSLATED_TAGS == flagged - {"mass-noun"}


@pytest.mark.parametrize("row", DIFF_ROWS, ids=[r["tag"] for r in DIFF_ROWS])
def test_our_drs_route_is_z3_equivalent_to_apes_own_tptp(row):
    mapping = map_ace_drs(parse_ape_drs(row["drs"]))
    ours = drs_to_fol(mapping.drs)
    theirs = conjoin([align_ape_tptp_formula(tf.formula)
                      for tf in parse_tptp(_repair_ape_tptp(row["tptp"])[0])])
    result = equivalent(ours, theirs)
    assert result.equivalent, (
        f"{row['tag']}: {ours.to_unicode_str()}  vs  "
        f"{theirs.to_unicode_str()}")


def test_the_differential_actually_covers_a_meaningful_slice():
    # 33 of the 55 corpus sentences are doubly covered as of ACE-4/5 (the
    # five under-translated tags are counted out above, mass-noun is in).
    # A floor rather than an exact count: new corpus sentences may grow it,
    # but a mapping or alignment regression that silently EMPTIES the
    # differential must fail here instead of passing vacuously.
    assert len(DIFF_ROWS) >= 30


def test_the_equivalence_probe_can_still_see_a_difference():
    """Non-vacuity: the same machinery must REJECT a wrong pair, or every
    green above is meaningless."""
    ours = drs_to_fol(_mapping("svo-intransitive").drs)
    wrong = drs_to_fol(_mapping("negation-verb").drs)
    assert not equivalent(ours, wrong).equivalent


# ---------------------------------------------------------------------------
# The drt widening ACE-2 forced (underscore predicates)
# ---------------------------------------------------------------------------

def test_underscore_predicates_now_enter_the_drs_core():
    """0.23.1 widened the GRAMMAR's PREDICATE to NAME's continuation class
    (chem's Has_bond_to); drt.nodes tracked the old rule until now, so a
    predicate the fol parser accepts could not be put in a DRS. Pinned
    here because ACE's comparative mapping (Tall_comp_than) hits it."""
    assert is_predicate_name("Tall_comp_than")
    assert is_predicate_name("Has_bond_to")
    assert not is_predicate_name("_leading")
    assert not is_predicate_name("lower_case")
    drs = parse_drs("[x | Has_bond_to(x, c_o1)]")
    assert drs_to_fol(drs).to_unicode_str() == "∃x Has_bond_to(x, c_o1)"


def test_comparative_maps_and_survives_the_fol_parser():
    from unicode_fol_kit import MSFLParser
    formula = drs_to_fol(_mapping("comparative").drs)
    assert MSFLParser().parse(formula.to_unicode_str()) == formula


# ---------------------------------------------------------------------------
# Live: the high-level route end to end
# ---------------------------------------------------------------------------

@live
def test_ace_to_drs_live_matches_the_recorded_mapping():
    drs = ace_to_drs("Every farmer who owns a donkey beats it.")
    assert drs == _mapping("donkey").drs


@live
def test_ace_to_drs_refuses_a_modal_text_with_the_formula_route_hint():
    with pytest.raises(AceUnsupportedError) as exc_info:
        ace_to_drs("John must wait.")
    assert "ace_to_formula" in str(exc_info.value)
