"""The reverse direction: kit DRS → ACE (`drs_to_ace`) and the round trip.

The offline half pins the generator itself: hand-checked texts and lexicon
entries for hand-built DRSs and mapped corpus DRSs (the generator is a pure
function — no APE involved). The live half is the ACTUAL correctness
argument: for every corpus sentence the mapping carries, the verbalized
text goes back through APE and the mapping, and Z3 must find the result
equivalent to what we started from. Natural English is explicitly NOT the
claim — "3 mans" is a documented, lexicon-defined surface — closing the
loop is.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.ace import (
    ace_round_trip, ace_to_drs, ape_available, chem_ulex, drs_to_ace,
    formula_to_ace, map_ace_drs, parse_ape_drs,
)
from unicode_fol_kit.ace.chem_lexicon import (
    CHEM_ADJECTIVES, CHEM_NOUNS, CHEM_UNSPEAKABLE, CHEM_VERBS, ace_kit_name,
)
from unicode_fol_kit.ace.verbalize import (
    AceVerbalizationError, _er_form, _s_form,
)
from unicode_fol_kit.drt import parse_drs

live = pytest.mark.skipif(not ape_available(),
                          reason="no APE binary reachable")

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
BY_TAG = {r["tag"]: r for r in ROWS}

#: Every corpus row the DRS mapping carries — the round-trip population.
MAPPABLE = [r for r in ROWS if r["status"] != "not_ace"
            and map_ace_drs(parse_ape_drs(r["drs"])).complete]


def _corpus_drs(tag):
    return map_ace_drs(parse_ape_drs(BY_TAG[tag]["drs"])).drs


# ---------------------------------------------------------------------------
# Offline: hand-checked verbalizations of hand-built DRSs
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("box,text", [
    ("[x1, e1 | Man(x1), Wait(e1, x1)]",
     "A man X1 waits."),
    ("[x1 | Man(x1), ~[e1 | Wait(e1, x1)]]",
     "There is a man X1. It is false that X1 waits."),
    # One-clause negations render directly …
    ("[ | ~[x1, e1 | Man(x1), Wait(e1, x1), Loudly(e1)]]",
     "It is false that a man X1 waits loudly."),
    # … multi-clause negations are REWRITTEN (¬∃(M∧W∧S) ≡ ∀(M∧W → ¬S)):
    # probed — "It is false that A and B." drops B out of the negation.
    ("[ | ~[x1, e1, e2 | Man(x1), Wait(e1, x1), Sleep(e2, x1)]]",
     "If a man X1 waits then it is false that X1 sleeps."),
    ("[ | [x1 | Man(x1)] -> [e1 | Wait(e1, x1)]]",
     "If there is a man X1 then X1 waits."),
    ("[ | [x1, e1 | Man(x1), Wait(e1, x1)] ∨ [x2, e2 | Dog(x2), Bark(e2, x2)]]",
     "A man X1 waits or a dog X2 barks."),
    ("[g1 | Card(g1, >=, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)]]",
     "There are at least 3 mans X1."),
    ("[g1, e1 | Card(g1, >, 2), [x1 | Part_of(x1, g1)] -> [ | Man(x1)],"
     " Wait(e1, g1)]",
     "There are more than 2 mans X1. X1 wait."),
    ("[g1, x1, e1 | Card(g1, =, 2), Part_of(john, g1), Part_of(mary, g1),"
     " Table(x1), Lift(e1, g1, x1)]",
     "John and Mary lift a table X1."),
    ("[x1 | Number(x1), x1 = c_30]",
     "There is a number X1. X1 is 30."),
])
def test_hand_built_boxes_land_on_their_hand_checked_text(box, text):
    result = drs_to_ace(parse_drs(box))
    assert result.text == text


def test_the_lexicon_is_exactly_the_words_the_text_uses():
    result = drs_to_ace(parse_drs("[x1, e1 | Man(x1), Wait(e1, x1)]"))
    assert result.ulex.splitlines() == [
        "iv_finsg(waits, wait).",
        "noun_sg(man, man, neutr).",
    ]
    plural = drs_to_ace(parse_drs(
        "[g1, e1 | Card(g1, >=, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)],"
        " Wait(e1, g1)]"))
    assert plural.ulex.splitlines() == [
        "iv_infpl(wait, wait).",
        "noun_pl(mans, man, neutr).",
    ]


def test_hyphenated_surfaces_for_underscore_predicates():
    # Bond_to → the verb "bond-to": underscores become hyphens on the
    # SURFACE, the logical symbol keeps the underscore (probed live).
    result = drs_to_ace(parse_drs(
        "[x1, x2, e1 | Atom(x1), Atom(x2), Bond_to(e1, x1, x2)]"))
    assert result.text == "An atom X1 bond-tos an atom X2."
    assert "tv_finsg('bond-tos', bond_to)." in result.ulex.splitlines()


# ---------------------------------------------------------------------------
# Offline: mapped corpus DRSs verbalize deterministically
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,text", [
    ("donkey", "If a farmer X1 owns a donkey X2 then X1 beats X2."),
    ("no-quantifier",
     "If there is a man X1 then it is false that X1 waits."),
    ("card-geq", "There are at least 3 mans X1. X1 wait."),
    ("collective", "John and Mary lift a table X1."),
    ("distributive-each-of", "Each of John and Mary waits."),
    ("genitive", "There is a dog X1 of John. X1 barks."),
    # The comparative rides on the copula's equality: Eq(john, x1) has no
    # noun for x1, so x1 is ALIASED to John and the Eq is consumed.
    ("comparative", "John is taller than Mary."),
    ("number-copula", "There is an age X1 of John. X1 is 30."),
    ("string-value", 'There is a name X1 of John. X1 is "Johnny".'),
    # The second unary becomes a predicative clause — noun category for
    # every unary predicate, no noun/adjective ambiguity in the lexicon.
    ("adjective", "A man X1 waits. X1 is a rich."),
    ("svo-ditransitive", "John gives a book X1 to Mary."),
    ("adverb-pp-combined", "A dog X1 barks in a garden X2 loudly."),
])
def test_mapped_corpus_boxes_land_on_their_pinned_text(tag, text):
    assert drs_to_ace(_corpus_drs(tag)).text == text


def test_the_comparative_lexicon_carries_both_adjective_forms():
    ulex = drs_to_ace(_corpus_drs("comparative")).ulex.splitlines()
    assert "adj_itr(tall, tall)." in ulex
    assert "adj_itr_comp(taller, tall)." in ulex


# ---------------------------------------------------------------------------
# Offline: mechanical morphology, hand-checked
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("base,form", [
    ("wait", "waits"), ("see", "sees"), ("watch", "watches"),
    ("pass", "passes"), ("fix", "fixes"), ("buzz", "buzzes"),
    ("push", "pushes"), ("fly", "flies"), ("buy", "buys"),
    ("man", "mans"),   # deliberate: lexicon-defined, not English
])
def test_the_s_form_rules(base, form):
    assert _s_form(base) == form


@pytest.mark.parametrize("base,form", [
    ("tall", "taller"), ("large", "larger"), ("happy", "happier"),
    ("grey", "greyer"),
])
def test_the_er_form_rules(base, form):
    assert _er_form(base) == form


# ---------------------------------------------------------------------------
# Offline: refusals, by name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("box,fragment", [
    # Probed: APE reads "at most"/"less than" as the maximality list.
    ("[g1 | Card(g1, <=, 5), [x1 | Part_of(x1, g1)] -> [ | Man(x1)]]",
     "no ACE surface"),
    ("[g1 | Card(g1, <, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)]]",
     "no ACE surface"),
    # A value can only sit on the right of an equality.
    ("[x1, e1 | Man(x1), See(e1, x1, c_30)]", "value constant"),
    # A 2-place atom over individuals has no event to ride on.
    ("[x1, x2 | Man(x1), Man(x2), Knows(x1, x2)]", "no event"),
    # No noun, no equality to ride on — nothing introduces the referent.
    ("[x1, e1 | Wait(e1, x1)]", "no noun"),
    # Non-invertible names: the mapping would respell them.
    ("[x1 | Ab_(x1)]", "not invertible"),
    ("[x1, e1 | Man(x1), See(e1, x1, c_o1)]", "value constant"),
    # Group shapes outside the three probed ones.
    ("[g1, e1 | Part_of(john, g1), Wait(e1, g1)]", "exactly one Card"),
    ("[g1, e1 | Card(g1, =, 3), Part_of(john, g1), Part_of(mary, g1),"
     " Wait(e1, g1)]", "does not close over"),
    # A coordination reused would denote a NEW group the second time.
    ("[g1, e1, e2 | Card(g1, =, 2), Part_of(john, g1), Part_of(mary, g1),"
     " Wait(e1, g1), Sleep(e2, g1)]", "more than once"),
    # Complexes nested deeper than the probed fragment.
    ("[ | ~[ | ~[ | ~[x1, e1 | Man(x1), Wait(e1, x1)]]]]", "deeper"),
])
def test_what_no_probed_surface_carries_is_refused_by_name(box, fragment):
    with pytest.raises(AceVerbalizationError, match=fragment):
        drs_to_ace(parse_drs(box))


# ---------------------------------------------------------------------------
# Offline: formula_to_ace — expressibility as two refusal-checked steps
# ---------------------------------------------------------------------------

def test_a_formula_in_the_drs_image_becomes_ace():
    from unicode_fol_kit import MSFLParser
    formula = MSFLParser().parse(
        "∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2)"
        " → ∃e2 Beat(e2, x1, x2))")
    result = formula_to_ace(formula)
    assert result.text == ("If a farmer X1 owns a donkey X2 then X1 "
                           "beats X2.")


def test_a_counting_formula_becomes_ace_through_the_card_reading():
    from unicode_fol_kit import MSFLParser
    formula = MSFLParser().parse(
        "∃g1 (∃≥3 p1 Part_of(p1, g1) ∧ ∀x1 (Part_of(x1, g1) → Man(x1)))")
    assert formula_to_ace(formula).text == "There are at least 3 mans X1."


def test_formula_to_ace_refuses_in_two_named_stages():
    from unicode_fol_kit import MSFLParser
    from unicode_fol_kit.drt import FolToDrsError

    # Stage 1: outside the DRS image (modality).
    with pytest.raises(FolToDrsError, match="no classical DRS condition"):
        formula_to_ace(MSFLParser(modal=True).parse("□∃e1 Wait(e1, john)"))
    # Stage 2: a DRS, but outside the probed ACE fragment (upper bound).
    with pytest.raises(AceVerbalizationError, match="no ACE surface"):
        formula_to_ace(MSFLParser().parse(
            "∃g1 (∃≤5 p1 Part_of(p1, g1) ∧ ∀x1 (Part_of(x1, g1) → Man(x1)))"))


# ---------------------------------------------------------------------------
# Offline: the chem lexicon tiles the signature
# ---------------------------------------------------------------------------

def test_the_chem_tables_tile_the_signature_exactly():
    from unicode_fol_kit.chem.signature import CHEMLOG_SIGNATURE
    covered = (set(CHEM_NOUNS) | set(CHEM_ADJECTIVES) | set(CHEM_VERBS)
               | set(CHEM_UNSPEAKABLE))
    assert covered == set(CHEMLOG_SIGNATURE.predicates)
    # And the exclusions are exactly the nullary predicates — a sentence
    # needs a subject.
    assert CHEM_UNSPEAKABLE == {
        n for n, d in CHEMLOG_SIGNATURE.predicates.items() if d.arity == 0}
    # No word serves two categories (that would make parses ambiguous).
    assert not (set(CHEM_NOUNS) & set(CHEM_ADJECTIVES))
    assert not (set(CHEM_NOUNS) & set(CHEM_VERBS))
    assert not (set(CHEM_ADJECTIVES) & set(CHEM_VERBS))


def test_the_chem_ulex_lines_are_well_formed():
    lines = chem_ulex().splitlines()
    assert "noun_sg(carbon, c, neutr)." in lines
    assert "noun_pl(carbons, c, neutr)." in lines
    assert "adj_itr(aromatic, aromatic)." in lines
    assert "tv_finsg(bonds, bond)." in lines
    assert "tv_finsg('single-bonds', 'bSINGLE')." in lines
    assert all(line.endswith(".") for line in lines)


def test_ace_kit_name_states_the_arriving_spelling():
    assert ace_kit_name("c") == "C"
    assert ace_kit_name("bond") == "Bond"
    assert ace_kit_name("bSINGLE") == "BSINGLE"
    assert ace_kit_name("has_bond_to") == "Has_bond_to"


# ---------------------------------------------------------------------------
# Live: the round trip closes — the actual ACE-6 claim
# ---------------------------------------------------------------------------

@live
@pytest.mark.parametrize("row", MAPPABLE, ids=[r["tag"] for r in MAPPABLE])
def test_every_mappable_corpus_sentence_round_trips(row):
    """DRS → ACE → APE → DRS, Z3-equivalent — over the WHOLE mappable
    corpus, not a curated subset. A generator change that breaks any
    surface form fails here with the offending text in the message."""
    drs = map_ace_drs(parse_ape_drs(row["drs"])).drs
    trip = ace_round_trip(drs)
    assert trip.equivalent, (
        f"{row['tag']}: {trip.verbalization.text!r} came back different: "
        f"{trip.detail}")


@live
@pytest.mark.parametrize("box", [
    # The negation rewrite is a semantic transformation — re-check it live.
    "[ | ~[x1, e1, e2 | Man(x1), Wait(e1, x1), Sleep(e2, x1)]]",
    # Hand-built counting force through the loop.
    "[g1, e1 | Card(g1, >, 2), [x1 | Part_of(x1, g1)] -> [ | Man(x1)],"
    " Wait(e1, g1)]",
    # Hyphenated verb surface for an underscore predicate.
    "[x1, x2, e1 | Atom(x1), Atom(x2), Bond_to(e1, x1, x2)]",
])
def test_hand_built_boxes_round_trip(box):
    trip = ace_round_trip(parse_drs(box))
    assert trip.equivalent, trip.detail


@live
def test_a_formula_round_trips_through_ace():
    # formula → DRS → ACE → APE → DRS → formula, Z3-equivalent: the whole
    # chain the expressibility check promises.
    from unicode_fol_kit import MSFLParser
    from unicode_fol_kit.drt import fol_to_drs
    from unicode_fol_kit.eval.equivalence import equivalent

    formula = MSFLParser().parse(
        "∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2)"
        " → ∃e2 Beat(e2, x1, x2))")
    trip = ace_round_trip(fol_to_drs(formula))
    assert trip.equivalent, trip.detail
    from unicode_fol_kit.drt import drs_to_fol
    assert equivalent(formula, drs_to_fol(trip.back)).equivalent


@live
def test_chem_sentences_arrive_in_the_chemlog_vocabulary():
    drs = ace_to_drs(
        "There is a carbon X1. There is an oxygen X2. X1 bonds X2. "
        "X1 single-bonds X2. X1 is aromatic.", ulex=chem_ulex())
    names = {c.name for c in drs.conditions if hasattr(c, "name")}
    # Kit-convention capitalization of the ChemLog symbols (documented at
    # ace_kit_name); the verbs arrive neo-Davidsonian (event first).
    assert {"C", "O", "Bond", "BSINGLE", "Aromatic"} <= names
    bond = next(c for c in drs.conditions
                if getattr(c, "name", "") == "Bond")
    assert len(bond.args) == 3
