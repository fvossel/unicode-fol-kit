"""Tests for the DRT/DRS subpackage (unicode_fol_kit.drt).

Sections, each hand-checked against classical Kamp/Reyle DRT (*From Discourse to Logic*,
1993) as documented in unicode_fol_kit/drt/*.py's module docstrings:

1. nodes.py construction validation (shape/type checks that ARE possible at __init__).
2. nodes.py accessibility (DRS.validate() against hand-derived accessible/inaccessible
   configurations, including the donkey configuration and a Neg-box violation).
3. parser.py box-notation parsing, round trips, and refusals.
4. parser.py SBN-subset parsing (2-3 examples CONSTRUCTED BY HAND for this test suite —
   not verbatim Parallel Meaning Bank corpus data) and refusals for unsupported constructs.
5. resolve.py anaphora resolution: most-recent binding, ambiguity policy, none-accessible.
6. export.py drs_to_fol: golden unicode strings hand-derived for simple/donkey/negation/
   disjunction DRSs, plus api.check closedness.
7. End-to-end: the classic donkey-sentence entailment via api.prove (z3).
"""

import pytest

import unicode_fol_kit.drt as drt
from unicode_fol_kit import api

DRS, Pred, Eq, Neg, Impl, Or = drt.DRS, drt.Pred, drt.Eq, drt.Neg, drt.Impl, drt.Or


# =============================================================================
# 1. nodes.py — construction-time (local) validation.
# =============================================================================

def test_is_referent_and_is_constant_classification():
    # Single lowercase letter [+ digits] => referent; lowercase-initial >=2 chars => constant.
    assert drt.is_referent("x") and drt.is_referent("y1") and drt.is_referent("e12")
    assert not drt.is_referent("john") and not drt.is_referent("X")
    assert drt.is_constant_name("john") and drt.is_constant_name("c_Fido")
    assert not drt.is_constant_name("x")                    # reserved for referents
    assert drt.is_predicate_name("Farmer") and not drt.is_predicate_name("farmer")


def test_pred_rejects_lowercase_predicate_name():
    with pytest.raises(ValueError, match="uppercase-initial"):
        Pred("farmer", ("x",))


def test_pred_rejects_empty_args():
    with pytest.raises(ValueError, match="at least one argument"):
        Pred("Farmer", ())


def test_pred_rejects_illegal_argument_shape():
    # "1x" starts with a digit: neither a legal referent nor a legal constant.
    with pytest.raises(ValueError, match="neither a legal referent"):
        Pred("Farmer", ("1x",))


def test_eq_rejects_illegal_names():
    with pytest.raises(ValueError, match="neither a legal referent"):
        Eq("x", "!!")


def test_drs_rejects_illegal_referent_name():
    # "ab" is a legal CONSTANT shape, not a legal REFERENT shape (>=2 letters).
    with pytest.raises(ValueError, match="not a legal referent name"):
        DRS(("ab",), ())


def test_drs_rejects_duplicate_referent_in_same_box():
    with pytest.raises(ValueError, match="duplicate referent"):
        DRS(("x", "x"), ())


def test_drs_rejects_non_condition_in_conditions():
    with pytest.raises(TypeError, match="not a Condition instance"):
        DRS((), ("not a condition",))


@pytest.mark.parametrize("build", [
    lambda: Neg("not a drs"),
    lambda: Impl(DRS((), ()), "not a drs"),
    lambda: Or("not a drs", DRS((), ())),
])
def test_duplex_conditions_reject_non_drs_operands(build):
    with pytest.raises(TypeError, match="must be a DRS"):
        build()


# =============================================================================
# 2. nodes.py — the accessibility relation (DRS.validate()).
# =============================================================================

def test_validate_referent_accessible_in_its_own_box():
    assert DRS(("x",), (Pred("Farmer", ("x",)),)).validate() is True


def test_validate_donkey_configuration_is_valid():
    # Antecedent's referents x, y are accessible in the consequent (the donkey rule):
    # [x,y | Farmer(x),Donkey(y),Owns(x,y)] -> [ | Beats(x,y)].
    antecedent = DRS(("x", "y"), (Pred("Farmer", ("x",)), Pred("Donkey", ("y",)),
                                  Pred("Owns", ("x", "y"))))
    consequent = DRS((), (Pred("Beats", ("x", "y")),))
    drs = DRS((), (Impl(antecedent, consequent),))
    assert drs.validate() is True


def test_validate_referent_accessible_inside_neg_from_outer_box():
    # x is declared in the outer box; Neg's accessible set = outer's referents UNION
    # its own, so x is visible inside the negated box.
    drs = DRS(("x",), (Pred("Farmer", ("x",)),
                       Neg(DRS(("y",), (Pred("Owns", ("x", "y")),)))))
    assert drs.validate() is True


def test_validate_neg_box_referent_is_not_accessible_outside():
    # Hand-derived violation: "No farmer owns a donkey. #It is grey." — y is
    # introduced ONLY inside the negated box, so a sibling condition referencing
    # y directly in the outer box is an accessibility violation.
    drs = DRS(("x",), (
        Pred("Farmer", ("x",)),
        Neg(DRS(("y",), (Pred("Donkey", ("y",)), Pred("Owns", ("x", "y"))))),
        Pred("Grey", ("y",)),                 # <- y not accessible here
    ))
    with pytest.raises(ValueError, match="not accessible"):
        drs.validate()


def test_validate_or_referents_not_accessible_across_disjuncts():
    # [ | [x|Farmer(x)] or [y|Owns(y,x)]] — the right disjunct references the LEFT
    # disjunct's referent x, which is not accessible to it (Or's disjuncts are
    # mutually independent, like Neg's operand).
    left = DRS(("x",), (Pred("Farmer", ("x",)),))
    right = DRS(("y",), (Pred("Owns", ("y", "x")),))
    drs = DRS((), (Or(left, right),))
    with pytest.raises(ValueError, match="not accessible"):
        drs.validate()


def test_validate_impl_antecedent_referent_not_accessible_after_the_impl():
    # The antecedent's referent x leaks INTO the consequent (donkey rule) but must
    # NOT leak past the whole Impl condition to a later sibling condition.
    antecedent = DRS(("x",), (Pred("Farmer", ("x",)),))
    consequent = DRS((), (Pred("Rich", ("x",)),))          # OK: donkey rule
    drs = DRS((), (Impl(antecedent, consequent), Pred("Grey", ("x",))))   # NOT OK
    with pytest.raises(ValueError, match="not accessible"):
        drs.validate()


def test_validate_undeclared_referent_raises():
    drs = DRS((), (Pred("Foo", ("z",)),))
    with pytest.raises(ValueError, match="not accessible"):
        drs.validate()


def test_validate_duplicate_referent_name_across_boxes_raises():
    # Two sibling Neg boxes both declaring "x" — this DRT implementation requires
    # globally distinct referent names (see nodes.py's module docstring).
    drs = DRS((), (
        Neg(DRS(("x",), (Pred("A", ("x",)),))),
        Neg(DRS(("x",), (Pred("B", ("x",)),))),
    ))
    with pytest.raises(ValueError, match="more than one box"):
        drs.validate()


# =============================================================================
# 3. parser.py — box notation.
# =============================================================================

def test_parse_drs_simple_box():
    assert drt.parse_drs("[x | Farmer(x)]") == DRS(("x",), (Pred("Farmer", ("x",)),))


def test_parse_drs_donkey_sentence():
    got = drt.parse_drs("[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]")
    antecedent = DRS(("x", "y"), (Pred("Farmer", ("x",)), Pred("Donkey", ("y",)),
                                  Pred("Owns", ("x", "y"))))
    consequent = DRS((), (Pred("Beats", ("x", "y")),))
    assert got == DRS((), (Impl(antecedent, consequent),))


def test_parse_drs_negation_at_top_level():
    got = drt.parse_drs("~[x | Farmer(x)]")
    assert got == DRS((), (Neg(DRS(("x",), (Pred("Farmer", ("x",)),))),))


def test_parse_drs_negation_as_a_nested_condition():
    got = drt.parse_drs("[x | Farmer(x), ~[y | Owns(x, y)]]")
    expected = DRS(("x",), (Pred("Farmer", ("x",)),
                            Neg(DRS(("y",), (Pred("Owns", ("x", "y")),)))))
    assert got == expected
    assert got.validate() is True


def test_parse_drs_disjunction():
    got = drt.parse_drs("[ | [x | Farmer(x)] ∨ [y | Clerk(y)]]")
    expected = DRS((), (Or(DRS(("x",), (Pred("Farmer", ("x",)),)),
                          DRS(("y",), (Pred("Clerk", ("y",)),))),))
    assert got == expected


def test_parse_drs_equality_condition():
    assert drt.parse_drs("[x, y | x = y]") == DRS(("x", "y"), (Eq("x", "y"),))


def test_parse_drs_quoted_constant_is_sanitized():
    # 'Fido the dog' has no legal bare-token spelling (spaces); NameMapping.for_constant
    # strips non-alnum and, since the original starts uppercase (not NAME-legal),
    # falls back to the explicit c_-prefixed form: c_ + "Fidothedog".
    got = drt.parse_drs('[ | Owns(john, "Fido the dog")]')
    [cond] = got.conditions
    assert cond.args == ("john", "c_Fidothedog")


def test_parse_drs_refuses_bare_drs_as_a_condition():
    with pytest.raises(drt.DRSSyntaxError, match="not a valid condition"):
        drt.parse_drs("[ | [x | Farmer(x)]]")


def test_parse_drs_refuses_chained_arrows():
    with pytest.raises(drt.DRSSyntaxError, match="unexpected trailing input"):
        drt.parse_drs("[x|Farmer(x)] -> [y|Donkey(y)] -> [z|Beats(z)]")


def test_parse_drs_refuses_unterminated_string():
    with pytest.raises(drt.DRSSyntaxError, match="unterminated string"):
        drt.parse_drs('[ | P("abc)]')


def test_parse_drs_refuses_missing_pipe():
    with pytest.raises(drt.DRSSyntaxError, match=r"expected '\|'"):
        drt.parse_drs("[x Farmer(x)]")


def test_parse_drs_refuses_illegal_token():
    # A digit-leading token is neither a referent, constant, nor predicate
    # name. Since Card entered the grammar, bare digits ARE tokens (the
    # cardinality position) — so the refusal moved from the tokenizer to
    # the term position, but a number as a term argument stays refused.
    with pytest.raises(drt.DRSSyntaxError,
                       match="expected a referent, constant"):
        drt.parse_drs("[ | P(1x)]")


@pytest.mark.parametrize("drs", [
    DRS(("x",), (Pred("Farmer", ("x",)),)),
    DRS((), (Impl(DRS(("x", "y"), (Pred("Farmer", ("x",)), Pred("Donkey", ("y",)),
                                   Pred("Owns", ("x", "y")))),
                  DRS((), (Pred("Beats", ("x", "y")),))),)),
    DRS((), (Neg(DRS(("x",), (Pred("Farmer", ("x",)),))),)),
    DRS((), (Or(DRS(("x",), (Pred("Farmer", ("x",)),)),
               DRS(("y",), (Pred("Clerk", ("y",)),))),)),
    DRS(("x", "y"), (Eq("x", "y"),)),
])
def test_parse_drs_round_trips_through_to_box_notation(drs):
    assert drt.parse_drs(drs.to_box_notation()) == drs


# =============================================================================
# 4. parser.py — SBN subset.
#
# All three snippets below are CONSTRUCTED BY HAND for this test suite (they
# illustrate the documented subset; they are not sourced from the PMB corpus).
# =============================================================================

def test_parse_sbn_simple_sentence_no_negation():
    # "A farmer owns a donkey.": line1=farmer(e1), line2=donkey(e2), line3=own(e3)
    # with Agent pointing back 2 lines (-2 -> e1) and Theme back 1 line (-1 -> e2).
    text = "farmer.n.01\ndonkey.n.01\nown.v.01 Agent -2 Theme -1"
    got, mapping = drt.parse_sbn(text)
    expected = DRS(("e1", "e2", "e3"), (
        Pred("FarmerN01", ("e1",)), Pred("DonkeyN01", ("e2",)), Pred("OwnV01", ("e3",)),
        Pred("Agent", ("e3", "e1")), Pred("Theme", ("e3", "e2")),
    ))
    assert got == expected
    assert got.validate() is True
    assert mapping.predicates == {
        "farmer.n.01": "FarmerN01", "donkey.n.01": "DonkeyN01", "own.v.01": "OwnV01"}
    assert mapping.constants == {}


def test_parse_sbn_quoted_constants():
    # "John owns Fido." with named entities instead of anaphoric offsets.
    text = 'own.v.01 Agent "john" Theme "fido"'
    got, mapping = drt.parse_sbn(text)
    expected = DRS(("e1",), (
        Pred("OwnV01", ("e1",)), Pred("Agent", ("e1", "john")), Pred("Theme", ("e1", "fido")),
    ))
    assert got == expected
    assert mapping.constants == {"john": "john", "fido": "fido"}


def test_parse_sbn_negation():
    # "A farmer does not own a donkey.": farmer(e1) at depth 0; NEGATION (e2, no
    # referent) opens a sub-box; donkey(e3) and own(e4) sit inside it at depth 1;
    # own's Agent (-3) reaches OUT of the sub-box to e1, Theme (-1) stays inside at e3.
    text = "farmer.n.01\nNEGATION\n\tdonkey.n.01\n\town.v.01 Agent -3 Theme -1"
    got, mapping = drt.parse_sbn(text)
    inner = DRS(("e3", "e4"), (
        Pred("DonkeyN01", ("e3",)), Pred("OwnV01", ("e4",)),
        Pred("Agent", ("e4", "e1")), Pred("Theme", ("e4", "e3")),
    ))
    expected = DRS(("e1",), (Pred("FarmerN01", ("e1",)), Neg(inner)))
    assert got == expected
    assert got.validate() is True
    assert mapping.predicates == {
        "farmer.n.01": "FarmerN01", "donkey.n.01": "DonkeyN01", "own.v.01": "OwnV01"}


def test_parse_sbn_refuses_unsupported_box_operator():
    with pytest.raises(drt.SBNSyntaxError, match="'POSSIBLE' is not supported"):
        drt.parse_sbn("POSSIBLE\n\tfarmer.n.01")


def test_parse_sbn_refuses_space_indentation():
    with pytest.raises(drt.SBNSyntaxError, match="TAB-only indentation"):
        drt.parse_sbn("farmer.n.01\n \tdonkey.n.01")


def test_parse_sbn_refuses_malformed_sense_token():
    with pytest.raises(drt.SBNSyntaxError, match="lemma.pos.NN"):
        drt.parse_sbn("notasensetoken")


def test_parse_sbn_refuses_offset_out_of_range():
    with pytest.raises(drt.SBNSyntaxError, match="outside the document"):
        drt.parse_sbn("farmer.n.01 Agent -5")


def test_parse_sbn_refuses_offset_targeting_a_negation_line():
    with pytest.raises(drt.SBNSyntaxError, match="box-operator line"):
        drt.parse_sbn("farmer.n.01\nNEGATION\n\tdonkey.n.01 Agent -1")


def test_parse_sbn_refuses_empty_negation_scope():
    with pytest.raises(drt.SBNSyntaxError, match="no content"):
        drt.parse_sbn("farmer.n.01\nNEGATION")


def test_parse_sbn_refuses_role_with_no_target():
    with pytest.raises(drt.SBNSyntaxError, match="has no target"):
        drt.parse_sbn("farmer.n.01 Agent")


def test_parse_sbn_refuses_lowercase_role():
    with pytest.raises(drt.SBNSyntaxError, match="uppercase-initial"):
        drt.parse_sbn("own.v.01 agent -1")


def test_parse_sbn_refuses_empty_input():
    with pytest.raises(drt.SBNSyntaxError, match="empty input"):
        drt.parse_sbn("   \n  \n")


# =============================================================================
# 5. resolve.py — accessibility-respecting anaphora resolution.
# =============================================================================

def test_resolve_anaphora_single_candidate_is_unambiguous():
    drs = DRS(("x", "z"), (Pred("Farmer", ("x",)), Pred(drt.PRONOUN, ("z",))))
    report = drt.resolve_anaphora(drs)
    assert report.resolutions == (drt.Resolution("z", "x", ("x",), False),)
    assert report.drs == DRS(("x", "z"), (Pred("Farmer", ("x",)), Eq("z", "x")))


def test_resolve_anaphora_ambiguous_strict_raises_listing_candidates():
    # x and y are both in z's own box; recency prefers the LATER tuple position (y).
    drs = DRS(("x", "y", "z"), (
        Pred("Farmer", ("x",)), Pred("Clerk", ("y",)), Pred(drt.PRONOUN, ("z",))))
    with pytest.raises(ValueError, match=r"2 accessible candidates \('y', 'x'\)"):
        drt.resolve_anaphora(drs)                          # strict=True is the default


def test_resolve_anaphora_ambiguous_non_strict_picks_most_recent():
    drs = DRS(("x", "y", "z"), (
        Pred("Farmer", ("x",)), Pred("Clerk", ("y",)), Pred(drt.PRONOUN, ("z",))))
    report = drt.resolve_anaphora(drs, strict=False)
    [res] = report.resolutions
    assert res.antecedent == "y" and res.ambiguous is True and res.candidates == ("y", "x")


def test_resolve_anaphora_no_accessible_candidate_raises():
    drs = DRS(("z",), (Pred(drt.PRONOUN, ("z",)),))
    with pytest.raises(ValueError, match="no accessible referent"):
        drt.resolve_anaphora(drs)


def test_resolve_anaphora_pronoun_in_consequent_binds_to_antecedent_referent():
    # Donkey-rule accessibility feeds resolution too: z (in the consequent) can only
    # see y (the antecedent's referent) — a single, unambiguous candidate.
    antecedent = DRS(("y",), (Pred("Donkey", ("y",)),))
    consequent = DRS(("z",), (Pred(drt.PRONOUN, ("z",)),))
    drs = DRS((), (Impl(antecedent, consequent),))
    report = drt.resolve_anaphora(drs)
    [res] = report.resolutions
    assert res.antecedent == "y" and res.ambiguous is False


def test_resolve_anaphora_missing_marker_for_requested_referent_raises():
    drs = DRS(("x",), (Pred("Farmer", ("x",)),))               # no PRONOUN marker at all
    with pytest.raises(ValueError, match="no PRONOUN marker"):
        drt.resolve_anaphora(drs, pronouns=["x"])


# =============================================================================
# 6. export.py — the standard translation, golden strings + closedness.
# =============================================================================

def test_drs_to_fol_simple_exists_golden_string():
    drs = DRS(("x",), (Pred("Farmer", ("x",)),))
    formula = drt.drs_to_fol(drs)
    assert formula.to_unicode_str() == "∃x Farmer(x)"


def test_drs_to_fol_donkey_sentence_golden_string():
    # Hand-derived: ∀x ∀y ((Farmer(x) ∧ Donkey(y) ∧ Owns(x,y)) -> Beats(x,y)) — the
    # donkey rule universally quantifies the ANTECEDENT's referents and conjoins its
    # conditions directly (not re-existentially-closed) into the implication's left side.
    antecedent = DRS(("x", "y"), (Pred("Farmer", ("x",)), Pred("Donkey", ("y",)),
                                  Pred("Owns", ("x", "y"))))
    consequent = DRS((), (Pred("Beats", ("x", "y")),))
    drs = DRS((), (Impl(antecedent, consequent),))
    formula = drt.drs_to_fol(drs)
    assert formula.to_unicode_str() == (
        "∀x ∀y (Farmer(x) ∧ Donkey(y) ∧ Owns(x, y) → Beats(x, y))")


def test_drs_to_fol_negation_golden_string():
    drs = DRS((), (Neg(DRS(("x",), (Pred("Farmer", ("x",)),))),))
    formula = drt.drs_to_fol(drs)
    assert formula.to_unicode_str() == "¬∃x Farmer(x)"


def test_drs_to_fol_disjunction_golden_string():
    drs = DRS((), (Or(DRS(("x",), (Pred("Farmer", ("x",)),)),
                     DRS(("y",), (Pred("Donkey", ("y",)),))),))
    formula = drt.drs_to_fol(drs)
    assert formula.to_unicode_str() == "∃x Farmer(x) ∨ ∃y Donkey(y)"


@pytest.mark.parametrize("drs", [
    DRS(("x",), (Pred("Farmer", ("x",)),)),
    DRS((), (Impl(DRS(("x", "y"), (Pred("Farmer", ("x",)), Pred("Donkey", ("y",)),
                                   Pred("Owns", ("x", "y")))),
                  DRS((), (Pred("Beats", ("x", "y")),))),)),
    DRS((), (Neg(DRS(("x",), (Pred("Farmer", ("x",)),))),)),
    DRS((), (Or(DRS(("x",), (Pred("Farmer", ("x",)),)),
               DRS(("y",), (Pred("Donkey", ("y",)),))),)),
    DRS((), (Pred("Farmer", ("john",)), Pred("Donkey", ("daisy",)),
             Pred("Owns", ("john", "daisy")))),
])
def test_drs_to_fol_produces_a_closed_formula(drs):
    assert api.check(drt.drs_to_fol(drs)).ok is True


def test_drs_to_fol_propagates_accessibility_violation():
    # Same Neg-box violation as the nodes-level test: drs_to_fol must refuse rather
    # than silently emit a formula with a free variable.
    drs = DRS(("x",), (
        Pred("Farmer", ("x",)),
        Neg(DRS(("y",), (Pred("Donkey", ("y",)),))),
        Pred("Grey", ("y",)),
    ))
    with pytest.raises(ValueError, match="not accessible"):
        drt.drs_to_fol(drs)


# =============================================================================
# 7. End-to-end: the classic donkey-sentence entailment via api.prove (z3).
# =============================================================================

def test_donkey_sentence_entailment_end_to_end():
    """"Every farmer who owns a donkey beats it" + facts entail "John beats Daisy".

    Hand-derived expected FOL: ∀x ∀y ((Farmer(x) ∧ Donkey(y) ∧ Owns(x,y)) -> Beats(x,y)).
    With Farmer(john), Donkey(daisy), Owns(john,daisy) as facts, instantiating x:=john,
    y:=daisy in the rule and discharging the (now true) antecedent yields Beats(john,daisy).
    """
    rule = drt.parse_drs(
        "[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]")
    facts = drt.parse_drs("[ | Farmer(john), Donkey(daisy), Owns(john, daisy)]")
    goal = drt.parse_drs("[ | Beats(john, daisy)]")

    verdict = api.prove(drt.drs_to_fol(goal),
                        [drt.drs_to_fol(rule), drt.drs_to_fol(facts)])
    assert verdict.status == "proved"


def test_donkey_sentence_not_entailed_without_the_owns_fact():
    # Drop Owns(john, daisy): the rule's antecedent is no longer satisfied by John and
    # Daisy specifically, so Beats(john, daisy) is no longer forced.
    rule = drt.parse_drs(
        "[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]")
    facts = drt.parse_drs("[ | Farmer(john), Donkey(daisy)]")
    goal = drt.parse_drs("[ | Beats(john, daisy)]")

    verdict = api.prove(drt.drs_to_fol(goal),
                        [drt.drs_to_fol(rule), drt.drs_to_fol(facts)])
    assert verdict.status != "proved"
