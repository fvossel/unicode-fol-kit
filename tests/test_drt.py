"""Tests for the DRT/DRS subpackage (unicode_logic_kit.drt).

Sections, each hand-checked against classical Kamp/Reyle DRT (*From Discourse to Logic*,
1993) as documented in unicode_logic_kit/drt/*.py's module docstrings:

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

import unicode_logic_kit.drt as drt
from unicode_logic_kit import api

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


def test_parse_sbn_hyphenated_role_in_indentation_dialect():
    # VerbNet's "Co-" role compounding (Co-Theme, Co-Agent, Co-Patient) is part of the
    # BASE ``ROLE`` grammar (see the module docstring's section 2), not a connector-
    # dialect-only addition -- this input has no NEGATION/connector anywhere, so it goes
    # through _parse_sbn_classic, exactly like the real corpus document
    # data/en/gold/p17/d2285/en.drs.sbn (pmb-5.1.0), which uses a hyphenated "Co-Theme"
    # role in an otherwise flat, connector-free document. The hyphen is dropped when the
    # role becomes a predicate name: Co-Theme(e1, fido) becomes CoTheme(e1, fido).
    got, mapping = drt.parse_sbn('like.v.01 Co-Theme "fido"')
    expected = DRS(("e1",), (Pred("LikeV01", ("e1",)), Pred("CoTheme", ("e1", "fido"))))
    assert got == expected
    assert mapping.constants == {"fido": "fido"}


def test_parse_sbn_bare_deictic_constant_in_indentation_dialect():
    # Bos (2023) §2.1: "now" is one of the four deictic references (speaker/hearer/
    # now/here), written bare (unquoted) -- "EQU" is a comparison OPERATOR, lexically
    # a role in this subset (see the module docstring), applied like any other. This
    # widening is part of the BASE grammar (section 2's "Bare (unquoted) constants"
    # bullet), not connector-dialect-only -- this input has no NEGATION/connector
    # anywhere, so it goes through _parse_sbn_classic (renamed/relocated from the
    # CONNECTOR-dialect test section, which it never actually exercised).
    got, _ = drt.parse_sbn("time.n.08 EQU now")
    assert got == DRS(("e1",), (Pred("TimeN08", ("e1",)), Pred("EQU", ("e1", "now"))))


def test_parse_sbn_bare_integer_constant_in_indentation_dialect():
    # A bare (unquoted) numeral is also a legal SBN constant (Bos 2023 §2.1,
    # "numerical values"); it is not itself a legal kit CONSTANT name (nodes.py's
    # NAME class needs an initial letter), so it is sanitized to the explicit 'c_...'
    # form via the same NameMapping quoted constants use. Same base-grammar widening
    # as above, exercised via _parse_sbn_classic (no NEGATION/connector in this input;
    # renamed/relocated from the CONNECTOR-dialect test section for the same reason).
    got, mapping = drt.parse_sbn("quantity.n.01 Quantity 3")
    assert got == DRS(("e1",), (Pred("QuantityN01", ("e1",)), Pred("Quantity", ("e1", "c_3"))))
    assert mapping.constants == {"3": "c_3"}


def test_parse_sbn_refuses_empty_input():
    with pytest.raises(drt.SBNSyntaxError, match="empty input"):
        drt.parse_sbn("   \n  \n")


# =============================================================================
# 4b. parser.py — the CONNECTOR dialect (PMB's own released SBN format, added for
# real-corpus coverage; see the module docstring's "Dialect selection"). The two
# negation examples are HAND-DERIVED from Bos (2023) "The Sequence Notation:
# Catching Complex Meanings in Simple Graphs" (IWCS 2023) Figures 3/4 -- an
# independent, external, authoritative source for the expected DRS/FOL shape, not
# just a self-consistency check against this module's own code.
# =============================================================================

def test_parse_sbn_connector_negation():
    # "She is not tired.": concept-only numbering (box-operator lines don't count,
    # unlike the indentation dialect) gives female.n.02 concept 1 (e1), tired.a.01
    # concept 2 (e2); NEGATION <1 attaches its Neg to context (1 - 1) = 0, the root.
    # tired's Experiencer -1 counts back one CONCEPT from itself (concept 2) to
    # concept 1 = e1 -- Bos (2023) Figure 3's exact mechanism.
    text = "female.n.02\nNEGATION <1\ntired.a.01 Experiencer -1"
    got, mapping = drt.parse_sbn(text)
    inner = DRS(("e2",), (Pred("TiredA01", ("e2",)), Pred("Experiencer", ("e2", "e1"))))
    expected = DRS(("e1",), (Pred("FemaleN02", ("e1",)), Neg(inner)))
    assert got == expected
    assert got.validate() is True
    assert mapping.predicates == {"female.n.02": "FemaleN02", "tired.a.01": "TiredA01"}


def test_parse_sbn_connector_two_negations_attach_to_same_context():
    # Bos (2023) Figure 4, "She is neither rich nor famous.", verbatim (its own
    # worked example -- an external cross-check, not a fact only this module
    # asserts): female.n.02(e1); NEGATION <1 introduces context 1 (rich), attached
    # to context (1-1)=0; NEGATION <2 introduces context 2 (famous), attached to
    # context (2-2)=0 -- THE SAME context 0, not nested inside the first negation,
    # so the reading is ¬Rich(e1) ∧ ¬Famous(e1), never ¬(¬Rich(e1)). Leading spaces
    # before each NEGATION are the real release's own cosmetic column-alignment
    # padding (verified against pmb-5.1.0) and carry no meaning in this dialect.
    text = ("female.n.02\n"
            "  NEGATION <1\n"
            "rich.a.01 AttributeOf -1\n"
            "  NEGATION <2\n"
            "famous.a.01 AttributeOf -2")
    got, mapping = drt.parse_sbn(text)
    rich = DRS(("e2",), (Pred("RichA01", ("e2",)), Pred("AttributeOf", ("e2", "e1"))))
    famous = DRS(("e3",), (Pred("FamousA01", ("e3",)), Pred("AttributeOf", ("e3", "e1"))))
    expected = DRS(("e1",), (Pred("FemaleN02", ("e1",)), Neg(rich), Neg(famous)))
    assert got == expected
    assert got.validate() is True
    # Second, independent check: drs_to_fol's translation is a flat conjunction of
    # two negations, matching "neither ... nor ..." -- never a nested double
    # negation, which would (wrongly) assert she IS rich-or-famous.
    fol = drt.drs_to_fol(got).to_unicode_str()
    assert fol == "∃e1 (FemaleN02(e1) ∧ ¬∃e2 (RichA01(e2) ∧ AttributeOf(e2, e1)) ∧ " \
                  "¬∃e3 (FamousA01(e3) ∧ AttributeOf(e3, e1)))"


def test_parse_sbn_connector_hyphenated_role():
    # The same "Co-" role compounding exercised by
    # test_parse_sbn_hyphenated_role_in_indentation_dialect above, but through the
    # CONNECTOR dialect's own code path this time (_parse_sbn_connector): the document
    # carries a real connector (NEGATION <1), so dialect selection picks dialect 2, and
    # role-hook offsets use its CONCEPT-only numbering. "she likes fido, and is not
    # tired": like.v.01 is concept 1 (e1); NEGATION <1 attaches to context 0;
    # tired.a.01 is concept 2 (e2), Experiencer -1 counts back one concept to e1.
    text = 'like.v.01 Co-Theme "fido"\nNEGATION <1\ntired.a.01 Experiencer -1'
    got, mapping = drt.parse_sbn(text)
    inner = DRS(("e2",), (Pred("TiredA01", ("e2",)), Pred("Experiencer", ("e2", "e1"))))
    expected = DRS(("e1",), (
        Pred("LikeV01", ("e1",)), Pred("CoTheme", ("e1", "fido")), Neg(inner)))
    assert got == expected
    assert got.validate() is True
    assert mapping.constants == {"fido": "fido"}


def test_parse_sbn_connector_bare_deictic_constant():
    # Same bare-deictic-constant widening as
    # test_parse_sbn_bare_deictic_constant_in_indentation_dialect above, but through
    # the CONNECTOR dialect's own code path this time (_parse_sbn_connector): the
    # document carries a real connector (NEGATION <1), so dialect selection picks
    # dialect 2. "she is not now tired" (contrived, but a legal instance of the
    # grammar): time.n.08 is concept 1 (e1); NEGATION <1 attaches to context 0;
    # tired.a.01 is concept 2 (e2), Experiencer -1 counts back one concept to e1. This
    # is also the DOMINANT real-world use of the feature: of the 1025 pmb-5.1.0
    # documents that parse via the connector dialect, 1009 (98%) have a bare
    # deictic/integer constant in the resulting SBNMapping.constants.
    text = "time.n.08 EQU now\nNEGATION <1\ntired.a.01 Experiencer -1"
    got, mapping = drt.parse_sbn(text)
    inner = DRS(("e2",), (Pred("TiredA01", ("e2",)), Pred("Experiencer", ("e2", "e1"))))
    expected = DRS(("e1",), (Pred("TimeN08", ("e1",)), Pred("EQU", ("e1", "now")), Neg(inner)))
    assert got == expected
    assert got.validate() is True
    assert mapping.constants == {"now": "now"}


def test_parse_sbn_connector_bare_integer_constant():
    # Same bare-integer-constant widening as
    # test_parse_sbn_bare_integer_constant_in_indentation_dialect above, but through
    # the CONNECTOR dialect's own code path (_parse_sbn_connector): a real connector
    # (NEGATION <1) is present, so dialect selection picks dialect 2. "not three tired
    # things" (contrived, but legal): quantity.n.01 is concept 1 (e1); NEGATION <1
    # attaches to context 0; tired.a.01 is concept 2 (e2), Experiencer -1 counts back
    # one concept to e1.
    text = "quantity.n.01 Quantity 3\nNEGATION <1\ntired.a.01 Experiencer -1"
    got, mapping = drt.parse_sbn(text)
    inner = DRS(("e2",), (Pred("TiredA01", ("e2",)), Pred("Experiencer", ("e2", "e1"))))
    expected = DRS(("e1",), (
        Pred("QuantityN01", ("e1",)), Pred("Quantity", ("e1", "c_3")), Neg(inner)))
    assert got == expected
    assert got.validate() is True
    assert mapping.constants == {"3": "c_3"}


def test_parse_sbn_connector_refuses_unsupported_separator():
    with pytest.raises(drt.SBNSyntaxError, match="'POSSIBILITY' is not supported"):
        drt.parse_sbn("thing.n.01\nPOSSIBILITY <1\nfarmer.n.01")


def test_parse_sbn_connector_refuses_forward_connector():
    with pytest.raises(drt.SBNSyntaxError, match="forward connector"):
        drt.parse_sbn("thing.n.01\nNEGATION >1\nfarmer.n.01")


def test_parse_sbn_connector_refuses_out_of_range_connector():
    with pytest.raises(drt.SBNSyntaxError, match="outside the document"):
        drt.parse_sbn("thing.n.01\nNEGATION <2\nfarmer.n.01")


def test_parse_sbn_connector_refuses_box_valued_role_target():
    # "hope.v.01 Proposition >1": Proposition's argument is an embedded CLAUSE
    # (a context), not an entity -- this subset only resolves entity-valued role
    # targets, so it is refused by name rather than silently mis-read as an offset.
    text = "hope.v.01 Proposition >1\nNEGATION <1\nsleep.v.01 Agent -1"
    with pytest.raises(drt.SBNSyntaxError, match="context/box reference"):
        drt.parse_sbn(text)


def test_parse_sbn_connector_refuses_empty_negation_scope():
    with pytest.raises(drt.SBNSyntaxError, match="empty context"):
        drt.parse_sbn("thing.n.01\nNEGATION <1\nNEGATION <2\nfarmer.n.01")


def test_parse_sbn_dialect_selection_ignores_leading_spaces_in_connector_mode():
    # The same leading-space shape that test_parse_sbn_refuses_space_indentation
    # (dialect 1) refuses outright is legal -- and semantically inert -- the moment
    # a connector is present anywhere in the document, confirming dialect selection
    # is document-wide, not per-line.
    got, _ = drt.parse_sbn("farmer.n.01\n NEGATION <1\n donkey.n.01")
    assert got == DRS(("e1",), (
        Pred("FarmerN01", ("e1",)),
        Neg(DRS(("e2",), (Pred("DonkeyN01", ("e2",)),))),
    ))


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
