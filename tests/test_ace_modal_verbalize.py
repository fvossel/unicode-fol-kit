"""ACE-7: modal/deontic formulas -> ACE text, round-trip-checked live.

Mirrors ``tests/test_ace_verbalize.py``'s structure and discipline exactly,
scoped to the two ACE modal surfaces measured against live APE (see
``unicode_fol_kit.ace.reverse_modal``'s module docstring): a modality
wrapping a whole formula ("John must wait.") and a modality nested in a
duplex's consequent ("Every man must wait.", verbalized as "If there is a
man X1 then X1 must wait."). Question/command generation is out of scope
(deferred), and ACE's modal surface is auxiliary-in-verb-phrase, never a
sentence-level paraphrase.
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.ace import ape_available
from unicode_fol_kit.ace.reverse_modal import ModalBox, ModalImpl, fol_to_modal_drs
from unicode_fol_kit.ace.verbalize import (
    AceVerbalizationError, modal_ace_round_trip, modal_drs_to_ace,
    modal_formula_to_ace,
)
from unicode_fol_kit.drt.export import drs_to_fol
from unicode_fol_kit.drt.nodes import DRS, Impl
from unicode_fol_kit.drt.reverse import FolToDrsError

live = pytest.mark.skipif(not ape_available(),
                          reason="no APE binary reachable")

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
BY_TAG = {r["tag"]: r for r in ROWS}

P = MSFLParser(modal=True)

#: The 5 recorded modal corpus fixtures (tag -> (sentence, kit MSFL source)).
#: The kit formulas are hand-built (the corpus rows predate ACE-7 and carry
#: no ``kit_formulas`` for these tags — ``status="tptp_unsupported"``,
#: Attempto's OWN TPTP translator declines modality, see the corpus JSON);
#: each source is the standard translation of the tag's recorded ``sentence``.
MODAL_FIXTURES = [
    ("modal-must", "□∃e1 Wait(e1, john)"),
    ("modal-can", "◇∃e1 Wait(e1, john)"),
    ("modal-should", "Ⓞ∃e1 Wait(e1, john)"),
    ("modal-may", "Ⓟ∃e1 Wait(e1, john)"),
    ("modal-universal", "∀x1 (Man(x1) → □∃e1 Wait(e1, x1))"),
]


def _sentence(tag: str) -> str:
    return BY_TAG[tag]["sentence"]


# ---------------------------------------------------------------------------
# Offline: fol_to_modal_drs on the 5 fixtures, structurally hand-checked
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,src", MODAL_FIXTURES, ids=[t for t, _ in MODAL_FIXTURES])
def test_fol_to_modal_drs_matches_the_recorded_corpus_shape(tag, src):
    """Each corpus row's own recorded DRS (``BY_TAG[tag]["drs"]``) already
    names the shape APE itself produced — a flat ``must(drs([A],[...]))`` or
    a duplex whose consequent is ``must(drs([B],[...]))`` (see the JSON).
    ``fol_to_modal_drs`` must land on the SAME shape family from the kit
    formula side: :class:`ModalBox` for the 4 flat sentences, :class:`ModalImpl`
    for the universal."""
    formula = P.parse(src)
    modal = fol_to_modal_drs(formula)
    is_universal = tag == "modal-universal"
    assert isinstance(modal, ModalImpl if is_universal else ModalBox)
    if is_universal:
        assert modal.modality == "must"
        assert modal.antecedent.referents == ("x1",)
        assert modal.consequent.referents == ("e1",)
    else:
        expected_modality = {"modal-can": "can", "modal-should": "should",
                             "modal-may": "may"}.get(tag, "must")
        assert modal.modality == expected_modality
        assert modal.drs.referents == ("e1",)


def test_fol_to_modal_drs_on_a_non_modal_formula_is_plain_fol_to_drs():
    from unicode_fol_kit.drt.reverse import fol_to_drs

    formula = P.parse("∃e1 Wait(e1, john)")
    assert fol_to_modal_drs(formula) == fol_to_drs(formula)


# ---------------------------------------------------------------------------
# Offline: the classical fixed point holds INSIDE the modal wrapper
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    "□∃e1 Wait(e1, john)", "◇∃e1 Wait(e1, john)",
    "Ⓞ∃e1 Wait(e1, john)", "Ⓟ∃e1 Wait(e1, john)",
])
def test_the_flat_wrapper_s_inner_drs_is_the_classical_fixed_point(src):
    """Oracle (c): ``drs_to_fol(modal.drs)`` reconstructs the modal node's
    own inner formula node-identically — the same fixed point
    ``drt.reverse``'s classical route pins for the 0.25.0 CHANGELOG's
    ``drs_to_fol(fol_to_drs(f)) == f``, applied to the piece INSIDE the
    wrapper (the wrapper itself carries no DRS content of its own)."""
    formula = P.parse(src)
    modal = fol_to_modal_drs(formula)
    assert isinstance(modal, ModalBox)
    assert drs_to_fol(modal.drs) == formula.formula


def test_the_duplex_wrapper_s_pieces_are_the_classical_fixed_point():
    """Same oracle for :class:`ModalImpl`: strip the modality tag, rebuild
    the plain ``drt.nodes.Impl`` from ``antecedent``/``consequent``, and
    ``drs_to_fol`` it — the result must match the DECLASSIFIED formula
    (modality stripped) node-identically, proving the graft reused
    ``fol_to_drs``'s own duplex handling rather than re-deriving it."""
    formula = P.parse("∀x1 (Man(x1) → □∃e1 Wait(e1, x1))")
    modal = fol_to_modal_drs(formula)
    assert isinstance(modal, ModalImpl)
    declassified = P.parse("∀x1 (Man(x1) → ∃e1 Wait(e1, x1))")
    whole = DRS((), (Impl(modal.antecedent, modal.consequent),))
    assert drs_to_fol(whole) == declassified


# ---------------------------------------------------------------------------
# Offline: modal_formula_to_ace lands on hand-checked ACE text
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("tag,src", MODAL_FIXTURES, ids=[t for t, _ in MODAL_FIXTURES])
def test_modal_formula_to_ace_lands_on_its_hand_checked_text(tag, src):
    formula = P.parse(src)
    result = modal_formula_to_ace(formula)
    if tag == "modal-universal":
        # Attempto's own duplex surface ("Every man must wait.") and the
        # verbalizer's if-then donkey surface are DIFFERENT English for the
        # same standard-translation shape — same relationship the classical
        # ACE-6 tests already document for plain (non-modal) duplexes.
        assert result.text == "If there is a man X1 then X1 must wait."
    else:
        assert result.text == _sentence(tag)  # "John must/can/should/may wait."


def test_modal_formula_to_ace_places_the_auxiliary_before_a_transitive_verb():
    # Probed live: "must see" needs the infpl/base lexicon form even though
    # the subject is singular — see test_the_modal_auxiliary_forces_the_
    # infinitive_lexicon_form below for the live confirmation.
    formula = P.parse("□∃e1 See(e1, john, mary)")
    result = modal_formula_to_ace(formula)
    assert result.text == "John must see Mary."
    assert "tv_infpl(see, see)." in result.ulex.splitlines()


def test_the_lexicon_under_a_modal_uses_the_infinitive_form_not_finsg():
    # Probed live (not just asserted): only iv_infpl parses after "must" for
    # a novel verb — iv_finsg alone is refused by APE even though the SAME
    # bare word alone (no modal) is not what finsg spells. See
    # test_a_modal_sentence_needing_only_the_infinitive_entry_round_trips
    # below for the live half of this claim.
    formula = P.parse("□∃e1 Wait(e1, john)")
    result = modal_formula_to_ace(formula)
    assert "iv_infpl(wait, wait)." in result.ulex.splitlines()
    assert not any(line.startswith("iv_finsg(") for line in result.ulex.splitlines())


# ---------------------------------------------------------------------------
# Offline: modal_drs_to_ace delegates a plain DRS to drs_to_ace unchanged
# ---------------------------------------------------------------------------

def test_modal_drs_to_ace_delegates_a_plain_drs():
    from unicode_fol_kit.ace.verbalize import drs_to_ace
    from unicode_fol_kit.drt.reverse import fol_to_drs

    formula = P.parse("∃x1 ∃e1 (Man(x1) ∧ Wait(e1, x1))")
    drs = fol_to_drs(formula)
    assert modal_drs_to_ace(drs) == drs_to_ace(drs)


def test_modal_drs_to_ace_refuses_anything_else_by_type():
    with pytest.raises(TypeError, match="ModalBox/ModalImpl"):
        modal_drs_to_ace(42)


# ---------------------------------------------------------------------------
# Offline: refusals, by name — every modal placement outside the 2 probed
# shapes falls straight through to fol_to_drs's own classical refusal
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src,fragment", [
    # Modality mixed with a classical conjunct in one box.
    ("□∃e1 Wait(e1, john) ∧ Man(john)", "no classical DRS condition"),
    # Modality nested inside another modality.
    ("□□∃e1 Wait(e1, john)", "no classical DRS condition"),
    # Modality in a duplex ANTECEDENT rather than its consequent.
    ("∀x1 (□Man(x1) → ∃e1 Wait(e1, x1))", "no classical DRS condition"),
    # Modality two ∀-levels deep below the immediate consequent.
    ("∀x1 (Man(x1) → ∀x2 (Dog(x2) → □∃e1 Wait(e1, x1)))",
     "no classical DRS condition"),
])
def test_every_placement_outside_the_two_probed_shapes_is_refused(src, fragment):
    formula = P.parse(src)
    with pytest.raises(FolToDrsError, match=fragment):
        fol_to_modal_drs(formula)


@pytest.mark.parametrize("src", [
    # A modal box with more than one clause: two conjoined atoms under □.
    "□∃e1 (Wait(e1, john) ∧ Man(john))",
])
def test_a_modal_box_with_more_than_one_clause_is_refused(src):
    formula = P.parse(src)
    with pytest.raises(AceVerbalizationError, match="single verb clause"):
        modal_formula_to_ace(formula)


@pytest.mark.parametrize("src", [
    # Predicative-constant path: no event at all, just "X is a NOUN" — the
    # modality has nowhere to attach ("John is a man." is not "John must be
    # a man."). This is the adversarial reviewer's bug #1: a naive
    # len(clauses) == 1 count let this through and silently dropped "must".
    "□Man(john)",
    # "there is a NOUN" introduction path: same defect, existential subject
    # instead of a named one. The reviewer's bug #2.
    "□∃x Man(x)",
])
def test_a_single_non_verb_clause_under_a_flat_modality_is_refused(src):
    formula = P.parse(src)
    with pytest.raises(AceVerbalizationError, match="single verb clause"):
        modal_formula_to_ace(formula)


def test_a_copula_only_duplex_consequent_is_refused():
    # The duplex-consequent counterpart of the same bug: the consequent box
    # has no event, so verb_clause is never reached and "must"/"can"/...
    # would silently vanish from the "then" clause.
    formula = P.parse("∀x1 (Man(x1) → □Rich(john))")
    with pytest.raises(AceVerbalizationError, match="single verb clause"):
        modal_formula_to_ace(formula)


# ---------------------------------------------------------------------------
# Live: the round trip closes for the 5 pinned corpus fixtures — the actual
# ACE-7 claim, probed against the SAME pinned APE commit as every other
# ace test (see unicode_fol_kit.ace.runner.APE_PINNED_COMMIT)
# ---------------------------------------------------------------------------

@live
@pytest.mark.parametrize("tag,src", MODAL_FIXTURES, ids=[t for t, _ in MODAL_FIXTURES])
def test_every_modal_corpus_fixture_round_trips(tag, src):
    """formula -> ACE -> APE -> formula, judged by eval.equivalence.equivalent
    (not raw Z3: a modal Node's own to_z3 refuses by design; equivalent()
    already routes a modal pair through modal_decide/qml_equivalent)."""
    formula = P.parse(src)
    trip = modal_ace_round_trip(formula)
    assert trip.equivalent, (
        f"{tag}: {trip.verbalization.text!r} came back different: "
        f"{trip.detail}")
    assert trip.back.kind == "assertion"


@live
def test_a_modal_sentence_needing_only_the_infinitive_entry_round_trips():
    # The lexicon generator never emits iv_finsg under a modal (see the
    # offline test above) — this is the live half of that claim: the
    # infpl-only lexicon it DOES emit is what APE actually needs.
    formula = P.parse("□∃e1 Wait(e1, john)")
    trip = modal_ace_round_trip(formula)
    assert trip.equivalent, trip.detail
    assert trip.back.modalities == ("must",)


@live
def test_a_transitive_verb_under_a_modal_round_trips():
    formula = P.parse("□∃e1 See(e1, john, mary)")
    trip = modal_ace_round_trip(formula)
    assert trip.equivalent, trip.detail


@live
def test_the_duplex_consequent_modal_reports_its_modality_on_the_backward_leg():
    formula = P.parse("∀x1 (Man(x1) → Ⓟ∃e1 Wait(e1, x1))")
    trip = modal_ace_round_trip(formula)
    assert trip.equivalent, trip.detail
    assert trip.back.modalities == ("may",)
