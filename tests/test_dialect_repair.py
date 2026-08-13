"""Tests for :mod:`unicode_fol_kit.fol.dialect_repair` — the same three
LLM-syntax failure classes as ``tests/test_tptp_repair.py``, but for
formulas written in the kit's own unicode surface syntax.

Every expected string/AST below is hand-derived (never copy-pasted from a
program run):

* **Case 1** (biimplication structure error) has no analogue here. The
  kit's grammar puts ``↔``/``→`` below ``∧``/``∨``, so
  ``P(x) ↔ A(x) ∧ B(x)`` is already unambiguous — and ``to_unicode_str``
  renders a formula back with exactly the brackets the grammar needs, not
  with unconditional ones, so there is nothing to normalise on either side.
  The tests below pin BOTH halves of that claim (input and output).
  What the grammar refuses instead — ``A ∧ B ∨ C``, mixed at one level — is
  reported and never repaired: two readings, no way to know which was meant.
* **Case 2** (invalid predicate name): the unicode grammar has no quoting
  mechanism, so the fix is a rename through
  :class:`~unicode_fol_kit.fol.sanitize.NameMapping`. Its rule, from
  ``sanitize.NameMapping.for_predicate``: keep the ASCII-alphanumerics, and
  if the result does not start with a letter, prefix ``P``; then upper-case
  the first character. Hand-applied per test, character by character.
* **Case 3** (unbound variable): identical to the TPTP path by
  construction — this module calls tptp_repair's own two fixes — so the
  tests here pin the two OUTCOMES (argument-drop vs. universal closure) on
  unicode input rather than re-deriving the fixes.
"""

import json

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import (
    And, Atom, Iff, Implies, Quantifier, Variable,
)
from unicode_fol_kit.fol.sanitize import NameMapping
from unicode_fol_kit.fol.dialect_repair import DialectRepairResult, repair_formula


def _kinds(result):
    return [issue.kind for issue in result.issues]


# ---------------------------------------------------------------------------
# Case 1 — the one that disappears, and the one that replaces it
# ---------------------------------------------------------------------------

def test_case1_has_no_analogue_the_unbracketed_biimplication_is_already_exact():
    """The Case-1 shape, in unicode: gavel rejects it, this grammar does not.

    Hand-derivation: the ladder has ``↔`` looser than ``∧``, so
    ``P(x) ↔ A(x) ∧ B(x)`` builds ``Iff(P(x), And(A(x), B(x)))`` — the same
    tree the explicitly bracketed form builds, which the second assertion
    checks independently. Nothing to repair: no issue, and ``changed`` is
    False because ``to_unicode_str`` re-emits exactly these brackets.
    """
    x = Variable("x")
    expected = Quantifier("∀", x, Iff(Atom("P", [x]),
                                      And(Atom("A", [x]), Atom("B", [x]))))

    result = repair_formula("∀x (P(x) ↔ A(x) ∧ B(x))")

    assert result.ok is True
    assert result.formula == expected
    assert result.issues == ()
    assert result.changed is False
    assert result.repaired_text == "∀x (P(x) ↔ A(x) ∧ B(x))"
    # …and the bracketed form a stricter parser demands means the same here,
    # so the author who writes it loses nothing either.
    assert api.parse_any("∀x (P(x) ↔ (A(x) ∧ B(x)))").formula == expected


def test_mixed_connectives_are_reported_and_never_bracketed():
    """``A ∧ B ∨ C`` has two readings. The grammar refuses it; this module
    passes the refusal on rather than picking one — repairing it would throw
    away the exact property that makes the dialect worth generating in."""
    text = "∀x (A(x) ∧ B(x) ∨ C(x))"

    result = repair_formula(text)

    assert result.ok is False
    assert result.formula is None
    assert _kinds(result) == ["mixed_connectives"]
    assert result.repaired_text == text          # untouched, to the character
    assert result.changed is False
    assert "cannot mix" in result.issues[0].message.lower()


# ---------------------------------------------------------------------------
# Case 2 — invalid names: renamed, invertibly
# ---------------------------------------------------------------------------

def test_case2_chemical_name_becomes_a_legal_predicate():
    """A literal Case-2 name.

    Hand-derivation of the legal token for
    ``1,2-diacyl-sn-glycero-3-phosphocholine``: keeping the ASCII-alphanumerics
    gives ``12diacylsnglycero3phosphocholine``; it starts with ``1``, not a
    letter, so ``P`` is prefixed; upper-casing the (already upper) first
    character leaves ``P12diacylsnglycero3phosphocholine``.
    """
    x = Variable("x")
    legal = "P12diacylsnglycero3phosphocholine"
    expected = Quantifier("∀", x, Implies(Atom(legal, [x]), Atom("Lipid", [x])))

    result = repair_formula(
        "∀x (1,2-diacyl-sn-glycero-3-phosphocholine(x) → Lipid(x))")

    assert result.ok is True
    assert result.names == (("1,2-diacyl-sn-glycero-3-phosphocholine", legal),)
    assert result.formula == expected
    assert _kinds(result) == ["invalid_predicate_name"]
    assert result.changed is True
    # The repaired text is text again: it re-parses to the same AST.
    assert api.parse_any(result.repaired_text).formula == expected


def test_case2_stereodescriptor_prefix_shape():
    """A second Case-2 shape, a parenthesised prefix glued to the name:
    ``(2S)Flavan4One`` → alphanumerics ``2SFlavan4One`` → starts with a
    digit → ``P2SFlavan4One``."""
    result = repair_formula("∀x ((2S)Flavan4One(x) → Flavan(x))")

    assert result.ok is True
    assert result.names == (("(2S)Flavan4One", "P2SFlavan4One"),)


def test_case2_rename_is_invertible():
    """The whole difference to a plain camelCase fallback: the original
    spelling survives, in the result and in the caller's mapping."""
    mapping = NameMapping()

    result = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))", mapping=mapping)

    original, legal = result.names[0]
    assert original == "1,2-diacyl"
    assert mapping.reverse()[legal] == original


def test_case2_one_shared_mapping_renames_a_name_identically_everywhere():
    """A run has to name the same ChEBI class the same way in every formula,
    or two definitions that mention it stop referring to one predicate."""
    mapping = NameMapping()

    first = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))", mapping=mapping)
    second = repair_formula("∀x (Fat(x) → 1,2-diacyl(x))", mapping=mapping)

    assert first.names[0][1] == second.names[0][1]


def test_case2_never_collides_with_a_name_already_in_the_text():
    """``1,2-diacyl`` legalises to ``P12diacyl`` — which this text already
    uses for a DIFFERENT predicate. Merging the two would silently identify
    two classes, so the reserved set is preseeded from the text itself and
    the rename lands on ``P12diacyl2`` instead."""
    result = repair_formula("∀x (1,2-diacyl(x) ∧ P12diacyl(x))")

    assert result.ok is True
    assert result.names == (("1,2-diacyl", "P12diacyl2"),)
    x = Variable("x")
    assert result.formula == Quantifier(
        "∀", x, And(Atom("P12diacyl2", [x]), Atom("P12diacyl", [x])))


def test_a_bound_variable_before_a_parenthesis_is_never_renamed():
    """``∀x (`` puts a bound variable immediately before an argument list's
    parenthesis, exactly where the case-2 detector looks. Renaming it would
    destroy the formula; what keeps it out is that ``x`` is a legal token in
    the variable class."""
    result = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))")

    assert result.ok is True
    assert result.formula.variable == Variable("x")
    assert [name for name, _legal in result.names] == ["1,2-diacyl"]


def test_a_rewrite_that_does_not_parse_is_discarded_whole():
    """A rename is kept only if it makes the input parse. Here the input is
    broken in a second way the rename cannot touch (a quantifier with no
    variable), so nothing is returned rewritten — the original text comes
    back untouched with an honest diagnosis."""
    text = "∀1,2-diacyl(x) → Lipid(x)"

    result = repair_formula(text)

    assert result.ok is False
    assert result.formula is None
    assert result.repaired_text == text
    assert _kinds(result) == ["syntax_error"]
    assert "renaming" in result.issues[0].message


def test_sanitize_invalid_names_false_reports_the_parser_untouched():
    """Opting out leaves the parser's own diagnosis as the only answer."""
    result = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))",
                            sanitize_invalid_names=False)

    assert result.ok is False
    assert result.names == ()
    assert "renaming" not in result.issues[0].message


# ---------------------------------------------------------------------------
# Case 3 — free variables: reported, or (opt-in) closed
# ---------------------------------------------------------------------------

def test_case3_free_variable_is_reported_but_not_touched_by_default():
    """``ok`` stays True: the AST is perfectly valid, the kit just will not
    guess how to close it."""
    result = repair_formula("P(x) ↔ ∃y Q(y)")

    assert result.ok is True
    assert _kinds(result) == ["free_variable"]
    assert result.changed is False
    assert result.repaired_text == "P(x) ↔ ∃y Q(y)"


def test_case3_argument_drop_when_the_definiendum_shape_holds():
    """The narrow argument-drop fix: ``x`` is the sole argument of the
    left-hand definiendum and does not recur on the right, so the definition
    is a 0-ary, molecule-level property that only accidentally carries an
    argument — ``P(x) ↔ ∃y Q(y)`` becomes ``P ↔ ∃y Q(y)``."""
    y = Variable("y")
    expected = Iff(Atom("P", []), Quantifier("∃", y, Atom("Q", [y])))

    result = repair_formula("P(x) ↔ ∃y Q(y)", close_free_variables=True)

    assert result.formula == expected
    assert result.repaired_text == "P ↔ ∃y Q(y)"
    assert _kinds(result) == ["free_variable"]


def test_case3_universal_closure_when_it_does_not():
    """No definiendum, so the standard convention applies instead."""
    x = Variable("x")
    expected = Quantifier("∀", x, And(Atom("Q", [x]), Atom("R", [x])))

    result = repair_formula("Q(x) ∧ R(x)", close_free_variables=True)

    assert result.formula == expected
    assert api.parse_any(result.repaired_text).formula == expected


# ---------------------------------------------------------------------------
# Cross-cutting
# ---------------------------------------------------------------------------

def test_unrepairable_input_keeps_its_text_and_reports_the_farthest_diagnosis():
    """Nothing is ever silently rewritten into something unverified, and the
    message is the one from the dialect that read FURTHEST — not the last
    one tried, which is a specialised dialect giving up at position 1."""
    text = "∀x (P(x) ∧"

    result = repair_formula(text)

    assert result.ok is False
    assert result.repaired_text == text
    assert _kinds(result) == ["syntax_error"]
    assert "ended unexpectedly" in result.issues[0].message.lower()


def test_the_result_is_a_repairresult_and_serialises():
    """A caller that already handles TPTP repairs handles these unchanged —
    same dataclass, two extra fields, JSON all the way down."""
    from unicode_fol_kit.fol.tptp_repair import RepairResult

    result = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))")

    assert isinstance(result, DialectRepairResult)
    assert isinstance(result, RepairResult)
    payload = json.loads(json.dumps(result.to_dict()))
    assert payload["dialect"] == "fol"
    assert payload["names"] == [{"original": "1,2-diacyl",
                                 "legal": "P12diacyl"}]
    assert payload["ok"] is True
