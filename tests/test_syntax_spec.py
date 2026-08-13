"""Tests for the machine-readable syntax spec (unicode_fol_kit.mcp.syntax_spec).

The point of this module is that the spec CANNOT LIE: every example it hands
to a model is parsed here with the dialect the spec claims for it, and its
rendering is compared to the rendering the spec advertises. A rule the parser
does not implement is a failing test, not a surprise for whoever trusts the
spec at runtime.

The remaining tests pin the facts the spec asserts in prose — the naming
kinds, the biconditional's precedence, the counting quantifier's semantics —
against the real parser, for the same reason.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import (
    Constant, Count, Function, Quantifier, Variable,
)
from unicode_fol_kit.mcp.syntax_spec import EXAMPLES, SPEC_TOPICS, syntax_spec


# ---------------------------------------------------------------------------
# The self-verification: every advertised example really parses that way
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("label,dialect,text,rendering", EXAMPLES,
                         ids=[e[0] for e in EXAMPLES])
def test_every_spec_example_parses_as_advertised(label, dialect, text, rendering):
    """Each EXAMPLES row is parsed with its own declared dialect and must
    render back exactly as the spec claims — the guarantee that keeps the
    served specification in step with the parser."""
    parsed = api.parse_any(text, hint=dialect)
    assert parsed.ok, f"{label}: {text!r} did not parse as {dialect}: {parsed.errors}"
    assert parsed.formula.to_unicode_str() == rendering


def test_example_labels_are_unique():
    labels = [label for label, _d, _t, _r in EXAMPLES]
    assert len(labels) == len(set(labels))


def test_every_topic_builds_and_carries_its_name():
    for topic in SPEC_TOPICS:
        spec = syntax_spec(topic)
        assert spec["topic"] == topic
        assert spec["summary"]


def test_unknown_topic_is_refused_with_the_valid_list():
    with pytest.raises(ValueError, match="unknown topic"):
        syntax_spec("no-such-topic")


def test_dialect_filter_narrows_examples():
    """The chemistry topic mixes dialects only in principle; filtering to
    tptp_bare must keep exactly the tptp_bare rows."""
    spec = syntax_spec("naming", dialect="tptp_bare")
    assert spec["filtered_to_dialect"] == "tptp_bare"
    assert spec["examples"]
    assert all(e["dialect"] == "tptp_bare" for e in spec["examples"])


# ---------------------------------------------------------------------------
# The prose claims, pinned against the parser
# ---------------------------------------------------------------------------

def test_naming_rules_hold_in_the_parser():
    """'a1' is a variable, 'alice' a constant, 'P' a predicate, and a
    lowercase applied name is a function — exactly what the naming topic
    claims, hand-derived from the kit's grammar conventions."""
    formula = api.parse_any("P(a1)").formula
    assert isinstance(formula.args[0], Variable)
    formula = api.parse_any("P(alice)").formula
    assert isinstance(formula.args[0], Constant)
    formula = api.parse_any("P(f(x))").formula
    assert isinstance(formula.args[0], Function)
    # A lowercase predicate is NOT accepted in the unicode dialect — the very
    # reason the chemistry topic insists on TPTP.
    assert not api.parse_any("p(x)", hint="fol").ok


def test_tptp_inverts_the_case_convention():
    """TPTP 'c(A1)' is predicate c applied to variable A1; the kit normalises
    to its own convention (C over a1), injectively."""
    formula = api.parse_any("c(A1)", hint="tptp_bare").formula
    assert formula.predicate == "C"
    assert isinstance(formula.args[0], Variable)
    assert formula.args[0].name == "a1"


def test_biconditional_precedence_claim():
    """The operators topic claims 'p <=> a & b' means 'p <=> (a & b)'."""
    loose = api.parse_any("p <=> a & b", hint="tptp_bare").formula
    tight = api.parse_any("p <=> (a & b)", hint="tptp_bare").formula
    assert loose == tight


def test_unicode_grammar_is_stricter_claim():
    """The operators topic warns that the numeric precedence levels describe
    the ASCII dialects, and that the kit's own unicode syntax REFUSES a
    mixed ∧/∨ chain rather than resolving it. Both halves pinned here,
    because a spec that promised a precedence the parser does not implement
    would send a generator into an unfixable loop."""
    assert not api.parse_any("A ∧ B ∨ C", hint="fol").ok
    assert api.parse_any("(A ∧ B) ∨ C", hint="fol").ok
    assert api.parse_any("A ∧ B ∧ C", hint="fol").ok      # same connective: fine
    assert api.parse_any("A ∧ B → C", hint="fol").ok      # → is a looser level
    # TPTP resolves the very input unicode refuses.
    assert (api.parse_any("a & b | c", hint="tptp_bare").formula
            == api.parse_any("(a & b) | c", hint="tptp_bare").formula)
    assert "SYNTAX" in syntax_spec("operators")["unicode_grammar_is_stricter"]


def test_quantifier_scope_pitfall_claim():
    """The quantifiers topic warns that '∀x P(x) → Q(x)' leaves x free in
    Q(x). Hand-derived: the quantifier binds only the prefix-level P(x)."""
    report = api.check("∀x P(x) → Q(x)")
    assert report.is_closed is False
    assert "x" in report.free_variables
    assert api.check("∀x (P(x) → Q(x))").is_closed is True


def test_counting_quantifier_semantics_claim():
    """'∃≥40 x Carbon(x)' parses to a Count node with a symbolic bound — the
    counting topic's claim that a large threshold costs nothing to write."""
    formula = api.parse_any("∃≥40 x Carbon(x)").formula
    assert isinstance(formula, Count)
    assert formula.op == "ge"
    assert formula.n.value == 40


def test_quoted_tptp_name_keeps_the_full_chemical_name():
    """The errors topic tells the model to quote rather than sanitise; that
    advice is only sound if quoting really preserves the name, prefix and
    all."""
    formula = api.parse_any("'1,2-diacyl-sn-glycero-3-phosphocholine'",
                            hint="tptp_bare").formula
    assert formula.predicate == "1,2-diacyl-sn-glycero-3-phosphocholine"


def test_mixed_connective_error_class_matches_the_real_rejection():
    """The errors catalogue quotes the message for 'A ∧ B ∨ C' and tells the
    reader to bracket rather than rename. Checked against the parser in all
    three parts, because this entry is advice about a message: the rejection
    really carries the mixing hint, both bracketings really parse, and they
    really denote different formulas — which is the whole reason the grammar
    refuses to pick one."""
    entry = next(c for c in syntax_spec("errors")["classes"]
                 if c["kind"] == "mixed_same_level_connectives")
    assert entry["topic"] == "operators"

    parsed = api.parse_any("A ∧ B ∨ C", hint="fol")
    assert not parsed.ok
    assert any("Cannot mix" in e["message"] for e in parsed.to_dict()["errors"])

    left = api.parse_any("(A ∧ B) ∨ C", hint="fol")
    right = api.parse_any("A ∧ (B ∨ C)", hint="fol")
    assert left.ok and right.ok
    assert left.formula != right.formula


def test_errors_topic_points_at_real_topics():
    """Every failure class routes the model to a topic that actually exists —
    the spec is a navigable loop, not a dead end."""
    for entry in syntax_spec("errors")["classes"]:
        assert entry["topic"] in SPEC_TOPICS


def test_overview_lists_the_live_dialect_order():
    """The overview reads its dialect order from the live detection table, so
    it cannot drift from parse_any's behaviour."""
    from unicode_fol_kit.fol.dialect_detect import detect_dialects

    order = syntax_spec("overview")["dialects_in_detection_order"]
    assert order[-1] == "unicode"
    assert detect_dialects("fof(a, axiom, p).")[0] in order
