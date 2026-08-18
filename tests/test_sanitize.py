"""Tests for name sanitisation: rewriting imported symbol names to MSFLParser-legal
tokens so a rendered formula re-parses.

The contract is ``parse(sanitize_names(node)[0].to_unicode_str()) == sanitize_names(node)[0]``
for the default (FOL) parser, with already-legal names left unchanged and a reversible
mapping. The driving use case is reading an OWL→FOL TPTP dump whose predicates/individuals
are IRIs with underscores, then rendering round-trippable Unicode.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, sanitize_names, sanitize_all, NameMapping, parse_tptp, parse_tptp_formula,
)
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Variable, Function, Quantifier, Implies, Number,
)

P = MSFLParser()


def _roundtrips(node):
    return P.parse(node.to_unicode_str()) == node


# ---------------------------------------------------------------------------
# Already-legal formulas pass through unchanged
# ---------------------------------------------------------------------------

def test_legal_formula_is_unchanged():
    f = P.parse("∀x (Human(x) → Mortal(x)) ∧ Loves(alice, bob)")
    s, m = sanitize_names(f)
    assert s == f
    assert _roundtrips(s)


def test_comparisons_and_arithmetic_not_renamed():
    f = P.parse("dist(x, y) > z ∧ P(x + y) ∧ a1 = b1")
    s, _ = sanitize_names(f)
    # the operator-valued names survive verbatim
    preds = {a.predicate for a in s.atoms()}
    assert ">" in preds and "=" in preds
    assert any(isinstance(n, Function) and n.name == "+" for n in s.walk())
    assert _roundtrips(s)


# ---------------------------------------------------------------------------
# Illegal names get rewritten and then round-trip
# ---------------------------------------------------------------------------

def test_underscored_predicate_round_trips():
    """The underscore became legal in predicate position after 0.23.0 (the
    chemical vocabulary needs it — see fol/_identifiers.predicate_pattern), so
    this IRI now parses on its own. sanitize_names still rewrites it, and must:
    its job is not "make it parseable" but "make it safe for the ASCII target
    formats", and it reaches that verdict through its OWN deliberately
    ASCII-strict _PRED_RE, never by asking the parser. The round-trip and the
    reverse mapping are what this test is actually about, and both still hold.
    """
    f = Atom("Http___www_w3_org_owl_Thing", [Variable("x")])
    assert P.parse(f.to_unicode_str()) == f   # legal now — but still rewritten
    s, m = sanitize_names(f)
    assert s.predicate != "Http___www_w3_org_owl_Thing"
    assert "_" not in s.predicate
    assert _roundtrips(s)
    assert m.reverse()[s.predicate] == "Http___www_w3_org_owl_Thing"


def test_single_letter_constant_becomes_c_form():
    # A single-letter constant would re-parse as a *variable* without the c_ form.
    f = Atom("P", [Constant("a")])
    assert isinstance(P.parse(f.to_unicode_str()).args[0], Variable)   # the hazard
    s, _ = sanitize_names(f)
    assert s.args[0].name.startswith("c_")
    reparsed = P.parse(s.to_unicode_str())
    assert isinstance(reparsed.args[0], Constant)
    assert _roundtrips(s)


def test_digit_tail_constant_becomes_c_form():
    # 'x1' lexes as a variable; a constant named x1 must take the c_ form.
    f = Atom("P", [Constant("x1")])
    s, _ = sanitize_names(f)
    assert isinstance(P.parse(s.to_unicode_str()).args[0], Constant)
    assert _roundtrips(s)


def test_legal_multichar_constant_kept_verbatim():
    f = Atom("P", [Constant("socrates")])
    s, _ = sanitize_names(f)
    assert s.args[0] == Constant("socrates")     # already legal bare NAME
    assert _roundtrips(s)


def test_distinct_names_stay_distinct():
    # Two predicates that share their alphanumerics must not collapse to one name.
    f = Implies(Atom("Foo__bar", [Variable("x")]), Atom("Foobar", [Variable("x")]))
    s, m = sanitize_names(f)
    assert s.left.predicate != s.right.predicate
    assert _roundtrips(s)


# ---------------------------------------------------------------------------
# Shared mapping keeps a whole problem consistent
# ---------------------------------------------------------------------------

def test_shared_mapping_is_consistent_across_formulas():
    f1 = Atom("Http___ex_org_C", [Variable("x")])
    f2 = Atom("Http___ex_org_C", [Constant("ind_1")])
    sans, m = sanitize_all([f1, f2])
    # same IRI -> same legal predicate token in both formulas
    assert sans[0].predicate == sans[1].predicate
    assert all(_roundtrips(s) for s in sans)
    assert m.reverse()[sans[0].predicate] == "Http___ex_org_C"


def test_variable_already_legal_is_kept():
    f = P.parse("∀x ∀x0 R(x, x0)")
    s, _ = sanitize_names(f)
    assert s == f
    assert _roundtrips(s)


# ---------------------------------------------------------------------------
# TPTP single-quoted atoms (the OWL→FOL dump shape) read + sanitise + round-trip
# ---------------------------------------------------------------------------

def test_tptp_single_quoted_atoms_read():
    text = ("fof(a, axiom, (![X]: ('http___ex_org_Thing'(X) | "
            "'http___ex_org_rel'(X, 'http___ex_org_indiv'))))." )
    recs = parse_tptp(text)
    f = recs[0].formula
    names = {a.predicate for a in f.atoms()}
    assert "Http___ex_org_Thing" in names          # IRI kept, capitalised in pred position
    assert "Http___ex_org_rel" in names
    # the individual is a constant argument carrying its IRI verbatim
    consts = {t.name for t in f.walk() if isinstance(t, Constant)}
    assert "http___ex_org_indiv" in consts


def test_tptp_single_quoted_then_sanitise_round_trips():
    text = ("fof(a, axiom, (![X]: ('http___ex_org_Thing'(X) => "
            "?[Y]: ('http___ex_org_rel'(X, Y) & 'http___ex_org_Other'(Y))))).")
    f = parse_tptp(text)[0].formula
    s, m = sanitize_names(f)
    assert _roundtrips(s)
    # the IRIs are recoverable
    rev = m.reverse()
    assert "Http___ex_org_Thing" in rev.values()


def test_tptp_single_quoted_escaped_quote():
    f = parse_tptp_formula(r"'a\'b'(x)")
    assert isinstance(f, Atom) and "'" in f.predicate   # the escaped quote is unescaped
    s, _ = sanitize_names(f)
    assert _roundtrips(s)


# ---------------------------------------------------------------------------
# Public API surface
# ---------------------------------------------------------------------------

def test_sanitize_exports():
    import unicode_fol_kit as u
    for name in ("sanitize_names", "sanitize_all", "NameMapping"):
        assert hasattr(u, name) and name in u.__all__, name
