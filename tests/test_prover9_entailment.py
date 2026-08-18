"""Tests for the Prover9 problem generator's ASCII/legality sanitisation
(atp.prover9_entailment) — the Prover9 half of the widened-identifier-grammar
fix (see atp._tptp_problem's tests/module docstring for the TPTP half, and
atp.prover9_entailment's own module docstring for exactly what is/isn't in
scope here: there is no Prover9 "detailed" route reading a proof or
countermodel back out of Prover9's own output today, so unlike TPTP/E/Twee
there is no Rückweg to test here — only the Hinweg (export) side).

No Prover9 binary is available in this environment (not even through WSL),
so every syntactic-legality claim below is verified EXECUTED against the
kit's OWN Prover9 reader (fol.prover9_input.parse_prover9) — the R5 fallback
the task specifies for exactly this situation ("wo ein externes Werkzeug
fehlt, ist der kit-eigene Leser der Prüfstein").
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Variable
from unicode_fol_kit.fol.prover9_input import parse_prover9
from unicode_fol_kit.atp.prover9_entailment import (
    _generate_prover9_input,
    _sanitize_for_prover9,
    generate_prover9_input_with_mapping,
)

_PARSE = MSFLParser().parse
_A = Variable("a")


def _formula_lines(text: str):
    """Pull the bare formula text out of each '  <formula>.' line inside a
    formulas(...)/end_of_list. block (strips the leading indent and the
    trailing '.')."""
    out = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped and stripped not in ("end_of_list.",) and not stripped.startswith(("set(", "clear(", "formulas(")):
            assert stripped.endswith(".")
            out.append(stripped[:-1])
    return out


# ---------------------------------------------------------------------------
# Pure-refactor / shape sanity (the pre-existing behaviour, unchanged).
# ---------------------------------------------------------------------------

def test_shape_unchanged_for_clean_ascii_formulas():
    premises = [Atom("Human", [Constant("socrates")])]
    conclusion = Atom("Mortal", [Constant("socrates")])
    text = _generate_prover9_input(premises, conclusion)
    assert "set(prolog_style_variables)." in text
    assert "  Human(socrates)." in text
    assert "  Mortal(socrates)." in text


def test_uppercase_initial_predicate_is_not_touched():
    # Pinned by tests/test_export_fixes.py's Atom("Rain", []).to_prover9()
    # == "Rain" -- deliberate, pre-existing, untouched behaviour (see this
    # module's docstring); must not change here.
    text = _generate_prover9_input([], Atom("Rain", []))
    assert "  Rain." in text


# ---------------------------------------------------------------------------
# Hinweg: świątek / 2008SummerOlympics / dani_Shapiro, each executed through
# the kit's own Prover9 reader (R5).
# ---------------------------------------------------------------------------

class TestHinwegNonAsciiAndDigitLeadingNames:
    def test_non_ascii_constant_becomes_ascii_and_reparses(self):
        f = _PARSE("LostTo(x, świątek)")
        text = _generate_prover9_input([], f)
        assert "świątek" not in text
        assert text.isascii()
        [body] = _formula_lines(text.rsplit("formulas(goals).", 1)[1])
        reparsed = parse_prover9(body)
        assert reparsed.predicate == "LostTo"

    def test_digit_leading_constant_becomes_legal_and_reparses(self):
        f = _PARSE("Hosted(beijing, 2008SummerOlympics)")
        text = _generate_prover9_input([], f)
        assert text.isascii()
        [body] = _formula_lines(text.rsplit("formulas(goals).", 1)[1])
        reparsed = parse_prover9(body)  # must not raise: NAME grammar requires [A-Za-z_] first
        assert reparsed.predicate == "Hosted"
        assert reparsed.args[1].name[0].isalpha()

    def test_underscore_name_already_legal_passes_through_unchanged(self):
        f = _PARSE("P(dani_Shapiro)")
        text = _generate_prover9_input([], f)
        assert "  P(dani_Shapiro)." in text

    def test_all_three_reparse_cleanly(self):
        f1 = _PARSE("LostTo(x, świątek)")
        f2 = _PARSE("Hosted(beijing, 2008SummerOlympics)")
        f3 = _PARSE("P(dani_Shapiro)")
        text = _generate_prover9_input([f1, f2], f3)
        assumptions_block = text.split("formulas(assumptions).", 1)[1].split("end_of_list.", 1)[0]
        goals_block = text.split("formulas(goals).", 1)[1].split("end_of_list.", 1)[0]
        for body in _formula_lines(assumptions_block):
            parse_prover9(body)  # must not raise
        for body in _formula_lines(goals_block):
            parse_prover9(body)


# ---------------------------------------------------------------------------
# R1: already-legal names are never touched.
# ---------------------------------------------------------------------------

class TestR1NoChangeForAlreadyLegalNames:
    @pytest.mark.parametrize("name", [
        "socrates", "a", "alice", "hasBond", "dani_Shapiro", "family_History",
    ])
    def test_constant_names_are_identity_mapped(self, name):
        _, mapping = generate_prover9_input_with_mapping([], Atom("P", [Constant(name)]))
        assert mapping.mapping[name] == name

    @pytest.mark.parametrize("name", ["Rain", "Human", "hasBond"])
    def test_predicate_names_are_identity_mapped_case_included(self, name):
        _, mapping = generate_prover9_input_with_mapping([], Atom(name, []))
        assert mapping.mapping[name] == name

    def test_single_letter_constant_is_not_touched(self):
        # "a" is a legal Prover9 NAME token even though it is not a legal
        # bare kit-level NAME (it would re-lex as a VARIABLE there).
        premise = Atom("=", [Constant("a"), Constant("a")])
        _, mapping = generate_prover9_input_with_mapping([premise], Atom("Q", [_A]))
        assert mapping.mapping["a"] == "a"


# ---------------------------------------------------------------------------
# R2: whole-problem-consistent, collision-free.
# ---------------------------------------------------------------------------

class TestR2ConsistencyAndCollisionAvoidance:
    def test_same_non_ascii_name_reused_maps_consistently(self):
        p1 = Atom("P", [Constant("świątek")])
        p2 = Atom("Q", [Constant("świątek")])
        c = Atom("R", [Constant("świątek")])
        text, mapping = generate_prover9_input_with_mapping([p1, p2], c)
        token = mapping.mapping["świątek"]
        # ONE consistent token for every occurrence -- three formulas, three
        # uses of "świątek", but the exported text must name the SAME
        # sanitised constant in all three.
        assert text.count(token) == 3

    def test_synthesised_token_never_collides_with_an_already_legal_name(self):
        # Same construction as atp._tptp_problem's equivalent test: "s015b"
        # (lower-cased synthesis prefix + escape) vs. a literal name that
        # happens to equal it; both orders must avoid a collision.
        for premise in (Atom("=", [Constant("s015b"), Constant("ś")]),
                       Atom("=", [Constant("ś"), Constant("s015b")])):
            sanitised, mapping = _sanitize_for_prover9([premise])
            assert mapping.mapping["s015b"] == "s015b"
            assert mapping.mapping["ś"] != "s015b"

    def test_two_different_non_ascii_names_stay_distinct(self):
        premise = Atom("P", [Constant("świątek")])
        conclusion = Atom("Q", [Constant("śledź")])
        text, mapping = generate_prover9_input_with_mapping([premise], conclusion)
        assert mapping.mapping["świątek"] != mapping.mapping["śledź"]
        assert text  # no exception


# ---------------------------------------------------------------------------
# Consistency with atp._tptp_problem's collision-error precedent: Prover9
# never case-folds, so an already-legal name can never collide with another
# already-legal name (unlike TPTP) — nothing to test here, this is simply
# structurally impossible given _is_prover9_safe never changes a passthrough
# name; documented for completeness, not asserted as a no-op test.
# ---------------------------------------------------------------------------
