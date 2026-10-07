"""What reads a text before the parser does, now that a constant can be quoted.

A constant may be written in single quotes, ``'k2'`` or ``'John Doe'``, and the
text between the quotes is its name exactly. Four places look at a text before
(or around) the parser and know nothing of that:

* the LaTeX reader rewrites its input with substitutions that would change a
  quoted name, so it refuses a quote;
* ``api.parse_any`` chooses the order in which readers try a text, and that
  order is pinned here so that no text that read before reads differently;
* the repair layer scans a text that failed to parse with regular expressions,
  and must leave every quoted constant as it was written;
* the MCP tools take formula text and give formula text back, so a quoted
  constant has to go in and come out of each of them.

Every expected value below is worked out by hand from the definition of the
syntax and written as a literal; none is read off the code under test. Where a
check could pass for the wrong reason, a control case shows it can fail.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.fol import latex_input
from unicode_logic_kit.fol.dialect_detect import detect_dialects
from unicode_logic_kit.fol.dialect_repair import (
    _find_name_candidates, _glyph_rewrites, repair_formula,
)
from unicode_logic_kit.fol.latex_input import (
    LatexParsingError, latex_to_unicode, parse_latex,
)
from unicode_logic_kit.fol.naming import ParsingError
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Implies, Quantifier, Variable,
)


# ---------------------------------------------------------------------------
# 1. The LaTeX reader refuses a quote
# ---------------------------------------------------------------------------

class TestTheLatexReaderRefusesAQuote:
    """``latex_to_unicode`` collapses runs of spaces, turns ``\\_`` into ``_`` and
    strips braces without knowing where a quoted name begins, so it would change
    the name between two quotes without a word. Until it knows quotes it reads
    no text that holds one."""

    def test_a_quoted_constant_is_refused_by_name(self):
        with pytest.raises(LatexParsingError) as caught:
            latex_to_unicode("P('k2')")
        message = str(caught.value)
        assert message.startswith("SYNTAX_ERROR: ")
        assert "does not read a quoted constant" in message
        assert "Unicode syntax" in message

    def test_parse_latex_refuses_it_too(self):
        with pytest.raises(LatexParsingError) as caught:
            parse_latex(r"\forall x P('k2')")
        assert "does not read a quoted constant" in str(caught.value)

    def test_the_refusal_is_a_parsing_error_so_the_callers_of_the_parser_catch_it(self):
        with pytest.raises(ParsingError):
            parse_latex("P('k2')")

    def test_the_refusal_names_the_first_quote_by_its_position(self):
        # P ( ' k 2 ' ): the first quote is the third character.
        with pytest.raises(LatexParsingError, match="position 3 "):
            latex_to_unicode("P('k2')")
        # \forall is seven characters, then five more (a space, x, a space, P
        # and a bracket): twelve in all, so the quote is the 13th character.
        with pytest.raises(LatexParsingError, match="position 13 "):
            latex_to_unicode(r"\forall x P('k2')")

    def test_a_prime_is_refused_the_same_way(self):
        # Before quoted constants this text was a syntax error of the parser
        # (an unexpected quote after the variable x); now it is this refusal.
        # P ( x ' ): the quote is the fourth character.
        with pytest.raises(LatexParsingError, match="position 4 "):
            parse_latex("P(x')")

    def test_control_a_text_without_a_quote_is_not_refused(self):
        assert latex_to_unicode(r"\forall x (P(x) \land Q(x))") == "∀ x (P(x) ∧ Q(x))"
        assert parse_latex("P(x)") == Atom("P", [Variable("x")])

    # What the substitutions would have done, which is why the refusal is there.
    # With the refusal removed, each of these texts keeps its quotes and loses
    # or changes a character of the name between them.
    @pytest.mark.parametrize("text, what_the_substitutions_make_of_it", [
        ("P('John  Doe')", "P('John Doe')"),       # two spaces collapse to one
        ("P('a\\_b')", "P('a_b')"),                 # \_ becomes _
        ("P('f{x}')", "P('fx')"),                   # braces are stripped
    ])
    def test_control_without_the_refusal_the_name_would_change(
            self, monkeypatch, text, what_the_substitutions_make_of_it):
        monkeypatch.setattr(latex_input, "_refuse_quote", lambda text: None)
        assert latex_to_unicode(text) == what_the_substitutions_make_of_it
        assert what_the_substitutions_make_of_it != text

    def test_parse_any_records_the_refusal_and_goes_on_to_the_next_candidate(self):
        # \forall nominates the LaTeX reader first. It refuses the quote, the
        # unicode ladder is tried next, and nothing parses \forall there.
        text = r"\forall x P('k2')"
        assert detect_dialects(text) == ("latex", "unicode")
        result = api.parse_any(text)
        assert result.ok is False
        assert result.errors[0]["dialect"] == "latex"
        assert "does not read a quoted constant" in result.errors[0]["message"]
        assert result.errors[1]["dialect"] == "fol"        # the ladder was tried

    def test_parse_any_with_the_latex_hint_answers_instead_of_raising(self):
        result = api.parse_any("P('k2')", hint="latex")
        assert result.ok is False
        assert [e["dialect"] for e in result.errors] == ["latex"]
        assert "Unicode syntax" in result.errors[0]["message"]

    def test_a_text_the_latex_reader_refuses_may_still_read_in_the_ladder(self):
        # The text holds a backslash word that the LaTeX detector keys on, but
        # inside quotes: P('\\forall') is the atom P of the constant named
        # \forall (inside quotes a backslash is written \\).
        text = "P('\\\\forall')"
        assert detect_dialects(text) == ("latex", "unicode")
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "fol"
        assert result.formula == Atom("P", [Constant("\\forall")])
        assert [e["dialect"] for e in result.errors] == ["latex"]


# ---------------------------------------------------------------------------
# 2. The order in which parse_any tries its readers is unchanged
# ---------------------------------------------------------------------------

class TestTheDialectOrderIsPinned:
    """A text with ``~``, ``|``, ``&`` and the like is still tried as TPTP or
    Prover9 first, even when the character stands inside quotes, so no text that
    was read before is read differently now."""

    def test_an_equation_with_a_tilde_in_a_quoted_name_is_read_by_tptp_bare(self):
        text = "x = 'a~b'"
        assert detect_dialects(text) == ("tptp_bare", "unicode")
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "tptp_bare"
        # TPTP reads x as a constant (a lower-case word) and 'a~b' as the
        # constant named a~b, exactly as 0.30.0 did.
        assert result.formula == Atom("=", [Constant("x"), Constant("a~b")])

    def test_control_the_fol_dialect_reads_the_same_text_as_another_formula(self):
        # Pinned to the fol dialect, x is a variable, not a constant: the order
        # of the readers is what decides which of the two is the answer.
        result = api.parse_any("x = 'a~b'", hint="fol")
        assert result.ok is True
        assert result.formula == Atom("=", [Variable("x"), Constant("a~b")])

    def test_an_equation_with_a_plain_quoted_name_is_read_by_the_fol_dialect(self):
        # No reader took this text in 0.30.0. Nothing nominates another reader
        # for it, so the ladder reads it: x is a variable, 'ab' the constant ab.
        text = "x = 'ab'"
        assert detect_dialects(text) == ("unicode",)
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "fol"
        assert result.errors == ()
        assert result.formula == Atom("=", [Variable("x"), Constant("ab")])

    def test_an_ampersand_in_a_quoted_name_is_tried_as_prover9_and_then_read_by_the_ladder(self):
        text = "P('a & b')"
        assert detect_dialects(text) == ("prover9", "unicode")
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "fol"
        assert result.formula == Atom("P", [Constant("a & b")])
        assert [e["dialect"] for e in result.errors] == ["prover9"]

    def test_a_tilde_in_a_quoted_name_is_tried_as_tptp_and_then_read_by_the_ladder(self):
        # P is upper case, which a bare TPTP formula refuses as a predicate.
        text = "P('a~b')"
        assert detect_dialects(text) == ("tptp_bare", "unicode")
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "fol"
        assert result.formula == Atom("P", [Constant("a~b")])
        assert [e["dialect"] for e in result.errors] == ["tptp_bare"]

    def test_a_plain_quoted_constant_reports_the_fol_dialect_with_no_earlier_attempt(self):
        text = "P('k2')"
        assert detect_dialects(text) == ("unicode",)
        result = api.parse_any(text)
        assert result.ok is True
        assert result.dialect == "fol"
        assert result.errors == ()
        assert result.formula == Atom("P", [Constant("k2")])

    def test_a_stray_pair_of_apostrophes_reads_as_one_constant(self):
        # The limit of a quote that has a partner far away: the text between
        # the first and the last quote is one name.
        result = api.parse_any("P('x) ∧ Q(y')")
        assert result.ok is True
        assert result.formula == Atom("P", [Constant("x) ∧ Q(y")])


# ---------------------------------------------------------------------------
# 3. The repair layer leaves every quoted span as it was written
# ---------------------------------------------------------------------------

class TestTheRepairLeavesQuotedConstantsAlone:
    """The repair runs after a failed parse and scans for name-shaped spans with
    regular expressions. What stands between a pair of single quotes is a
    constant's name, exactly, and is never a candidate for a rename."""

    def test_a_name_in_functor_position_inside_quotes_is_no_candidate(self):
        assert _find_name_candidates("P('1,2-diacyl(x)')") == []

    def test_control_the_same_spelling_outside_quotes_is_a_candidate(self):
        # Unquoted, 1,2-diacyl(x) is a name in functor position that no symbol
        # class accepts. P is legal and is not reported.
        assert _find_name_candidates("P(1,2-diacyl(x))") == ["1,2-diacyl"]

    def test_an_escaped_quote_does_not_end_the_span(self):
        # 'it\'s 1,2-diacyl(x)' is ONE constant, named it's 1,2-diacyl(x).
        assert _find_name_candidates("P('it\\'s 1,2-diacyl(x)')") == []

    def test_an_escaped_backslash_does_end_it_at_the_next_quote(self):
        # 'a\\' is the constant named a\, and what follows it is outside.
        text = "P('a\\\\') ∧ 1,2-diacyl(x)"
        assert _find_name_candidates(text) == ["1,2-diacyl"]

    def test_quotes_pair_from_left_to_right(self):
        # 'a' and 'b' are two spans; the text between them is outside.
        assert _find_name_candidates("P('a', 1,2-diacyl(x), 'b')") == ["1,2-diacyl"]

    def test_a_quote_without_a_partner_is_no_span(self):
        # The one quote is a stray prime; both names stay candidates.
        text = "Foo-bar(x') ∧ Baz-q(y)"
        assert _find_name_candidates(text) == ["Foo-bar", "Baz-q"]

    def test_a_repair_keeps_each_quoted_constant_byte_for_byte(self):
        # 1,2-diacyl(x) is renamed (rule of NameMapping.for_predicate: keep the
        # ASCII alphanumerics 12diacyl, which does not start with a letter, so
        # prefix P). The four quoted constants are an upper-case word, a
        # variable-shaped word, a word with an underscore and a name that holds
        # the very spelling that is being renamed, each followed by a bracket
        # where it could be mistaken for a name in functor position.
        text = ("∀x (1,2-diacyl(x) → Lipid(x, 'Alice', 'k2', 'x_1(y)', "
                "'1,2-diacyl(x)'))")
        result = repair_formula(text)
        assert result.ok is True
        assert result.names == (("1,2-diacyl", "P12diacyl"),)
        expected_text = ("∀x (P12diacyl(x) → Lipid(x, 'Alice', 'k2', 'x_1(y)', "
                         "'1,2-diacyl(x)'))")
        assert result.repaired_text == expected_text
        for quoted in ("'Alice'", "'k2'", "'x_1(y)'", "'1,2-diacyl(x)'"):
            assert quoted in result.repaired_text
        x = Variable("x")
        assert result.formula == Quantifier("∀", x, Implies(
            Atom("P12diacyl", [x]),
            Atom("Lipid", [x, Constant("Alice"), Constant("k2"),
                           Constant("x_1(y)"), Constant("1,2-diacyl(x)")])))

    def test_control_the_same_name_outside_quotes_is_renamed_while_the_quoted_one_is_not(self):
        # x_1 is a legal name in no class (a variable is one letter and digits,
        # a name has two letters). Renamed by NameMapping.for_predicate: keep
        # the alphanumerics x1, upper-case the first letter, X1.
        text = "∀x (x_1(x) → Lipid(x, 'x_1(y)'))"
        result = repair_formula(text)
        assert result.ok is True
        assert result.names == (("x_1", "X1"),)
        assert result.repaired_text == "∀x (X1(x) → Lipid(x, 'x_1(y)'))"

    def test_a_text_that_cannot_be_repaired_is_reported_without_a_rename_attempt(self):
        # The only functor-position name is inside the quotes, so there is
        # nothing to rename; the text lacks its closing bracket and the parser's
        # own diagnosis is what comes back, with the text untouched.
        text = "P('1,2-diacyl(x)'"
        result = repair_formula(text)
        assert result.ok is False
        assert result.repaired_text == text
        assert result.names == ()
        assert [issue.kind for issue in result.issues] == ["syntax_error"]
        assert "renaming" not in result.issues[0].message

    def test_mixed_connectives_are_still_reported_and_never_bracketed(self):
        result = repair_formula("P('a b') ∧ Q ∨ R")
        assert result.ok is False
        assert result.repaired_text == "P('a b') ∧ Q ∨ R"
        assert [issue.kind for issue in result.issues] == ["mixed_connectives"]

    def test_a_truth_glyph_inside_quotes_is_not_a_glyph(self):
        # Outside the quotes the glyph is spelled as Prover9's constant (column
        # 0) and then as TPTP's (column 1); inside them it is part of a name.
        assert list(_glyph_rewrites("P('⊥') -> ⊥")) == [
            ("P('⊥') -> $F", 0), ("P('⊥') -> $false", 1)]

    def test_a_text_whose_only_glyph_is_quoted_has_no_glyph_rewrite(self):
        assert list(_glyph_rewrites("P('⊥') -> Q")) == []

    def test_control_the_same_glyph_outside_quotes_is_rewritten(self):
        assert list(_glyph_rewrites("P(⊥) -> Q")) == [
            ("P($F) -> Q", 0), ("P($false) -> Q", 1)]

    def test_a_repair_that_reads_a_glyph_keeps_the_quoted_glyph_as_a_name(self):
        # p('⊥') => ⊥ in TPTP: the quoted ⊥ is the constant named ⊥, the bare
        # one is falsity. If the rewrite touched the quoted one the constant
        # would be named $false.
        result = repair_formula("p('⊥') => ⊥", dialect="tptp_bare")
        assert result.ok is True
        assert [issue.kind for issue in result.issues] == ["truth_glyph"]
        assert result.formula == Implies(Atom("P", [Constant("⊥")]),
                                         Atom("$false", []))


# ---------------------------------------------------------------------------
# 4. The MCP tools take a quoted constant and give it back
# ---------------------------------------------------------------------------

FORMULA = "P('k2') ∧ Q('John Doe')"
#: The AST of FORMULA in the JSON shape of ``Node.to_dict``.
FORMULA_AST = {
    "_type": "And",
    "left": {"_type": "Atom", "predicate": "P",
             "args": [{"_type": "Constant", "name": "k2"}]},
    "right": {"_type": "Atom", "predicate": "Q",
              "args": [{"_type": "Constant", "name": "John Doe"}]},
}


@pytest.fixture(scope="module")
def tools():
    pytest.importorskip("mcp", reason="optional [mcp] extra not installed")
    from unicode_logic_kit.mcp import server
    return server


class TestParseFormulaAndRender:

    def test_parse_formula_reads_both_constants_and_writes_the_same_text_back(self, tools):
        result = tools.parse_formula(FORMULA)
        assert result["ok"] is True
        assert result["dialect"] == "fol"
        assert result["formula"] == FORMULA_AST
        assert result["unicode"] == FORMULA

    def test_parse_formula_answers_a_quote_that_is_never_closed_as_a_failure(self, tools):
        result = tools.parse_formula("P('k2")
        assert result["ok"] is False
        assert result["argument"] == "text"
        assert result["errors"]

    def test_parse_formula_unquotes_the_escapes_and_quotes_them_again(self, tools):
        # 'it\'s' is the constant it's, and 'a\\b' the constant a\b.
        text = "P('it\\'s') ∧ Q('a\\\\b')"
        result = tools.parse_formula(text)
        assert result["ok"] is True
        assert result["formula"]["left"]["args"] == [{"_type": "Constant", "name": "it's"}]
        assert result["formula"]["right"]["args"] == [{"_type": "Constant", "name": "a\\b"}]
        assert result["unicode"] == text

    def test_render_unicode_gives_the_quoted_text(self, tools):
        assert tools.render(FORMULA, to="unicode") == {
            "ok": True, "to": "unicode", "rendered": FORMULA}

    def test_render_json_carries_the_names_unquoted(self, tools):
        rendered = tools.render("P('John Doe')", to="json")["rendered"]
        assert rendered["root"] == {
            "_type": "Atom", "predicate": "P",
            "args": [{"_type": "Constant", "name": "John Doe"}]}

    def test_render_latex_writes_a_constant_by_its_name(self, tools):
        # The LaTeX text of a constant is its name: k2 reads back as a variable,
        # which is why the tool says to pass the unicode text on.
        assert tools.render("P('k2')", to="latex") == {
            "ok": True, "to": "latex", "rendered": "P(k2)"}

    def test_the_latex_text_of_a_quoted_constant_does_not_read_back_as_that_constant(self, tools):
        latex = tools.render("P('k2')", to="latex")["rendered"]
        assert api.parse_any(latex).formula == Atom("P", [Variable("k2")])

    def test_render_tptp_writes_a_name_tptp_can_spell(self, tools):
        assert tools.render("P('k2')", to="tptp") == {
            "ok": True, "to": "tptp", "rendered": "p(k2)"}

    def test_render_tptp_refuses_a_name_it_cannot_spell_as_a_structured_error(self, tools):
        result = tools.render("P('k2') ∧ Q('a b')", to="tptp")
        assert result["error"]["type"] == "NotImplementedError"
        assert "'a b'" in result["error"]["message"]


class TestProve:

    def test_a_conjunct_follows_from_a_conjunction_of_quoted_atoms(self, tools):
        assert tools.prove("P('k2')", [FORMULA])["status"] == "proved"

    def test_an_unrelated_atom_does_not_follow(self, tools):
        assert tools.prove("R('k2')", [FORMULA])["status"] == "refuted"

    def test_equal_constants_substitute(self, tools):
        premises = ["P('k2')", "'k2' = 'John Doe'"]
        assert tools.prove("P('John Doe')", premises)["status"] == "proved"

    def test_control_without_the_equation_the_other_constant_is_not_covered(self, tools):
        assert tools.prove("P('John Doe')", ["P('k2')"])["status"] == "refuted"

    def test_a_quoted_one_letter_name_is_a_constant_and_a_bare_one_is_a_variable(self, tools):
        # ∀x P(x) gives P('a'); P('a') says nothing of every x.
        assert tools.prove("P('a')", ["∀x P(x)"])["status"] == "proved"
        assert tools.prove("∀x P(x)", ["P('a')"])["status"] == "refuted"

    def test_a_quoted_name_that_is_spelled_like_a_variable_is_not_that_variable(self, tools):
        # ∀k2 P(k2) gives P('k2'); but P('k2') does not give the open P(k2),
        # which stands for every k2.
        assert tools.prove("P('k2')", ["∀k2 P(k2)"])["status"] == "proved"
        assert tools.prove("P(k2)", ["P('k2')"])["status"] == "refuted"

    def test_two_constants_that_differ_in_case_are_two_constants(self, tools):
        assert tools.prove("'k2' = 'k2'")["status"] == "proved"
        assert tools.prove("'k2' = 'K2'")["status"] == "refuted"

    def test_existential_generalisation_over_a_quoted_constant(self, tools):
        assert tools.prove("∃x P(x)", ["P('k2')"])["status"] == "proved"

    def test_a_countermodel_names_a_constant_by_its_name(self, tools):
        # Keys of a model are names, never quoted text (see the key of an atom).
        verdict = tools.prove("R('k2')", [FORMULA])
        assert verdict["status"] == "refuted"
        assert {"k2", "John Doe"} <= set(verdict["countermodel"]["assignment"])

    def test_a_quote_that_is_never_closed_in_a_premise_is_a_structured_failure(self, tools):
        result = tools.prove("P('k2')", ["P('k2"])
        assert result["ok"] is False
        assert result["argument"] == "premise[0]"

    def test_find_countermodel_finds_one_for_an_unrelated_atom(self, tools):
        assert tools.find_countermodel("R('k2')", [FORMULA])["found"] is True

    def test_check_consistency_decides_over_quoted_atoms(self, tools):
        assert tools.check_consistency(["P('k2')", "¬P('k2')"])["consistent"] is False
        assert tools.check_consistency(["P('k2')", "¬P('John Doe')"])["consistent"] is True


class TestTranslate:

    def test_a_sorted_quoted_constant_comes_out_quoted_with_its_membership_axiom(self, tools):
        from unicode_logic_kit.eval import canonicalize

        # ∃x:Mountain (x = 'k2':Mountain) becomes ∃x (Mountain(x) ∧ x = 'k2'),
        # and the constant of sort Mountain is an element of Mountain.
        result = tools.translate("∃x:Mountain (x = 'k2':Mountain)", "msfol", "fol")
        assert result["unicode"] == "∃x (Mountain(x) ∧ x = 'k2')"
        axioms = result["axioms_unicode"]
        assert len(axioms) == 2
        assert "Mountain('k2')" in axioms
        non_empty = [a for a in axioms if a != "Mountain('k2')"][0]
        assert (canonicalize(api.parse_any(non_empty).formula)
                == canonicalize(api.parse_any("∃x Mountain(x)").formula))

    def test_the_translated_text_and_its_axioms_go_back_into_prove_as_the_same_formula(self, tools):
        # ∃x:Mountain (x = 'k2':Mountain) is valid in many-sorted logic, because
        # 'k2' is a Mountain. Its image is valid only together with the axioms.
        result = tools.translate("∃x:Mountain (x = 'k2':Mountain)", "msfol", "fol")
        with_axioms = tools.prove(result["unicode"], result["axioms_unicode"])
        without = tools.prove(result["unicode"])
        assert with_axioms["status"] == "proved"
        assert without["status"] == "refuted"

    def test_a_modal_image_keeps_the_quoted_constant_and_adds_the_world(self, tools):
        # □P('k2') is ∀w0 (R(w, w0) → P('k2', w0)), anchored at the free world w.
        result = tools.translate("□P('k2')", "modal", "fol")
        assert result["unicode"] == "∀w0 (R(w, w0) → P('k2', w0))"
        assert result["axioms_unicode"] == []

    def test_the_image_of_a_modal_axiom_is_valid_exactly_under_its_frame_axioms(self, tools):
        # □P('k2') → P('k2') is valid when the relation is reflexive (frame T),
        # and not when it is unconstrained (frame K).
        in_t = tools.translate("□P('k2') → P('k2')", "modal", "fol", frame="T")
        assert in_t["axioms_unicode"] == ["∀v0 R(v0, v0)"]
        assert tools.prove(in_t["unicode"], in_t["axioms_unicode"])["status"] == "proved"
        in_k = tools.translate("□P('John Doe') → P('John Doe')", "modal", "fol")
        assert in_k["axioms_unicode"] == []
        assert tools.prove(in_k["unicode"], in_k["axioms_unicode"])["status"] == "refuted"

    def test_a_fuzzy_source_reads_and_writes_quoted_constants(self, tools):
        # The fuzzy source is read in the fl and msfl modes, not the fol one.
        result = tools.translate(FORMULA, "fuzzy", "msfol")
        assert result["unicode"] == FORMULA
        assert result["axioms_unicode"] == []

    def test_an_image_that_holds_a_constant_without_a_text_is_a_structured_error(
            self, tools, monkeypatch):
        # A name with a line break has no text, bare or quoted. A translation
        # cannot make one out of parsed text, so the registry is replaced by one
        # that does: the tool must answer with an error and not raise.
        from unicode_logic_kit.comorphism import DEFAULT_REGISTRY

        class _Image:
            result = Atom("P", [Constant("a\nb")])
            axioms = ()

            def to_dict(self):
                return {"result": None}

        monkeypatch.setattr(DEFAULT_REGISTRY, "translate",
                            lambda *args, **kwargs: _Image())
        result = tools.translate("P(x)", "msfol", "fol")
        assert result["error"]["type"] == "ValueError"
        assert "'a\\nb'" in result["error"]["message"]


class TestTheTextTheOtherToolsCanRead:
    """``_text_of`` renders a translated node as text another tool can read, as
    the same formula. Each way out of it is reached by a node a translation can
    hold, so none of the code is dead."""

    def test_a_constant_of_a_one_letter_name_reads_back_as_itself_at_the_first_spelling(self, tools):
        node = Atom("P", [Constant("a")])
        text = tools._text_of(node)
        assert text == "P('a')"
        assert api.parse_any(text).formula == node

    def test_a_constant_of_an_upper_case_name_reads_back_as_itself(self, tools):
        node = Atom("P", [Constant("Alice"), Constant("John Doe")])
        text = tools._text_of(node)
        assert text == "P('Alice', 'John Doe')"
        assert api.parse_any(text).formula == node

    def test_a_bound_variable_named_like_a_constant_is_renamed_to_read_back(self, tools):
        # ∀hasChild is refused (a binder is one letter and digits). Renamed to
        # q0, the formula is the same formula up to the name of the binder.
        h = Variable("hasChild")
        node = Quantifier("∀", h, Atom("P", [h]))
        assert tools._text_of(node) == "∀q0 P(q0)"

    def test_a_free_variable_named_like_a_constant_is_printed_as_it_is(self, tools):
        # No spelling reads back as the same formula (the text reads as the
        # constant hasChild, and alpha-renaming leaves a free name alone), so
        # the first spelling that parses at all is returned.
        node = Atom("P", [Variable("hasChild")])
        text = tools._text_of(node)
        assert text == "P(hasChild)"
        assert api.parse_any(text).formula == Atom("P", [Constant("hasChild")])

    def test_the_renamed_spelling_wins_when_only_it_parses(self, tools):
        # The binder makes the first spelling unreadable; the second reads, as
        # a formula whose free name is a constant now, which is the best there is.
        h = Variable("hasChild")
        node = Quantifier("∀", h, Atom("P", [h, Variable("other")]))
        assert api.parse_any(node.to_unicode_str()).ok is False
        assert tools._text_of(node) == "∀q0 P(q0, other)"

    def test_a_predicate_that_starts_in_lower_case_is_printed_as_it_is(self, tools):
        # hasChild(x, x) reads as a function application, which is no formula,
        # and no renaming of a variable changes that.
        x = Variable("x")
        node = Atom("hasChild", [x, x])
        assert api.parse_any(node.to_unicode_str()).ok is False
        assert tools._text_of(node) == "hasChild(x, x)"

    @pytest.mark.parametrize("name, fragment", [
        ("a\nb", "'a\\nb'"),
        ("", "''"),
    ])
    def test_a_constant_that_has_no_text_is_refused_by_name(self, tools, name, fragment):
        with pytest.raises(ValueError) as caught:
            tools._text_of(Atom("P", [Constant(name)]))
        assert fragment in str(caught.value)


class TestTheOtherToolsThatTakeFormulaText:

    def test_check_formula_lists_the_constants_by_name(self, tools):
        report = tools.check_formula(FORMULA)
        assert report["ok"] is True
        assert report["constants"] == ["John Doe", "k2"]
        assert report["free_variables"] == []

    def test_check_formula_tells_a_quoted_constant_from_a_free_variable(self, tools):
        report = tools.check_formula("P('k2') ∧ Q(x)")
        assert report["constants"] == ["k2"]
        assert report["free_variables"] == ["x"]

    def test_check_formula_holds_a_constant_to_a_signature_by_its_name(self, tools):
        loose = {"predicates": {"P": 1, "Q": 1}, "constants": ["k2", "John Doe"]}
        assert tools.check_formula(FORMULA, signature=loose)["ok"] is True
        missing = {"predicates": {"P": 1, "Q": 1}, "constants": ["k2"]}
        report = tools.check_formula(FORMULA, signature=missing)
        assert report["ok"] is False
        assert [(e["kind"], e["symbol"]) for e in report["signature_errors"]] == [
            ("unknown_constant", "John Doe")]

    def test_get_signature_keys_the_constants_by_name(self, tools):
        constants = tools.get_signature([FORMULA])["signature"]["constants"]
        assert constants == {"John Doe": None, "k2": None}

    def test_check_equivalence_sees_a_commuted_conjunction_of_quoted_atoms(self, tools):
        assert tools.check_equivalence(FORMULA, "Q('John Doe') ∧ P('k2')")["equivalent"] is True

    def test_check_equivalence_does_not_identify_a_constant_with_the_variable_of_its_name(self, tools):
        assert tools.check_equivalence("P('k2')", "P(k2)")["equivalent"] is False

    def test_compare_formulas_tells_two_constants_apart(self, tools):
        same = tools.compare_formulas(FORMULA, "Q('John Doe') ∧ P('k2')")
        assert same["canonical_exact_match"] is True
        assert same["vocabulary"]["constants"]["shared"] == ["John Doe", "k2"]
        other = tools.compare_formulas("P('k2')", "P('K2')")
        assert other["canonical_exact_match"] is False

    def test_score_batch_scores_an_exact_match(self, tools):
        assert tools.score_batch([FORMULA], [FORMULA])["exact_match"] == 1.0

    def test_normalize_writes_the_normal_form_with_the_constants_quoted(self, tools):
        # De Morgan: ¬(A ∧ B) is ¬A ∨ ¬B.
        result = tools.normalize("¬(P('k2') ∧ Q('John Doe'))", form="nnf")
        assert result["unicode"] == "¬P('k2') ∨ ¬Q('John Doe')"

    def test_diagnose_finds_nothing_to_fix(self, tools):
        step = tools.diagnose(FORMULA)
        assert step["ok"] is True
        assert step["converged"] is True

    def test_diagnose_of_a_latex_text_with_a_quote_says_what_the_latex_reader_refuses(self, tools):
        # The LaTeX reader got furthest into this text (the quote is its 13th
        # character; the unicode ladder stops at the first backslash), so its
        # objection is the one the suggestion carries.
        step = tools.diagnose(r"\forall x P('k2')")
        assert step["ok"] is False
        assert "does not read a quoted constant" in step["suggestion"]

    def test_parse_formula_of_a_latex_text_with_a_quote_lists_the_latex_refusal_first(self, tools):
        result = tools.parse_formula(r"\forall x (P(x) \land Q('John Doe'))")
        assert result["ok"] is False
        assert result["errors"][0]["dialect"] == "latex"
        assert "Unicode syntax" in result["errors"][0]["message"]

    def test_detect_dialect_reports_the_ladder_and_the_mode(self, tools):
        assert tools.detect_dialect(FORMULA) == {
            "ok": True, "candidates": ["unicode"], "parsed_as": "fol", "errors": []}

    def test_repair_formula_renames_the_predicate_and_keeps_the_quoted_constant(self, tools):
        result = tools.repair_formula("∀x (1,2-diacyl(x) → Lipid(x, 'x_1(y)'))")
        assert result["ok"] is True
        assert result["repaired_text"] == "∀x (P12diacyl(x) → Lipid(x, 'x_1(y)'))"
        assert result["names"] == [{"original": "1,2-diacyl", "legal": "P12diacyl"}]

    def test_probability_query_reads_quoted_atoms(self, tools):
        # P(A ∨ B) = 1 - (1 - 3/10)(1 - 1/2) = 13/20 for independent facts.
        result = tools.probability_query(
            "Smokes('John Doe') ∨ Smokes('k2')",
            [{"atom": "Smokes('John Doe')", "prob": "3/10"},
             {"atom": "Smokes('k2')", "prob": "1/2"}])
        assert result["ok"] is True
        assert result["probability"] == "13/20"

    def test_probability_bounds_reads_quoted_atoms(self, tools):
        # P ∧ Q ≥ 1/2 forces P ≥ 1/2, and nothing bounds P above.
        result = tools.probability_bounds(
            "P('k2')", [{"formula": "P('k2') ∧ Q('John Doe')", "lower": "1/2"}])
        assert (result["lower"], result["upper"]) == ("1/2", "1")
