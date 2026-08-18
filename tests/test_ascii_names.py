"""Tests for the shared ASCII-identifier sanitisation primitives
(atp._ascii_names), used by atp._tptp_problem, atp.prover9_entailment, and
atp.cvc5_backend to fix the digit-leading/non-ASCII export gaps the widened
FOL-parser identifier grammar opened up.

Each expectation below is hand-checked against the function's own documented
contract, not just "whatever it happens to return".
"""

from unicode_fol_kit.atp._ascii_names import ascii_safe_base, reserve_rendered, reverse_map_text


class TestAsciiSafeBase:
    def test_ascii_name_passes_through_unchanged(self):
        # Pure ASCII, not digit-leading: constant_name_to_ascii is a no-op
        # and no digit-prefix is needed.
        assert ascii_safe_base("socrates", "n") == "socrates"

    def test_digit_leading_ascii_name_gets_prefixed(self):
        # constant_name_to_ascii("2008SummerOlympics") == the name itself
        # (pure ASCII), so the ONLY thing left to fix is the digit-leading
        # first character.
        assert ascii_safe_base("2008SummerOlympics", "n") == "n2008SummerOlympics"

    def test_greek_letter_transliterates_by_name(self):
        # theta -> reversible spelled-out name (unicode_fol_kit.fol._fol_nodes
        # ._GREEK_CONST_TO_ASCII); always letter-initial, so no digit-prefix
        # is ever needed for a Greek-only name.
        assert ascii_safe_base("θ", "n") == "theta"

    def test_non_greek_non_ascii_uses_reversible_uxxxx_escape(self):
        # 'ś' (U+015B) is not a Greek letter -> reversible u015b escape, one
        # 4-hex-digit block per non-ASCII codepoint.
        assert ascii_safe_base("ś", "n") == "u015b"

    def test_mixed_ascii_and_non_ascii_escapes_only_the_non_ascii_part(self):
        # 'ś' (U+015B) and 'ą' (U+0105) each become their own u-escape; the
        # ASCII letters 'w', 'i', 't', 'e', 'k' pass through raw in between —
        # verified against świątek's actual decomposition used throughout
        # this module's docstrings.
        assert ascii_safe_base("świątek", "n") == "u015bwiu0105tek"

    def test_uxxxx_escape_result_is_never_digit_leading(self):
        # A digit-leading raw name that is ALSO non-ASCII cannot arise from
        # the widened grammar (digit-leading NAME tokens are ASCII digits
        # only), but the function must still be safe if handed one: the
        # escape always starts with a letter ('t' for Greek, 'u' for uXXXX),
        # so no digit-prefix step ever fires on a transliterated result.
        assert ascii_safe_base("ś2008", "n")[0].isalpha()

    def test_prefix_only_used_when_needed(self):
        assert not ascii_safe_base("alice", "n").startswith("n")
        assert ascii_safe_base("2alice", "n").startswith("n")


class TestReserveRendered:
    def test_first_candidate_wins_when_free(self):
        used = set()
        assert reserve_rendered("foo", used) == "foo"
        assert used == {"foo"}

    def test_collision_gets_numeric_suffix(self):
        used = {"foo"}
        assert reserve_rendered("foo", used) == "foo2"
        assert used == {"foo", "foo2"}

    def test_suffix_increments_past_multiple_collisions(self):
        used = {"foo", "foo2", "foo3"}
        assert reserve_rendered("foo", used) == "foo4"

    def test_reserves_the_rendered_form_not_the_raw_candidate(self):
        # render folds the first char lower-case (TPTP-fold style); the raw
        # candidate returned is "Foo2" (case preserved) but "foo2" — the
        # RENDERED form — is what gets checked/reserved, mirroring how a
        # predicate token and its TPTP text differ.
        used = {"foo"}
        render = lambda s: s[:1].lower() + s[1:]
        token = reserve_rendered("Foo", used, render=render)
        assert token == "Foo2"
        assert used == {"foo", "foo2"}

    def test_two_distinct_bases_never_collide_with_each_other(self):
        used = set()
        a = reserve_rendered("foo", used)
        b = reserve_rendered("bar", used)
        assert {a, b} == {"foo", "bar"}


class TestReverseMapText:
    def test_empty_dicts_leave_text_unchanged(self):
        text = "fof(premise_1, axiom, p(a))."
        assert reverse_map_text(text, {}) == text

    def test_empty_text_returns_empty(self):
        assert reverse_map_text("", {"foo": "bar"}) == ""

    def test_replaces_whole_token_only(self):
        text = "lostTo(x,u015bwiu0105tek)"
        out = reverse_map_text(text, {"u015bwiu0105tek": "świątek"})
        assert out == "lostTo(x,świątek)"

    def test_does_not_partially_rewrite_a_substring_of_another_identifier(self):
        # "foo" is a mapped token, but "foobar" (a DIFFERENT, unmapped
        # identifier that happens to contain "foo" as a prefix) must not be
        # partially rewritten — the whole-word boundary is the point.
        out = reverse_map_text("foobar(x)", {"foo": "bar"})
        assert out == "foobar(x)"

    def test_longest_token_wins_when_one_is_a_prefix_of_another(self):
        # Only relevant when BOTH full tokens actually occur as whole words
        # somewhere; here "abc" alone (not "abcdef") is what is present, so
        # only the "abc" -> "X" mapping can fire, and it must not accidentally
        # eat characters belonging to "abcdef" being tried second.
        out = reverse_map_text("abc(1) abcdef(2)", {"abc": "X", "abcdef": "Y"})
        assert out == "X(1) Y(2)"

    def test_multiple_dicts_merge_first_match_wins(self):
        out = reverse_map_text("foo bar", {"foo": "FIRST"}, {"foo": "SECOND", "bar": "BAR"})
        assert out == "FIRST BAR"

    def test_multiple_occurrences_all_replaced(self):
        out = reverse_map_text("p(a,a,a)", {"a": "świątek"})
        assert out == "p(świątek,świątek,świątek)"
