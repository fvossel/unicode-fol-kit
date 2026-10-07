"""Exhaustive equivalence check for ``unicode_logic_kit.fol._identifiers``'s
lookahead-based letter atoms against the module's own, fully-enumerated
ground truth.

``_identifiers.py`` used to build every terminal pattern by splicing the
explicit ``upper``/``lower``/``combining`` class bodies in directly, several
times per terminal — the single biggest source of the ~190KB
``terminal_block(include_sort=True)`` this repo used to generate (NAME alone
was over 100KB). That module now builds PREDICATE/CONSTANT/NAME/VARIABLE/
SORT from small, fixed-size lookahead atoms instead (see
``_identifiers.py``'s "WHY THE GENERATED PATTERNS ARE SMALL" docstring
section) — ``_letter_atom()`` standing in for "any letter, upper or lower or
caseless, excluding Greek/Coptic/Greek-Extended/OHM SIGN" wherever that
class used to be spelled out, and ``_lowerish_atom()`` standing in for the
term-valued ("lowerish") letter the same way.

That substitution is only safe if the two atoms match EXACTLY the same set
of codepoints the old, fully-enumerated classes did — not "close enough", not
"correct on the corpus this kit happens to test with". This file is that
proof, run over every one of the 0x30000 codepoints from 0x0000 to 0x2FFFF
(``_identifiers._MAX_CODEPOINT``), not a sample: for each codepoint it
directly computes the ground truth from ``str.isalpha()``/``str.isupper()``
and the module's own ``_EXCLUDED_RANGES``, and compares it against what the
compiled regex atoms actually match. Measured at ~0.2s for the full range
(well under the 2s this repo's slow-test convention — see
``pyproject.toml``'s ``isabelle_live``/``hets_live`` markers, both about
external-dependency gating rather than raw duration — would call for a
marker), so it runs as an ordinary test, every time, not opt-in.

NOTE ON THE GROUND TRUTH FOR ``_letter_atom()``: LETTER is the union of
``uppercase_class()`` (``str.isupper()``, no ``isalpha()`` condition) and
``lowercase_class()`` (``str.isalpha() and not str.isupper()``) — i.e.
``str.isalpha() or str.isupper()``, NOT ``str.isalpha()`` alone.
``str.isupper()`` is not a subset of ``str.isalpha()``: Roman numerals
(U+2160-U+216F, category Nl) and circled/squared Latin capitals (e.g.
U+24B6, category So) are ``isupper() == True`` but ``isalpha() == False``,
and a continuation position (PREDICATE/SORT/NAME's own, before the
lookahead rewrite) that used to splice ``uppercase_class()`` directly
accepted them on that basis alone. ``TestLetterAtomRespectsCeiling`` below
additionally checks the one thing the exhaustive scan cannot, by
construction: that codepoints strictly ABOVE ``_MAX_CODEPOINT`` are
rejected, since ``[^\\W\\d_]`` alone has no ceiling of its own.

For good measure this also re-pins the THREE class-body functions that were
NOT touched by the lookahead rewrite (``uppercase_class``, ``lowercase_class``,
``combining_class`` — still literal enumerations, since ``dialect_repair.py``
splices them inside its own ``[...]`` and a lookahead atom cannot go there)
against the same ground truth, so a regression in either half of the module
(the untouched literal classes, or the new lookahead atoms replacing their
repeated use) would show up here.
"""

import itertools
import re
import unicodedata

from unicode_logic_kit.fol import _identifiers as ident

MAX_CODEPOINT = ident._MAX_CODEPOINT  # 0x2FFFF, per the module's own docstring


def _is_excluded(codepoint: int) -> bool:
    """Ground truth for exclusion, computed directly from the module's own
    ``_EXCLUDED_RANGES`` tuple — not a second, hand-copied range list."""
    return any(lo <= codepoint <= hi for lo, hi in ident._EXCLUDED_RANGES)


class TestExhaustiveLetterAtomEquivalence:
    """(D-EQUIV) Over EVERY codepoint 0x0000-0x2FFFF: the new lookahead
    atoms and the old, still-present literal class bodies must pick out
    exactly the sets their docstrings claim — ``str.isalpha()``/
    ``str.isupper()``, each minus the excluded Greek/Coptic/Greek-Extended/
    OHM-SIGN ranges."""

    def test_full_range_equivalence(self):
        letter_re = re.compile(ident._letter_atom())
        lowerish_re = re.compile(ident._lowerish_atom())
        upper_re = re.compile(f"[{ident.uppercase_class()}]")
        lower_re = re.compile(f"[{ident.lowercase_class()}]")
        combining_re = re.compile(f"[{ident.combining_class()}]")

        letter_mismatches = []
        lowerish_mismatches = []
        upper_mismatches = []
        lower_mismatches = []
        combining_mismatches = []

        for codepoint in range(MAX_CODEPOINT + 1):
            ch = chr(codepoint)
            excluded = _is_excluded(codepoint)
            # LETTER is the union of uppercase_class() and lowercase_class()
            # — i.e. str.isupper() OR str.isalpha(), not str.isalpha() alone.
            # str.isupper() is not a subset of str.isalpha(): Roman numerals
            # (U+2160-U+216F) and circled/squared Latin capitals (e.g.
            # U+24B6) are isupper()==True, isalpha()==False, and were always
            # letters as far as uppercase_class() (str.isupper()-based, no
            # isalpha() condition) was concerned.
            is_letter = (ch.isalpha() or ch.isupper()) and not excluded
            is_upper = ch.isupper() and not excluded
            is_lowerish = ch.isalpha() and not ch.isupper() and not excluded
            is_combining = (
                unicodedata.category(ch) in ("Mn", "Mc") and not excluded)

            if bool(letter_re.match(ch)) != is_letter:
                letter_mismatches.append(codepoint)
            if bool(lowerish_re.match(ch)) != is_lowerish:
                lowerish_mismatches.append(codepoint)
            if bool(upper_re.match(ch)) != is_upper:
                upper_mismatches.append(codepoint)
            if bool(lower_re.match(ch)) != is_lowerish:
                lower_mismatches.append(codepoint)
            if bool(combining_re.match(ch)) != is_combining:
                combining_mismatches.append(codepoint)

        # Assert with the offending codepoints in the failure message (a
        # bare "False != True" over 196609 codepoints tells nobody
        # anything) rather than failing on the first mismatch — if this
        # ever regresses, the FULL set of offending codepoints matters for
        # diagnosing whether it's a whole excluded range or one boundary.
        assert not letter_mismatches, (
            f"_letter_atom() disagrees with "
            f"(str.isalpha() or str.isupper())-minus-excluded "
            f"at {len(letter_mismatches)} codepoints, "
            f"e.g. {[hex(c) for c in letter_mismatches[:10]]}")
        assert not lowerish_mismatches, (
            f"_lowerish_atom() disagrees with "
            f"str.isalpha()-and-not-isupper()-minus-excluded at "
            f"{len(lowerish_mismatches)} codepoints, "
            f"e.g. {[hex(c) for c in lowerish_mismatches[:10]]}")
        assert not upper_mismatches, (
            f"uppercase_class() disagrees with str.isupper()-minus-excluded "
            f"at {len(upper_mismatches)} codepoints, "
            f"e.g. {[hex(c) for c in upper_mismatches[:10]]}")
        assert not lower_mismatches, (
            f"lowercase_class() disagrees with "
            f"str.isalpha()-and-not-isupper()-minus-excluded at "
            f"{len(lower_mismatches)} codepoints, "
            f"e.g. {[hex(c) for c in lower_mismatches[:10]]}")
        assert not combining_mismatches, (
            f"combining_class() disagrees with category-Mn/Mc-minus-"
            f"excluded at {len(combining_mismatches)} codepoints, "
            f"e.g. {[hex(c) for c in combining_mismatches[:10]]}")


class TestLetterAtomsAreNotClassBodies:
    """The lookahead atoms open with a group or ``(?!...)`` — splicing one
    inside a caller's own ``[...]`` (the way ``uppercase_class()`` etc. are
    meant to be used) would silently stop meaning "letter" and start
    meaning "one of these literal characters: ( ? ! ...", so this pins that
    they are NOT valid to embed that way, as a guard against ever exposing
    them through the same calling convention as the three class-body
    functions."""

    def test_letter_atom_is_not_a_bracket_safe_body(self):
        assert ident._letter_atom().startswith("(?:")

    def test_lowerish_atom_is_not_a_bracket_safe_body(self):
        assert ident._lowerish_atom().startswith("(?!")


class TestLetterAtomRespectsCeiling:
    """(D-CEILING) ``[^\\W\\d_]`` alone has no ceiling — Python's ``\\w``
    matches any ``str.isalnum()`` codepoint up to U+10FFFF — so without an
    explicit CEILING lookahead the lookahead-based LETTER atom would accept
    letters the fully-enumerated ``upper``/``lower`` classes it stands in
    for never scanned past ``_MAX_CODEPOINT`` (0x2FFFF), breaking this
    module's "differently-spelled pattern for the exact same set of
    strings, never a different one" promise. CJK Unified Ideograph
    Extension G (U+30000-U+3134A, category Lo, ``str.isalpha()`` true) is
    the concrete script that sits just past the ceiling and is exhaustive
    enough here as a sample: the exhaustive scan above already covers
    every codepoint up to the ceiling, so only a handful of over-the-
    ceiling probes are needed to pin the boundary itself."""

    def test_letter_atom_rejects_first_codepoint_past_ceiling(self):
        letter_re = re.compile(ident._letter_atom())
        over = chr(MAX_CODEPOINT + 1)
        assert over.isalpha()  # sanity: it IS a letter, just past the ceiling
        assert not letter_re.match(over)

    def test_letter_atom_rejects_cjk_extension_g(self):
        letter_re = re.compile(ident._letter_atom())
        ch = chr(0x30000)  # CJK Unified Ideograph Extension G, category Lo
        assert ch.isalpha()
        assert not letter_re.match(ch)

    def test_letter_atom_still_accepts_last_codepoint_at_ceiling(self):
        """The ceiling excludes strictly ABOVE ``_MAX_CODEPOINT`` — it must
        not accidentally clip the boundary codepoint itself."""
        letter_re = re.compile(ident._letter_atom())
        ch = chr(MAX_CODEPOINT)
        if ch.isalpha() or ch.isupper():
            assert letter_re.match(ch)


class TestTerminalBlockShrank:
    """A coarse regression guard, not the equivalence proof above: the
    lookahead rewrite's entire point was to stop re-spelling multi-kilobyte
    classes several times per terminal, so ``terminal_block`` should be a
    small fraction of what it was (measured ~192KB before this module's
    lookahead rewrite, ~58KB after, on this interpreter). A generous 100KB
    ceiling here catches a future change that accidentally reintroduces the
    old repeated-enumeration pattern without pinning an exact byte count
    that would make this test brittle against harmless future additions (a
    new mode, an extra terminal)."""

    def test_terminal_block_is_well_under_the_old_size(self):
        size = len(ident.terminal_block(include_sort=True))
        assert size < 100_000, (
            f"terminal_block(include_sort=True) is {size} chars — the "
            "lookahead-based atoms should keep this well under the ~192KB "
            "it was before _identifiers.py stopped repeating class bodies")


class TestConstantMatchesWholeWordsOnly:
    """CONSTANT's ``c_`` form is a lexer terminal that wins over NAME by priority, and the lexer
    takes the first terminal that matches, not the longest. A ``c_`` word that goes on after
    its first run of letters and digits (``c_new_york``) must therefore not be matched in part:
    the pattern ends in a negative lookahead for any character that continues a NAME."""

    CONSTANT = re.compile(ident.constant_pattern())
    NAME = re.compile(ident.name_pattern())

    WHOLE_WORDS = ("c_k2", "c_1", "c_12", "c_alpha", "c_ab", "c_świątek",
                   "α", "θ", "αβ", "ωω")
    DECLINED_WORDS = ("c_a_b", "c_a_", "c_ab_c", "c_1_a", "c_a1_b", "c_a__b", "c_", "c_1_",
                      "c_new_york")

    def test_a_word_is_matched_whole(self):
        for word in self.WHOLE_WORDS:
            assert self.CONSTANT.fullmatch(word), word

    def test_a_word_that_goes_on_is_not_matched_at_all_and_not_in_part(self):
        for word in self.DECLINED_WORDS:
            assert self.CONSTANT.fullmatch(word) is None, word
            assert self.CONSTANT.match(word) is None, word

    def test_a_declined_word_is_a_name_when_it_has_two_letters(self):
        # the NAME terminal reads all of it: the words of the lexer's second choice
        for word in ("c_a_b", "c_a_", "c_ab_c", "c_1_a", "c_a1_b", "c_a__b", "c_new_york"):
            assert self.NAME.fullmatch(word), word
        # one letter only (the c): no NAME either, so the word is no term at all
        for word in ("c_", "c_1_"):
            assert self.NAME.fullmatch(word) is None, word

    def test_a_match_ends_where_no_name_character_follows(self):
        """Over every string of up to five characters of an alphabet whose characters ALL
        continue a NAME (letters, a digit, an underscore, a combining mark), a match of CONSTANT is
        the whole string: there is no character after it that could continue the word."""
        alphabet = ["c", "_", "a", "1", "é", chr(0x301)]
        checked = 0
        for length in range(1, 6):
            for chars in itertools.product(alphabet, repeat=length):
                text = "".join(chars)
                found = self.CONSTANT.match(text)
                if found is not None:
                    assert found.end() == len(text), text
                    checked += 1
        assert checked > 20      # the check had something to check

    def test_control_without_the_lookahead_a_match_stops_inside_the_word(self):
        """The check can fail: the ``c_`` form as it was, without the lookahead, matches the
        part ``c_a`` of ``c_a_b``, which is what made the lexer cut the word short."""
        without_lookahead = re.compile(f"c_{ident._continuation_atom(underscore=False)}+")
        assert without_lookahead.match("c_a_b").group() == "c_a"
        assert without_lookahead.match("c_ab_c").group() == "c_ab"

    def test_the_greek_run_is_unchanged(self):
        # no lookahead on it: a Greek run is taken as far as the Greek letters go
        assert self.CONSTANT.match("αβγ").group() == "αβγ"
        assert self.CONSTANT.match("αa").group() == "α"
        assert self.CONSTANT.match("α1").group() == "α"
        assert self.CONSTANT.match("aα") is None


class TestAsciiCoreOfABareConstant:
    """``is_bare_constant`` decides an ASCII name with a small pattern that needs no scan of the
    Unicode tables. It has to be the CONSTANT or NAME pattern restricted to ASCII."""

    def test_the_core_agrees_with_the_generated_patterns_on_short_strings(self):
        name = re.compile(ident.name_pattern())
        constant = re.compile(ident.constant_pattern())
        checked = 0
        for length in (1, 2, 3):
            for chars in itertools.product("aAcz_09 -'", repeat=length):
                text = "".join(chars)
                expected = bool(name.fullmatch(text) or constant.fullmatch(text))
                assert (ident._ASCII_BARE_CONSTANT.fullmatch(text) is not None) is expected, text
                checked += 1
        for chars in itertools.product("acB_1", repeat=4):
            text = "".join(chars)
            expected = bool(name.fullmatch(text) or constant.fullmatch(text))
            assert (ident._ASCII_BARE_CONSTANT.fullmatch(text) is not None) is expected, text
            checked += 1
        assert checked == 10 + 100 + 1000 + 625

    def test_control_a_core_that_forgets_the_c_form_disagrees(self):
        without_c_form = re.compile(
            r"[a-z][0-9_]*[a-zA-Z][a-zA-Z0-9_]*|[0-9]+[a-zA-Z][a-zA-Z0-9_]*")
        constant = re.compile(ident.constant_pattern())
        assert constant.fullmatch("c_1")                     # a CONSTANT, and no NAME
        assert without_c_form.fullmatch("c_1") is None
        assert ident._ASCII_BARE_CONSTANT.fullmatch("c_1") is not None


class TestQuotedNameTerminal:
    """QUOTED_NAME: a quote, one or more of (an ordinary character, or a backslash and a quote, or
    two backslashes), a quote. The characters no spelling can carry are not ordinary."""

    QUOTED = re.compile(ident.quoted_name_pattern())
    BS = chr(92)

    def test_what_it_matches(self):
        bs = self.BS
        for text in ("'a'", "'k2'", "'a b'", "'G-910'", "'1,2-diacyl'", "'é北'", "'𝔸'",
                     "' '", "'('", "'" + bs + "''", "'" + bs + bs + "'", "'a" + bs + "'b'",
                     "'" + bs + bs + bs + "''"):
            assert self.QUOTED.fullmatch(text), text

    def test_what_it_does_not_match(self):
        bs = self.BS
        for text in ("''", "'", "'a", "a'", "a", "'a'b'", "'a" + bs + "b'", "'a" + bs + "'",
                     "'" + bs + "'", "\"a\"", "'a'" + "'"):
            assert self.QUOTED.fullmatch(text) is None, text

    def test_the_excluded_characters_are_not_ordinary(self):
        for code in (0x00, 0x09, 0x0A, 0x0D, 0x1F, 0x7F, 0x85, 0x2028, 0x2029, 0xD800, 0xDFFF):
            assert self.QUOTED.fullmatch("'a" + chr(code) + "b'") is None, hex(code)

    def test_the_neighbours_of_the_excluded_characters_are_ordinary(self):
        for code in (0x20, 0x7E, 0x80, 0x84, 0x86, 0x9F, 0xA0, 0x2027, 0x202A, 0xE000):
            assert self.QUOTED.fullmatch("'a" + chr(code) + "b'"), hex(code)

    def test_it_is_declared_without_a_priority_in_every_terminal_block(self):
        for include_sort in (False, True):
            lines = ident.terminal_block(include_sort=include_sort).split("\n")
            declared = [line for line in lines if line.startswith("QUOTED_NAME")]
            assert len(declared) == 1
            assert declared[0].startswith("QUOTED_NAME: /")

    def test_no_other_terminal_can_begin_with_a_quote(self):
        quote = chr(39)
        for pattern in (ident.predicate_pattern(), ident.name_pattern(), ident.constant_pattern(),
                        ident.variable_pattern(), ident.sort_pattern()):
            assert re.match(pattern, quote) is None

    def test_it_has_a_description_for_messages(self):
        assert "QUOTED_NAME" in ident.HUMAN_READABLE_PATTERNS
        assert ident.HUMAN_READABLE_PATTERNS["QUOTED_NAME"] == (
            "a single quote, then the name, then a single quote; inside, a quote is written "
            + self.BS + chr(39) + " and a backslash " + self.BS + self.BS)
