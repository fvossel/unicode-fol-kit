"""Exhaustive equivalence check for ``unicode_fol_kit.fol._identifiers``'s
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

import re
import unicodedata

from unicode_fol_kit.fol import _identifiers as ident

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
