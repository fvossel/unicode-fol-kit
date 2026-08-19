"""An operator glyph is never an identifier character.

``Ⓞ`` (CIRCLED LATIN CAPITAL LETTER O) is the deontic Obligatory operator, and
Unicode also says ``"Ⓞ".isupper()`` is True. Since 0.23.0 that test is exactly
how this kit decides "this character opens a PREDICATE", so up to 0.23.1 the
string ``ⓄP`` had two readings at once -- ``Obligatory(P)``, and the atom whose
predicate is named ``ⓄP`` -- and nothing in the kit chose between them on
purpose. Asked for every derivation (``ambiguity="explicit"``), lark reported
the node as ambiguous; asked for one, its Earley parser happened to return the
operator reading, while a table-driven lexer returns the other. Seven glyphs
were in that state: Ⓒ Ⓕ Ⓖ Ⓝ Ⓞ Ⓟ Ⓤ.

The rule now, and the reason this file exists: a glyph that is a registered
operator ANYWHERE is not an identifier character ANYWHERE -- the same rule λ
and μ have had since the identifier classes were widened. The carve-out is
deliberately a list of symbols the grammar spends, not a whole Unicode block:
Ⓐ and the Roman numerals are not operators and stay writable.

The first two tests are derived from the LIVE operator registry rather than
from a copy of the glyph list, so registering a new letter-like operator fails
here instead of quietly becoming a name.
"""

import re

import pytest

from lark import Lark

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol import _identifiers
from unicode_fol_kit.fol._fol_nodes import OPERATORS, build_grammar
from unicode_fol_kit.fol.msflparser import (
    _allow_single_letter_function_calls, _GRAMMARS_DIR, _REGISTRY_MODE)


def _identifier_patterns():
    return {name: re.compile(getattr(_identifiers, name + "_pattern")())
            for name in ("predicate", "name", "constant", "variable", "sort")}


def _single_char_operator_symbols():
    """Every registered operator whose symbol is one character."""
    return sorted({spec.unicode for spec in OPERATORS.values()
                   if len(spec.unicode) == 1 and spec.unicode.strip()})


def test_no_single_character_operator_can_open_an_identifier():
    """The invariant, checked against the registry rather than a glyph list.

    Both forms are tried: the glyph alone (a one-character name) and the glyph
    followed by a letter (the ``ⓄP`` shape that actually bit).
    """
    patterns = _identifier_patterns()
    offenders = []
    for symbol in _single_char_operator_symbols():
        for terminal, pattern in patterns.items():
            if pattern.fullmatch(symbol) or pattern.fullmatch(symbol + "x"):
                offenders.append((symbol, hex(ord(symbol)), terminal))
    assert not offenders, (
        "these operator symbols can still open an identifier, so a formula "
        f"using them has two readings: {offenders}")


def test_the_probe_finds_operators_at_all():
    """Guard against the test above passing because the registry looks empty
    or the symbols were filtered out by the length rule."""
    symbols = _single_char_operator_symbols()
    assert len(symbols) >= 15, symbols
    for expected in ["¬", "∧", "∨", "→", "Ⓒ", "Ⓞ", "Ⓤ"]:
        assert expected in symbols, (expected, symbols)


@pytest.mark.parametrize("glyph, codepoint", [
    ("Ⓒ", 0x24B8), ("Ⓕ", 0x24BB), ("Ⓖ", 0x24BC), ("Ⓝ", 0x24C3),
    ("Ⓞ", 0x24C4), ("Ⓟ", 0x24C5), ("Ⓤ", 0x24CA),
])
def test_each_carved_glyph_is_gone_from_every_letter_class(glyph, codepoint):
    assert ord(glyph) == codepoint
    assert (codepoint, codepoint) in _identifiers._EXCLUDED_RANGES
    for cls in (_identifiers.uppercase_class(), _identifiers.lowercase_class(),
                _identifiers.combining_class()):
        assert glyph not in cls, (glyph, cls[:60])


# --- the carve-out must not take innocent bystanders ------------------------

@pytest.mark.parametrize("text, predicate", [
    ("Ⓐ(x)", "Ⓐ"),          # CIRCLED LATIN CAPITAL LETTER A — not an operator
    ("Ⓑ(x)", "Ⓑ"),
    ("Ⓩ(x)", "Ⓩ"),
    ("Ⅳ(x)", "Ⅳ"),          # ROMAN NUMERAL FOUR — isupper(), not isalpha()
])
def test_circled_and_numeral_non_operators_stay_writable(text, predicate):
    """The carve-out is seven symbols, not the enclosed-alphanumerics block."""
    parsed = MSFLParser().parse(text)
    assert parsed.predicate == predicate


# --- the ambiguity is actually gone -----------------------------------------

MODAL_SHAPES = ["ⓄP", "ⓅP", "ⒼP", "ⒻP", "ⓃP", "ⓄⓄP", "¬ⓄP", "∀x ⓄP(x)"]


def test_the_modal_prefix_shapes_have_exactly_one_derivation():
    """``ambiguity="explicit"`` makes lark report every derivation it found.
    Before the carve-out, each of these produced an ``_ambig`` node."""
    grammar = _allow_single_letter_function_calls(
        build_grammar(_REGISTRY_MODE["modal"]))
    explicit = Lark(grammar, parser="earley", ambiguity="explicit",
                    import_paths=[str(_GRAMMARS_DIR)], propagate_positions=True)
    ambiguous = []
    for text in MODAL_SHAPES:
        tree = explicit.parse(text)
        if any(getattr(n, "data", None) == "_ambig" for n in tree.iter_subtrees()):
            ambiguous.append(text)
    assert not ambiguous, f"still more than one derivation: {ambiguous}"


def test_the_ambiguity_probe_can_still_see_an_ambiguity():
    """Proof the check above is not vacuous: a deliberately ambiguous grammar
    does produce an ``_ambig`` node under the same settings."""
    ambiguous_grammar = """
        start: ab
        ab: A B | AB
        A: "a"
        B: "b"
        AB: "ab"
    """
    explicit = Lark(ambiguous_grammar, parser="earley", ambiguity="explicit")
    tree = explicit.parse("ab")
    assert any(getattr(n, "data", None) == "_ambig" for n in tree.iter_subtrees())


# --- multi-character operators need no carve-out, and must keep working -----

@pytest.mark.parametrize("text, head", [
    ("K_alice(P(x))", "KNOWS"),
    ("B_bob(P(x))", "BELIEVES"),
])
def test_underscore_operators_win_by_length_not_by_carve_out(text, head):
    """``K_`` opens with an ordinary capital K, which obviously cannot be
    carved out of the letter classes -- and does not need to be. The KNOWS
    terminal covers the whole ``K_alice``, so longest-match settles it with no
    ambiguity. This is why the carve-out is restricted to SINGLE-character
    symbols; widening it would make ``K`` an illegal predicate name.
    """
    parser = MSFLParser(modal=True).parser
    tokens = [t for t in parser.parse(text).scan_values(lambda v: True)]
    assert any(t.type == head for t in tokens), [t.type for t in tokens]
    assert MSFLParser().parse("K(x)").predicate == "K"
