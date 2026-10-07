"""A constant of any name has a text: the quoted constant, and the printer that writes it.

``'k2'``, ``'Alice'``, ``'G-910'``, ``'John Doe'`` are constants; the text between the quotes
is the name, exactly. The printer writes a constant bare when the bare word reads back as that
very constant and in quotes otherwise, so the text of a formula reads back as the formula for
every constant that has a text.

Every expected value below is worked out by hand from the definition (a name is bare when it is
one whole CONSTANT or NAME token; a quote and a backslash inside quotes are written ``\\'`` and
``\\\\``) and written as a literal. The two checks that secure the printer run against the real
parsers of every dialect, and each has a control that shows it can fail:

* every name of a large set, printed and read back, gives the node that was built;
* ``is_bare_constant(name)`` is true exactly when the bare text reads as ``Constant(name)``.

The parsers are built once per module and the names of the set are looked up one by one, so the
whole check takes seconds per dialect.
"""

import functools
import itertools
import random
import re

import pytest

import unicode_logic_kit
from unicode_logic_kit import fol as fol_package
from unicode_logic_kit.fol import _identifiers as ident
from unicode_logic_kit.fol._msfl_nodes import key_text
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.naming import NamingError, ParsingError
from unicode_logic_kit.fol.nodes import (
    And, Announce, Application, Atom, Box, Constant, Function, Implies, Knows, Lambda,
    LambdaVar, Nominal, Not, Number, PredicateTerm, Quantifier, SortedConstant, Variable,
)
from unicode_logic_kit.fol.spans import UNKNOWN

BS = chr(92)       # a backslash, spelled out so that no escape has to be read twice
QUOTE = chr(39)    # a single quote


# ---------------------------------------------------------------------------
# The dialects: the ten of api.parse_any and the combined modes
# ---------------------------------------------------------------------------

UNSORTED = {
    "fol": {},
    "modal": {"modal": True},
    "second_order": {"second_order": True},
    "third_order": {"third_order": True},
    "dependence": {"dependence": True},
    "fl": {"fuzzy": True},
    "linear": {"linear": True},
    "lambek": {"lambek": True},
    "third_order+modal": {"third_order": True, "modal": True},
}
SORTED = {
    "msfol": {"many_sorted": True},
    "msfl": {"many_sorted": True, "fuzzy": True},
    "modal+many_sorted": {"modal": True, "many_sorted": True},
    "second_order+many_sorted": {"second_order": True, "many_sorted": True},
}


@functools.lru_cache(maxsize=None)
def parser(label):
    """One parser per dialect for the whole module."""
    return MSFLParser(**{**UNSORTED, **SORTED}[label])


def reads(label, text):
    """What ``text`` reads as in the dialect, or the exception that refuses it."""
    try:
        return parser(label).parse(text)
    except Exception as exc:  # a refusal is the answer being checked here
        return exc


def refused(label, text):
    return isinstance(reads(label, text), (NamingError, ParsingError))


P = lambda *terms: Atom("P", list(terms))  # noqa: E731


# ---------------------------------------------------------------------------
# Hand-made tables
# ---------------------------------------------------------------------------

#: names whose bare text reads back as the constant: one whole NAME or CONSTANT token
BARE_NAMES = (
    "ab", "aB", "a_b", "cc", "alpha", "1a", "2008SummerOlympics", "świątek", "北京",
    "true", "in", "mu", "lambda", "c__a", "cc_a", "ab_", "a1b", "dani_Shapiro", "k_a",
    "1e5", "0x1F", "c_a", "c_k2", "c_ab", "c_1", "c_12", "α", "θ", "αβ",
    "c_a_b", "c_a_", "c_ab_c", "c_1_a", "c_a1_b", "c_a__b", "c_new_york", "socrates",
)

#: names whose bare text reads as something else or as nothing: a variable, a predicate, a
#: number, an operator, no term at all
QUOTED_NAMES = (
    "a", "x1", "k2", "é", "北", "ß",
    "λ", "μ", "ς", "Δ", "c_", "c_1_", "α1", "αa", "cα", "c_α", "a_1", "1_a", "x_", "x_1",
    "_x", "x²", "ⓐ", "a b", "C++",
    "Alice", "G910", "K_a", "X", "Ab", "B_a", "Ⓐ", "Ⅻ",
    "1", "12", "1.5", "-3", "007",
    "a-b", "G-910", "_sk0", "1,2-diacyl", "John Doe",
)

#: names with a quote or a backslash, and the text that reads back as them (a quote is
#: written as a backslash and a quote, a backslash as two backslashes)
ESCAPES = (
    ("it's", r"'it\'s'"),
    ("a" + BS + "b", r"'a\\b'"),
    (QUOTE, r"'\''"),
    (BS, r"'\\'"),
    (BS + QUOTE, r"'\\\''"),
    (QUOTE + QUOTE, r"'\'\''"),
    ("a" + QUOTE + "b" + QUOTE + "c", r"'a\'b\'c'"),
    (BS + BS, r"'\\\\'"),
)


# ---------------------------------------------------------------------------
# The names of the securing checks
# ---------------------------------------------------------------------------

_PAIR_ALPHABET = ["a", "B", "c", "_", "1", QUOTE, BS, " ", "-", "θ", "λ", "(", ","]
_TRIPLE_ALPHABET = ["a", "B", "c", "_", "1", QUOTE, " ", "θ", "-"]
_WIDE_ALPHABET = (
    list("abcxkyzABKX_120") + [QUOTE, BS, " ", "-", "+", ".", ",", "(", ")", ":", "θ", "α", "λ",
                               "μ", "é", "ś", "北", "Ⓐ", "²", "ⓐ", "Ⅻ", "~", "&", "|", "$",
                               '"', "@", "/", "*", "<", ">", "=", "[", "]", "{", "}", "∀", "¬",
                               "∧", "→", "⊤"])
_PIECES = ["c_", "c_", "a", "b", "k", "B", "1", "_", "θ", "é", "ś", "x", "ab", "Alice", "2"]


@functools.lru_cache(maxsize=None)
def name_set():
    """Every sample of the tables, all strings of two characters over a small alphabet that
    mixes the classes, all of three over a smaller one, and seeded random strings of up to
    eight characters over a wide alphabet and over word-like pieces."""
    names = set(BARE_NAMES) | set(QUOTED_NAMES) | {name for name, _ in ESCAPES}
    names |= {"e" + chr(0x301), "e" + chr(0x301) + "e", "a" + chr(0x301) + "b"}
    names |= {x + y for x in _PAIR_ALPHABET for y in _PAIR_ALPHABET} | set(_PAIR_ALPHABET)
    names |= {"".join(t) for t in itertools.product(_TRIPLE_ALPHABET, repeat=3)}
    rng = random.Random(20261007)
    for _ in range(800):
        names.add("".join(rng.choice(_WIDE_ALPHABET) for _ in range(rng.randint(1, 8))))
    for _ in range(800):
        names.add("".join(rng.choice(_PIECES) for _ in range(rng.randint(1, 4))))
    return tuple(sorted(names))


def unreadable(render, names, label):
    """The names for which the text ``render(name)`` does not read back, in the dialect, as the
    atom ``P`` of the one constant of that name."""
    return [name for name in names
            if reads(label, render(name)) != P(Constant(name))]


def has_no_text(name):
    """Whether a name holds a character that neither spelling can carry: a control character,
    DEL, NEL, a line or paragraph separator, a surrogate."""
    return any(ord(c) < 0x20 or ord(c) in (0x7F, 0x85, 0x2028, 0x2029) or 0xD800 <= ord(c) <= 0xDFFF
               for c in name)


def printed(name):
    """The text of a formula as the kit prints it."""
    return P(Constant(name)).to_unicode_str()


def bare_text_as_0_30_0_printed_it(name):
    """The text the kit printed before the quoted form existed: the name, as it is."""
    return "P(" + name + ")"


# ---------------------------------------------------------------------------
# The syntax: what reads as which constant
# ---------------------------------------------------------------------------

class TestQuotedConstantsAreRead:
    @pytest.mark.parametrize("text, name", [
        ("P('k2')", "k2"),
        ("P('K2')", "K2"),
        ("P('G-910')", "G-910"),
        ("P('C++')", "C++"),
        ("P('John Doe')", "John Doe"),
        ("P('1,2-diacyl')", "1,2-diacyl"),
        ("P('1')", "1"),
        ("P('x')", "x"),
        ("P(' ')", " "),
        ("P('𝔸')", "𝔸"),
        ("P('北')", "北"),
    ])
    def test_a_quoted_name_is_the_constant_of_exactly_that_name(self, text, name):
        assert reads("fol", text) == P(Constant(name))

    def test_a_quoted_name_that_could_be_written_bare_is_the_same_constant(self):
        assert reads("fol", "P('socrates')") == reads("fol", "P(socrates)") == P(Constant("socrates"))
        assert reads("fol", "P('c_k2')") == reads("fol", "P(c_k2)") == P(Constant("c_k2"))

    @pytest.mark.parametrize("name, text", ESCAPES)
    def test_a_quote_and_a_backslash_inside_are_escaped(self, name, text):
        assert reads("fol", "P(" + text + ")") == P(Constant(name))
        assert ident._unquote_constant(text) == name

    def test_in_a_comparison_and_in_arguments_and_in_terms(self):
        assert reads("fol", "'a b' = 'c'") == Atom("=", [Constant("a b"), Constant("c")])
        assert reads("fol", "P('k2', x, 'G-910')") == P(Constant("k2"), Variable("x"), Constant("G-910"))
        assert reads("fol", "P(foo('a b'))") == P(Function("foo", [Constant("a b")]))
        assert reads("fol", "P('a b' + 'c d')") == P(
            Function("+", [Constant("a b"), Constant("c d")]))

    def test_a_quoted_constant_is_neither_the_number_nor_the_variable_of_its_name(self):
        assert reads("fol", "P('1')") != P(Number(1))
        assert reads("fol", "P('x')") != P(Variable("x"))
        bound = reads("fol", "∀x P(x, 'x')")
        assert bound == Quantifier("∀", Variable("x"), P(Variable("x"), Constant("x")))

    @pytest.mark.parametrize("label", sorted(UNSORTED))
    def test_every_unsorted_dialect_reads_it(self, label):
        assert reads(label, "P('k2', 'a b')") == P(Constant("k2"), Constant("a b"))

    def test_a_third_order_dialect_reads_a_quoted_upper_case_name_as_a_constant(self):
        # bare, ``Alice`` is a predicate term there; quoted it is an individual
        assert reads("third_order", "P(Alice)") == P(PredicateTerm("Alice"))
        assert reads("third_order", "P('Alice')") == P(Constant("Alice"))


class TestWhatIsNotAQuotedName:
    """The quote has no other use: every one of these is refused, with the lexer's message."""

    @pytest.mark.parametrize("text", [
        "P('')",                          # no empty name
        "P('a" + BS + "b')",              # no escape but the two
        "P('a" + BS + "n')",
        "P('abc",                         # unterminated
        "P('a" + BS + "')",               # the backslash escapes the closing quote
        "P('a'b)",                        # a letter after the closing quote
        "P('a' 'b')",                     # two constants side by side
        "P(x')",                          # a quote after a variable
        "'foo'(x)",                       # a function head has no quoted form
        "'P'(x)",                         # nor a predicate
        "∀'x' P(x)",                      # nor a variable
    ])
    def test_refused(self, text):
        assert refused("fol", text), text

    @pytest.mark.parametrize("excluded", [
        0x00, 0x09, 0x0A, 0x0D, 0x1F, 0x7F, 0x85, 0x2028, 0x2029, 0xD800, 0xDFFF,
    ])
    def test_no_control_character_and_no_line_separator_and_no_surrogate_inside(self, excluded):
        text = "P('a" + chr(excluded) + "b')"
        assert refused("fol", text), hex(excluded)
        assert refused("modal", text), hex(excluded)

    @pytest.mark.parametrize("above", [0x20, 0x7E, 0xA0, 0x84, 0x86, 0x2027, 0x202A, 0xE000])
    def test_the_characters_next_to_the_excluded_ones_are_allowed(self, above):
        name = "a" + chr(above) + "b"
        assert reads("fol", "P('" + name + "')") == P(Constant(name)), hex(above)

    def test_modal_subscripts_nominals_and_binders_have_no_quoted_form(self):
        assert refused("modal", "K_'a' P")
        assert refused("modal", "@'i' P")
        assert refused("fol", "λ'x'. P(x)")
        assert refused("fol", "∃'x' P(x)")


class TestSortedDialects:
    """A sorted dialect has no bare constant, so its quoted constant carries a sort too."""

    @pytest.mark.parametrize("label", sorted(SORTED))
    def test_a_quoted_constant_with_a_sort_is_a_sorted_constant(self, label):
        assert reads(label, "P('k2':Mountain)") == P(SortedConstant("k2", "Mountain"))
        assert reads(label, "P('G-910':Peak, 'a b':Peak)") == P(
            SortedConstant("G-910", "Peak"), SortedConstant("a b", "Peak"))

    @pytest.mark.parametrize("label", sorted(SORTED))
    def test_without_a_sort_it_stays_an_error(self, label):
        assert refused(label, "P('k2')")
        assert refused(label, "P(socrates)")
        assert refused(label, "P(k2:Mountain)")      # a variable takes no sort

    @pytest.mark.parametrize("label", sorted(SORTED))
    def test_a_bare_name_with_a_sort_reads_as_before(self, label):
        assert reads(label, "P(socrates:Human)") == P(SortedConstant("socrates", "Human"))
        assert reads(label, "P(c_k2:Human)") == P(SortedConstant("c_k2", "Human"))

    @pytest.mark.parametrize("label", sorted(UNSORTED))
    def test_an_unsorted_dialect_has_no_sorted_constant(self, label):
        assert refused(label, "P('k2':Mountain)")


class TestModalFallback:
    """The modal dialect tries its table-driven parser first and falls back to the one that
    weighs every terminal. The quoted constant reads the same in both."""

    TEXT = "¬(p∧q) → P('k2', 'a b')"

    @pytest.mark.parametrize("label", ["modal", "third_order+modal"])
    def test_a_text_that_only_the_fallback_reads(self, label):
        from lark.exceptions import LarkError
        modal = parser(label)
        with pytest.raises(LarkError):
            modal.parser.parse(self.TEXT)             # the control: the first parser refuses it
        read = modal.parse(self.TEXT)
        assert isinstance(read, Implies)
        assert isinstance(read.left, Not)
        assert read.right == P(Constant("k2"), Constant("a b"))

    def test_a_quoted_constant_in_a_modal_formula(self):
        assert reads("modal", "□P('k2') ∧ K_a P('G-910')") == And(
            Box(P(Constant("k2"))), Knows(Constant("a"), P(Constant("G-910"))))


class TestSpans:
    @pytest.mark.parametrize("label", ["fol", "modal", "second_order", "third_order",
                                       "third_order+modal", "dependence", "fl"])
    def test_the_extent_of_a_quoted_constant_includes_its_quotes(self, label):
        text = "P('a b', x) ∧ 'k2' = y"
        read = parser(label).parse_with_spans(text)
        formula, spans = read.formula, read.spans
        # the connective is the conjunction of the dialect (a weak one in the fuzzy dialect)
        assert formula.left == P(Constant("a b"), Variable("x"))
        assert formula.right == Atom("=", [Constant("k2"), Variable("y")])
        first = spans.get((0, 0))      # 'a b' in P(...)
        second = spans.get((1, 0))     # 'k2' in the equation
        assert first.extent is not UNKNOWN and second.extent is not UNKNOWN
        assert (first.extent.start, first.extent.end) == (2, 7)
        assert first.extent.text == "'a b'"
        assert (second.extent.start, second.extent.end) == (14, 18)
        assert second.extent.text == "'k2'"
        # a leaf term is its own head
        assert first.head.text == "'a b'"
        assert second.head.text == "'k2'"

    def test_the_extent_in_a_text_that_only_the_fallback_reads(self):
        text = "¬(p∧q) → P('k2', 'a b')"
        read = parser("modal").parse_with_spans(text)
        assert read.formula.right == P(Constant("k2"), Constant("a b"))
        assert read.spans.get((1, 0)).extent.text == "'k2'"
        assert read.spans.get((1, 1)).extent.text == "'a b'"

    def test_the_spans_of_a_sorted_constant_cover_the_quoted_name_and_the_sort(self):
        text = "P('k2':Mountain)"
        read = parser("msfol").parse_with_spans(text)
        assert read.formula == P(SortedConstant("k2", "Mountain"))
        extent = read.spans.get((0,)).extent
        assert extent.text == "'k2':Mountain"


# ---------------------------------------------------------------------------
# The printer
# ---------------------------------------------------------------------------

class TestConstantText:
    @pytest.mark.parametrize("name", BARE_NAMES)
    def test_a_name_that_reads_back_bare_is_written_as_it_is(self, name):
        assert ident.is_bare_constant(name) is True
        assert ident.constant_text(name) == name

    @pytest.mark.parametrize("name", QUOTED_NAMES)
    def test_any_other_name_is_written_in_quotes(self, name):
        assert ident.is_bare_constant(name) is False
        assert ident.constant_text(name) == QUOTE + name + QUOTE

    @pytest.mark.parametrize("name, text", ESCAPES)
    def test_a_quote_and_a_backslash_are_escaped(self, name, text):
        assert ident.is_bare_constant(name) is False
        assert ident.constant_text(name) == text

    def test_the_samples_of_the_contract(self):
        for name in ("socrates", "c_k2", "θ", "2008SummerOlympics", "świątek"):
            assert ident.constant_text(name) == name
        quoted = {"a": "'a'", "k2": "'k2'", "Alice": "'Alice'", "1": "'1'", "-3": "'-3'",
                  "G-910": "'G-910'", "C++": "'C++'", "a b": "'a b'", "_sk0": "'_sk0'",
                  "λ": "'λ'", "x_1": "'x_1'"}
        for name, text in quoted.items():
            assert ident.constant_text(name) == text

    def test_a_letter_with_a_combining_mark_is_quoted_unless_a_second_letter_follows(self):
        # e + COMBINING ACUTE: one letter and a mark, which VARIABLE does not take and NAME
        # needs a second letter for
        one_letter = "e" + chr(0x301)
        assert ident.is_bare_constant(one_letter) is False
        assert ident.constant_text(one_letter) == QUOTE + one_letter + QUOTE
        two_letters = "e" + chr(0x301) + "e"
        assert ident.is_bare_constant(two_letters) is True

    @pytest.mark.parametrize("name", ["", "a" + chr(0) + "b", "a" + chr(10) + "b", "a" + chr(9),
                                      "a" + chr(0x7F), "a" + chr(0x85), "a" + chr(0x2028),
                                      "a" + chr(0x2029), "a" + chr(0xD800), chr(0x1F)])
    def test_a_name_without_a_text_is_refused_naming_the_constant(self, name):
        assert ident.is_bare_constant(name) is False
        with pytest.raises(ValueError) as info:
            ident.constant_text(name)
        assert repr(name) in str(info.value)
        with pytest.raises(ValueError, match=re.escape(repr(name))):
            P(Constant(name)).to_unicode_str()
        with pytest.raises(ValueError, match=re.escape(repr(name))):
            P(SortedConstant(name, "Human")).to_unicode_str()

    @pytest.mark.parametrize("name", [5, None, 1.5, b"ab", ("a",)])
    def test_a_name_that_is_not_a_string_is_a_type_error_that_says_so(self, name):
        assert ident.is_bare_constant(name) is False
        with pytest.raises(TypeError, match="must be a string"):
            ident.constant_text(name)
        with pytest.raises(TypeError, match="must be a string"):
            P(Constant(name)).to_unicode_str()


class TestIsVariableName:
    @pytest.mark.parametrize("text", ["x", "y12", "a", "k2", "é", "北", "ß", "z0"])
    def test_one_letter_and_digits(self, text):
        assert ident.is_variable_name(text) is True

    @pytest.mark.parametrize("text", ["", "xy", "x_1", "x_", "X", "Alice", "1", "12", "λ", "μ", "α",
                                      "x²", "c_k2", "a b", "x'", "e" + chr(0x301)])
    def test_nothing_else(self, text):
        assert ident.is_variable_name(text) is False

    @pytest.mark.parametrize("text", [None, 1, b"x", ("x",)])
    def test_something_that_is_not_a_string_is_no_variable_name(self, text):
        assert ident.is_variable_name(text) is False


class TestOtherNamesKeepPrintingAsTheyDo:
    def test_variables_lambda_variables_and_predicate_terms(self):
        assert P(Variable("k2")).to_unicode_str() == "P(k2)"
        assert Lambda(LambdaVar("x"), P(LambdaVar("x"), Constant("k2"))).to_unicode_str() \
            == "λx. P(x, 'k2')"
        assert P(PredicateTerm("Alice")).to_unicode_str() == "P(Alice)"

    def test_heads_of_functions_and_of_applications(self):
        assert P(Function("foo", [])).to_unicode_str() == "P(foo())"
        assert P(Function("G-910", [Variable("x")])).to_unicode_str() == "P(G-910(x))"
        assert P(Function("foo", [Constant("a b")])).to_unicode_str() == "P(foo('a b'))"
        assert P(Application(Constant("Alice"), Constant("k2"))).to_unicode_str() \
            == "P(Alice('k2'))"

    def test_modal_subscripts_and_nominals(self):
        assert Knows(Constant("Alice"), Atom("P", [])).to_unicode_str() == "K_Alice P"
        assert Knows(Constant("a"), P(Constant("k2"))).to_unicode_str() == "K_a P('k2')"
        assert Nominal("Alice").to_unicode_str() == "Alice"

    def test_numbers(self):
        assert P(Number(1), Constant("1")).to_unicode_str() == "P(1, '1')"


class TestSortedConstantText:
    def test_the_name_has_the_text_of_a_constant_and_the_sort_follows(self):
        assert P(SortedConstant("socrates", "Human")).to_unicode_str() == "P(socrates:Human)"
        assert P(SortedConstant("k2", "Mountain")).to_unicode_str() == "P('k2':Mountain)"
        assert P(SortedConstant("it's", "Thing")).to_unicode_str() == r"P('it\'s':Thing)"


class TestTheTextOfAFormula:
    def test_it_reads_back_with_the_quotes(self):
        formula = Implies(P(Constant("k2"), Variable("x")),
                          Atom("=", [Constant("a b"), Constant("Alice")]))
        assert formula.to_unicode_str() == "P('k2', x) → 'a b' = 'Alice'"
        assert reads("fol", formula.to_unicode_str()) == formula

    def test_a_constant_that_is_written_like_a_variable_is_told_apart_from_it(self):
        formula = Quantifier("∀", Variable("x"), P(Variable("x"), Constant("x")))
        assert formula.to_unicode_str() == "∀x P(x, 'x')"
        assert reads("fol", formula.to_unicode_str()) == formula


# ---------------------------------------------------------------------------
# The check that secures the printer
# ---------------------------------------------------------------------------

class TestThePrintedTextReadsBack:
    """For a large set of names: ``P`` of the constant, printed, read back in a dialect, is the
    node that was built. Names that need no quotes and names that do, escapes included."""

    def test_the_set_is_large_and_holds_every_sample_of_the_tables(self):
        names = set(name_set())
        assert len(names) > 1500
        assert set(BARE_NAMES) | set(QUOTED_NAMES) <= names
        assert {name for name, _ in ESCAPES} <= names
        # every name of the set has a text (the names that have none are refused elsewhere)
        assert not any(has_no_text(n) for n in names)

    @pytest.mark.parametrize("label", sorted(UNSORTED))
    def test_unsorted_dialects(self, label):
        assert unreadable(printed, name_set(), label) == []

    @pytest.mark.parametrize("label", sorted(SORTED))
    def test_sorted_dialects(self, label):
        sort = "Human"
        failures = [
            name for name in name_set()
            if reads(label, P(SortedConstant(name, sort)).to_unicode_str())
            != P(SortedConstant(name, sort))]
        assert failures == []

    def test_control_the_text_of_0_30_0_does_not_read_back(self):
        """The check can fail: the text the kit printed before the quoted form existed, ``P(k2)``,
        reads as a variable, ``P(Alice)`` as nothing in the first-order dialect, and so on."""
        failures = unreadable(bare_text_as_0_30_0_printed_it, name_set(), "fol")
        for name in ("k2", "a", "Alice", "G-910", "C++", "a b", "1", "-3", "_sk0", "λ", "x_1"):
            assert name in failures, name
        assert reads("fol", "P(k2)") == P(Variable("k2"))
        assert reads("fol", "P(k2)") != P(Constant("k2"))
        for name in BARE_NAMES:
            assert name not in failures, name

    def test_control_the_third_order_dialect_reads_the_old_text_of_alice_as_another_node(self):
        assert reads("third_order", "P(Alice)") != P(Constant("Alice"))
        assert "Alice" in unreadable(bare_text_as_0_30_0_printed_it, ["Alice"], "third_order")
        assert unreadable(printed, ["Alice"], "third_order") == []


class TestBareMeansOneWholeToken:
    """``is_bare_constant(name)`` is true exactly when ``P(name)`` reads as ``P`` of ``Constant(name)``
    in the dialect: the lexer's first match, not "some dialect accepts it"."""

    @staticmethod
    def disagreements(is_bare, label):
        read = parser(label).parse
        out = []
        for name in name_set():
            try:
                reads_as_constant = read("P(" + name + ")") == P(Constant(name))
            except Exception:  # a refusal means "does not read as the constant"
                reads_as_constant = False
            if reads_as_constant != is_bare(name):
                out.append(name)
        return out

    @pytest.mark.parametrize("label", sorted(UNSORTED))
    def test_the_converse_holds_in_every_unsorted_dialect(self, label):
        assert self.disagreements(ident.is_bare_constant, label) == []

    def test_control_a_rule_that_looks_at_one_pattern_only_disagrees(self):
        """Greek names are CONSTANT tokens that NAME does not accept: a rule that asked NAME alone
        would call ``θ`` quoted, and the converse check says it is not."""
        name_only = lambda n: ident._compiled("name").fullmatch(n) is not None  # noqa: E731
        wrong = self.disagreements(name_only, "fol")
        assert "θ" in wrong and "αβ" in wrong
        assert "socrates" not in wrong

    def test_the_c_words_that_go_on_after_a_second_underscore_are_bare_and_read(self):
        """``c_a_b`` is one NAME token, not ``c_a`` followed by ``_b``: CONSTANT matches whole
        words only, so every dialect reads these words as the constant of that name."""
        for word in ("c_a_b", "c_a_", "c_ab_c", "c_1_a", "c_a1_b", "c_a__b", "c__a", "cc_a"):
            assert ident.is_bare_constant(word) is True, word
            for label in sorted(UNSORTED):
                assert reads(label, "P(" + word + ")") == P(Constant(word)), (word, label)

    def test_the_words_c_and_c_one_underscore_stay_unreadable(self):
        for word in ("c_", "c_1_"):
            assert ident.is_bare_constant(word) is False
            assert refused("fol", "P(" + word + ")")


# ---------------------------------------------------------------------------
# The text of a formula and the key of an atom
# ---------------------------------------------------------------------------

class TestKeyText:
    def formula(self):
        return And(P(Constant("a"), Constant("Alice")),
                   Atom("Q", [SortedConstant("k2", "Mountain"), Constant("socrates")]))

    def test_the_key_writes_every_constant_by_its_name_as_0_30_0_did(self):
        assert key_text(self.formula()) == "P(a, Alice) ∧ Q(k2:Mountain, socrates)"

    def test_the_text_of_the_formula_quotes_the_constants_that_need_it(self):
        assert self.formula().to_unicode_str() == "P('a', 'Alice') ∧ Q('k2':Mountain, socrates)"

    def test_for_constants_that_are_all_bare_the_two_are_the_same_string(self):
        node = Implies(P(Constant("socrates"), Variable("x")), Atom("Q", [Constant("c_k2"), Number(2)]))
        assert key_text(node) == node.to_unicode_str() == "P(socrates, x) → Q(c_k2, 2)"

    def test_the_key_is_the_same_rendering_through_the_other_node_modules(self):
        node = Announce(P(Constant("k2")), Atom("Q", [Constant("k3")]))
        assert node.to_unicode_str() == "[P('k2')!]Q('k3')"
        assert key_text(node) == "[P(k2)!]Q(k3)"
        modal = Box(Knows(Constant("a"), P(Constant("1"))))
        assert modal.to_unicode_str() == "□K_a P('1')"
        assert key_text(modal) == "□K_a P(1)"

    def test_the_key_of_a_name_that_has_no_text_is_still_the_name(self):
        assert key_text(P(Constant(""))) == "P()"
        assert key_text(P(Constant("a" + chr(10) + "b"))) == "P(a" + chr(10) + "b)"

    def test_the_key_keeps_the_names_that_collide_with_a_variable_and_a_number(self):
        # the refusal of two different atoms with one key relies on this
        assert key_text(P(Constant("x"))) == key_text(P(Variable("x"))) == "P(x)"
        assert key_text(P(Constant("1"))) == key_text(P(Number(1))) == "P(1)"

    def test_the_setting_is_restored_after_a_call(self):
        atom = P(Constant("k2"))
        assert atom.to_unicode_str() == "P('k2')"
        assert key_text(atom) == "P(k2)"
        assert atom.to_unicode_str() == "P('k2')"

    def test_the_setting_is_restored_when_the_rendering_raises(self):
        class Raises:
            def to_unicode_str(self):
                raise RuntimeError("no text")

        with pytest.raises(RuntimeError):
            key_text(Raises())
        assert P(Constant("k2")).to_unicode_str() == "P('k2')"

    def test_a_call_inside_a_rendering_does_not_disturb_it(self):
        atom = P(Constant("k2"))

        class Nested:
            def to_unicode_str(self):
                before = atom.to_unicode_str()
                inner = key_text(atom)
                after = atom.to_unicode_str()
                return "|".join([before, inner, after])

        # a rendering for a person: the nested key is bare, the text around it still quoted
        assert Nested().to_unicode_str() == "P('k2')|P(k2)|P('k2')"
        # a rendering for a key: bare throughout, and still bare after the nested call
        assert key_text(Nested()) == "P(k2)|P(k2)|P(k2)"
        # and the default is back
        assert atom.to_unicode_str() == "P('k2')"


class TestAtomKeys:
    """``atom_key`` and ``AtomKeys.key`` use the key text; see tests/test_atom_keys.py for the rest."""

    def test_the_key_of_an_atom_is_typed_the_0_30_0_way(self):
        from unicode_logic_kit.fol._atom_keys import AtomKeys, atom_key
        assert atom_key(P(Constant("a"))) == "P(a)"
        assert atom_key(P(SortedConstant("k2", "Mountain"))) == "P(k2)"
        assert AtomKeys("route").key(P(Constant("Alice"))) == "P(Alice)"

    def test_the_variable_and_the_constant_of_one_name_are_still_refused(self):
        from unicode_logic_kit.fol._atom_keys import AtomKeys
        keys = AtomKeys("the route")
        keys.key(P(Constant("x")))
        with pytest.raises(NotImplementedError, match="have one key"):
            keys.key(P(Variable("x")))


# ---------------------------------------------------------------------------
# Messages
# ---------------------------------------------------------------------------

class TestMessages:
    def test_a_character_after_the_closing_quote_is_named_with_the_shape_of_the_terminal(self):
        with pytest.raises(NamingError) as info:
            parser("fol").parse("P('a'b)")
        message = str(info.value)
        assert message.startswith(
            "SYNTAX_ERROR: Invalid quoted constant ''a'' - unexpected character 'b' at position 6. "
            "Expected pattern: a single quote, then the name, then a single quote; inside, a quote "
            "is written ")
        assert message.endswith(BS + QUOTE + " and a backslash " + BS + BS)
        assert "QUOTED_NAME" not in message

    def test_an_unterminated_quote_gives_the_message_it_always_gave(self):
        with pytest.raises(NamingError) as info:
            parser("fol").parse("P('abc")
        assert str(info.value) == (
            "SYNTAX_ERROR: Unexpected character ''' at position 3 after opening parenthesis '('")

    def test_the_list_of_what_may_stand_there_names_the_quoted_constant_in_words(self):
        with pytest.raises(ParsingError) as info:
            parser("fol").parse("P(")
        message = str(info.value)
        assert "quoted constant" in message
        assert "QUOTED_NAME" not in message

    def test_a_quoted_constant_without_its_sort_in_a_sorted_dialect_is_refused_in_words(self):
        with pytest.raises(NamingError) as info:
            parser("msfol").parse("P('k2')")
        assert "QUOTED_NAME" not in str(info.value)
        assert "quoted constant" in str(info.value)

    def test_the_message_for_a_missing_sort_says_that_the_sort_is_missing(self):
        # P('k2') is seven characters, and the one that cannot stand there is the last
        with pytest.raises(NamingError) as info:
            parser("msfol").parse("P('k2')")
        assert str(info.value) == (
            "SYNTAX_ERROR: Unexpected character ')' at position 7 after the quoted constant "
            "'k2'. In a many-sorted formula a constant carries its sort: write 'k2':Sort")
        # ... and with the sort the same text reads
        assert parser("msfol").parse("P('k2':Mountain)") == P(SortedConstant("k2", "Mountain"))

    @pytest.mark.parametrize("label, text, position", [
        ("fol", "'Alice'(x)", 8),
        ("fol", "'1,2-diacyl'(x)", 13),
        ("fol", "P('f'(x))", 6),
        ("msfol", "'k2'(x)", 5),
    ])
    def test_a_quoted_name_with_arguments_is_told_that_it_is_a_constant(
            self, label, text, position):
        with pytest.raises(NamingError) as info:
            parser(label).parse(text)
        quoted = text[text.index(QUOTE):text.index("(", text.index(QUOTE))]
        assert str(info.value) == (
            f"SYNTAX_ERROR: Unexpected character '(' at position {position} after the quoted "
            f"constant {quoted}. A name in quotes is a constant and takes no arguments; a "
            f"predicate or function name has no quoted form")

    def test_the_good_name_is_not_called_invalid(self):
        for label, text in (("fol", "'Alice'(x)"), ("msfol", "P('k2')")):
            with pytest.raises(NamingError) as info:
                parser(label).parse(text)
            assert "Invalid" not in str(info.value)


class TestAStrayApostropheCanSwallowText:
    """The limit of the quoted form, documented: the first quote opens a name that runs to the
    next quote, wherever that is."""

    def test_two_atoms_with_one_apostrophe_each_are_one_atom_of_one_odd_constant(self):
        assert reads("fol", "P('x) ∧ Q(y')") == P(Constant("x) ∧ Q(y"))


# ---------------------------------------------------------------------------
# The public names
# ---------------------------------------------------------------------------

class TestPublicNames:
    @pytest.mark.parametrize("name", ["is_variable_name", "is_bare_constant", "constant_text"])
    def test_exported_from_the_package_and_from_fol(self, name):
        assert name in unicode_logic_kit.__all__
        assert name in fol_package.__all__
        assert getattr(unicode_logic_kit, name) is getattr(ident, name)
        assert getattr(fol_package, name) is getattr(ident, name)
