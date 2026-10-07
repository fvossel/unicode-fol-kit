"""The MiniZinc backend writes a model for any symbol name, and every name is a legal identifier.

A constant may be written in quotes (``'a b'``, ``'G-910'``, ``'C++'``), a TPTP file may quote a
predicate or a function, and a hand-built node may carry any text. The backend used to write
``k_`` followed by the transliterated name, which is no MiniZinc identifier for a name that holds a
space, a hyphen, a quote or a ``+``: MiniZinc then rejected the model and the answer was
``error`` / ``infra``, which says the tool is broken. Nothing is broken; the name had no carrier.

The rule (see the module docstring of ``atp.minizinc_backend``): a name that is made of ASCII
letters, digits and underscores once the kit has folded it to ASCII keeps ``<role>_<name>``, the
identifier it always had; any other name is written ``<role>x_<code>`` where the code keeps ASCII
letters and digits and writes every other character as an underscore, the code point in lower-case
hexadecimal, and an underscore. The role letter is ``p`` (predicate), ``f`` (function), ``k``
(constant) or ``v`` (bound variable).

The identifiers below are worked out by hand from that rule:

=========  ======================================================================
name       identifier
=========  ======================================================================
``a b``    ``a``, the space is U+0020 so ``_20_``, ``b``: ``kx_a_20_b``
``a_b``    made of letters and an underscore, so plain: ``k_a_b``
``G-910``  the hyphen is U+002D so ``_2d_``: ``kx_G_2d_910``
``G910``   plain: ``k_G910``
``it's``   the quote is U+0027 so ``_27_``: ``kx_it_27_s``
``C++``    the plus is U+002B twice: ``kx_C_2b__2b_``
``C``      plain: ``k_C``
``Alice``  plain: ``k_Alice``
``alice``  plain: ``k_alice`` (MiniZinc tells ``Alice`` and ``alice`` apart)
``θ``      folds to ``theta``, so plain: ``k_theta`` (as it always was)
``1``      plain: ``k_1`` (the role prefix is a letter, so a digit may follow it)
=========  ======================================================================
"""
import pathlib
import re

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import minizinc_backend as mb
from unicode_logic_kit.atp.clingo_backend import ClingoBackend, clingo_available
from unicode_logic_kit.atp.finite_domain import FiniteDomainProblem
from unicode_logic_kit.atp.minizinc_backend import MinizincBackend, minizinc_available, to_minizinc
from unicode_logic_kit.atp.protocol import ERROR, REFUTED, UNKNOWN
from unicode_logic_kit.fol._fol_nodes import constant_name_to_ascii
from unicode_logic_kit.fol.nodes import (
    And, Atom, Cardinality, Constant, Contrast, Count, Function, Iff, Implies, Not, Number, Or,
    Quantifier, Variable, Xor,
)
from unicode_logic_kit.semantics import evaluate_in_structure, structure_from_dict

FIXDIR = pathlib.Path(__file__).parent / "fixtures" / "minizinc"

live = pytest.mark.skipif(not minizinc_available(), reason="no minizinc binary reachable")
live_clingo = pytest.mark.skipif(not clingo_available(), reason="clingo is not installed")

# MiniZinc's identifier rule (the MiniZinc specification, "Identifiers"): an ASCII letter
# followed by ASCII letters, digits and underscores, and not a reserved word.
MZN_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*")

# The reserved words of MiniZinc (the specification's list, checked against MiniZinc 2.8.4, which
# rejects every one of them as an identifier). ``op`` and ``lp`` are kept in as well: some
# versions of the specification reserve them, and none of our identifiers may be one.
MZN_KEYWORDS = frozenset("""
    ann annotation any array bool case constraint default diff div else elseif endif enum false
    float function if in include int intersect let list lp maximize minimize mod not of op opt
    output par predicate record satisfy set solve string subset superset symdiff test then true
    tuple type union var where xor
""".split())


def _is_mzn_identifier(text):
    return MZN_IDENTIFIER.fullmatch(text) is not None and text not in MZN_KEYWORDS


# The rule this module had before names of any shape were written: the role prefix, then the
# transliterated name, whatever characters that holds.
def _old_constant_rule(name):
    return "k_" + constant_name_to_ascii(name)


ELEVEN_NAMES = [
    ("a b", "kx_a_20_b"),
    ("a_b", "k_a_b"),
    ("G-910", "kx_G_2d_910"),
    ("G910", "k_G910"),
    ("it's", "kx_it_27_s"),
    ("C++", "kx_C_2b__2b_"),
    ("C", "k_C"),
    ("Alice", "k_Alice"),
    ("alice", "k_alice"),
    ("θ", "k_theta"),
    ("1", "k_1"),
]


# =============================================================================
# The identifiers (offline, derived by hand)
# =============================================================================

@pytest.mark.parametrize("name, expected", ELEVEN_NAMES, ids=[row[0] for row in ELEVEN_NAMES])
def test_a_constant_is_written_under_the_identifier_worked_out_by_hand(name, expected):
    assert mb._mzn_const_name(name) == expected


def test_every_one_of_the_eleven_identifiers_is_legal_and_no_two_are_alike():
    identifiers = [mb._mzn_const_name(name) for name, _ in ELEVEN_NAMES]
    for name, identifier in zip((n for n, _ in ELEVEN_NAMES), identifiers):
        assert _is_mzn_identifier(identifier), (name, identifier)
    assert len(set(identifiers)) == len(identifiers) == 11


def test_the_old_rule_gave_no_identifier_for_the_four_names_that_were_refused():
    # 'a b', 'G-910', "it's" and 'C++' are the names of the four problems that ended in
    # error / infra: the old rule wrote ``k_a b``, ``k_G-910``, ``k_it's`` and ``k_C++``.
    for name, old in [("a b", "k_a b"), ("G-910", "k_G-910"), ("it's", "k_it's"), ("C++", "k_C++")]:
        assert _old_constant_rule(name) == old
        assert not _is_mzn_identifier(old)
        # ... and the rule now in force gives one.
        assert _is_mzn_identifier(mb._mzn_const_name(name))
    # The names of the twin side of those problems were legal before and stay as they were.
    for name in ["a_b", "G910", "its", "C"]:
        assert _is_mzn_identifier(_old_constant_rule(name))
        assert mb._mzn_const_name(name) == _old_constant_rule(name)


def test_a_predicate_a_function_and_a_variable_get_the_same_two_forms():
    # A TPTP file may quote a predicate or a function, and a hand-built variable may be named
    # anything: ``'foo bar'``, ``'f-g'``, ``x-1``.
    assert mb._mzn_pred_name("Foo bar") == "px_Foo_20_bar"        # space is U+0020
    assert mb._mzn_pred_name("F-g") == "px_F_2d_g"                # hyphen is U+002D
    assert mb._mzn_pred_name("It's") == "px_It_27_s"              # quote is U+0027
    assert mb._mzn_pred_name("P") == "p_P"                        # plain, as always
    assert mb._mzn_func_name("f-g") == "fx_f_2d_g"
    assert mb._mzn_func_name("f_g") == "f_f_g"                    # plain
    assert mb._mzn_var_name("x-1") == "vx_x_2d_1"
    assert mb._mzn_var_name("x_1") == "v_x_1"                     # plain, as always
    assert mb._mzn_var_name("ą") == "v_u0105"                     # plain after folding, as always
    for identifier in ["px_Foo_20_bar", "px_F_2d_g", "px_It_27_s", "fx_f_2d_g", "vx_x_2d_1"]:
        assert _is_mzn_identifier(identifier)


def test_an_underscore_of_a_name_that_is_written_in_the_escaped_form_is_escaped_too():
    # 'a_b c': the underscore is U+005F, so ``_5f_``; the space is ``_20_``.
    assert mb._mzn_const_name("a_b c") == "kx_a_5f_b_20_c"
    # 'a b_c' is a different name and gets a different identifier.
    assert mb._mzn_const_name("a b_c") == "kx_a_20_b_5f_c"
    # A newline is U+000A: ``_a_``. A name that looks like an escape is plain or escaped as itself.
    assert mb._mzn_const_name("a\nb") == "kx_a_a_b"
    assert mb._mzn_const_name("a_a_b") == "k_a_a_b"
    # A code point above U+FFFF has more hexadecimal digits: U+1F600 is ``_1f600_``. (A name that
    # holds no ASCII character outside letters, digits and underscore is plain even when it holds
    # non-ASCII letters: the folding turns U+1F600 into ``u1f600``, so ``a`` followed by it is
    # ``k_au1f600``; the escaped form writes the original character.)
    assert mb._mzn_const_name("a\U0001F600") == "k_au1f600"
    assert mb._mzn_const_name("a b\U0001F600") == "kx_a_20_b_1f600_"
    assert mb._mzn_const_name("θ b") == "kx__3b8__20_b"
    # The empty name keeps the identifier it always had; ``k_`` is a legal identifier.
    assert mb._mzn_const_name("") == "k_"
    assert _is_mzn_identifier("k_")


def test_the_escaped_form_never_meets_the_plain_form_nor_the_names_the_model_declares():
    # Plain identifiers have an underscore second, escaped ones an ``x``; the model's own names
    # (``n``, ``DOM``, ``i0``, ``i1`` ...) hold no underscore, and no keyword holds one either.
    own = {"n", "DOM", "i0", "i1", "i2", "i3"}
    assert not any("_" in word for word in MZN_KEYWORDS | own)
    for name, identifier in [(n, mb._mzn_const_name(n)) for n, _ in ELEVEN_NAMES]:
        if identifier.startswith("kx_"):
            assert identifier[1] == "x" and identifier[2] == "_"
            assert identifier not in own and identifier not in MZN_KEYWORDS
        else:
            assert identifier.startswith("k_")


# =============================================================================
# Injective and legal for a large set of names (offline, with controls)
# =============================================================================

# Ten characters of different kinds: a letter, a digit, an underscore, a space, a hyphen, a Greek
# letter that folds to a word, a quote, a letter that folds to a codepoint escape, a line break
# and a character of the ASCII punctuation. No ``t``, ``h``, ``e``, ``u`` or ``0`` among them, so
# no two names of the set can fold to one plain identifier (the folding of ``θ`` is ``theta``
# and that of ``é`` is ``u00e9``).
ALPHABET = ["a", "1", "_", " ", "-", "θ", "'", "é", "\n", "~"]


def _all_names(max_length):
    names = [""]
    layer = [""]
    for _ in range(max_length):
        layer = [prefix + ch for prefix in layer for ch in ALPHABET]
        names.extend(layer)
    return names


def _decode(code):
    """Read an escaped code back: groups ``_<hex>_`` are characters, everything else stands for itself."""
    assert re.fullmatch(r"(?:[A-Za-z0-9]|_[0-9a-f]+_)*", code), code
    return re.sub(r"_([0-9a-f]+)_", lambda m: chr(int(m.group(1), 16)), code)


def test_every_name_of_length_up_to_three_gets_a_legal_identifier_and_no_two_share_one():
    names = _all_names(3)
    assert len(names) == 1 + 10 + 100 + 1000
    identifiers = {name: mb._mzn_const_name(name) for name in names}
    for name, identifier in identifiers.items():
        assert _is_mzn_identifier(identifier), (name, identifier)
    assert len(set(identifiers.values())) == len(names)


def test_the_escaped_code_reads_back_as_the_name():
    for name in _all_names(3):
        identifier = mb._mzn_const_name(name)
        if identifier.startswith("kx_"):
            assert _decode(identifier[3:]) == name
        else:
            assert identifier.startswith("k_")


def test_the_same_holds_for_a_predicate_a_function_and_a_variable():
    names = _all_names(2)
    for namer, role in [(mb._mzn_pred_name, "p"), (mb._mzn_func_name, "f"), (mb._mzn_var_name, "v")]:
        identifiers = [namer(name) for name in names]
        assert all(_is_mzn_identifier(identifier) for identifier in identifiers)
        assert all(identifier[0] == role for identifier in identifiers)
        assert len(set(identifiers)) == len(names)


def test_control_the_old_rule_fails_the_legality_check_on_the_same_names():
    # The legality check can fail: the old rule gives no identifier for every name that holds one
    # of the five characters the alphabet has that are no part of an identifier (space, hyphen,
    # quote, line break, tilde). Of the 10 names of length one that is 5, of the 100 of length two
    # it is 100 - 5 * 5 = 75 (only the other five characters, a, 1, _, θ and é, make a legal one).
    names = _all_names(2)
    illegal = [name for name in names if not _is_mzn_identifier(_old_constant_rule(name))]
    assert len(illegal) == 5 + 75
    assert "a " in illegal and "a-" in illegal and "θ'" in illegal
    assert all(_is_mzn_identifier(mb._mzn_const_name(name)) for name in illegal)


def test_control_a_lossy_escape_fails_the_distinctness_check_on_the_same_names():
    # The distinctness check can fail too: an escape that turns every other character into one
    # underscore writes ``a b``, ``a-b`` and ``a~b`` alike.
    def lossy(name):
        return "kx_" + re.sub(r"[^A-Za-z0-9]", "_", name)

    names = _all_names(3)
    assert len({lossy(name) for name in names}) < len(names)
    assert lossy("a b") == lossy("a-b") == lossy("a~b")
    assert len({mb._mzn_const_name(name) for name in names}) == len(names)


# =============================================================================
# The model text (offline)
# =============================================================================

def _fixture_problems():
    """The problem of each recorded model under ``tests/fixtures/minizinc``, built by hand."""
    x, y, v, w = Variable("x"), Variable("y"), Variable("v"), Variable("w")
    a, b = Constant("a"), Constant("b")
    loves = Quantifier("forall", x, Quantifier("exists", y, Atom("Loves", (x, y))))
    return {
        "forall_exists_loves_size2.mzn": FiniteDomainProblem((loves,), 2),
        "refutation_goal_not_loves_size2.mzn": FiniteDomainProblem((Not(loves),), 2),
        "counting_fragment_size3.mzn": FiniteDomainProblem((
            Count("ge", Number(2), x, Atom("P", (x,))),
            Atom(">", (Cardinality(v, Atom("Q", (v,))), Cardinality(w, Atom("R", (w,))))),
        ), 3),
        "connectives_and_alldifferent_size3.mzn": FiniteDomainProblem((
            Atom("≠", (a, b)),
            Xor(Atom("P", (a,)), Atom("Q", (a,))),
            Iff(Atom("P", (a,)), Atom("Q", (b,))),
            And(Atom("Rain", ()), Or(Atom("P", (a,)), Not(Atom("Q", (b,))))),
            Implies(Atom("Rain", ()), Atom("P", (a,))),
        ), 3, all_different=True),
        "contrast_verification_gap_size2.mzn": FiniteDomainProblem(
            (Contrast(Atom("P", (a,)), Atom("Q", (b,))),), 2),
        "function_verification_gap_size2.mzn": FiniteDomainProblem(
            (Quantifier("exists", x, Atom("=", (Function("f", (x,)), x))),), 2),
    }


def test_every_recorded_model_is_still_written_byte_for_byte():
    problems = _fixture_problems()
    # No recorded model is left out of this check.
    assert sorted(path.name for path in FIXDIR.glob("*.mzn")) == sorted(problems)
    for name, problem in problems.items():
        # Read as text, so that a checkout that turned the line ends into CRLF compares equal.
        recorded = (FIXDIR / name).read_text(encoding="utf-8")
        assert to_minizinc(problem) == recorded, name


MODEL_OF_A_QUOTED_CONSTANT = r"""% Generated by unicode_logic_kit.atp.minizinc_backend.to_minizinc --
% bounded refutation search, |D| = 2, 1 sentence(s) to satisfy simultaneously.
% REFUTATION-ONLY: SATISFIABLE here witnesses a finite countermodel;
% UNSATISFIABLE proves nothing about validity at a larger domain size.

int: n = 2;
set of int: DOM = 0..n-1;

array[DOM] of var bool: p_P;

var DOM: kx_a_20_b;

constraint p_P[kx_a_20_b]; % sentence 1

solve satisfy;

output [
  "UFK-SOLUTION-BEGIN\n",
  "UFK p_P 1 " ++ show([p_P[i0] | i0 in DOM]) ++ "\n",
  "UFK kx_a_20_b 0 " ++ show(kx_a_20_b) ++ "\n",
  "UFK-SOLUTION-END\n"
];

"""

MODEL_OF_A_QUOTED_PREDICATE_FUNCTION_AND_VARIABLE = r"""% Generated by unicode_logic_kit.atp.minizinc_backend.to_minizinc --
% bounded refutation search, |D| = 2, 1 sentence(s) to satisfy simultaneously.
% REFUTATION-ONLY: SATISFIABLE here witnesses a finite countermodel;
% UNSATISFIABLE proves nothing about validity at a larger domain size.

int: n = 2;
set of int: DOM = 0..n-1;

array[DOM] of var bool: px_Foo_20_bar;

array[DOM] of var DOM: fx_f_2d_g;

constraint exists(vx_x_2d_1 in DOM)(px_Foo_20_bar[fx_f_2d_g[vx_x_2d_1]]); % sentence 1

solve satisfy;

output [
  "UFK-SOLUTION-BEGIN\n",
  "UFK px_Foo_20_bar 1 " ++ show([px_Foo_20_bar[i0] | i0 in DOM]) ++ "\n",
  "UFK fx_f_2d_g 1 " ++ show([fx_f_2d_g[i0] | i0 in DOM]) ++ "\n",
  "UFK-SOLUTION-END\n"
];

"""


def test_the_model_of_a_quoted_constant_is_written_with_its_escaped_identifier():
    problem = FiniteDomainProblem((Atom("P", (Constant("a b"),)),), 2)
    assert to_minizinc(problem) == MODEL_OF_A_QUOTED_CONSTANT


def test_the_model_of_a_quoted_predicate_function_and_variable_is_written_with_escaped_identifiers():
    x = Variable("x-1")
    sentence = Quantifier("exists", x, Atom("Foo bar", (Function("f-g", (x,)),)))
    assert to_minizinc(FiniteDomainProblem((sentence,), 2)) == MODEL_OF_A_QUOTED_PREDICATE_FUNCTION_AND_VARIABLE


def test_two_constants_that_differ_only_in_a_character_are_two_declarations():
    # ``a b`` and ``a_b`` are two constants: the first is escaped, the second plain, and
    # ``sorted`` puts the space before the underscore.
    problem = FiniteDomainProblem((Atom("=", (Constant("a b"), Constant("a_b"))),), 2)
    text = to_minizinc(problem)
    assert "var DOM: kx_a_20_b;\nvar DOM: k_a_b;\n" in text
    assert "constraint (kx_a_20_b = k_a_b); % sentence 1" in text


def test_every_identifier_in_a_model_of_odd_names_is_legal():
    x, y = Variable("x-1"), Variable("y 2")
    sentences = (
        Quantifier("forall", x, Quantifier("exists", y, Atom("R s", (x, y, Constant("C++"))))),
        Atom("=", (Function("g h", (Constant("a b"), Constant("G-910"))), Constant("it's"))),
        Atom("Rain!", ()),
    )
    text = to_minizinc(FiniteDomainProblem(sentences, 2, all_different=True))
    assert text.isascii()
    declared = re.findall(r"^(?:array\[[A-Z, ]+\] of var \w+|var \w+): (\w+);$", text, re.M)
    assert sorted(declared) == sorted([
        "px_R_20_s", "px_Rain_21_", "fx_g_20_h", "kx_C_2b__2b_", "kx_a_20_b", "kx_G_2d_910", "kx_it_27_s",
    ])
    assert all(_is_mzn_identifier(identifier) for identifier in declared)
    assert "constraint alldifferent([kx_C_2b__2b_, kx_G_2d_910, kx_a_20_b, kx_it_27_s]);" in text
    assert "forall(vx_x_2d_1 in DOM)(exists(vx_y_20_2 in DOM)(px_R_20_s[vx_x_2d_1, vx_y_20_2, kx_C_2b__2b_]))" in text


# =============================================================================
# What is still refused, and how (offline)
# =============================================================================

def test_two_names_that_fold_to_one_plain_identifier_are_still_refused_by_name():
    # ``theta`` and ``θ`` both fold to ``theta``: both keep the identifier they always had, so
    # the model cannot hold both, and it says so instead of writing one symbol for two.
    problem = FiniteDomainProblem((Atom("=", (Constant("theta"), Constant("θ"))),), 2)
    with pytest.raises(NotImplementedError) as info:
        to_minizinc(problem)
    assert "'theta'" in str(info.value) and "'θ'" in str(info.value) and "k_theta" in str(info.value)


def test_two_bound_variables_that_fold_to_one_identifier_are_refused_by_name():
    # The folding of ``ą`` is ``u0105``, which is also the name of another variable: an inner
    # binder would capture the outer one's occurrences if both were written ``v_u0105``.
    first, second = Variable("ą"), Variable("u0105")
    assert mb._mzn_var_name("ą") == mb._mzn_var_name("u0105") == "v_u0105"
    sentence = Quantifier("forall", first, Quantifier("forall", second, Atom("R", (first, second))))
    with pytest.raises(NotImplementedError) as info:
        to_minizinc(FiniteDomainProblem((sentence,), 2))
    message = str(info.value)
    assert "variable" in message and "'ą'" in message and "'u0105'" in message and "v_u0105" in message


def test_a_binder_alone_counts_as_a_variable_name_for_the_guard():
    # ``∀ą ∀u0105 P(a)`` does not use either variable, but both binders are written. The names are
    # taken in sorted order, and ``u`` (U+0075) sorts before ``ą`` (U+0105).
    sentence = Quantifier("forall", Variable("ą"), Quantifier("forall", Variable("u0105"), Atom("P", (Constant("a"),))))
    with pytest.raises(NotImplementedError, match="'u0105' and 'ą'"):
        to_minizinc(FiniteDomainProblem((sentence,), 2))


def test_decide_answers_unsupported_and_names_the_two_symbols_for_such_a_pair():
    goal = Atom("=", (Constant("theta"), Constant("θ")))
    verdict = MinizincBackend().decide(goal, [], minizinc_path="unused: refused before a model is run")
    assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
    assert "'theta'" in verdict.detail and "'θ'" in verdict.detail


def test_a_name_that_is_not_a_string_is_refused_by_name_not_reported_as_a_tool_failure():
    verdict = MinizincBackend().decide(
        Atom("P", (Constant(5),)), [], minizinc_path="unused: refused before a model is run")
    assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
    assert "constant name 5" in verdict.detail and "not a string" in verdict.detail
    for namer in (mb._mzn_pred_name, mb._mzn_func_name, mb._mzn_var_name):
        with pytest.raises(NotImplementedError, match="not a string"):
            namer(5)


# =============================================================================
# decide() with escaped names, the solver stubbed (offline)
# =============================================================================

def _size_of(model_path):
    match = re.search(r"int: n = (\d+);", pathlib.Path(model_path).read_text(encoding="utf-8"))
    assert match is not None
    return int(match.group(1))


def test_the_solution_of_a_model_with_escaped_names_is_read_back_under_the_kit_names(monkeypatch):
    # ``P('a b') ⊢ P(a_b)``: the sentences are ``P('a b')`` and ``¬P(a_b)``. Size 1 has no model
    # (one element would be in P and not in P); at size 2 the stub answers the model
    # P = {0}, 'a b' = 0, a_b = 1, written under the two identifiers the model declares.
    seen = []

    def fake_run(model_path, binary, solver, time_limit_ms):
        text = pathlib.Path(model_path).read_text(encoding="utf-8")
        seen.append(text)
        if _size_of(model_path) == 1:
            return "=====UNSATISFIABLE=====\n", "", False
        assert "var DOM: kx_a_20_b;" in text and "var DOM: k_a_b;" in text
        return (
            "UFK-SOLUTION-BEGIN\n"
            "UFK p_P 1 [true, false]\n"
            "UFK kx_a_20_b 0 0\n"
            "UFK k_a_b 0 1\n"
            "UFK-SOLUTION-END\n"
            "----------\n"
        ), "", False

    monkeypatch.setattr(mb, "_run_minizinc", fake_run)
    goal, premise = Atom("P", (Constant("a_b"),)), Atom("P", (Constant("a b"),))
    verdict = MinizincBackend().decide(goal, [premise], max_size=2, minizinc_path="FAKE")
    assert len(seen) == 2
    assert verdict.status == REFUTED, verdict
    structure = structure_from_dict(verdict.countermodel["data"])
    assert dict(structure.constants) == {"a b": "0", "a_b": "1"}
    assert evaluate_in_structure(premise, structure) is True
    assert evaluate_in_structure(goal, structure) is False


# =============================================================================
# Live: the four problems that ended in error / infra, and their valid twin
# =============================================================================

def _read(text):
    result = api.parse_any(text, hint="fol")
    assert result.ok, result
    return result.formula


# premise, conclusion. None of the four is valid: in each the two constants may be two elements,
# P holding of the first and not of the second.
INVALID_PROBLEMS = [
    ("P('a b')", "P(a_b)"),
    ("P('G-910')", "P('G910')"),
    ("P('it\\'s')", "P(its)"),
    ("P('C++')", "P('C')"),
]
# The names of the constants of each problem, as the countermodel reports them.
NAMES_OF_THE_PROBLEMS = [("a b", "a_b"), ("G-910", "G910"), ("it's", "its"), ("C++", "C")]


@live
@pytest.mark.parametrize("premise, conclusion", INVALID_PROBLEMS, ids=[p + " |- " + c for p, c in INVALID_PROBLEMS])
def test_live_a_problem_with_a_quoted_constant_is_refuted_not_reported_as_infra(premise, conclusion):
    verdict = api.prove(_read(conclusion), [_read(premise)], backends=["minizinc"], timeout=60000)
    assert verdict.status == REFUTED, verdict
    assert verdict.status != ERROR


@live
@pytest.mark.parametrize("problem, names", list(zip(INVALID_PROBLEMS, NAMES_OF_THE_PROBLEMS)),
                         ids=[p + " |- " + c for p, c in INVALID_PROBLEMS])
def test_live_the_countermodel_gives_the_two_constants_two_elements_and_checks(problem, names):
    premise, conclusion = _read(problem[0]), _read(problem[1])
    verdict = MinizincBackend().decide(conclusion, [premise], timeout=60000)
    assert verdict.status == REFUTED, verdict
    structure = structure_from_dict(verdict.countermodel["data"])
    first, second = names
    # By hand: the premise puts the first constant's element in P, the negated conclusion keeps
    # the second one's out of it, so the two denote different elements.
    assert structure.constants[first] != structure.constants[second]
    assert evaluate_in_structure(premise, structure) is True
    assert evaluate_in_structure(conclusion, structure) is False


@live
def test_live_the_twin_with_the_quoted_constant_is_not_refuted():
    # ``P('a b'), ∀x (P(x) → Q(x)) ⊢ Q('a b')`` is valid: the backend only refutes, so it must
    # say it found no countermodel up to the bound (unknown / bound_hit), never refuted.
    premises = [_read("P('a b')"), _read("∀x (P(x) → Q(x))")]
    goal = _read("Q('a b')")
    verdict = MinizincBackend().decide(goal, premises, timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict
    through_the_api = api.prove(goal, premises, backends=["minizinc"], timeout=60000)
    assert through_the_api.status not in (REFUTED, ERROR), through_the_api
    assert through_the_api.status == UNKNOWN


@live
def test_live_a_quoted_constant_is_the_same_constant_each_time_it_is_written():
    # ``P('a b') ⊢ P('a b')`` is valid, and it was an error / infra before.
    verdict = MinizincBackend().decide(_read("P('a b')"), [_read("P('a b')")], timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict


@live
def test_live_a_quoted_predicate_and_a_quoted_function_are_written_too():
    a, b = Constant("a"), Constant("b")
    foo_bar_a, foo_bar_b = Atom("Foo bar", (a,)), Atom("Foo bar", (b,))
    # Valid: the same atom twice.
    verdict = MinizincBackend().decide(foo_bar_a, [foo_bar_a], timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict
    # Not valid: the relation may hold of ``a`` and not of ``b``.
    verdict = MinizincBackend().decide(foo_bar_b, [foo_bar_a], timeout=60000)
    assert verdict.status == REFUTED, verdict
    # Two functions that differ in one hyphen: ``p(f-g(a)) ⊢ p(f_g(a))`` is not valid, the same
    # function on both sides is.
    p = lambda f: Atom("P", (Function(f, (a,)),))
    verdict = MinizincBackend().decide(p("f_g"), [p("f-g")], timeout=60000)
    assert verdict.status == REFUTED, verdict
    verdict = MinizincBackend().decide(p("f-g"), [p("f-g")], timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict


@live
def test_live_a_bound_variable_with_an_odd_name_is_written():
    x = Variable("x-1")
    # ``∀x-1 P(x-1) ⊢ P(a)`` is valid; ``⊢ ∀x-1 P(x-1)`` is not.
    universal = Quantifier("forall", x, Atom("P", (x,)))
    verdict = MinizincBackend().decide(Atom("P", (Constant("a"),)), [universal], timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict
    verdict = MinizincBackend().decide(universal, [], timeout=60000)
    assert verdict.status == REFUTED, verdict


@live
def test_live_control_with_the_old_rule_the_four_problems_end_in_error_infra(monkeypatch):
    # The control that shows the live checks above can fail: write the constants as the old
    # rule did and MiniZinc rejects the model, which the backend can only report as infra.
    monkeypatch.setattr(mb, "_mzn_const_name", _old_constant_rule)
    for premise, conclusion in INVALID_PROBLEMS:
        verdict = MinizincBackend().decide(_read(conclusion), [_read(premise)], timeout=60000)
        assert (verdict.status, verdict.reason) == (ERROR, "infra"), (premise, conclusion, verdict)


# =============================================================================
# The ASP backend names every symbol by number, so these names never reach its program
# =============================================================================

@live_clingo
@pytest.mark.parametrize("premise, conclusion", INVALID_PROBLEMS, ids=[p + " |- " + c for p, c in INVALID_PROBLEMS])
def test_clingo_refutes_the_same_four_problems(premise, conclusion):
    verdict = ClingoBackend().decide(_read(conclusion), [_read(premise)], timeout=60000)
    assert verdict.status == REFUTED, verdict


@live_clingo
def test_clingo_does_not_refute_the_valid_twin():
    premises = [_read("P('a b')"), _read("∀x (P(x) → Q(x))")]
    verdict = ClingoBackend().decide(_read("Q('a b')"), premises, timeout=60000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "bound_hit"), verdict
