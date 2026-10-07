r"""A numeral is ONE constant per VALUE in the Prover9 text, and both programs that read the text
(Prover9 and Mace4) read it as an ordinary constant.

A numeral (a :class:`Number` node) is a constant symbol identified by its value on every route
that was not asked for arithmetic: ``Number(1) == Number(1.0)``, so ``1`` and ``1.0`` are one
constant; two numerals of different value may denote the same element (``⊢ 1 ≠ 2`` is not valid);
``+ - * /`` are uninterpreted function symbols and ``< > ≤ ≥`` uninterpreted predicates.

The Prover9 file writes every numeral as its value in double quotes: ``"1"`` for ``1`` and for
``1.0``, ``"2.5"``, ``"-1"``. Never as bare digits: Mace4, which reads the same formula lists (not
the flags the file sets before them: it stops at ``auto_denials`` and the ``print_*`` flags with
"Flag not recognized"), takes a bare integer for a domain element of its own and all of them for
DISTINCT elements, so ``1 != 2`` would have no countermodel there; a quoted symbol is a plain
constant for Prover9 and for Mace4.

The eleven problems below are decided by hand from that definition. For a valid problem Prover9
finds a proof and Mace4 finds no countermodel; for a problem that is not valid Prover9 finds no
proof and Mace4 finds a countermodel (the universe and the interpretation are in each row).
The live tests run the real programs where there are some and skip, with a reason, where there are
none; the offline tests derive the written text.
"""

import os
import re
import subprocess
import tempfile

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
from unicode_logic_kit.atp.protocol import Prover9Backend, get_backend
from unicode_logic_kit.atp.vampire_entailment import _to_wsl_path
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Number, Variable
from unicode_logic_kit.fol.prover9_input import Prover9ParsingError, parse_prover9, parse_prover9_problem


def _formula(text):
    result = api.parse_any(text)
    assert result.ok, text
    return result.formula


# id, premises, goal, valid?, why (hand-derived from the definition above)
PROBLEMS = [
    ("instance-of-universal", ["∀x P(x)"], "P(1)", True, "an instance of the universal"),
    ("one-and-one-point-zero", ["P(1)"], "P(1.0)", True, "one constant: Number(1) == Number(1.0)"),
    ("distinct-numerals", [], "1 ≠ 2", False, "universe {0}: both numerals denote 0"),
    ("less-than-numerals", [], "1 < 2", False, "< is empty"),
    ("sum-of-numerals", [], "1 + 1 = 2", False, "universe {0, 1}: 1 -> 0, 2 -> 1, + is constantly 0"),
    ("two-numerals-two-elements", ["P(1)", "P(2)"], "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", False, "universe {0}"),
    ("numeral-and-word", ["P(1)"], "P(one)", False, "universe {0, 1}: 1 -> 0, one -> 1, P = {0}"),
    ("commutativity-instance", ["∀x ∀y x + y = y + x"], "1 + 2 = 2 + 1", True, "an instance of the premise"),
    ("order-instance", ["∀x (x < 2 → Q(x))", "1 < 2"], "Q(1)", True, "an instance, then modus ponens"),
    ("decimal-reflexivity", [], "2.5 = 2.5", True, "reflexivity: a decimal numeral must be writable"),
    ("negative-numeral", ["P(-1)"], "∃x P(x)", True, "a negative numeral must be writable"),
]
_IDS = [row[0] for row in PROBLEMS]


# --------------------------------------------------------------------------- #
# The text.
# --------------------------------------------------------------------------- #

def _written(premises, goal):
    text, names = generate_prover9_input_with_mapping([_formula(p) for p in premises], _formula(goal))
    lines = [line.strip() for line in text.splitlines()]
    assumptions = lines[lines.index("formulas(assumptions).") + 1:lines.index("end_of_list.")]
    goals = lines[lines.index("formulas(goals).") + 1:-1]
    return assumptions, goals, names


# What each problem is written as: every numeral is its value in double quotes, everything else
# is what the writer always writes (variables upper-case, infix operators in parentheses).
_TEXT = {
    "instance-of-universal": (["(all X P(X))."], ['P("1").']),
    "one-and-one-point-zero": (['P("1").'], ['P("1").']),
    "distinct-numerals": ([], ['("1" != "2").']),
    "less-than-numerals": ([], ['("1" < "2").']),
    "sum-of-numerals": ([], ['(("1" + "1") = "2").']),
    "two-numerals-two-elements": (['P("1").', 'P("2").'], ["(exists X (exists Y (((X != Y) & P(X)) & P(Y))))."]),
    "numeral-and-word": (['P("1").'], ["P(one)."]),
    "commutativity-instance": (["(all X (all Y ((X + Y) = (Y + X))))."], ['(("1" + "2") = ("2" + "1")).']),
    "order-instance": (['(all X ((X < "2") -> Q(X))).', '("1" < "2").'], ['Q("1").']),
    "decimal-reflexivity": ([], ['("2.5" = "2.5").']),
    "negative-numeral": (['P("-1").'], ["(exists X P(X))."]),
}


@pytest.mark.parametrize("name, premises, goal, valid, why", PROBLEMS, ids=_IDS)
def test_every_numeral_is_written_as_its_value_in_double_quotes(name, premises, goal, valid, why):
    assumptions, goals, _ = _written(premises, goal)
    assert (assumptions, goals) == _TEXT[name]


def test_one_and_one_point_zero_are_written_as_one_symbol_and_recorded_once():
    text, names = generate_prover9_input_with_mapping([Atom("P", [Number(1)])], Atom("P", [Number(1.0)]))
    assert text.count('"1"') == 2 and '"1.0"' not in text
    assert names.numerals == {"1": '"1"'}


@pytest.mark.parametrize("value, written", [
    (1, '"1"'), (1.0, '"1"'), (0, '"0"'), (-0.0, '"0"'), (7.0, '"7"'), (2.5, '"2.5"'),
    (-2.5, '"-2.5"'), (-1, '"-1"'), (0.1, '"0.1"'), (1e-07, '"0.0000001"'),
])
def test_a_numeral_is_the_quoted_text_of_its_value(value, written):
    assert Number(value).to_prover9() == written


def test_numerals_of_equal_value_have_one_text_and_numerals_of_other_values_do_not():
    values = [0, 1, 1.0, 2, 2.0, 2.5, -1, -1.0, 0.5, 0.25, 3, 10, 100.0, -0.0]
    for first in values:
        for second in values:
            same_value = first == second
            assert (Number(first).to_prover9() == Number(second).to_prover9()) == same_value, (first, second)


def test_a_number_spelled_like_a_constant_is_refused_by_name_in_every_spelling():
    # Number(1) and Constant('1') are ONE symbol for Z3, and the TPTP writers refuse the pair; 1.0 is
    # the numeral 1 (Number(1.0) IS Number(1): a value has one spelling), so the constant '1' is
    # spelled like Number(1.0) too. The constant '1.0' is spelled like no numeral: it is another
    # symbol, whether the numeral was written 1 or 1.0.
    for numeral, name in ((1, "1"), (1.0, "1"), (2.5, "2.5"), (-1, "-1")):
        with pytest.raises(NotImplementedError, match="spelled alike"):
            generate_prover9_input_with_mapping([Atom("P", [Number(numeral)])], Atom("Q", [Constant(name)]))
        with pytest.raises(NotImplementedError, match="spelled alike"):
            generate_prover9_input_with_mapping([Atom("Q", [Constant(name)])], Atom("P", [Number(numeral)]))
    for numeral in (1, 1.0):
        generate_prover9_input_with_mapping([Atom("P", [Number(numeral)])], Atom("Q", [Constant("1.0")]))
    generate_prover9_input_with_mapping([Atom("P", [Number(1)])], Atom("Q", [Constant("one")]))


# --------------------------------------------------------------------------- #
# The reader: the symbol the writer writes is read back as the Number.
# --------------------------------------------------------------------------- #

def test_the_symbol_the_writer_writes_is_read_back_as_the_number():
    for value in (1, 1.0, 0, 2.5, -1, -2.5, 100.0, 0.1):
        node = Atom("P", [Number(value)])
        back = parse_prover9(node.to_prover9())
        assert back == node
        assert isinstance(back.args[0], Number) and back.args[0].value == value


def test_a_written_problem_is_read_back_as_the_formulas_it_was_written_from():
    premises = [_formula(p) for p in ("P(1)", "∀x (x < 2 → Q(x))")]
    goal = _formula("Q(1.0)")
    text, _ = generate_prover9_input_with_mapping(premises, goal)
    records = parse_prover9_problem(text)
    assert [record.formula for record in records] == premises + [goal]


@pytest.mark.parametrize("spelling", ["1.0", "100.0", "-0.0", "2.50", "01", "+1", "1e5"])
def test_the_reader_refuses_a_quoted_numeral_that_is_a_second_spelling_of_a_value(spelling):
    # Prover9 keeps "1" and "1.0" apart as two symbols; the kit's numerals are identified by value,
    # so reading both would give two Prover9 symbols one meaning.
    with pytest.raises(Prover9ParsingError):
        parse_prover9(f'P("{spelling}")')


def test_a_file_that_keeps_two_spellings_of_a_value_apart_is_refused():
    with pytest.raises(Prover9ParsingError):
        parse_prover9('P("1") & Q("1.0")')


# --------------------------------------------------------------------------- #
# The real programs.
# --------------------------------------------------------------------------- #

_PROVER9 = Prover9Backend._binary()
_NO_PROVER9 = ("no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or put "
               "'prover9' on PATH; the offline tests above carry the claim")
live_prover9 = pytest.mark.skipif(not _PROVER9, reason=_NO_PROVER9)


def _mace4_binary():
    """The Mace4 that sits next to the Prover9 binary, or ``None``."""
    if not _PROVER9:
        return None
    candidate = re.sub(r"prover9(\.exe)?$", "mace4", _PROVER9)
    if candidate == _PROVER9:
        return None
    use_wsl = os.environ.get("UFK_PROVER9_WSL", "") not in ("", "0")
    if use_wsl:
        probe = subprocess.run(["wsl.exe", "test", "-x", candidate], capture_output=True, stdin=subprocess.DEVNULL,
                               timeout=30)
        return candidate if probe.returncode == 0 else None
    return candidate if os.path.isfile(candidate) else None


try:
    _MACE4 = _mace4_binary()
except (OSError, subprocess.SubprocessError):
    _MACE4 = None
live_mace4 = pytest.mark.skipif(not _MACE4, reason="no Mace4 next to the Prover9 binary: the Prover9 tests carry the claim")


def _mace4_finds_a_countermodel(premises, goal, max_size=4):
    """Whether Mace4 finds a model of the premises and the negated goal of the file the writer writes
    (``-n 1``: from the one-element universe). Mace4 does not know Prover9's ``auto_denials`` and the
    ``clear`` flags, which are dropped."""
    text, _ = generate_prover9_input_with_mapping([_formula(p) for p in premises], _formula(goal))
    text = "\n".join(line for line in text.splitlines() if not line.startswith(("set(auto_denials", "clear(")))
    with tempfile.NamedTemporaryFile(mode="w", suffix=".in", delete=False, encoding="utf-8", newline="\n") as handle:
        handle.write(text)
        path = handle.name
    try:
        use_wsl = os.environ.get("UFK_PROVER9_WSL", "") not in ("", "0")
        command = ["wsl.exe", _MACE4] if use_wsl else [_MACE4]
        run = subprocess.run(command + ["-n", "1", "-N", str(max_size), "-t", "20", "-f",
                                        _to_wsl_path(path) if use_wsl else path],
                             capture_output=True, text=True, encoding="utf-8", errors="replace",
                             stdin=subprocess.DEVNULL, timeout=120)
    finally:
        os.unlink(path)
    if "Exiting with 1 model" in run.stdout:
        return True
    assert "Exiting with failure" in run.stdout, run.stdout[-600:]
    return False


@live_prover9
@pytest.mark.parametrize("name, premises, goal, valid, why", PROBLEMS, ids=_IDS)
def test_live_prover9_proves_exactly_the_valid_problems(name, premises, goal, valid, why):
    verdict = get_backend("prover9").decide(_formula(goal), [_formula(p) for p in premises], timeout=30000)
    if valid:
        assert verdict.status == "proved", (name, why, verdict)
    else:
        assert (verdict.status, verdict.reason) == ("unknown", "incomplete"), (name, why, verdict)


@live_mace4
@pytest.mark.parametrize("name, premises, goal, valid, why", PROBLEMS, ids=_IDS)
def test_live_mace4_finds_a_countermodel_of_exactly_the_problems_that_are_not_valid(name, premises, goal, valid, why):
    assert _mace4_finds_a_countermodel(premises, goal) == (not valid), (name, why)


@live_mace4
def test_live_mace4_reads_a_bare_integer_as_a_domain_element_and_a_quoted_one_as_a_constant():
    # What the quoting is for: the same two numerals, bare and quoted. Bare, Mace4 has no countermodel of
    # 1 != 2 (they are distinct elements by its own convention); quoted, it has one-element universe.
    def mace4(body):
        text = "set(prolog_style_variables).\nformulas(goals).\n  " + body + "\nend_of_list.\n"
        with tempfile.NamedTemporaryFile(mode="w", suffix=".in", delete=False, encoding="utf-8", newline="\n") as handle:
            handle.write(text)
            path = handle.name
        try:
            use_wsl = os.environ.get("UFK_PROVER9_WSL", "") not in ("", "0")
            command = ["wsl.exe", _MACE4] if use_wsl else [_MACE4]
            return subprocess.run(command + ["-n", "1", "-N", "3", "-t", "20", "-f",
                                             _to_wsl_path(path) if use_wsl else path],
                                  capture_output=True, text=True, encoding="utf-8", errors="replace",
                                  stdin=subprocess.DEVNULL, timeout=120).stdout
        finally:
            os.unlink(path)

    assert "Exiting with failure" in mace4("1 != 2.")
    assert "Exiting with 1 model" in mace4('"1" != "2".')
