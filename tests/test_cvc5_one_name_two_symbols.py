"""cvc5 and a name that is two symbols, or a numeral that is a constant's text.

The cvc5 route writes the problem as SMT-LIB text, where two declarations of ONE name are an error, and
cvc5 answers that error by ending the Python process with a native access violation (measured on 1.3.4:
a predicate ``P`` and a function ``P``, a proposition ``a`` and a constant ``a``, and a variable and a
predicate of one name all did). A symbol is ``(kind, name, arity)``: the first symbol of a name keeps the
name, every later one is declared under a token of its own (``P_2``), and a countermodel reports each
symbol under its ORIGINAL name, with the arity when one name is declared more than once (``"P/1"``,
``"P/2"``), as the Z3 route does.

A numeral and a constant of one text are one symbol and are refused by name, as on the Z3 route; the
numeral ``2.5`` or ``-1``, which cvc5's reader takes for a literal and which ended the process before, is
declared under a token like any other illegal name.

Every decision runs in a CHILD process, so that a regression is a failed assertion about an exit code and
not the death of the test run. The differential reuses the generator and the enumeration oracle of
``test_z3_one_name_two_symbols`` (``_one_name_problems``): with the premise "there are at most two things"
cvc5 proves a problem only if the enumeration finds no countermodel (and cannot refute one, a satisfiable
quantified problem being "unknown" to it); without that premise it never contradicts Z3.
"""
import json
import os
import subprocess
import sys

import pytest

pytest.importorskip("cvc5")

import z3

from unicode_logic_kit.atp.cvc5_backend import SmtNameMap, _sanitize_many_for_smtlib
from unicode_logic_kit.atp.z3_input import to_smtlib
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, Count, Function, Number, Quantifier, SortedCount, SortedQuantifier, Variable,
)

from _one_name_problems import FAMILIES, make_problem, oracle_has_countermodel

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
A, B = Constant("a"), Constant("b")
X, Y = Variable("x"), Variable("y")

_CHILD = r"""
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import Node

spec = json.loads(sys.argv[1])
out = []
for item in spec:
    premises = [Node.from_dict(d) for d in item["premises"]]
    goal = Node.from_dict(item["goal"])
    verdict = Cvc5Backend().decide(goal, premises, timeout=20000)
    out.append({"status": verdict.status, "reason": verdict.reason, "detail": verdict.detail,
                "assignment": (verdict.countermodel or {}).get("assignment")})
print(json.dumps(out))
"""

_DIFFERENTIAL_CHILD = r"""
import json, sys
sys.path.insert(0, sys.argv[1])
from _one_name_problems import AT_MOST_TWO, FAMILIES, make_problem
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend

def answer(goal, premises):
    verdict = Cvc5Backend().decide(goal, premises, timeout=10000)
    return {"status": verdict.status, "reason": verdict.reason,
            "keys": sorted((verdict.countermodel or {}).get("assignment") or [])}

out = []
for family_index, seed in json.loads(sys.argv[2]):
    premises, goal = make_problem(seed, FAMILIES[family_index])
    out.append({"bounded": answer(goal, list(premises) + [AT_MOST_TWO]),
                "free": answer(goal, list(premises))})
print(json.dumps(out))
"""


def _run(source, *argv):
    done = subprocess.run([sys.executable, "-c", source, *argv], capture_output=True, text=True,
                          encoding="utf-8", timeout=900)
    # 0, not 3221225477 (Windows access violation) or -11 (SIGSEGV)
    assert done.returncode == 0, (done.returncode, done.stderr[-600:])
    return json.loads(done.stdout.strip().splitlines()[-1])


def decide_all(*problems):
    """``[(premises, goal), ...]`` through ``Cvc5Backend().decide`` in one child; the verdict dicts."""
    spec = json.dumps([{"premises": [p.to_dict() for p in premises], "goal": goal.to_dict()}
                       for premises, goal in problems])
    return _run(_CHILD, spec)


def decide_one(goal, premises=()):
    return decide_all((list(premises), goal))[0]


# ---------------------------------------------------------------------------------------------
# hand-derived: one name, two symbols
# ---------------------------------------------------------------------------------------------
def test_one_predicate_at_two_arities_is_two_relations():
    # P(a) ⊬ P(a, b): the universe {0}, P1 = {0}, P2 = {}.  (cvc5 may answer unknown; it must not prove it)
    refutable = decide_one(Atom("P", [A, B]), [Atom("P", [A])])
    assert refutable["status"] in ("refuted", "unknown")
    # P(a, b) ⊢ P(a, b) trivially, with both arities in one problem
    both = decide_one(Atom("P", [A, B]), [Atom("P", [A]), Atom("P", [A, B])])
    assert both["status"] == "proved"


def test_a_function_at_two_arities_is_two_functions_and_the_countermodel_says_so():
    # f(a) = b ⊬ f(a, a) = b: the universe {0, 1}, a = 0, b = 1, f1(0) = 1, f2(0, 0) = 0
    verdict = decide_one(Atom("=", [Function("f", [A, A]), B]), [Atom("=", [Function("f", [A]), B])])
    assert verdict["status"] == "refuted"
    assert set(verdict["assignment"]) == {"a", "b", "f/1", "f/2"}


def test_a_predicate_and_a_function_of_one_name_end_no_process():
    # P(a) ⊬ P(P(a)): the universe {0, 1}, a = 0, the predicate P = {0}, the function P(0) = 1.
    # (This ended the process: two declarations of the name P.)
    refuted = decide_one(Atom("P", [Function("P", [A])]), [Atom("P", [A])])
    assert refuted["status"] == "refuted"
    assert set(refuted["assignment"]) == {"a", "P/1:Bool", "P/1:S"}
    assert decide_one(Atom("P", [Function("P", [A])]), [Atom("P", [Function("P", [A])])])["status"] == "proved"


def test_a_proposition_and_a_constant_of_one_name_are_two_symbols():
    # the proposition a does not follow from Q(a), the constant a
    verdict = decide_one(Atom("a", []), [Atom("Q", [A])])
    assert verdict["status"] == "refuted"
    assert set(verdict["assignment"]) == {"Q", "a/0:Bool", "a/0:S"}


def test_a_predicate_named_like_a_variable_is_another_symbol():
    # the predicate x of two arguments next to the variable x: ⊢ ∃x:T x(x, x) is not valid
    # (the universe {0}, T = {0}, x = {}); the variable and the predicate were two declarations of one name
    verdict = decide_one(SortedQuantifier("∃", X, "T", Atom("x", [X, X])))
    assert verdict["status"] in ("refuted", "unknown")


def test_a_predicate_of_another_arity_named_like_a_sort_is_not_the_sort():
    some_pair = SortedQuantifier("∃", X, "Car", SortedQuantifier("∃", Y, "Car", Atom("Car", [X, Y])))
    every_pair = SortedQuantifier("∀", X, "Car", SortedQuantifier("∀", Y, "Car", Atom("Car", [X, Y])))
    assert decide_one(some_pair)["status"] in ("refuted", "unknown")           # never proved
    # ∀x:Car ∀y:Car Car(x, y) ⊢ ∃x:Car ∃y:Car Car(x, y) is valid (a sort is never empty), so cvc5 must not
    # refute it; it gives up on it even with the relation renamed (instantiation is incomplete), which is
    # why the Z3 route pins "proved" and this one "not refuted"
    assert decide_one(some_pair, [every_pair])["status"] in ("proved", "unknown")


def test_a_name_declared_once_keeps_its_plain_key():
    verdict = decide_one(Atom("P", [A]))
    assert verdict["status"] == "refuted" and set(verdict["assignment"]) == {"a", "P"}


# ---------------------------------------------------------------------------------------------
# the sanitiser and the exported text
# ---------------------------------------------------------------------------------------------
def test_the_first_symbol_of_a_name_keeps_it_and_the_others_get_tokens_of_their_own():
    nodes = [Atom("P", [A]), Atom("P", [A, B]), Atom("Q", [Function("P", [A])])]
    sanitised, names = _sanitize_many_for_smtlib(nodes)
    assert names.symbol("predicate", "P", 1) == "P"
    assert names.symbol("predicate", "P", 2) == "P_2"
    assert names.symbol("function", "P", 1) == "P_1"
    assert [type(n).__name__ for n in sanitised] == ["Atom", "Atom", "Atom"]
    assert sanitised[1].predicate == "P_2" and sanitised[2].args[0].name == "P_1"
    # every token reads back as the name it stands for
    assert names.reverse() == {"P": "P", "P_2": "P", "P_1": "P", "a": "a", "b": "b", "Q": "Q"}


def test_a_token_never_takes_the_name_of_another_symbol_of_the_problem():
    # a symbol literally called P_2 is a name of its own; the second P must not be called that
    nodes = [Atom("P", [A]), Atom("P", [A, B]), Atom("P_2", [A])]
    _, names = _sanitize_many_for_smtlib(nodes)
    tokens = [names.symbol("predicate", "P", 1), names.symbol("predicate", "P", 2),
              names.symbol("predicate", "P_2", 1)]
    assert len(set(tokens)) == 3 and tokens[2] == "P_2"


def test_a_numeral_and_a_constant_of_one_text_are_refused_by_the_sanitiser():
    with pytest.raises(NotImplementedError, match="numeral 1 and a constant named '1'"):
        _sanitize_many_for_smtlib([Atom("P", [Number(1)]), Atom("Q", [Constant("1")])])
    names = SmtNameMap()
    names.collect("1", numeral=True)
    with pytest.raises(NotImplementedError, match="one symbol"):
        names.collect("1")


def test_the_same_numeral_twice_and_two_numerals_are_not_a_clash():
    _sanitize_many_for_smtlib([Atom("P", [Number(1)]), Atom("Q", [Number(1)]), Atom("R", [Number(2)])])


def test_the_text_to_smtlib_writes_has_every_name_declared_once():
    problem = [Atom("P", [A]), Atom("P", [A, B]), Atom("R", [Function("P", [A])])]
    text = to_smtlib(Atom("P", [B]), problem)
    declared = [line.split()[1] for line in text.splitlines() if line.startswith("(declare-fun")]
    assert len(declared) == len(set(declared)) and len(declared) >= 6, declared
    z3.parse_smt2_string(text)                                  # and it is text a solver reads


def test_to_smtlib_refuses_a_numeral_and_a_constant_of_one_text():
    with pytest.raises(NotImplementedError, match="numeral 1"):
        to_smtlib(Atom("=", [Number(1), Constant("1")]))


def test_cvc5_reads_the_text_to_smtlib_writes_for_a_name_at_two_arities():
    text = to_smtlib(Atom("P", [A, B]), [Atom("P", [A]), Atom("Q", [Function("P", [A])])])
    source = (
        "import sys, cvc5\n"
        "text = sys.stdin.read()\n"
        "solver = cvc5.Solver()\n"
        "parser = cvc5.InputParser(solver)\n"
        "manager = parser.getSymbolManager()\n"
        "parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, text, 'text')\n"
        "while True:\n"
        "    command = parser.nextCommand()\n"
        "    if command.isNull():\n"
        "        break\n"
        "    command.invoke(solver, manager)\n"
        "print('read')\n")
    done = subprocess.run([sys.executable, "-c", source], input=text, capture_output=True, text=True,
                          encoding="utf-8", timeout=300)
    assert done.returncode == 0 and "read" in done.stdout, (done.returncode, done.stderr[-400:])


# ---------------------------------------------------------------------------------------------
# numerals
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("value, key", [
    (1, "1"), (2.5, "2.5"), (-1, "-1"), (-2.5, "-2.5"), (1e-05, "1e-05"), (0, "0"),
    # a numeral is the constant of its VALUE: an integral float is written as the integer it is
    (1.0, "1"), (1e+22, "10000000000000000000000"),
])
def test_a_numeral_of_any_spelling_is_a_symbol_cvc5_declares_and_reports_by_its_text(value, key):
    # P(v) ⊢ P(v) is valid; P(v) ⊬ Q(v): the universe {0}, v = 0, P = {0}, Q = {}
    entailed, not_entailed = decide_all(
        ([Atom("P", [Number(value)])], Atom("P", [Number(value)])),
        ([Atom("P", [Number(value)])], Atom("Q", [Number(value)])))
    assert entailed["status"] == "proved"
    assert not_entailed["status"] == "refuted"
    assert set(not_entailed["assignment"]) == {key, "P", "Q"}       # the numeral, not a token


@pytest.mark.parametrize("value, key, stays", [
    (0, "0", True), (12, "12", True), (1e-07, "1e-07", True), (1.5e-05, "1.5e-05", True),      # digits; digits with an exponent
    (1e+16, "10000000000000000", True), (1.0, "1", True),      # an integral float is the integer of that value: digits
    (2.5, "2.5", False), (0.25, "0.25", False), (-1, "-1", False), (-2.5, "-2.5", False),      # a decimal; a negative number
])
def test_a_numeral_keeps_its_text_when_cvc5_takes_it_and_is_renamed_when_cvc5_reads_it_as_a_literal(value, key, stays):
    # Z3 pipe-quotes |12| and |1e-07| and cvc5 declares them; |2.5| and -1 end cvc5's process
    _, names = _sanitize_many_for_smtlib([Atom("P", [Number(value)])])
    token = names.symbol("function", key, 0)
    assert (token == key) is stays, (value, token)
    if not stays:
        assert not token[0].isdigit() and token[0] != "-"      # a renamed numeral is no literal either


def test_two_numerals_are_two_things_and_one_numeral_is_one():
    # ⊢ 1 = 2 is not valid (a universe of two), ⊢ 1 = 1 is
    distinct, same = decide_all(([], Atom("=", [Number(1), Number(2)])), ([], Atom("=", [Number(1), Number(1)])))
    assert distinct["status"] == "refuted" and same["status"] == "proved"


def test_a_numeral_and_a_constant_of_one_text_are_refused_by_name_through_the_backend():
    problems = [([Atom("P", [Number(1)])], Atom("P", [Constant("1")])),     # premise and goal
                ([], Atom("=", [Number(1), Constant("1")])),                 # one formula
                ([Atom("P", [Number(2.5)]), Atom("Q", [Constant("2.5")])], Atom("R", [A]))]
    for verdict in decide_all(*problems):
        assert (verdict["status"], verdict["reason"]) == ("unknown", "unsupported")
        assert "one symbol" in verdict["detail"]


def test_the_bound_of_a_counting_quantifier_is_no_numeral_of_the_problem():
    # ∃>=2 x P(x) ⊢ ∃x P(x), with a constant named 2 in the problem: the 2 of the quantifier is a parameter of
    # the node, not the numeral 2, so there is no clash with the constant (and the node keeps its Number)
    two_ps = Count("ge", Number(2), X, Atom("P", [X]))
    some_p = Quantifier("∃", X, Atom("P", [X]))
    two_ss = SortedCount("ge", Number(2), X, "S", Atom("P", [X]))
    some_s = SortedQuantifier("∃", X, "S", Atom("P", [X]))
    q_two = Atom("Q", [Constant("2")])
    verdicts = decide_all(([two_ps], some_p), ([two_ps, q_two], q_two), ([two_ss], some_s), ([two_ss, q_two], q_two))
    assert [v["status"] for v in verdicts] == ["proved"] * 4


# ---------------------------------------------------------------------------------------------
# the differential: cvc5 against the enumeration written from the definition
# ---------------------------------------------------------------------------------------------
BATCH = [(index, seed) for index in range(len(FAMILIES)) for seed in range(1, 21)]


@pytest.fixture(scope="module")
def differential():
    """Per problem: cvc5's answer with the premise "at most two things" (``bounded``) and without it (``free``)."""
    answers = _run(_DIFFERENTIAL_CHILD, TESTS_DIR, json.dumps(BATCH))
    rows = []
    for (index, seed), answer in zip(BATCH, answers):
        family = FAMILIES[index]
        premises, goal = make_problem(seed, family)
        rows.append((family, seed, premises, goal, answer, oracle_has_countermodel(premises, goal, family)))
    return rows


def test_cvc5_never_proves_what_a_small_structure_refutes_and_never_refutes_what_none_does(differential):
    # "at most two things" is a premise, so a structure of at most two elements is all there is: cvc5 proves a
    # problem only if the enumeration finds no countermodel, and refutes one only if it finds one
    wrong = [(family.label, seed, answer["bounded"]["status"], countermodel)
             for family, seed, premises, goal, answer, countermodel in differential
             if (answer["bounded"]["status"] == "proved" and countermodel)
             or (answer["bounded"]["status"] == "refuted" and not countermodel)]
    assert wrong == []


def test_cvc5_proves_nearly_every_valid_problem_of_the_batch(differential):
    # (it cannot refute the bounded ones: a satisfiable problem with quantifiers is "unknown" to it)
    valid = [(family.label, seed, answer["bounded"]["status"])
             for family, seed, _, _, answer, countermodel in differential if not countermodel]
    proved = [v for v in valid if v[2] == "proved"]
    assert len(valid) >= 30 and len(proved) >= 0.75 * len(valid), valid


def test_without_the_bound_cvc5_and_z3_never_contradict_each_other(differential):
    from unicode_logic_kit.atp.protocol import Z3Backend
    refuted_by_cvc5 = 0
    for family, seed, premises, goal, answer, _ in differential:
        z3_status = Z3Backend().decide(goal, list(premises)).status
        cvc5_status = answer["free"]["status"]
        assert not (cvc5_status == "proved" and z3_status == "refuted"), (family.label, seed)
        assert not (cvc5_status == "refuted" and z3_status == "proved"), (family.label, seed)
        refuted_by_cvc5 += cvc5_status == "refuted"
    assert refuted_by_cvc5 >= 20                         # the countermodels the next test reads exist


def test_a_cvc5_countermodel_has_one_key_per_symbol_of_the_problem(differential):
    checked = 0
    for family, seed, premises, goal, answer, _ in differential:
        if answer["free"]["status"] != "refuted":
            continue
        symbols = set()
        for node in [goal, *premises]:
            for n in node.walk():
                if isinstance(n, Atom) and n.predicate != "=":
                    symbols.add(("predicate", n.predicate, len(n.args)))
                elif isinstance(n, Function):
                    symbols.add(("function", n.name, len(n.args)))
                elif type(n).__name__ in ("Constant", "SortedConstant"):
                    symbols.add(("function", n.name, 0))
                if type(n).__name__ in ("SortedQuantifier", "SortedConstant"):
                    symbols.add(("predicate", n.sort, 1))
        keys = answer["free"]["keys"]
        assert len(keys) == len(symbols), (family.label, seed, keys, sorted(symbols))
        checked += 1
    assert checked >= 20
