"""The symbols of an SMT-LIB text: the names Z3's printer writes, a counting bound of 500, two symbols that read as
one, and a core that names a symbol the problem does not have.

Every expectation is derived by hand and written next to the test.

* **The printer's own names.** Z3 writes a shared sub-term as ``(let (($x24 (R c d))) ...)`` (``?x10`` for a
  term that is no formula) without looking at the symbols the text declares; a declared symbol of that spelling
  is shadowed inside the ``let``, the text then says another formula, and cvc5 ends its process on it. No symbol
  of a text is spelled so: the sanitiser renames it, like any other name that cannot be written as it is.
* **A counting bound up to 500** is a formula of that many nested quantifiers. Nothing that handles it recurses
  on it. The tests of the whole path lower the interpreter's recursion limit instead of building the formula
  of the documented size (which takes minutes to translate); the renaming of the largest expansion is run as it is.
* **One name per symbol when a text is read.** The writer gives the constant ``a!c`` the symbol ``a!c!c``; the
  symbol ``a!c`` is written for no constant and is the constant ``a!c``; a text with both holds two constants.
* **What cvc5 reports back** carries the caller's names, and a token is renamed back only where it is a whole
  symbol, never inside the pipe-quoted symbol of another name.

Every cvc5 call that could end the process runs in a CHILD process.
"""
import importlib.util
import itertools
import json
import random
import re
import subprocess
import sys

import pytest
import z3

from unicode_logic_kit import api
from unicode_logic_kit.atp.cvc5_backend import (
    Cvc5Backend, _collect_names_for_smtlib, _is_smtlib_safe, _lower_counting_for_smtlib, _reverse_map_smtlib_text,
    _sanitize_many_for_smtlib, SmtNameMap,
)
from unicode_logic_kit.atp.protocol import ERROR, REFUTED, UNKNOWN
from unicode_logic_kit.atp.z3_input import from_z3, parse_smtlib, to_smtlib
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Or, Quantifier, SortedCount, SortedQuantifier,
    Variable, Z3Env,
)

HAS_CVC5 = importlib.util.find_spec("cvc5") is not None

#: What a text must not declare or bind: the names Z3's printer writes for a shared sub-term (a sign, an ``x`` and
#: the number of the term), and the ``@`` form of them, which no problem's symbol has either.
_PRINTER_NAME = re.compile(r"[$?@]x[0-9]+")
X = Variable("x")


def P(*args):
    return Atom("P", list(args))


def run_child(source, *args, timeout=240):
    """The exit code, the standard output and the error output of a child interpreter running ``source``."""
    done = subprocess.run([sys.executable, "-c", source, *args], capture_output=True, text=True,
                          encoding="utf-8", timeout=timeout)
    return done.returncode, done.stdout, done.stderr


# ---------------------------------------------------------------------------------------------------------
# the names Z3's printer writes
# ---------------------------------------------------------------------------------------------------------
PRINTER_NUMBERS = (0, 1, 7, 10, 24, 38, 123)
PRINTER_NAMES = [f"{sign}x{number}" for sign in "$?@" for number in PRINTER_NUMBERS]


def one_name_in_every_role(name):
    """A problem in which ``name`` is a constant, a unary function, a binary predicate, a proposition, a bound
    variable and a sort (the guard predicate of a sorted quantifier): six symbols of that one name, next to the
    five of ``P``, ``Q``, ``c``, ``d`` and ``y``."""
    c, d, y = Constant("c"), Constant("d"), Variable("y")
    return And(
        Atom("P", [Constant(name), Function(name, [c])]),
        And(Atom(name, [c, d]),
            And(Atom(name, []),
                And(Quantifier("∃", Variable(name), Atom("Q", [Variable(name)])),
                    SortedQuantifier("∀", y, name, Atom("Q", [y]))))))


@pytest.mark.parametrize("name", PRINTER_NAMES)
def test_a_symbol_spelled_like_a_name_of_the_printer_is_renamed_and_reported_under_its_own_name(name):
    assert not _is_smtlib_safe(name)
    _, names = _sanitize_many_for_smtlib([one_name_in_every_role(name)])
    tokens = list(names.symbols.values())
    assert len(tokens) == len(set(tokens)) == 5 + 6            # P, Q, c, d, y; and the six symbols of the name
    assert not [token for token in tokens if _PRINTER_NAME.fullmatch(token)]
    # each of the six symbols of the name is reported under that name
    assert sorted(original for original in names.reverse().values() if original == name) == [name] * 6


@pytest.mark.parametrize("name", ["$x", "?x", "$x_2", "$y24", "x24", "$x24a", "n$x24", "$xx24"])
def test_a_name_that_is_not_a_name_of_the_printer_is_left_as_it_is(name):
    assert _is_smtlib_safe(name)
    _, names = _sanitize_many_for_smtlib([P(Constant(name))])
    assert names.reverse()[name] == name


def test_no_token_is_a_name_of_the_printer_whatever_names_a_problem_holds():
    # Every name of one to four characters over ``$ ? @ x 1 2 _`` (2800 of them, among them every ``$x`` and
    # ``?x`` followed by up to two digits), each as a constant, a unary function, a binary predicate, a
    # proposition and a variable, in ONE problem, so that the sanitiser numbers the tokens that meet
    # (``base``, ``base2``, ...): no symbol of the result is spelled like a name the printer mints, and the
    # symbols are as many as the problem's.
    names = ["".join(chars) for size in range(1, 5) for chars in itertools.product("$?@x12_", repeat=size)]
    formulas = []
    for start in range(0, len(names), 40):
        parts = []
        for name in names[start:start + 40]:
            parts += [Atom("P", [Constant(name), Function(name, [Constant("c")])]),
                      Atom(name, [Constant("c"), Constant("d")]), Atom(name, []),
                      Quantifier("∃", Variable(name), Atom("Q", [Variable(name)]))]
        formula = parts[0]
        for part in parts[1:]:
            formula = And(formula, part)
        formulas.append(formula)
    _, symbols = _sanitize_many_for_smtlib(formulas)
    tokens = list(symbols.symbols.values())
    assert len(tokens) == len(set(tokens)) == 5 * len(names) + 4        # the five roles of a name, P, Q, c and d
    assert [token for token in tokens if _PRINTER_NAME.fullmatch(token)] == []


def test_a_constant_next_to_the_token_of_a_printer_name_keeps_apart_from_it():
    # $x24 is renamed to a token; a constant that is spelled like that token is another symbol
    token = _sanitize_many_for_smtlib([P(Constant("$x24"))])[1].symbol("function", "$x24", 0)
    assert token != "$x24"
    sanitised, _ = _sanitize_many_for_smtlib([P(Constant("$x24"), Constant(token))])
    assert len({arg.name for arg in sanitised[0].args}) == 2


def declared_and_bound_names(text):
    """Every name a text of Z3's printer declares or binds in a quantifier (not a ``let``)."""
    declared = re.findall(r"\(declare-(?:fun|const) (\|[^|]*\||[^\s()|]+)", text)
    bound = re.findall(r"\((\|[^|]*\||[^\s()|]+) S\)", text)
    return {name.strip("|") for name in declared + bound}


@pytest.mark.parametrize("sign", "$?@")
def test_no_symbol_of_the_text_is_spelled_like_a_name_of_the_printer(sign):
    # a constant, a function, a predicate, a proposition, a variable and a sort of such a name: the text declares
    # and binds none of them, and it says what the sanitised problem says (z3 finds the two equivalent)
    for number in PRINTER_NUMBERS:
        name = f"{sign}x{number}"
        problem = one_name_in_every_role(name)
        text = to_smtlib(problem)
        assert not [n for n in declared_and_bound_names(text) if _PRINTER_NAME.fullmatch(n)], (name, text)
        [back] = parse_smtlib(text)
        [expected], _ = _sanitize_many_for_smtlib([problem])
        solver = z3.Solver()
        solver.add(z3.Not(z3.And(z3.Implies(expected.to_z3(), back.to_z3()), z3.Implies(back.to_z3(), expected.to_z3()))))
        assert solver.check() == z3.unsat, name


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
@pytest.mark.parametrize("name", ["$x24", "?x10"])
def test_cvc5_reports_a_symbol_spelled_like_a_printer_name_under_that_name(name):
    # P(c) ⊢ Q is not valid (Q false): the countermodel has the symbols P, Q and c, each under the caller's name
    source = r'''
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import Atom, Constant
verdict = Cvc5Backend().decide(Atom("Q", []), [Atom("P", [Constant(sys.argv[1])])], timeout=10000)
print(json.dumps({"status": verdict.status, "keys": sorted((verdict.countermodel or {}).get("assignment", {}))}))
'''
    code, out, err = run_child(source, name)
    assert code == 0, err[-500:]
    assert json.loads(out) == {"status": REFUTED, "keys": sorted(["P", "Q", name])}


def shared_terms(constant):
    """Two problems, each tautologically valid: ``(A → B) ∧ (B ∨ ¬A)`` with ``B = A ∨ R(...)``, ``A`` a counting
    quantifier whose expansion shares ``constant`` (a Boolean sub-term ``R(c, d)`` is shared in the first, a term
    ``g(g(g(c)))`` that is no formula in the second)."""
    k = Constant(constant)
    a1 = Count("ge", Number(2), X, Atom("P", [X, k]))
    b1 = Or(a1, Atom("R", [Constant("c"), Constant("d")]))
    g = Function("g", [Function("g", [Function("g", [Constant("c")])])])
    a2 = Count("ge", Number(2), X, And(Atom("P", [X, g]), Atom("Q", [Function("g", [g])])))
    b2 = Or(a2, Atom("R", [g, k]))
    return [And(Implies(a1, b1), Or(b1, Not(a1))), And(Implies(a2, b2), Or(b2, Not(a2)))]


def test_every_name_z3_writes_for_a_shared_sub_term_is_a_name_the_sanitiser_keeps_clear_of():
    seen = set()
    for problem in shared_terms("k"):
        text = to_smtlib(problem)
        seen.update(re.findall(r"\(let \(\(([^\s()|]+) ", text))
    assert seen, "no shared sub-term was written as a let: the premise of this test is gone"
    assert [name for name in seen if not _PRINTER_NAME.fullmatch(name)] == []
    assert {name[0] for name in seen} == {"$", "?"}           # a formula and a term that is no formula


def test_a_constant_spelled_like_any_name_of_the_printer_is_never_shadowed_in_one_process():
    # One process, so the let names run through many numbers as the terms of the process pile up: for each of
    # 80 numbers, the constant of the two problems of ``shared_terms`` is spelled ``$x<n>`` and then ``?x<n>``:
    # no declared or bound symbol of the text is a name that opens a ``let``.
    for number in range(80):
        for sign in "$?":
            name = f"{sign}x{number}"
            for shape in shared_terms(name):
                text = to_smtlib(shape)
                lets = set(re.findall(r"\(let \(\(([^\s()|]+) ", text))
                assert not declared_and_bound_names(text) & lets, (name, text[:300])


_LET_CHILD = r'''
import importlib.util, json, re, sys
import z3
from unicode_logic_kit.atp.z3_input import to_smtlib
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Count, Function, Implies, Not, Number, Or, Variable

shape, constant, mode = sys.argv[1], sys.argv[2], sys.argv[3]
x = Variable("x")
k = Constant(constant)
if shape == "formula":
    a = Count("ge", Number(2), x, Atom("P", [x, k]))
    b = Or(a, Atom("R", [Constant("c"), Constant("d")]))
else:
    g = Function("g", [Function("g", [Function("g", [Constant("c")])])])
    a = Count("ge", Number(2), x, And(Atom("P", [x, g]), Atom("Q", [Function("g", [g])])))
    b = Or(a, Atom("R", [g, k]))
goal = And(Implies(a, b), Or(b, Not(a)))
text = to_smtlib(goal, [])
lets = re.findall(r"\(let \(\(([$?]x[0-9]+) ", text)
bound_to = {"formula": r"\(let \(\((\$x[0-9]+) \(R c d\)\)\)",
            "term": r"\(let \(\((\?x[0-9]+) \(g \(g \(g c\)\)\)\)"}[shape]
found = re.search(bound_to, text)
answer = {"shared": found.group(1) if found else None, "lets": lets,
          "declared": re.findall(r"\(declare-fun (\S+) \(\) S\)", text)}
if mode == "check":
    try:
        asserted = z3.parse_smt2_string(text)
        solver = z3.Solver()
        solver.add(z3.Not(asserted[-1]))
        answer["z3_on_the_negated_goal"] = str(solver.check())
    except Exception as exc:
        answer["z3_on_the_negated_goal"] = "the text is not read: " + str(exc)[:200]
    if importlib.util.find_spec("cvc5") is not None:
        from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
        answer["cvc5"] = Cvc5Backend().decide(goal, [], timeout=10000).status
print(json.dumps(answer))
'''


@pytest.mark.parametrize("shape", ["formula", "term"])
def test_a_constant_spelled_like_the_name_of_a_shared_sub_term_is_neither_shadowed_nor_fatal(shape):
    # The names Z3 writes depend on the order in which it made its terms, so the name is found in one fresh
    # interpreter (with a constant ``zz``) and the problem with that very constant is run in a second one.
    # The goal is valid by propositional logic alone: (A → B) ∧ (B ∨ ¬A) with B = A ∨ R(..) is a tautology
    # in A and B, whatever P, R and the constant mean.
    code, out, err = run_child(_LET_CHILD, shape, "zz", "probe")
    assert code == 0, err[-500:]
    name = json.loads(out)["shared"]
    assert name, "the shared sub-term was not written as a let"
    code, out, err = run_child(_LET_CHILD, shape, name, "check")
    assert code == 0, f"the child ended with exit code {code & 0xFFFFFFFF:#x}: {err[-300:]}"
    answer = json.loads(out)
    assert not set(answer["declared"]) & set(answer["lets"]), answer         # no declared symbol is shadowed
    assert answer["z3_on_the_negated_goal"] == "unsat", answer
    if HAS_CVC5:
        assert answer["cvc5"] == "proved", answer


# ---------------------------------------------------------------------------------------------------------
# a counting bound, expanded to that many nested quantifiers
# ---------------------------------------------------------------------------------------------------------
def nested_quantifiers(depth):
    """``∃v0 ∃v1 … ∃v{depth-1} select(v{depth-1})``, built without recursion: ``select`` is a symbol of SMT-LIB."""
    body = Atom("select", [Variable(f"v{depth - 1}")])
    for i in reversed(range(depth)):
        body = Quantifier("∃", Variable(f"v{i}"), body)
    return body


def test_the_names_of_a_chain_far_deeper_than_the_recursion_limit_are_collected_and_rewritten():
    depth = 3000
    assert depth > 2 * sys.getrecursionlimit()
    chain = nested_quantifiers(depth)
    names = SmtNameMap()
    _collect_names_for_smtlib(chain, names)
    names.finalize()
    assert {original for (kind, original, arity) in names.symbols if kind == "variable"} == {f"v{i}" for i in range(depth)}
    [sanitised], _ = _sanitize_many_for_smtlib([chain])
    # every quantifier of the chain still binds its own variable, and ``select`` (a symbol of SMT-LIB) is
    # the token ``nselect`` at the bottom
    bound, node = [], sanitised
    while isinstance(node, Quantifier):
        bound.append(node.variable.name)
        node = node.formula
    assert bound == [f"v{i}" for i in range(depth)]
    assert isinstance(node, Atom) and node.predicate != "select"
    assert node.args[0] == Variable(f"v{depth - 1}")


def stack_depth():
    frame, depth = sys._getframe(), 0
    while frame is not None:
        frame, depth = frame.f_back, depth + 1
    return depth


def under_a_recursion_budget(frames, function):
    """``function()`` with the recursion limit ``frames`` above the present depth; what it returned or raised."""
    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(stack_depth() + frames)
    try:
        return "value", function()
    except RecursionError as exc:
        return "recursion", exc
    finally:
        sys.setrecursionlimit(limit)


@pytest.mark.parametrize("make", [
    lambda body: Count("ge", Number(500), X, body),
    lambda body: SortedCount("ge", Number(500), X, "Person", body),
], ids=["plain", "sorted"])
def test_the_expansion_of_the_largest_counting_bound_is_lowered_and_renamed_without_recursing_on_it(make):
    # ∃≥500 x P(x) is 500 nested quantifiers ``∃x0 … ∃x499`` over about 125 000 pairwise conditions. With a budget
    # of 300 frames, far below the 3.5 frames a nested quantifier cost when the renaming recursed on it (1750 for
    # 500), lowering and renaming must work.
    def lower_and_rename():
        lowered, _ = _lower_counting_for_smtlib([make(Atom("P", [X]))])
        return _sanitize_many_for_smtlib(lowered)[0][0]

    outcome, sanitised = under_a_recursion_budget(300, lower_and_rename)
    assert outcome == "value", sanitised
    witnesses, node = [], sanitised
    while isinstance(node, Quantifier):
        witnesses.append(node.variable.name)
        node = node.formula
    assert node is not None and len(witnesses) == 500 and len(set(witnesses)) == 500


def test_the_text_of_a_counting_quantifier_needs_a_stack_that_does_not_grow_with_its_bound():
    # ∃≥100 x P(x) is 100 nested quantifiers (and about 5000 conjuncts). Measured: lowering it, renaming it and
    # writing it takes about 130 frames beyond the caller's when nothing recurses on the nesting, and about
    # 350 when the renaming does (3.5 frames a level); 250 separates the two.
    formula = Count("ge", Number(100), X, Atom("P", [X]))
    outcome, result = under_a_recursion_budget(250, lambda: to_smtlib(formula))
    assert outcome == "value", result
    assert result.count("(exists ") == 100


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
def test_cvc5_decides_a_counting_bound_under_a_small_recursion_limit():
    # ¬∃≥100 x (P(x) ∧ ¬P(x)) is valid: no element satisfies a contradiction, so fewer than 100 do. The child
    # lowers the recursion limit to 250 frames above its own, with which nothing may recurse on the 100
    # nested quantifiers of the expansion (cvc5 answers by propositional reasoning on the skolemised witnesses).
    source = r'''
import sys
sys.setrecursionlimit(len(__import__("traceback").extract_stack()) + 250)
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import And, Atom, Count, Not, Number, Variable
x = Variable("x")
contradiction = And(Atom("P", [x]), Not(Atom("P", [x])))
goal = Not(Count("ge", Number(100), x, contradiction))
verdict = Cvc5Backend().decide(goal, [], timeout=20000)
print(verdict.status, verdict.reason, (verdict.detail or "")[:200])
'''
    code, out, err = run_child(source)
    assert code == 0, err[-500:]
    assert out.split()[0] == "proved", out


@pytest.mark.parametrize("bound", [501, 5000])
def test_a_counting_bound_above_the_limit_is_refused_by_name_with_its_bound(bound):
    formula = Count("ge", Number(bound), X, Atom("P", [X]))
    sorted_formula = SortedCount("ge", Number(bound), X, "Person", Atom("P", [X]))
    for f in (formula, sorted_formula):
        with pytest.raises(NotImplementedError, match=f"n={bound}"):
            to_smtlib(f)
        if HAS_CVC5:
            verdict = Cvc5Backend().decide(f, [])
            assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
            assert f"n={bound}" in verdict.detail


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
def test_a_formula_too_deep_for_the_recursion_limit_is_an_error_verdict_and_not_an_exception():
    deep = P(Constant("c"))
    for _ in range(3 * sys.getrecursionlimit()):
        deep = Not(deep)
    verdict = Cvc5Backend().decide(deep, [])
    assert verdict.status == ERROR and verdict.reason == "infra"
    assert verdict.detail.startswith("RecursionError")


# ---------------------------------------------------------------------------------------------------------
# reading a text: two symbols are two names
# ---------------------------------------------------------------------------------------------------------
TWO_CONSTANTS_ONE_NAME_APART = """(declare-sort S 0)
(declare-fun a!c () S)
(declare-fun a!c!c () S)
(declare-fun P (S) Bool)
(assert (not (= a!c a!c!c)))
(assert (P a!c))
(assert (not (P a!c!c)))
"""


def test_the_symbols_a_c_and_a_c_c_of_one_text_are_two_constants():
    # satisfiable: the universe {0, 1}, a!c = 0, a!c!c = 1, P = {0} (and z3 says so about the text itself)
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(TWO_CONSTANTS_ONE_NAME_APART))
    assert solver.check() == z3.sat
    nodes = parse_smtlib(TWO_CONSTANTS_ONE_NAME_APART)
    assert [n.to_unicode_str() for n in nodes] == ["¬a!c = a!c!c", "P(a!c)", "¬P(a!c!c)"]
    verdict = api.prove(Atom("$false", []), nodes, backends=["z3"], timeout=8000)
    assert verdict.status == REFUTED
    # the countermodel has the three symbols of the text, the two constants told apart
    assignment = verdict.countermodel["assignment"]
    assert set(assignment) == {"P", "a!c", "a!c!c"}
    assert assignment["a!c"] != assignment["a!c!c"]


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
def test_cvc5_does_not_prove_falsity_from_that_text_either():
    source = r'''
import sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.atp.z3_input import parse_smtlib
from unicode_logic_kit.fol.nodes import Atom
nodes = parse_smtlib(sys.argv[1])
print(Cvc5Backend().decide(Atom("$false", []), nodes, timeout=10000).status)
'''
    code, out, err = run_child(source, TWO_CONSTANTS_ONE_NAME_APART)
    assert code == 0, err[-500:]
    assert out.strip() == REFUTED


MARKED_PIECES = ("a", "!c", "!v")


def names_of_up_to(pieces_count):
    return ["".join(parts) for size in range(1, pieces_count + 1)
            for parts in itertools.product(MARKED_PIECES, repeat=size)]


def read_constants(names):
    """The arguments of ``R(n1, …, nk)`` as the reader gives them, for ``k`` symbols of the sort ``S`` named ``names``."""
    declarations = "".join(f"(declare-fun |{name}| () S)" for name in names)
    text = (f"(declare-sort S 0){declarations}(declare-fun R ({' '.join('S' for _ in names)}) Bool)"
            f"(assert (R {' '.join('|' + name + '|' for name in names)}))")
    [atom] = parse_smtlib(text)
    return list(atom.args)


def test_two_symbols_of_a_text_are_never_read_as_one_name_for_any_two_of_the_names_made_of_a_c_v():
    # 39 names: every string of one, two or three of the pieces ``a``, ``!c``, ``!v``; every pair of them
    names = names_of_up_to(3)
    for first, second in itertools.combinations(names, 2):
        read = read_constants([first, second])
        assert read[0] != read[1], (first, second, read)


def test_the_chain_of_a_name_and_its_escapes_is_read_as_that_many_names():
    # a, a!c, a!c!c, a!c!c!c: each name is the escape of the one before it, or the name of its own
    for stem in ("a", "a!c", "a!v", "a!c!v", "!c"):
        chain = [stem + "!c" * i for i in range(5)]
        for size in range(1, 6):
            for subset in itertools.combinations(chain, size):
                read = read_constants(list(subset))
                assert len(set(read)) == len(subset), (subset, read)


def test_sets_of_marked_names_are_read_as_that_many_names():
    rng = random.Random(20261005)
    names = names_of_up_to(3)
    for _ in range(300):
        subset = rng.sample(names, rng.randint(3, 7))
        read = read_constants(subset)
        assert len(set(read)) == len(subset), (subset, read)


def test_a_symbol_is_read_as_the_name_the_writer_gave_it_wherever_the_text_holds_no_other_symbol_of_that_name():
    # the writer's own names: the constant a!c is the symbol a!c!c, and the plain a!c is nobody's
    assert read_constants(["a!c!c"]) == [Constant("a!c")]
    assert read_constants(["a!c"]) == [Constant("a!c")]
    assert read_constants(["a!c", "a!c!c"]) == [Constant("a!c"), Constant("a!c!c")]
    assert read_constants(["a!c", "a!c!c", "a!c!c!c"]) == [Constant("a!c"), Constant("a!c!c"), Constant("a!c!c!c")]
    assert read_constants(["a!c!c!c"]) == [Constant("a!c!c")]
    assert read_constants(["a!v!c", "a!v"]) == [Constant("a!v"), Variable("a")]


def test_a_symbol_is_read_under_one_name_whatever_the_order_of_the_declarations():
    names = ["a!c!c!c", "a!c", "a!c!c", "a"]
    reading = dict(zip(names, read_constants(names)))
    assert reading == {"a": Constant("a"), "a!c": Constant("a!c"), "a!c!c": Constant("a!c!c"),
                       "a!c!c!c": Constant("a!c!c!c")}
    for order in itertools.permutations(names):
        assert dict(zip(order, read_constants(list(order)))) == reading, order


def test_what_the_kit_writes_for_a_set_of_marked_names_reads_back_as_those_names():
    names = ["a", "a!c", "a!v", "a!c!c", "a!v!c", "a!v!v", "!c", "!v", "a!c!v"]
    atom = Atom("R", [Constant(name) for name in names] + [Variable("a")])
    for formula in (atom, Quantifier("∀", Variable("a"), atom)):
        assert from_z3(formula.to_z3(Z3Env())) == formula


def test_one_expression_with_the_two_symbols_is_read_as_two_constants_too():
    sort = z3.DeclareSort("S")
    first, second = z3.Const("a!c", sort), z3.Const("a!c!c", sort)
    atom = from_z3(z3.Function("R", sort, sort, z3.BoolSort())(first, second))
    assert atom == Atom("R", [Constant("a!c"), Constant("a!c!c")])


# ---------------------------------------------------------------------------------------------------------
# what cvc5 reports back
# ---------------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("text, reverse, expected", [
    ("(Q |is n<|)", {"n<": "<"}, "(Q |is n<|)"),                         # another name, quoted: a token inside it is not one
    ("(Q |a n< b|)", {"n<": "<"}, "(Q |a n< b|)"),
    ("(Q |n< a|)", {"n<": "<"}, "(Q |n< a|)"),
    ("(n< a |x n<|)", {"n<": "<"}, "(< a |x n<|)"),                      # a whole symbol next to such a name
    ("(Q |is n<| n<)", {"n<": "<"}, "(Q |is n<| <)"),
    ("|n<|", {"n<": "<"}, "|<|"),                                        # the token as a quoted symbol, which it is
    ("(Q |n<| n<)", {"n<": "<"}, "(Q |<| <)"),
    ("(P \"n< |\" n<)", {"n<": "<"}, "(P \"n< |\" <)"),                  # a pipe in a string opens no quoted symbol
    ("; |\n(n< a b)", {"n<": "<"}, "; |\n(< a b)"),                      # nor one in a comment
    ("(n+ |a n+| (n+ b c))", {"n+": "+"}, "(+ |a n+| (+ b c))"),
    ("(nselect a |nselect|)", {"nselect": "select"}, "(select a |select|)"),
])
def test_a_token_is_renamed_back_only_as_a_whole_symbol(text, reverse, expected):
    assert _reverse_map_smtlib_text(text, reverse) == expected


_CORE_CHILD = r'''
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import And, Atom, Constant
a, b, c = Constant("a"), Constant("b"), Constant("is n<")
premises = [Atom("<", [a, b]), Atom("Q", [c])]
goal = And(Atom("<", [a, b]), Atom("Q", [c]))
verdict = Cvc5Backend().decide(goal, premises, timeout=10000, proof=sys.argv[1] == "proof")
print(json.dumps({"status": verdict.status, "core": (verdict.proof or {}).get("unsat_core"),
                  "text": (verdict.proof or {}).get("text")}))
'''


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
def test_the_unsat_core_names_the_constant_the_problem_has_and_no_other():
    # a < b, Q(c) ⊢ a < b ∧ Q(c) with the constant c named ``is n<``: the predicate ``<`` is a symbol of SMT-LIB
    # and is renamed to the token ``n<``, and the constant ``is n<`` is a legal name that is written as it is
    code, out, err = run_child(_CORE_CHILD, "core")
    assert code == 0, err[-500:]
    answer = json.loads(out)
    assert answer["status"] == "proved"
    core = " ".join(answer["core"])
    assert "(Q |is n<|)" in core and "(< a b)" in core, answer
    assert "|is <|" not in core and "n<" not in core.replace("|is n<|", ""), answer


@pytest.mark.skipif(not HAS_CVC5, reason="cvc5 is not installed")
def test_the_proof_text_names_the_constant_the_problem_has_and_no_other():
    # the same problem, with the Alethe text asked for: its assumptions are the premises as the caller wrote them
    code, out, err = run_child(_CORE_CHILD, "proof")
    assert code == 0, err[-500:]
    answer = json.loads(out)
    assert answer["status"] == "proved"
    if answer["text"] is None:
        pytest.skip("cvc5 gave no proof text on this machine")
    assert "(Q |is n<|)" in answer["text"] and "(< a b)" in answer["text"], answer["text"]
    assert "|is <|" not in answer["text"], answer["text"]
