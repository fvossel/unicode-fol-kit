"""The names of the problem and the names the kit mints never meet, on Z3, on cvc5 and in the SMT-LIB text.

Every expectation is derived by hand (the structure that is a countermodel, or the sentence that is the
proof), and written down next to the test. The decision procedures read the problem under ONE universe;
a proposition is a predicate of no arguments.

* **Tracking literals.** The Z3 backend asserts the negated goal and each premise under a Boolean tag, to
  read an unsat core back. A proposition spelled like a tag would BE the tag, assumed true, and prove any
  goal; the tags are constants with an integer symbol, which no name of a problem is.
* **Witnesses.** A counting quantifier is expanded into distinct witnesses, and a sort gets a non-emptiness
  axiom with a witness of its own. In an SMT-LIB text a bound variable and a predicate, a function or a sort
  of the same spelling are ONE identifier (``(exists ((x0 S)) (x0 x0))``), which cvc5 answers by ending the
  process; so a witness is a name that no symbol of the problem has. Every cvc5 call that could end the
  process runs in a CHILD process.
* **The escape of the Z3 environment** (``a!v`` is written ``a!v!c``) and **the tokens of the sanitiser**
  never read as another symbol, and what cvc5 reports back carries the caller's names.
"""
import json
import subprocess
import sys

import pytest
import z3

from unicode_fol_kit import api
from unicode_fol_kit.atp import cvc5_backend
from unicode_fol_kit.atp.cvc5_backend import _SMTLIB_THEORY_SYMBOLS, _sanitize_many_for_smtlib
from unicode_fol_kit.atp.incremental import IncrementalSession
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, Z3Backend, z3_relevant_premises
from unicode_fol_kit.atp.z3_input import parse_smtlib, to_smtlib
from unicode_fol_kit.atp.z3_models import is_satisfiable
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Quantifier, SortedConstant, SortedCount,
    SortedQuantifier, Variable,
)

X, Y, W = Variable("x"), Variable("y"), Variable("w")


def prop(name):
    return Atom(name, [])


def P(*args):
    return Atom("P", list(args))


# ---------------------------------------------------------------------------------------------------------
# the tracking literals of the Z3 backend
# ---------------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["goal", "p0", "p1"])
def test_a_proposition_named_like_a_tag_is_not_valid(name):
    # ⊢ name: the universe {0} with the proposition false is a countermodel
    verdict = Z3Backend().decide(prop(name), [])
    assert verdict.status == REFUTED
    assert verdict.countermodel["assignment"] == {name: "False"}


def test_a_premise_that_is_no_help_does_not_prove_a_proposition_named_p0():
    # R ⊢ p0: R true, p0 false
    verdict = Z3Backend().decide(prop("p0"), [prop("R")])
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == {"R", "p0"}
    assert verdict.countermodel["assignment"]["p0"] == "False"


@pytest.mark.parametrize("premises, goal, countermodel", [
    ([Not(prop("p0"))], prop("Q"), {"p0": "False", "Q": "False"}),                       # ¬p0 ⊢ Q
    ([prop("A"), Not(prop("p1"))], prop("Q"), {"A": "True", "p1": "False", "Q": "False"}),   # A, ¬p1 ⊢ Q
    ([Not(prop("goal"))], prop("Q"), {"goal": "False", "Q": "False"}),                    # ¬goal ⊢ Q
    ([prop("p1")], prop("p0"), {"p1": "True", "p0": "False"}),                            # p1 ⊢ p0
])
def test_propositions_named_like_tags_have_the_countermodel_written_down(premises, goal, countermodel):
    verdict = Z3Backend().decide(goal, premises)
    assert verdict.status == REFUTED
    assert verdict.countermodel["assignment"] == countermodel


def test_the_default_chain_does_not_prove_a_proposition_named_goal():
    assert api.prove(prop("goal"), []).status == REFUTED


def test_a_valid_problem_over_propositions_named_like_tags_is_proved_with_both_premises_relevant():
    # p0, p0 → p1 ⊢ p1: valid (modus ponens), and neither premise alone proves p1, so both are relevant
    premises = [prop("p0"), Implies(prop("p0"), prop("p1"))]
    verdict = Z3Backend().decide(prop("p1"), premises)
    assert verdict.status == PROVED
    # the proof names the tags it reports, ``goal`` and ``p<i>`` (0-based premise numbers)
    assert verdict.proof["core"] == ["goal", "p0", "p1"]
    assert z3_relevant_premises(prop("p1"), premises) == (0, 1)


def test_a_symbol_spelled_like_the_text_of_a_tag_is_still_no_tag():
    # Z3 prints an integer symbol as ``k!<number>``; a proposition that is spelled so is another symbol
    from unicode_fol_kit.atp.protocol import _z3_tag
    tag = _z3_tag(1)
    names = [str(tag), str(_z3_tag(0))]
    assert names[0] != names[1]
    verdict = Z3Backend().decide(prop(names[0]), [prop(names[1])])        # k!… ⊢ k!… (the other one)
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == set(names)
    assert z3_relevant_premises(prop(names[0]), [prop(names[1])]) is None


def test_a_tag_is_recognised_by_its_symbol_and_nothing_else_is():
    from unicode_fol_kit.atp.protocol import _z3_tag, _z3_tag_number
    assert _z3_tag_number(_z3_tag(0).decl()) == 0
    assert _z3_tag_number(_z3_tag(7).decl()) == 7
    assert _z3_tag_number(z3.Bool("goal").decl()) is None
    assert _z3_tag_number(z3.Bool("p0").decl()) is None
    assert _z3_tag_number(z3.Function("P", z3.IntSort(), z3.BoolSort())) is None


# ---------------------------------------------------------------------------------------------------------
# witnesses, on every route: Z3, the SMT-LIB text, cvc5 (in a child process)
# ---------------------------------------------------------------------------------------------------------
def counting_ge2(variable, body):
    return Count("ge", Number(2), variable, body)


# problems that are NOT valid, each with the countermodel (universe {0, 1}) that makes it so:
#  nullary_function_x0:  ∃≥1 x R(x, x0) ⊬ ∃y R(y, y)   x0 = 1, R = {(0, 1)}: x = 0 has R(0, 1); no y has R(y, y)
#  proposition_x0:       ⊬ ∃≥2 x x0                     the proposition x0 false: no element satisfies it
#  function_x0:          ⊬ ∃≥2 x P(x0(x))              P = {}: no element satisfies P(x0(x))
#  sort_x1_variable_x0:  ∀y:x1 ∀x0 R(x0, y) ⊬ Q(a)     Q = {}: the premise says nothing about Q
#  sorted_constant_x0:   R(c:x0) ⊬ Q(a)                 Q = {}
NOT_VALID = {
    "nullary_function_x0": (Quantifier("∃", Y, Atom("R", [Y, Y])),
                           [Count("ge", Number(1), X, Atom("R", [X, Function("x0", [])]))]),
    "proposition_x0": (counting_ge2(X, prop("x0")), []),
    "function_x0": (counting_ge2(X, P(Function("x0", [X]))), []),
    "sort_x1_variable_x0": (Atom("Q", [Constant("a")]),
                            [SortedQuantifier("∀", Y, "x1", Quantifier(
                                "∀", Variable("x0"), Atom("R", [Variable("x0"), Y])))]),
    "sorted_constant_x0": (Atom("Q", [Constant("a")]), [Atom("R", [SortedConstant("c", "x0")])]),
}

# problems that ARE valid, each with its proof:
#  sort_x0:              ⊢ ∃w:x0 x0(w)       the sort x0 is non-empty: some w is in x0, and x0(w) is that membership
#  count_over_predicate: ⊢ ¬∃≥2 y (y0(y) ∧ ¬y0(y))   no y satisfies a contradiction, so fewer than two do
#  count_of_function:    ∃≥2 x P(x0(x)) ⊢ ∃≥2 x P(x0(x))    a premise entails itself
#  sorted_count:         ∃≥2 w:x0 R(w) ⊢ ∃≥2 w:x0 R(w)      the same
#  mark_escape:          a!v!c(a!v) ⊢ a!v!c(a!v)             the same, a predicate and a constant spelled alike
VALID = {
    "sort_x0": (SortedQuantifier("∃", W, "x0", Atom("x0", [W])), []),
    "count_over_predicate": (Not(counting_ge2(Y, And(Atom("y0", [Y]), Not(Atom("y0", [Y]))))), []),
    "count_of_function": (counting_ge2(X, P(Function("x0", [X]))), [counting_ge2(X, P(Function("x0", [X])))]),
    "sorted_count": (SortedCount("ge", Number(2), W, "x0", Atom("R", [W])),
                     [SortedCount("ge", Number(2), W, "x0", Atom("R", [W]))]),
    "mark_escape": (Atom("a!v!c", [Constant("a!v")]), [Atom("a!v!c", [Constant("a!v")])]),
}

_CASES = {**{name: (goal, premises, {}) for name, (goal, premises) in NOT_VALID.items()},
          **{name: (goal, premises, {}) for name, (goal, premises) in VALID.items()}}
_CASES.update({
    # the names of SMT-LIB's own vocabulary under an explicit logic: P(c) ⊢ P(c), whatever c is called
    **{f"theory_{name}": (Atom("P", [Constant(name)]), [Atom("P", [Constant(name)])], {"logic": "ALL"})
       for name in ("sep", "pto", "wand", "str.indexof_re", "tuple.unit")},
    "keys_of_a_constant_named_a!c": (prop("Q"), [P(Constant("a!c"))], {}),
    "keys_of_a_constant_named_x!v!c": (prop("Q"), [P(Constant("x!v!c"))], {}),
    "core_of_a_predicate_named_<": (Atom("<", [Constant("a"), Constant("b")]), [Atom("<", [Constant("a"), Constant("b")])],
                                   {"proof": True}),
    "core_of_a_function_named_+": (P(Function("+", [Constant("a"), Constant("b")])),
                                   [P(Function("+", [Constant("a"), Constant("b")]))], {"proof": True}),
})

_CHILD = r"""
import json, sys
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.fol.nodes import Node

for line in sys.stdin.read().splitlines():
    spec = json.loads(line)
    print(json.dumps({"case": spec["case"], "status": "started"}), flush=True)
    premises = [Node.from_dict(d) for d in spec["premises"]]
    goal = Node.from_dict(spec["goal"])
    verdict = Cvc5Backend().decide(goal, premises, timeout=20000, **spec["options"])
    proof = verdict.proof or {}
    countermodel = verdict.countermodel or {}
    print(json.dumps({"case": spec["case"], "status": verdict.status,
                      "keys": sorted(countermodel.get("assignment", {})),
                      "core": proof.get("unsat_core"), "text": proof.get("text")}), flush=True)
"""


@pytest.fixture(scope="module")
def cvc5():
    """The answer of ``Cvc5Backend`` to every case, from ONE child process (which must not die)."""
    pytest.importorskip("cvc5")
    lines = "\n".join(json.dumps({"case": name, "goal": goal.to_dict(), "premises": [p.to_dict() for p in premises],
                                  "options": options})
                      for name, (goal, premises, options) in _CASES.items())
    done = subprocess.run([sys.executable, "-c", _CHILD], input=lines, capture_output=True, text=True,
                          encoding="utf-8", timeout=900)
    answers = [json.loads(line) for line in done.stdout.splitlines()]
    assert done.returncode == 0, (
        f"the cvc5 child process ended with exit code {done.returncode & 0xFFFFFFFF:#x} on the case "
        f"{answers[-1]['case'] if answers else '?'}")
    return {a["case"]: a for a in answers if a["status"] != "started"}


@pytest.mark.parametrize("name", sorted(NOT_VALID))
def test_a_problem_with_a_countermodel_is_refuted_by_z3_and_never_proved_by_cvc5(name, cvc5):
    goal, premises = NOT_VALID[name]
    assert Z3Backend().decide(goal, premises).status == REFUTED
    assert IncrementalSession(premises).decide(goal).status == REFUTED
    assert cvc5[name]["status"] in (REFUTED, UNKNOWN)


@pytest.mark.parametrize("name", sorted(VALID))
def test_a_valid_problem_is_proved_by_z3_and_by_cvc5(name, cvc5):
    goal, premises = VALID[name]
    assert Z3Backend().decide(goal, premises).status == PROVED
    assert IncrementalSession(premises).decide(goal).status == PROVED
    assert cvc5[name]["status"] == PROVED


def test_the_text_of_a_counting_quantifier_over_a_predicate_named_like_the_witness_reads_back():
    # ∃≥2 y y0(y): the text holds two witnesses that are not called y0 (the predicate's name), and it reads
    # back as a formula that says "at least two things are y0"
    formula = counting_ge2(Y, Atom("y0", [Y]))
    text = to_smtlib(formula)
    assert "(exists ((y0 S))" not in text
    [back] = parse_smtlib(text)
    solver = z3.Solver()
    for premise, goal in ((formula, back), (back, formula)):
        solver.push()
        solver.add(premise.to_z3(), z3.Not(goal.to_z3()))
        assert solver.check() == z3.unsat
        solver.pop()


def test_the_text_of_a_counting_quantifier_over_a_nullary_function_x0_keeps_the_function():
    # ∃≥1 x R(x, x0) with the constant x0, and the negated goal ∃y R(y, y): satisfiable (the countermodel
    # above). The text must declare x0 and bind a witness of another name.
    goal, [premise] = NOT_VALID["nullary_function_x0"]
    text = to_smtlib(Not(goal), [premise])
    assert "(declare-fun x0 () S)" in text
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(text))
    assert solver.check() == z3.sat


def test_the_text_of_a_sort_named_x0_is_read_by_z3():
    # sort axiom witnesses are asked for by the caller; the text of the axiom must be a sentence
    from unicode_fol_kit.fol._msfl_nodes import sort_axioms
    goal, premises = VALID["sort_x0"]
    text = to_smtlib(goal, list(sort_axioms(goal)))
    assert len(z3.parse_smt2_string(text)) == 2


# ---------------------------------------------------------------------------------------------------------
# the escape of the Z3 environment, the tokens of the sanitiser, and what is reported back
# ---------------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["a!c", "a!v", "!v", "!c", "x!v!c", "x!c!v", "a!c!c"])
@pytest.mark.parametrize("kind", ["constant", "variable"])
def test_no_token_of_a_constant_or_a_variable_ends_in_a_mark_of_the_z3_codec(name, kind):
    node = Constant(name) if kind == "constant" else Variable(name)
    sanitised, names = _sanitize_many_for_smtlib([Atom("P", [node])])
    [token] = [t for t, original in names.reverse().items() if original == name]
    assert not token.endswith(("!v", "!c")), token
    assert sanitised[0].args[0].name == token
    assert names.reverse()[token] == name                    # and the caller's name is what it stands for


def test_a_predicate_spelled_like_the_escape_of_a_constant_is_not_that_constant():
    # a!v!c(a!v): the predicate a!v!c of one argument, applied to the constant a!v. The Z3 environment writes
    # the constant a!v as the symbol ``a!v!c``, the predicate's very spelling.
    goal = Atom("a!v!c", [Constant("a!v")])
    text = to_smtlib(goal, [goal])
    declared = [line.split()[1] for line in text.splitlines() if line.startswith("(declare-fun")]
    assert len(declared) == len(set(declared)) == 2, declared
    nodes = parse_smtlib(text)
    assert len(nodes) == 2 and nodes[0] == nodes[1]
    assert nodes[0].predicate == "a!v!c" and isinstance(nodes[0].args[0], Constant)


@pytest.mark.parametrize("spelling", ["a!c", "x!v!c"])
def test_cvc5_and_z3_report_a_constant_under_its_own_name(spelling, cvc5):
    # P(c) ⊢ Q: the countermodel has the symbols P, Q and the constant, each under the caller's name
    premise, goal = P(Constant(spelling)), prop("Q")
    z3_keys = set(Z3Backend().decide(goal, [premise]).countermodel["assignment"])
    assert z3_keys == {"P", "Q", spelling}
    assert set(cvc5[f"keys_of_a_constant_named_{spelling}"]["keys"]) == z3_keys


def test_a_free_variable_a_constant_of_its_name_and_a_constant_spelled_like_its_symbol_have_three_keys():
    # P(x) (the variable), P(x) (the constant), P(x!v) (the constant spelled so) ⊢ Q: three symbols, and the
    # constants keep their plain names, the variable takes the first spelling that is nobody's
    premises = [P(Variable("x")), P(Constant("x")), P(Constant("x!v"))]
    keys = set(Z3Backend().decide(prop("Q"), premises).countermodel["assignment"])
    assert keys == {"P", "Q", "x", "x!v", "x!v!v"}


@pytest.mark.parametrize("case, token", [("core_of_a_predicate_named_<", "n<"), ("core_of_a_function_named_+", "n+")])
def test_the_unsat_core_and_the_proof_text_carry_the_names_of_the_caller(case, token, cvc5):
    answer = cvc5[case]
    assert answer["status"] == PROVED
    assert answer["core"], answer
    assert all(token not in term for term in answer["core"]), answer["core"]
    if answer["text"] is not None:
        assert token not in answer["text"]


def test_the_core_of_a_predicate_named_less_than_is_written_with_that_name(cvc5):
    # a < b ⊢ a < b: the core is the premise and the negated goal, as the caller wrote them
    assert cvc5["core_of_a_predicate_named_<"]["core"] == ["(< a b)", "(not (< a b))"]
    assert cvc5["core_of_a_function_named_+"]["core"] == ["(P (+ a b))", "(not (P (+ a b)))"]


@pytest.mark.parametrize("text, reverse, expected", [
    ("(n< a b)", {"n<": "<"}, "(< a b)"),
    ("(n+ a (n+ b c))", {"n+": "+"}, "(+ a (+ b c))"),
    ("(n<= a b)", {"n<": "<", "n<=": "<="}, "(<= a b)"),               # the longer token wins
    ("(n<x a)", {"n<": "<"}, "(n<x a)"),                                # not a whole symbol
    ("(xn< a)", {"n<": "<"}, "(xn< a)"),                                # not a whole symbol
    ("(nselect a b)", {"nselect": "select"}, "(select a b)"),
    ("|n<|", {"n<": "<"}, "|<|"),                                       # inside a quoted symbol
    ("(P a)", {"P": "P"}, "(P a)"),                                     # a name left as it is
])
def test_reverse_mapping_of_smtlib_text_reads_whole_symbols(text, reverse, expected):
    from unicode_fol_kit.atp.cvc5_backend import _reverse_map_smtlib_text
    assert _reverse_map_smtlib_text(text, reverse) == expected


# ---------------------------------------------------------------------------------------------------------
# the names cvc5 knows under every logic
# ---------------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["sep", "pto", "wand", "str.indexof_re", "tuple.unit"])
def test_a_constant_named_like_a_cvc5_symbol_is_proved_under_logic_all(name, cvc5):
    assert name in _SMTLIB_THEORY_SYMBOLS
    assert cvc5[f"theory_{name}"]["status"] == PROVED          # and the process is alive to say so
    sanitised, names = _sanitize_many_for_smtlib([Atom("P", [Constant(name)])])
    assert sanitised[0].args[0].name != name


# ---------------------------------------------------------------------------------------------------------
# reading a text back
# ---------------------------------------------------------------------------------------------------------
PRELUDE = "(declare-sort S 0)(declare-fun P (S) Bool)(declare-fun Q () Bool)"


@pytest.mark.parametrize("name", ["inf", "infinity", "Infinity", "nan", "NaN", "+5", "1_000", "5.", "٣", "５"])
def test_a_symbol_that_python_reads_as_a_number_but_the_kit_never_writes_is_a_constant(name):
    # the kit writes the numeral 5 as ``5``, 2.5 as ``2.5``, 1e-07 as ``1e-07``: only those are numbers
    [back] = parse_smtlib(f"{PRELUDE}(declare-fun |{name}| () S)(assert (P |{name}|))")
    assert back == Atom("P", [Constant(name)])


@pytest.mark.parametrize("name, number", [("5", 5), ("-3", -3), ("0", 0), ("2.5", 2.5), ("1e-07", 1e-07)])
def test_a_symbol_that_is_the_text_of_a_finite_number_is_that_number(name, number):
    [back] = parse_smtlib(f"{PRELUDE}(declare-fun |{name}| () S)(assert (P |{name}|))")
    assert back == Atom("P", [Number(number)])


def test_two_constants_that_python_would_read_as_one_number_stay_two():
    # P(inf) ∧ ¬P(infinity): satisfiable (inf = 0, infinity = 1, P = {0}); read as one number it is not
    f = And(P(Constant("inf")), Not(P(Constant("infinity"))))
    [back] = parse_smtlib(to_smtlib(f))
    assert back == f
    assert is_satisfiable(back)


def test_a_text_that_binds_a_name_and_its_marked_form_binds_two_variables():
    # ∀a!v ∀a (P2(a!v, a) → Q), P2(c1, c2), ¬Q: unsatisfiable (instantiate a!v = c1, a = c2). Read with the mark
    # stripped it would be ∀a ∀a (P2(a, a) → Q), which holds in a structure with P2 = {(c1, c2)}, c1 ≠ c2, Q false.
    text = ("(declare-sort S 0)(declare-fun P2 (S S) Bool)(declare-fun Q () Bool)"
            "(declare-fun c1 () S)(declare-fun c2 () S)"
            "(assert (forall ((a!v S) (a S)) (=> (P2 a!v a) Q)))(assert (P2 c1 c2))(assert (not Q))")
    nodes = parse_smtlib(text)
    outer = nodes[0]
    assert outer.variable.name != outer.formula.variable.name
    assert not is_satisfiable(And(And(nodes[0], nodes[1]), nodes[2]))


def test_a_marked_name_that_nothing_else_uses_is_read_as_the_variable_it_was_written_for():
    # to_z3 writes the variable x as the symbol x!v; the way back reads it as x
    f = Quantifier("∀", X, P(X))
    from unicode_fol_kit.atp.z3_input import from_z3
    assert from_z3(f.to_z3()) == f


def test_a_free_marked_symbol_next_to_a_bound_variable_of_its_stripped_name_is_not_captured():
    # ∀a P2(a, a!v): the free symbol a!v is a parameter and stays one: reading it as the variable a would let the
    # quantifier bind it (∀a P2(a, a)), a stronger sentence
    text = "(declare-sort S 0)(declare-fun P2 (S S) Bool)(declare-fun a!v () S)(assert (forall ((a S)) (P2 a a!v)))"
    [back] = parse_smtlib(text)
    assert back == Quantifier("∀", Variable("a"), Atom("P2", [Variable("a"), Variable("a!v")]))


def test_two_free_symbols_one_of_which_is_the_escape_of_the_other_are_two_constants():
    # P(n) ∧ ¬P(n!c): the symbol n!c is written for no constant (the constant n is written n), so it is the
    # constant named n!c, not n: satisfiable
    text = f"{PRELUDE}(declare-fun n () S)(declare-fun n!c () S)(assert (and (P n) (not (P n!c))))"
    [back] = parse_smtlib(text)
    assert back == And(P(Constant("n")), Not(P(Constant("n!c"))))
    assert is_satisfiable(back)


# ---------------------------------------------------------------------------------------------------------
# a name Z3 cannot carry
# ---------------------------------------------------------------------------------------------------------
#: Z3 reads a name as a C string, which ends at a NUL: ``a\x00b``, ``a\x00c`` and ``a`` would be one symbol
#: (so ``⊢ a\x00b = a\x00c`` would be "proved"; the two constants are different things, and the problem is not
#: valid), ``\x00`` and the empty name too. A lone surrogate is no text at all.
UNCARRIABLE = [
    Atom("=", [Constant("a\x00b"), Constant("a\x00c")]),
    Atom("=", [Constant("a\x00b"), Constant("a")]),
    Atom("=", [Constant("\x00"), Constant("")]),
    P(Constant("\ud800")),
    Atom("\x00x", []),
    P(Function("f\x00", [Constant("a")])),
    SortedQuantifier("∃", W, "S\x00", prop("Q")),
]


@pytest.mark.parametrize("goal", UNCARRIABLE)
def test_a_name_that_z3_cannot_carry_is_refused_by_name_on_every_z3_route(goal):
    verdict = Z3Backend().decide(goal, [])
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
    assert "NUL" in verdict.detail or "surrogate" in verdict.detail
    assert z3_relevant_premises(goal, []) is None
    answer = api.prove(goal, [], backends=["z3"])
    assert answer.status == UNKNOWN
    assert "NUL" in (answer.detail or "") or "surrogate" in (answer.detail or "")
    with pytest.raises(NotImplementedError):
        goal.to_z3()
    with pytest.raises(NotImplementedError):
        IncrementalSession([goal])


@pytest.mark.parametrize("goal", UNCARRIABLE)
def test_a_name_that_z3_cannot_carry_is_refused_by_cvc5_too(goal):
    pytest.importorskip("cvc5")
    verdict = cvc5_backend.Cvc5Backend().decide(goal, [])        # refused before cvc5 is asked
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"


def test_a_nul_in_a_name_is_not_a_proof_of_anything():
    # the default chain may answer from another member; it never proves ⊢ a\x00b = a\x00c
    assert api.prove(UNCARRIABLE[0], []).status != PROVED


def test_a_name_that_z3_cannot_carry_is_refused_by_the_arithmetic_translation(arith):
    for goal in UNCARRIABLE[:4]:
        with pytest.raises(NotImplementedError):
            arith.is_valid_arith(goal)


# ---------------------------------------------------------------------------------------------------------
# the text of a truth constant
# ---------------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("premises, goal", [
    ([], Atom("⊤", [])),
    ([P(Constant("a"))], Atom("⊤", [])),
    ([Atom("⊤", [])], P(Constant("a"))),
    ([Atom("⊤", []), P(Constant("a"))], Atom("⊤", [])),
    ([], Atom("⊥", [])),
    ([P(Constant("a"))], Atom("⊥", [])),
])
def test_every_formula_of_the_problem_is_one_assertion_of_its_text(premises, goal):
    text = to_smtlib(goal, premises)
    assert text.count("(assert") == len(premises) + 1
    assert len(parse_smtlib(text)) == len(premises) + 1


def test_the_text_of_a_lone_true_reads_back_as_true():
    [back] = parse_smtlib(to_smtlib(Atom("⊤", [])))
    assert back == Atom("$true", [])


# ---------------------------------------------------------------------------------------------------------
# counting in the arithmetic translation
# ---------------------------------------------------------------------------------------------------------
@pytest.fixture(scope="module")
def arith():
    from unicode_fol_kit.atp import z3_arith
    return z3_arith


def between_0_and_3(variable=X):
    return And(Atom(">", [variable, Number(0)]), Atom("<", [variable, Number(3)]))


@pytest.mark.parametrize("op, bound, sort, valid, satisfiable", [
    # over the integers exactly 1 and 2 lie strictly between 0 and 3
    ("ge", 2, "int", True, True), ("ge", 3, "int", False, False), ("eq", 2, "int", True, True),
    ("le", 1, "int", False, False), ("le", 2, "int", True, True),
    # over the reals infinitely many do
    ("ge", 3, "real", True, True), ("eq", 2, "real", False, False), ("le", 5, "real", False, False),
])
def test_a_counting_quantifier_is_counted_in_the_theory_of_numbers(arith, op, bound, sort, valid, satisfiable):
    formula = Count(op, Number(bound), X, between_0_and_3())
    assert arith.is_valid_arith(formula, sort=sort) is valid
    assert arith.is_satisfiable_arith(formula, sort=sort) is satisfiable


def test_a_counting_quantifier_next_to_a_constant_spelled_like_its_witness_is_translated(arith):
    # ∃≥2 x (x > x0) with the constant x0, over the integers: x0 + 1 and x0 + 2. Valid.
    formula = Count("ge", Number(2), X, Atom(">", [X, Constant("x0")]))
    assert arith.is_valid_arith(formula, sort="int") is True
    # ∃≥1 x (x > x0 ∧ x < x0) is false whatever x0 is
    empty = Count("ge", Number(1), X, And(Atom(">", [X, Constant("x0")]), Atom("<", [X, Constant("x0")])))
    assert arith.is_satisfiable_arith(empty, sort="int") is False


def test_a_counting_quantifier_is_translated_as_its_expansion_is(arith):
    formula = Count("eq", Number(2), X, between_0_and_3())
    assert z3.eq(arith.to_z3_arith(formula, arith.ArithEnv("int")),
                 arith.to_z3_arith(formula._expand(), arith.ArithEnv("int")))
