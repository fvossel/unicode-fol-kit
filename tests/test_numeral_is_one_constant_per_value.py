"""A numeral is a constant, named by its VALUE, on every route that was not asked for arithmetic.

``Number(1) == Number(1.0)`` is ``True`` in the kit (they hash alike), so ``1``, ``1.0`` and ``01`` are ONE
constant. Nothing else is known about a numeral: ``1`` and ``2`` may denote the same element, ``+ - * /`` are
uninterpreted function symbols and ``< > ≤ ≥`` uninterpreted binary predicates, ``=`` is equality.

The problems, each derived by hand (``one`` is an ordinary constant):

======  =======================================  =========  ==============================================
 #      problem                                  answer     why
======  =======================================  =========  ==============================================
 A1     ``∀x P(x) ⊢ P(1)``                       valid      instance
 A2     ``P(1) ⊢ P(1.0)``                        valid      one constant
 A3     ``⊢ 1 ≠ 2``                              not valid  one-element universe
 A4     ``⊢ 1 < 2``                              not valid  ``<`` empty
 A5     ``⊢ 1 + 1 = 2``                          not valid  universe {0, 1}: 1 ↦ 0, 2 ↦ 1, ``+`` constantly 0
 A6     ``P(1), P(2) ⊢ ∃x∃y (x≠y ∧ P(x) ∧ P(y))``  not valid  one-element universe
 A7     ``P(1) ⊢ P(one)``                        not valid  universe {0, 1}: 1 ↦ 0, one ↦ 1, P = {0}
 A8     ``∀x∀y x+y = y+x ⊢ 1+2 = 2+1``           valid      instance
 A9     ``∀x (x < 2 → Q(x)), 1 < 2 ⊢ Q(1)``      valid      instance and modus ponens
 A10    ``⊢ 2.5 = 2.5``                          valid      reflexivity
 A11    ``P(-1) ⊢ ∃x P(x)``                      valid      witness
======  =======================================  =========  ==============================================

A route answers a valid problem with ``proved`` (or says it does not know) and a problem that is not valid
with ``refuted`` (or says it does not know): never the opposite.
"""
import json
import subprocess
import sys

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import resolution
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, Z3Backend
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Number, Quantifier, Variable, Z3Env
from unicode_logic_kit.semantics.modelfinder import find_countermodel
from unicode_logic_kit.semantics.tarski import Structure, satisfies, term_value

# (label, premises, goal, valid)
A_PROBLEMS = [
    ("A1", ["∀x P(x)"], "P(1)", True),
    ("A2", ["P(1)"], "P(1.0)", True),
    ("A3", [], "1 ≠ 2", False),
    ("A4", [], "1 < 2", False),
    ("A5", [], "1 + 1 = 2", False),
    ("A6", ["P(1)", "P(2)"], "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", False),
    ("A7", ["P(1)"], "P(one)", False),
    ("A8", ["∀x ∀y x + y = y + x"], "1 + 2 = 2 + 1", True),
    ("A9", ["∀x (x < 2 → Q(x))", "1 < 2"], "Q(1)", True),
    ("A10", [], "2.5 = 2.5", True),
    ("A11", ["P(-1)"], "∃x P(x)", True),
]


def F(text):
    parsed = api.parse_any(text)
    assert parsed.ok, (text, parsed)
    return parsed.formula


def problem(label):
    for name, premises, goal, valid in A_PROBLEMS:
        if name == label:
            return [F(p) for p in premises], F(goal), valid
    raise KeyError(label)


# ---------------------------------------------------------------------------------------------
# what a numeral is called
# ---------------------------------------------------------------------------------------------
VALUES = [0, -0.0, 0.0, 1, 1.0, True, 2, 2.0, 2.5, -1, -1.0, 1e22, 10 ** 22, 1e23, 10 ** 23, 1e-07, 0.1]


def test_two_numerals_have_one_key_exactly_when_they_are_equal():
    from unicode_logic_kit.fol._fol_nodes import numeral_key
    for a in VALUES:
        for b in VALUES:
            assert (Number(a) == Number(b)) == (numeral_key(a) == numeral_key(b)), (a, b)


def test_the_key_of_a_numeral_is_the_text_of_its_value():
    from unicode_logic_kit.fol._fol_nodes import numeral_key
    assert [numeral_key(v) for v in (1, 1.0, -0.0, 2.5, -1, 1e16, 1e-07, 10 ** 22)] == [
        "1", "1", "0", "2.5", "-1", "10000000000000000", "1e-07", "10000000000000000000000"]


def test_the_parser_reads_one_two_spellings_as_equal_numerals():
    for text in ("P(1)", "P(1.0)", "P(01)"):
        assert F(text).args[0] == Number(1)


def test_a_numeral_is_one_z3_constant_for_every_spelling_of_its_value():
    one, spelled, other = Number(1).to_z3(), Number(1.0).to_z3(), Number(2).to_z3()
    assert one.eq(spelled) and not one.eq(other)
    env = Z3Env()
    assert Number(7).to_z3(env).eq(Number(7.0).to_z3(env))


# ---------------------------------------------------------------------------------------------
# the routes of the kit's own: Z3, the model finder, the tableau, resolution
# ---------------------------------------------------------------------------------------------
def _prove(label, backend):
    premises, goal, _ = problem(label)
    return api.prove(goal, premises, backends=[backend], timeout=20000)


@pytest.mark.parametrize("label", [name for name, *_ in A_PROBLEMS])
def test_z3_answers_every_problem_as_derived(label):
    _, _, valid = problem(label)
    assert _prove(label, "z3").status == (PROVED if valid else REFUTED)


@pytest.mark.parametrize("label", [name for name, *_ in A_PROBLEMS])
def test_the_model_finder_finds_a_countermodel_exactly_for_the_problems_that_are_not_valid(label):
    _, _, valid = problem(label)
    verdict = _prove(label, "modelfinder")
    assert verdict.status == (UNKNOWN if valid else REFUTED)       # a bounded search never proves


@pytest.mark.parametrize("label", [name for name, *_ in A_PROBLEMS])
def test_the_tableau_and_resolution_never_answer_the_opposite(label):
    _, _, valid = problem(label)
    for backend in ("tableau", "resolution"):
        status = _prove(label, backend).status
        assert status != (REFUTED if valid else PROVED), (label, backend, status)


@pytest.mark.parametrize("label", ["A1", "A2", "A8", "A9", "A11"])
def test_the_tableau_proves_the_valid_problems_it_can(label):
    assert _prove(label, "tableau").status == PROVED


@pytest.mark.parametrize("label", ["A1", "A2", "A8", "A9", "A10", "A11"])
def test_resolution_proves_every_valid_problem(label):
    # A8 ends in a RecursionError on an equation whose two sides are the same terms under another naming
    assert _prove(label, "resolution").status == PROVED


def test_the_model_finder_does_not_split_one_numeral_in_two():
    premises, goal, _ = problem("A2")
    assert find_countermodel(premises, goal) is None


def test_a_countermodel_has_one_entry_per_numeral_value():
    # ⊢ Q(1) ∧ Q(1.0) ∧ Q(01) ∧ Q(2): not valid; the numerals are the constants 1 and 2
    goal = F("Q(1) ∧ Q(1.0) ∧ Q(01) ∧ Q(2)")
    structure = find_countermodel([], goal)
    assert structure is not None
    assert set(structure.constants) == {"1", "2"}
    assert not satisfies(goal, structure, {})
    # and the Z3 countermodel: P(1), P(1.0), P(2) ⊬ Q(1.0)
    verdict = Z3Backend().decide(F("Q(1.0)"), [F("P(1)"), F("P(1.0)"), F("P(2)")])
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == {"1", "2", "P", "Q"}


def test_the_countermodel_of_the_distinct_numerals_has_one_element():
    premises, goal, _ = problem("A3")
    structure = find_countermodel(premises, goal)
    assert len(structure.domain) == 1 and structure.constants == {"1": 0, "2": 0}


def test_the_countermodel_of_the_sum_has_two_elements():
    # one element makes 1 + 1 = 2 true (everything is that element); the smallest structure that falsifies it has two
    premises, goal, _ = problem("A5")
    structure = find_countermodel(premises, goal)
    assert len(structure.domain) == 2 and not satisfies(goal, structure, {})


def test_the_evaluator_reads_a_numeral_through_the_name_of_its_value():
    structure = Structure({0, 1, 5}, constants={"1": 5, "2.5": 1})
    assert term_value(Number(1), structure, {}) == 5
    assert term_value(Number(1.0), structure, {}) == 5                    # the same constant
    assert term_value(Number(2.5), structure, {}) == 1
    assert term_value(Number(3), structure, {}) == 3                      # nothing declared: the number itself
    assert satisfies(Atom("=", [Number(1), Number(1.0)]), structure, {})


def test_the_operators_are_uninterpreted_for_the_model_finder_and_z3():
    # + and < are no arithmetic: ⊢ 1 + 1 = 2 and ⊢ 1 < 2 are not valid, and an instance of an axiom about them is
    assert Z3Backend().decide(F("1 + 1 = 2"), []).status == REFUTED
    assert Z3Backend().decide(F("1 < 2"), []).status == REFUTED
    assert Z3Backend().decide(F("1 + 1 = 1 + 1"), []).status == PROVED


def test_a_numeral_and_a_variable_spelled_alike_are_two_symbols_for_z3():
    # ∀v P(v, 1) with a variable v spelled 1 (no grammar writes one) binds the variable and not the numeral:
    # P(alpha, 1) follows from it, P(alpha, alpha) does not (the universe {0, 1}, 1 = 0, alpha = 1, P = {(0,0),(1,0)})
    variable = Variable("1")
    premise = Quantifier("∀", variable, Atom("P", [variable, Number(1)]))
    alpha = Constant("alpha")
    assert Z3Backend().decide(Atom("P", [alpha, Number(1)]), [premise]).status == PROVED
    assert Z3Backend().decide(Atom("P", [alpha, alpha]), [premise]).status == REFUTED


# ---------------------------------------------------------------------------------------------
# cvc5, in a child process
# ---------------------------------------------------------------------------------------------
_CHILD = r"""
import json, sys
from unicode_logic_kit import api
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend

out = []
for premises, goal in json.loads(sys.argv[1]):
    verdict = Cvc5Backend().decide(api.parse_any(goal).formula, [api.parse_any(p).formula for p in premises],
                                   timeout=20000)
    out.append({"status": verdict.status, "assignment": (verdict.countermodel or {}).get("assignment")})
print(json.dumps(out))
"""


def test_cvc5_answers_every_problem_without_the_opposite_answer():
    pytest.importorskip("cvc5")
    spec = json.dumps([(premises, goal) for _, premises, goal, _ in A_PROBLEMS])
    done = subprocess.run([sys.executable, "-c", _CHILD, spec], capture_output=True, text=True,
                          encoding="utf-8", timeout=600)
    assert done.returncode == 0, done.stderr[-400:]
    answers = json.loads(done.stdout.strip().splitlines()[-1])
    for (label, _, _, valid), answer in zip(A_PROBLEMS, answers):
        if valid:
            assert answer["status"] == "proved", (label, answer["status"])      # every valid one is within cvc5's reach
        else:
            assert answer["status"] != "proved", (label, answer["status"])
    by_label = {label: answer for (label, *_), answer in zip(A_PROBLEMS, answers)}
    # the countermodel of P(1) ⊬ P(one) names the numeral by its value and the constant as it is
    assert by_label["A7"]["status"] == "refuted" and set(by_label["A7"]["assignment"]) == {"1", "one", "P"}


# ---------------------------------------------------------------------------------------------
# resolution: the matcher of a demodulation is one-sided and is not followed through its own bindings
# ---------------------------------------------------------------------------------------------
X, Y, Z = Variable("x"), Variable("y"), Variable("z")


def test_a_matcher_that_binds_a_variable_to_a_variable_it_binds_is_applied_in_one_step():
    # the rule f(x, y) → g(x) against P(f(y, z)) ∨ Q(y) matches {x: y, y: z}: the instance of the rule is
    # f(y, z) = g(y), so the clause becomes P(g(y)) ∨ Q(y). Following the chain would read x as z and give
    # P(g(z)) ∨ Q(y), which does not follow (g(z) is not g(y)). (The old expectation, None, was the prover
    # declining to rewrite at all, because it could not apply this matcher correctly.)
    rule = (Function("f", [X, Y]), Function("g", [X]))
    clause = frozenset([Atom("P", [Function("f", [Y, Z])]), Atom("Q", [Y])])
    assert resolution._demodulate_once(clause, [rule]) == frozenset(
        [Atom("P", [Function("g", [Y])]), Atom("Q", [Y])])


def test_a_rule_that_binds_variables_to_other_terms_is_still_applied():
    rule = (Function("f", [X, Y]), Function("g", [X]))
    a, b = Constant("alpha"), Constant("beta")
    clause = frozenset([Atom("P", [Function("f", [a, b])])])
    assert resolution._demodulate_once(clause, [rule]) == frozenset([Atom("P", [Function("g", [a])])])
    clause = frozenset([Atom("P", [Function("f", [Z, b])])])           # a target variable that the rule does not bind
    assert resolution._demodulate_once(clause, [rule]) == frozenset([Atom("P", [Function("g", [Z])])])


def test_an_equation_is_rewritten_by_itself_once_and_then_stops():
    # x + y = y + x as a rule against the unit clause of the same equation. The two sides weigh the same and "x + y"
    # sorts before "y + x", so the rule is y + x → x + y. Against the right side y + x the matcher is {y: y, x: x}
    # (a variable bound to itself): the instance is y + x = x + y and the clause becomes x + y = x + y. Against the
    # left side x + y the matcher is {y: x, x: y} (cyclic): the instance is x + y = y + x, which is not simpler, so
    # nothing more happens. (The old expectation, no rewrite at all, was the prover declining to apply either
    # matcher.)
    equation = Atom("=", [Function("+", [X, Y]), Function("+", [Y, X])])
    rules = resolution._unit_rewrite_rules([frozenset([equation])])
    assert rules == [(Function("+", [Y, X]), Function("+", [X, Y]))]
    clause, count = resolution._demodulate_to_fixpoint(frozenset([equation]), rules)
    assert clause == frozenset([Atom("=", [Function("+", [X, Y]), Function("+", [X, Y])])]) and count == 1


def test_commutativity_gives_its_instance():
    premise = F("∀x ∀y plus(x, y) = plus(y, x)")
    goal = F("plus(alpha, beta) = plus(beta, alpha)")
    assert api.prove(goal, [premise], backends=["resolution"], timeout=20000).status == PROVED
