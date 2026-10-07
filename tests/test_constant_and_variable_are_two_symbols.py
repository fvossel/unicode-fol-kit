"""A constant and a variable of one name are two symbols, on Z3 and on cvc5.

``Constant('x')`` and the bound variable ``x`` print alike, and both Z3 routes used to make ONE Z3 symbol of
them, so the quantifier of ``∀x P(x, c)`` (with ``c = Constant('x')``) bound the constant as well. The
definition, written down once and derived by hand:

* a constant is a rigid symbol of the problem; a variable is a place the quantifier binds. A variable's
  occurrences are never the constant of the same name, free or bound.
* ``c = Constant('x')``, ``α = Constant('alpha')``:
  ``∀x P(x, c) ⊢ P(α, c)`` is VALID (instance: x := α).
  ``∀x P(x, c) ⊢ P(α, α)`` is NOT valid: the universe {0, 1}, ``c`` = 0, ``α`` = 1,
  ``P`` = {(0,0), (1,0)} makes the premise true (``P(x, 0)`` for both x) and the goal ``P(1, 1)`` false.
  ``⊢ ∀x x = c`` is NOT valid (the universe {0, 1}, ``c`` = 0); ``⊢ ∃x x = c`` is valid (x := c).
* the free variable ``x`` of ``P(x) ⊢ P(c)`` is not ``c``: universe {0, 1}, ``x`` = 1, ``c`` = 0, ``P`` = {1}.
* ``∀x P(x, c)`` and ``∀y P(y, c)`` are equivalent (a renaming of the bound variable), ``∀x P(x, c)`` and
  ``∀x P(x, x)`` are not (the second says P holds of every element with itself).

A countermodel reports a constant under its plain name, and a free variable under its own name, ``x!v`` when
a constant of that name is declared too.
"""
import itertools
import json
import subprocess
import sys

import pytest
import z3

from unicode_logic_kit.atp.incremental import IncrementalSession
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, Z3Backend, z3_relevant_premises
from unicode_logic_kit.atp.z3_equivalence import formulas_are_equivalent
from unicode_logic_kit.atp.z3_input import from_z3, parse_smtlib, to_smtlib
from unicode_logic_kit.atp.z3_models import get_model, is_valid
from unicode_logic_kit.eval.equivalence import equivalent
from unicode_logic_kit.fol.modal_translation import hybrid_is_valid
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Constant, Count, Diamond, Implies, Not, Number, Quantifier, SortedConstant, SortedQuantifier,
    Variable, Z3Env,
)
from unicode_logic_kit.fol.qml import qml_is_valid
from unicode_logic_kit.semantics.tarski import Structure, satisfies

X, Y = Variable("x"), Variable("y")
C = Constant("x")                  # spelled like the bound variable
ALPHA = Constant("alpha")


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


def P(*args):
    return Atom("P", list(args))


PREMISE = forall(X, P(X, C))                   # ∀x P(x, c)
INSTANCE = P(ALPHA, C)                         # P(α, c): follows
NOT_ENTAILED = P(ALPHA, ALPHA)                 # P(α, α): does not


# ---------------------------------------------------------------------------------------------
# the hand derivation, checked by enumeration (so that the tests below test the solvers, not a slip)
# ---------------------------------------------------------------------------------------------
def test_the_derivation_of_the_two_entailments_holds_in_every_structure_of_two_elements():
    domain = (0, 1)
    pairs = list(itertools.product(domain, repeat=2))
    for relation in itertools.chain.from_iterable(itertools.combinations(pairs, k) for k in range(5)):
        for c, alpha in itertools.product(domain, repeat=2):
            structure = Structure(domain, constants={"x": c, "alpha": alpha}, predicates={("P", 2): set(relation)})
            if satisfies(PREMISE, structure, {}):
                assert satisfies(INSTANCE, structure, {})          # valid: an instance
    countermodel = Structure(domain, constants={"x": 0, "alpha": 1}, predicates={("P", 2): {(0, 0), (1, 0)}})
    assert satisfies(PREMISE, countermodel, {}) and not satisfies(NOT_ENTAILED, countermodel, {})


# ---------------------------------------------------------------------------------------------
# the environment
# ---------------------------------------------------------------------------------------------
def test_a_variable_and_a_constant_of_one_name_are_different_z3_symbols():
    env = Z3Env()
    assert not X.to_z3(env).eq(C.to_z3(env))
    assert X.to_z3(env).eq(Variable("x").to_z3(env))
    assert C.to_z3(env).eq(Constant("x").to_z3(env))
    assert not X.to_z3().eq(C.to_z3())            # with no environment at all


def test_two_environments_name_every_symbol_alike():
    # the cvc5 route and the writers translate formula by formula, each in an environment of its own
    one, two = Z3Env(), Z3Env()
    for node in (X, C, Constant("x!v"), Constant("x!c"), Variable("x!v")):
        assert node.to_z3(one).eq(node.to_z3(two)), node


NAMES = ["x", "", "x!v", "x!c", "!v", "!c", "a!v!c", "a!c!v", "x!v!v", "é", "x0", "1", "2.5", "a b", "P(1)"]


def test_the_names_of_the_symbols_of_constants_and_variables_never_meet_and_read_back():
    from unicode_logic_kit.fol._fol_nodes import kit_name_of_z3_symbol, z3_constant_name, z3_variable_name
    constants = {z3_constant_name(name) for name in NAMES}
    variables = {z3_variable_name(name) for name in NAMES}
    assert len(constants) == len(variables) == len(NAMES)           # each map is injective
    assert not constants & variables
    for name in NAMES:
        assert kit_name_of_z3_symbol(z3_constant_name(name)) == (name, False)
        assert kit_name_of_z3_symbol(z3_variable_name(name)) == (name, True)
    assert z3_constant_name("alpha") == "alpha"                       # an ordinary constant is named as it is
    assert z3_variable_name("x") == "x!v"


# ---------------------------------------------------------------------------------------------
# the Z3 routes
# ---------------------------------------------------------------------------------------------
def test_z3_proves_the_instance_and_refutes_the_non_consequence():
    assert Z3Backend().decide(INSTANCE, [PREMISE]).status == PROVED
    refuted = Z3Backend().decide(NOT_ENTAILED, [PREMISE])
    assert refuted.status == REFUTED
    assert set(refuted.countermodel["assignment"]) == {"x", "alpha", "P"}       # the constant under its plain name


def test_the_bounded_checks_of_z3_models_agree():
    assert is_valid(Implies(PREMISE, INSTANCE))
    assert not is_valid(Implies(PREMISE, NOT_ENTAILED))
    assert set(get_model(Not(Implies(PREMISE, NOT_ENTAILED)))) == {"x", "alpha", "P"}


def test_a_universal_over_x_does_not_say_that_everything_is_the_constant_x():
    # ⊢ ∀x x = c is not valid; ⊢ ∃x x = c is
    assert Z3Backend().decide(forall(X, Atom("=", [X, C])), []).status == REFUTED
    assert Z3Backend().decide(exists(X, Atom("=", [X, C])), []).status == PROVED


def test_the_relevant_premises_see_the_instance():
    relevant = z3_relevant_premises(INSTANCE, [PREMISE, P(ALPHA, ALPHA)])
    assert relevant is not None and 0 in relevant


def test_a_nested_binder_of_the_same_name_still_shadows():
    # ∀x (P(x, c) → ∃x P(x, c)) is valid, and ∃x P(x, c) ⊬ P(c, c): the bound x is not the constant
    assert is_valid(forall(X, Implies(P(X, C), exists(X, P(X, C)))))
    assert not is_valid(Implies(exists(X, P(X, C)), P(C, C)))


def test_a_free_variable_is_not_the_constant_of_its_name():
    # P(x) ⊢ P(c): the universe {0, 1}, x = 1, c = 0, P = {1}
    verdict = Z3Backend().decide(Atom("P", [C]), [Atom("P", [X])])
    assert verdict.status == REFUTED
    assignment = verdict.countermodel["assignment"]
    assert set(assignment) == {"x", "x!v", "P"}               # the constant keeps its plain name
    assert assignment["x"] != assignment["x!v"]
    # the same variable twice is one symbol
    assert Z3Backend().decide(Atom("P", [X]), [Atom("P", [X])]).status == PROVED


def test_a_free_variable_alone_is_reported_under_its_own_name():
    verdict = Z3Backend().decide(Atom("Q", [X]), [Atom("P", [X])])
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == {"x", "P", "Q"}


@pytest.mark.parametrize("spelling", ["x!v", "x!c", "x!v!c"])
def test_a_constant_spelled_like_the_symbol_of_a_variable_is_still_not_that_variable(spelling):
    constant = Constant(spelling)
    premise = forall(X, P(X, constant))
    assert Z3Backend().decide(P(ALPHA, constant), [premise]).status == PROVED
    assert Z3Backend().decide(P(ALPHA, ALPHA), [premise]).status == REFUTED
    verdict = Z3Backend().decide(Atom("Q", [constant]), [Atom("P", [Variable(spelling)])])
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == {spelling, spelling + "!v", "P", "Q"}


def test_the_equivalence_checks_keep_the_variable_and_the_constant_apart():
    renamed = forall(Y, P(Y, C))
    assert formulas_are_equivalent(PREMISE, renamed)
    assert not formulas_are_equivalent(PREMISE, forall(X, P(X, X)))
    assert equivalent(PREMISE, renamed, method="solver").equivalent is True
    result = equivalent(PREMISE, forall(X, P(X, X)), method="solver")
    assert result.equivalent is False
    assert set(result.counterexample["assignment"]) >= {"x", "P"}


def test_an_incremental_session_keeps_them_apart():
    session = IncrementalSession([PREMISE])
    assert session.decide(INSTANCE).status == PROVED
    assert session.decide(NOT_ENTAILED).status == REFUTED
    session.assert_premise(P(ALPHA, ALPHA))
    assert session.decide(NOT_ENTAILED).status == PROVED


# ---------------------------------------------------------------------------------------------
# the text, and the way back
# ---------------------------------------------------------------------------------------------
def test_the_smt_text_of_the_problem_is_unsatisfiable_exactly_when_the_entailment_holds():
    # the premise and the NEGATED goal, as text a solver reads
    for goal, entailed in ((INSTANCE, True), (NOT_ENTAILED, False)):
        text = to_smtlib(Not(goal), [PREMISE])
        solver = z3.Solver()
        solver.add(z3.parse_smt2_string(text))
        assert (solver.check() == z3.unsat) is entailed, text


def test_the_text_of_a_free_variable_is_a_constant_of_that_name():
    text = to_smtlib(Atom("P", [X]))
    assert "(declare-fun x () S)" in text and "!v" not in text
    [back] = parse_smtlib(text)
    assert back == Atom("P", [Constant("x")])            # the documented lossiness


def test_the_text_of_a_free_variable_and_a_constant_of_one_name_declares_two_symbols():
    text = to_smtlib(Atom("P", [C]), [Atom("P", [X])])
    declared = [line.split()[1] for line in text.splitlines() if line.startswith("(declare-fun")]
    assert len(declared) == len(set(declared)) == 3, declared          # P, the variable, the constant


def test_from_z3_reads_the_symbols_to_z3_writes_back_as_what_they_were():
    assert from_z3(PREMISE.to_z3()) == forall(X, P(X, Constant("x")))
    assert from_z3(Atom("Q", [X]).to_z3()) == Atom("Q", [Variable("x")])
    assert from_z3(Atom("Q", [Constant("x!v")]).to_z3()) == Atom("Q", [Constant("x!v")])
    assert from_z3(Atom("Q", [Constant("x!c")]).to_z3()) == Atom("Q", [Constant("x!c")])


# ---------------------------------------------------------------------------------------------
# cvc5, in a child process (a text it cannot read ends the process)
# ---------------------------------------------------------------------------------------------
_CHILD = r"""
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import Node

out = []
for spec in json.loads(sys.argv[1]):
    premises = [Node.from_dict(d) for d in spec["premises"]]
    goal = Node.from_dict(spec["goal"])
    verdict = Cvc5Backend().decide(goal, premises, timeout=20000)
    assignment = (verdict.countermodel or {}).get("assignment")
    out.append({"status": verdict.status, "assignment": assignment})
print(json.dumps(out))
"""


def _cvc5(*problems):
    """``(premises, goal)`` each, decided in a child process; the list of ``{"status", "assignment"}``."""
    pytest.importorskip("cvc5")
    spec = json.dumps([{"premises": [p.to_dict() for p in premises], "goal": goal.to_dict()}
                       for premises, goal in problems])
    done = subprocess.run([sys.executable, "-c", _CHILD, spec], capture_output=True, text=True,
                          encoding="utf-8", timeout=600)
    assert done.returncode == 0, f"the child process ended with exit code {done.returncode}: {done.stderr[-400:]}"
    return json.loads(done.stdout.strip().splitlines()[-1])


def test_cvc5_proves_the_instance_and_does_not_prove_the_non_consequence():
    instance, not_entailed, everything, something = _cvc5(
        ([PREMISE], INSTANCE), ([PREMISE], NOT_ENTAILED), ([], forall(X, Atom("=", [X, C]))),
        ([], exists(X, Atom("=", [X, C]))))
    assert instance["status"] == "proved"
    assert not_entailed["status"] != "proved"           # refuted, or unknown: cvc5 does not always find the model
    assert everything["status"] != "proved"             # ⊢ ∀x x = c is not valid
    assert something["status"] == "proved"


def test_cvc5_reports_a_constant_under_its_plain_name_and_a_variable_under_its_own():
    both, alone = _cvc5(([Atom("P", [X])], Atom("P", [C])), ([Atom("P", [X])], Atom("Q", [X])))
    assert both["status"] == "refuted" and set(both["assignment"]) == {"x", "x!v", "P"}
    assert alone["status"] == "refuted" and set(alone["assignment"]) == {"x", "P", "Q"}


def test_cvc5_keeps_a_variable_and_a_constant_spelled_like_a_theory_symbol_apart():
    select = Constant("select")
    premise = forall(Variable("select"), P(Variable("select"), select))
    instance, not_entailed = _cvc5(([premise], P(ALPHA, select)), ([premise], P(ALPHA, ALPHA)))
    assert instance["status"] == "proved"
    assert not_entailed["status"] != "proved"


def test_the_sanitiser_gives_a_variable_and_a_constant_of_one_name_two_tokens():
    from unicode_logic_kit.atp.cvc5_backend import _sanitize_many_for_smtlib
    (quantified, goal), names = _sanitize_many_for_smtlib([PREMISE, INSTANCE])
    variable_token = quantified.variable.name
    constant_token = quantified.formula.args[1].name
    assert variable_token != constant_token
    assert names.variable_tokens() == {variable_token}
    assert goal.args[1] == Constant(constant_token)
    assert names.reverse()[variable_token] == names.reverse()[constant_token] == "x"
    # a variable spelled like a numeral is no clash for the numeral: they are two symbols
    _sanitize_many_for_smtlib([Atom("P", [Number(1), Variable("1")])])


# ---------------------------------------------------------------------------------------------
# a minted variable named like a user constant
#
# The routes that mint variables and go through Z3: a counting witness (x0, x1 for the counting variable x),
# the guard variable of a sort's non-emptiness axiom (x0), and the world variables of the standard
# translation (w for the current world, w0, w1 for the worlds a modality ranges over). Each is checked with a
# user constant of exactly the minted name.
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["x0", "x1"])
def test_a_counting_witness_does_not_capture_a_constant_of_its_name(name):
    constant = Constant(name)
    at_least_two = Count("ge", Number(2), X, Atom("R", [X, constant]))
    some = exists(Y, Atom("R", [Y, constant]))
    assert Z3Backend().decide(some, [at_least_two]).status == PROVED
    at_most_one = Count("le", Number(1), X, Atom("R", [X, constant]))
    a1, a2 = Constant("a1"), Constant("a2")
    both = [at_most_one, Atom("R", [a1, constant]), Atom("R", [a2, constant])]
    assert Z3Backend().decide(Atom("=", [a1, a2]), both).status == PROVED
    # and it does not say more than it should: with no second fact the two need not be equal
    assert Z3Backend().decide(Atom("=", [a1, a2]), both[:2]).status == REFUTED


@pytest.mark.parametrize("name", ["x0", "x"])
def test_the_guard_variable_of_a_sort_does_not_capture_a_constant_of_its_name(name):
    guarded = SortedQuantifier("∀", X, "S", Atom("P", [X]))
    assert Z3Backend().decide(Atom("P", [SortedConstant(name, "S")]), [guarded]).status == PROVED
    some = SortedQuantifier("∃", Y, "S", Atom("P", [Y]))
    assert Z3Backend().decide(some, [guarded, Atom("Q", [Constant(name)])]).status == PROVED


@pytest.mark.parametrize("name", ["w", "w0", "w1"])
def test_the_hybrid_route_does_not_close_over_a_constant_spelled_like_its_world_variable(name):
    # □Human(c:Human) is valid (a sorted constant is a rigid member of its sort), ◇Human(c:Human) is not (a
    # world with no successor, in K), and a rigid constant does not make Q world-independent
    member = SortedConstant(name, "Human")
    plain = Constant(name)
    assert hybrid_is_valid(Box(Atom("Human", [member])))
    assert not hybrid_is_valid(Diamond(Atom("Human", [member])))
    assert not hybrid_is_valid(Implies(Atom("Q", [plain]), Box(Atom("Q", [plain]))))
    assert hybrid_is_valid(Box(Implies(Atom("Q", [plain]), Atom("Q", [plain]))))


@pytest.mark.parametrize("name", ["w", "w0"])
@pytest.mark.parametrize("mode", ["constant", "varying"])
def test_the_quantified_modal_route_does_not_capture_a_constant_spelled_like_a_world_variable(name, mode):
    assert qml_is_valid(Box(Atom("Human", [SortedConstant(name, "Human")])), mode=mode)


@pytest.mark.parametrize("name", ["w", "w0"])
def test_the_hybrid_backend_does_not_refute_what_holds_for_a_constant_spelled_like_its_world_variable(name):
    from unicode_logic_kit import api
    from unicode_logic_kit.fol.nodes import At, Nominal
    here = Nominal("here")
    member = SortedConstant(name, "Human")
    assert api.prove(At(here, Box(Atom("Human", [member]))), [], backends=["hybrid"], timeout=20000).status == PROVED
    assert api.prove(At(here, Diamond(Atom("Human", [member]))), [], backends=["hybrid"],
                     timeout=20000).status == REFUTED
