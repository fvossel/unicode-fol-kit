"""One name, two symbols: the Z3 conversion keys a predicate and a function on (name, arity).

A predicate named ``P`` at arity 1 and one at arity 2 are TWO relations, a function ``f`` at arity 1 and
at arity 2 are two functions, a predicate ``Q`` and a function ``Q`` of the same arity are two symbols, a
proposition ``a`` (a predicate of no arguments) and a constant ``a`` are two, and the guard predicate of a
sort ``Car`` (arity 1) is not the predicate ``Car`` of ``Car(x, y)`` (arity 2). A conversion that looked a
name up without its arity would end in Z3's own ``index out of bounds`` as soon as one formula used a name
twice, and a countermodel would report the two declarations under one key, the second overwriting the first.

Two things are checked:

* hand-derived problems, each with its countermodel written down in the test;
* a differential against an ORACLE written here from the definition, which shares no code with the kit: for
  generated problems that use one name as two symbols, Z3's verdict equals a brute-force search over EVERY
  structure of at most two elements in which the two symbols are independent. To make "no countermodel of
  at most two elements" mean "valid", every problem carries the premise "there are at most two things"
  (``∀x ∀y ∀z (x = y ∨ x = z ∨ y = z)``), so a countermodel with three elements does not exist. And the
  countermodel Z3 returns is rebuilt as a structure and evaluated by the kit's own evaluator
  (``semantics.tarski``): it makes every premise true and the goal false.

The numeral ``Number(1)`` and a constant ``Constant('1')`` are one Z3 symbol: the pair is refused by name,
wherever the two meet (one formula, two premises, a premise and the goal, an incremental session).

Everything runs in this process on Z3 alone.
"""
import itertools

import pytest
import z3

from unicode_logic_kit.atp.incremental import IncrementalSession
from unicode_logic_kit.atp.protocol import (
    PROVED, REFUTED, UNKNOWN, Z3Backend, _z3_model_assignment, _z3_sort_axioms, _z3_tag_number,
    _z3_track_and_check, z3_relevant_premises,
)
from unicode_logic_kit.atp.z3_arith import get_model_arith, is_satisfiable_arith, is_valid_arith
from unicode_logic_kit.atp.z3_models import get_model, is_satisfiable, is_valid
from unicode_logic_kit.fol._fol_nodes import _SORT
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Quantifier, SortedQuantifier, Variable, Z3Env,
)
from unicode_logic_kit.semantics.tarski import Structure, satisfies

from _one_name_problems import AT_MOST_TWO, FAMILIES, make_problem, oracle_has_countermodel

X, Y, Z = Variable("x"), Variable("y"), Variable("z")
A, B = Constant("a"), Constant("b")


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


def _status(goal, premises=()):
    return Z3Backend().decide(goal, list(premises)).status


# ---------------------------------------------------------------------------------------------
# the environment
# ---------------------------------------------------------------------------------------------
def test_one_predicate_name_at_two_arities_is_two_declarations_in_one_formula():
    env = Z3Env()
    one = Atom("P", [A]).to_z3(env)
    two = Atom("P", [A, B]).to_z3(env)             # raised Z3Exception 'index out of bounds'
    assert one.decl().arity() == 1 and two.decl().arity() == 2
    assert one.decl() != two.decl()
    # and one formula that uses both converts at all
    both = Implies(Atom("P", [A]), Atom("P", [A, B])).to_z3()
    assert z3.is_expr(both)


def test_one_function_name_at_two_arities_is_two_declarations_in_one_formula():
    formula = Atom("=", [Function("f", [A]), Function("f", [A, B])])
    z3_formula = formula.to_z3()                   # raised Z3Exception 'index out of bounds'
    left, right = z3_formula.arg(0), z3_formula.arg(1)
    assert (left.decl().arity(), right.decl().arity()) == (1, 2)


def test_a_predicate_and_a_function_of_one_name_and_arity_are_two_symbols():
    # the predicate returns Bool, the function returns the sort of individuals
    z3_formula = Atom("P", [Function("P", [A])]).to_z3()
    assert z3_formula.decl().range() == z3.BoolSort()
    assert z3_formula.arg(0).decl().range() == _SORT


def test_a_proposition_and_a_constant_of_one_name_are_two_symbols():
    z3_formula = Implies(Atom("a", []), Atom("Q", [A])).to_z3()
    proposition = z3_formula.arg(0)
    constant = z3_formula.arg(1).arg(0)
    assert proposition.sort() == z3.BoolSort() and constant.sort() == _SORT


def test_the_guard_predicate_of_a_sort_is_not_the_predicate_of_another_arity():
    formula = SortedQuantifier("∃", X, "Car", SortedQuantifier("∃", Y, "Car", Atom("Car", [X, Y])))
    assert z3.is_expr(formula.to_z3())             # raised Z3Exception 'index out of bounds'


# ---------------------------------------------------------------------------------------------
# hand-derived verdicts and countermodels
# ---------------------------------------------------------------------------------------------
def test_P_of_one_argument_does_not_entail_P_of_two():
    # P(a) ⊬ P(a, b): the universe {0}, a = b = 0, P1 = {0}, P2 = {} (two relations)
    goal = Atom("P", [A, B])
    verdict = Z3Backend().decide(goal, [Atom("P", [A])])
    assert verdict.status == REFUTED


def test_the_premises_and_the_goal_of_two_arities_each_mean_what_they_say():
    # P(a, b) ⊢ P(a, b) is valid, ⊢ P(a) → P(a, b) is not, and so is ∀x ∃y P(x, y) ⊬ ∀x P(x)
    assert _status(Atom("P", [A, B]), [Atom("P", [A, B])]) == PROVED
    assert _status(Implies(Atom("P", [A]), Atom("P", [A, B]))) == REFUTED
    assert _status(forall(X, Atom("P", [X])), [forall(X, exists(Y, Atom("P", [X, Y])))]) == REFUTED


def test_a_function_name_at_two_arities_is_two_functions():
    # f(a) = b ⊬ f(a, a) = b: the universe {0, 1}, a = 0, b = 1, f1(0) = 1, f2(0, 0) = 0
    assert _status(Atom("=", [Function("f", [A, A]), B]), [Atom("=", [Function("f", [A]), B])]) == REFUTED
    # but f(a) = b, f(a, a) = a ⊢ f(a) = b, of course
    assert _status(Atom("=", [Function("f", [A]), B]),
                   [Atom("=", [Function("f", [A]), B]), Atom("=", [Function("f", [A, A]), A])]) == PROVED


def test_a_predicate_and_a_function_named_alike_are_two_symbols():
    # P(a) ⊬ P(P(a)): the universe {0, 1}, a = 0, the predicate P = {0}, the function P(0) = 1
    verdict = Z3Backend().decide(Atom("P", [Function("P", [A])]), [Atom("P", [A])])
    assert verdict.status == REFUTED
    # whereas one symbol could not be refuted: P(P(a)) follows from itself
    assert _status(Atom("P", [Function("P", [A])]), [Atom("P", [Function("P", [A])])]) == PROVED


def test_a_proposition_and_a_constant_named_alike_are_two_symbols():
    # the proposition a together with Q(a), the constant a: a does not follow from Q(a)
    assert _status(Atom("a", []), [Atom("Q", [A])]) == REFUTED
    assert _status(Atom("a", []), [Atom("a", [])]) == PROVED


def test_a_predicate_of_another_arity_named_like_a_sort_is_not_the_sort():
    some_car_pair = SortedQuantifier("∃", X, "Car", SortedQuantifier("∃", Y, "Car", Atom("Car", [X, Y])))
    every_car_pair = SortedQuantifier("∀", X, "Car", SortedQuantifier("∀", Y, "Car", Atom("Car", [X, Y])))
    # ⊬ ∃x:Car ∃y:Car Car(x, y): the universe {0}, Car = {0} (the sort), Car2 = {} (a relation of its own)
    assert _status(some_car_pair) == REFUTED
    # ∀x:Car ∀y:Car Car(x, y) ⊢ ∃x:Car ∃y:Car Car(x, y): a sort is never empty, so a pair exists
    assert _status(some_car_pair, [every_car_pair]) == PROVED
    # and the sort is the unary predicate: ⊢ ∃x:Car Car(x)
    assert _status(SortedQuantifier("∃", X, "Car", Atom("Car", [X]))) == PROVED


def test_get_model_and_is_valid_and_is_satisfiable_accept_one_name_twice():
    formula = And(Atom("P", [A]), Not(Atom("P", [A, B])))
    assert is_satisfiable(formula)
    assert not is_valid(formula)
    model = get_model(formula)
    assert model is not None


def test_relevant_premises_with_one_name_at_two_arities():
    premises = [Atom("P", [A]), Atom("P", [A, B]), Atom("Q", [A])]
    assert z3_relevant_premises(Atom("P", [A, B]), premises) == (1,)


def test_the_countermodel_reports_each_symbol_under_its_own_name_and_arity():
    verdict = Z3Backend().decide(Atom("P", [A, B]), [Atom("P", [A])])
    assignment = verdict.countermodel["assignment"]
    # P at arity 1 is true of a, at arity 2 it is false of (a, b): two entries, none overwritten
    assert set(assignment) == {"a", "b", "P/1", "P/2"}
    assert "True" in assignment["P/1"] or "->" in assignment["P/1"]
    assert assignment["P/2"] == "[else -> False]"


def test_a_name_declared_once_keeps_its_plain_key():
    verdict = Z3Backend().decide(Atom("P", [A]))
    assert set(verdict.countermodel["assignment"]) == {"a", "P"}
    assert get_model(Atom("P", [A])).keys() == {"a", "P"}


def test_a_predicate_and_a_function_of_one_name_and_arity_are_told_apart_by_what_they_return():
    verdict = Z3Backend().decide(Atom("P", [Function("P", [A])]), [Atom("P", [A])])
    assert set(verdict.countermodel["assignment"]) == {"a", "P/1:Bool", "P/1:S"}


def test_a_proposition_and_a_constant_of_one_name_are_reported_apart():
    verdict = Z3Backend().decide(Atom("a", []), [Atom("Q", [A])])
    assert set(verdict.countermodel["assignment"]) == {"Q", "a/0:Bool", "a/0:S"}


def test_declaration_keys_are_the_name_when_unique_then_name_and_arity_then_the_result_sort():
    from unicode_logic_kit.atp.z3_models import declaration_keys
    assert declaration_keys([("P", 1, "Bool"), ("a", 0, "S")]) == ["P", "a"]
    assert declaration_keys([("P", 1, "Bool"), ("P", 2, "Bool"), ("a", 0, "S")]) == ["P/1", "P/2", "a"]
    assert declaration_keys([("P", 1, "Bool"), ("P", 1, "S")]) == ["P/1:Bool", "P/1:S"]
    # a symbol that is literally called "P/1" does not meet the key of another one
    keys = declaration_keys([("P", 1, "Bool"), ("P", 2, "Bool"), ("P/1", 0, "S")])
    assert len(set(keys)) == 3 and keys[2] == "P/1" and keys[0] != "P/1"


def test_the_arithmetic_route_keeps_one_name_at_two_arities_apart():
    # P(a) ∧ ¬P(a, b): two relations of one name; with one symbol the second use of P would not even type-check
    formula = And(Atom("P", [A]), Not(Atom("P", [A, B])))
    assert is_satisfiable_arith(formula)
    assert not is_valid_arith(formula)
    # P(a) → P(a, b) is not valid, and P(a) ∧ P(a, b) → P(a) is
    assert not is_valid_arith(Implies(Atom("P", [A]), Atom("P", [A, B])))
    assert is_valid_arith(Implies(And(Atom("P", [A]), Atom("P", [A, B])), Atom("P", [A])))
    # a function of one name at two arities: f(a) = 1 ∧ f(a, a) = 2 has a model, f(a) = 1 → f(a, a) = 1 is not valid
    assert is_satisfiable_arith(And(Atom("=", [Function("f", [A]), Number(1)]),
                                    Atom("=", [Function("f", [A, A]), Number(2)])))
    assert not is_valid_arith(Implies(Atom("=", [Function("f", [A]), Number(1)]),
                                      Atom("=", [Function("f", [A, A]), Number(1)])))


def test_the_arithmetic_model_reports_each_arity_under_its_own_key():
    model = get_model_arith(And(Atom("P", [A]), Not(Atom("P", [A, B]))))
    assert model is not None
    assert {"P/1", "P/2"} <= set(model) and "P" not in model
    model = get_model_arith(And(Atom("=", [Function("f", [A]), Number(1)]),
                                Atom("=", [Function("f", [A, A]), Number(2)])))
    assert {"f/1", "f/2"} <= set(model)
    # a name that is declared once keeps its plain key
    assert get_model_arith(Atom("=", [Function("+", [X, Number(1)]), Number(2)])) == {"x": "1"}


# ---------------------------------------------------------------------------------------------
# the differential: Z3 against an enumeration written from the definition
# ---------------------------------------------------------------------------------------------
# -- a Z3 model, rebuilt as a structure of the kit -------------------------------------------------
def structure_of_model(model, family):
    """Read the model through the Z3 API (not through the printed strings) into a kit ``Structure``.

    The domain is the model's universe plus every value a constant or a function of the model takes
    (a value no symbol mentions is a value the evaluator cannot tell apart from another one anyway).
    """
    values, index = [], {}

    def element(z3_value):
        key = str(z3_value)
        if key not in index:
            index[key] = len(values)
            values.append(z3_value)
        return index[key]

    def evaluate(expr):
        return model.eval(expr, model_completion=True)

    for e in (model.get_universe(_SORT) or []):
        element(e)
    constants = {name: element(evaluate(z3.Const(name, _SORT)))
                 for name in tuple(family.constants) + tuple(family.sorted_constants)}
    if not values:
        element(evaluate(z3.Const("anything", _SORT)))
    while True:
        known = len(values)
        domain = list(range(known))
        functions, predicates, sorts = {}, {}, {}
        for name, arity in family.functions:
            decl = z3.Function(name, *([_SORT] * arity), _SORT)
            functions[(name, arity)] = {
                args: element(evaluate(decl(*[values[i] for i in args])))
                for args in itertools.product(domain, repeat=arity)}
        if len(values) == known:
            break
    for name, arity in family.predicates:
        decl = z3.Function(name, *([_SORT] * arity), z3.BoolSort())
        extension = {args for args in itertools.product(domain, repeat=arity)
                     if z3.is_true(evaluate(decl(*[values[i] for i in args])))}
        predicates[(name, arity)] = bool(extension) if arity == 0 else extension
    if family.sort:
        decl = z3.Function(family.sort, _SORT, z3.BoolSort())
        sorts[family.sort] = [i for i in domain if z3.is_true(evaluate(decl(values[i])))]
    return Structure(domain, constants, functions, predicates, sorts)


class Answer:
    """What Z3 said about one problem, and the model it found if it refuted it."""

    def __init__(self, status, model=None, assignment=None, declared=0):
        self.status = status
        self.model = model
        self.assignment = assignment
        self.declared = declared              # declarations in the model, read BEFORE anything evaluates it


def _z3_answer(premises, goal):
    nodes = list(premises) + [AT_MOST_TWO]
    z3_goal = goal.to_z3()
    z3_premises = [p.to_z3() for p in nodes]
    z3_sorts = _z3_sort_axioms(goal, nodes)
    result, solver = _z3_track_and_check(z3_goal, z3_premises, 10000, z3_sorts)
    if result == z3.unsat:
        return Answer(PROVED)
    if result == z3.sat:
        model = solver.model()
        # the tracking literals are the constants with an integer symbol; no symbol of a problem is one
        declared = sum(1 for d in model.decls() if _z3_tag_number(d) is None)
        return Answer(REFUTED, model, _z3_model_assignment(model, len(z3_premises)), declared)
    return Answer(UNKNOWN)


class Case:
    def __init__(self, seed, family):
        self.seed, self.family = seed, family
        self.premises, self.goal = make_problem(seed, family)
        self.answer = _z3_answer(self.premises, self.goal)
        self.small_countermodel = oracle_has_countermodel(self.premises, self.goal, family)

    @property
    def label(self):
        return (self.seed, self.family.label)


BATCH = [(seed, family) for family in FAMILIES for seed in range(1, 41)]


@pytest.fixture(scope="module")
def cases():
    return [Case(seed, family) for seed, family in BATCH]


def test_z3_never_gives_up_on_these_problems(cases):
    assert [c.label for c in cases if c.answer.status == UNKNOWN] == []


def test_z3_agrees_with_the_enumeration_on_every_problem(cases):
    # at most two elements exist (the premise), so "no countermodel of <= 2 elements" IS validity
    wrong = [(c.label, c.answer.status, c.small_countermodel) for c in cases
             if (c.answer.status == REFUTED) != c.small_countermodel]
    assert wrong == []


def test_the_batch_has_valid_and_invalid_problems_in_every_family(cases):
    for family in FAMILIES:
        verdicts = [c.answer.status for c in cases if c.family is family]
        assert verdicts.count(PROVED) >= 4, (family.label, verdicts)
        assert verdicts.count(REFUTED) >= 4, (family.label, verdicts)


def test_a_countermodel_reports_every_symbol_it_declares_under_a_key_of_its_own(cases):
    for c in cases:
        if c.answer.status == REFUTED:
            assert len(c.answer.assignment) == c.answer.declared, (c.label, c.answer.assignment)


def test_every_countermodel_makes_the_premises_true_and_the_goal_false(cases):
    bad = []
    for c in cases:
        if c.answer.status != REFUTED:
            continue
        structure = structure_of_model(c.answer.model, c.family)
        nodes = list(c.premises) + [AT_MOST_TWO]
        if not all(satisfies(p, structure) for p in nodes) or satisfies(c.goal, structure):
            bad.append(c.label)
    assert bad == []


def test_the_verdict_of_the_backend_is_the_one_computed_here(cases):
    for c in cases[::7]:
        backend = Z3Backend().decide(c.goal, list(c.premises) + [AT_MOST_TWO])
        assert backend.status == c.answer.status, c.label
        if c.answer.status == REFUTED:
            assert len(backend.countermodel["assignment"]) == len(c.answer.assignment)


# ---------------------------------------------------------------------------------------------
# the numeral and the constant of one text
# ---------------------------------------------------------------------------------------------
def test_a_numeral_and_a_constant_of_one_text_are_refused_inside_one_formula():
    with pytest.raises(NotImplementedError, match="numeral 1 and a constant named '1'"):
        Atom("=", [Number(1), Constant("1")]).to_z3()
    with pytest.raises(NotImplementedError, match="numeral 1 and a constant named '1'"):
        Atom("=", [Constant("1"), Number(1)]).to_z3()


def test_a_numeral_and_a_variable_of_one_text_are_two_symbols():
    # A variable is a symbol of its own, apart from every constant of its name, and a numeral
    # is a constant: the pair is not one symbol, so there is nothing to refuse. ∀x P(1, x) with a variable
    # spelled 1 reads as P(1, v) for every v, and the numeral 1 is not the variable.
    env = Z3Env()
    assert not Number(1).to_z3(env).eq(Variable("1").to_z3(env))
    assert z3.is_expr(Atom("P", [Number(1), Variable("1")]).to_z3())


def test_two_different_numerals_and_a_numeral_next_to_other_constants_are_fine():
    assert z3.is_expr(Atom("=", [Number(1), Number(2)]).to_z3())
    assert z3.is_expr(Atom("=", [Number(1), Constant("one")]).to_z3())
    # A float and an int of the same value are ONE numeral: Number(1) == Number(1.0), and a
    # numeral is the constant of its value (the old comment called them two symbols, '1' and '1.0')
    assert Number(1).to_z3().eq(Number(1.0).to_z3())
    assert Number(2).to_z3().eq(Number(2.0).to_z3()) and not Number(2).to_z3().eq(Number(1).to_z3())


def test_the_refusal_is_reported_by_name_through_the_backend_wherever_the_pair_meets():
    one, quoted = Number(1), Constant("1")
    for premises, goal in (([Atom("P", [one])], Atom("P", [quoted])),        # premise and goal
                           ([Atom("P", [one]), Atom("Q", [quoted])], Atom("R", [A])),   # two premises
                           ([], Atom("=", [one, quoted]))):                  # one formula
        verdict = Z3Backend().decide(goal, premises)
        assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
        assert "numeral 1" in verdict.detail and "constant named '1'" in verdict.detail
    assert z3_relevant_premises(Atom("P", [quoted]), [Atom("P", [one])]) is None


def test_the_bound_of_a_counting_quantifier_is_no_numeral_of_the_problem():
    # ∃>=2 x P(x) ⊢ ∃x P(x) with a constant named 2 next to it: the 2 of the quantifier is a parameter of the
    # node, never a symbol, so it does not meet the constant
    two_ps = Count("ge", Number(2), X, Atom("P", [X]))
    q_two = Atom("Q", [Constant("2")])
    assert _status(exists(X, Atom("P", [X])), [two_ps, q_two]) == PROVED
    assert _status(q_two, [two_ps, q_two]) == PROVED


def test_the_same_numeral_everywhere_is_still_one_symbol():
    # P(1) ⊢ P(1) is valid, P(1) ⊬ P(2) is not
    assert _status(Atom("P", [Number(1)]), [Atom("P", [Number(1)])]) == PROVED
    assert _status(Atom("P", [Number(2)]), [Atom("P", [Number(1)])]) == REFUTED


def test_an_incremental_session_refuses_the_pair_and_a_retraction_takes_the_claim_back():
    session = IncrementalSession([Atom("P", [Number(1)])])
    with pytest.raises(NotImplementedError, match="numeral 1"):
        session.assert_premise(Atom("Q", [Constant("1")]))
    assert session.scope_depth == 0                                 # nothing was pushed
    verdict = session.decide(Atom("P", [Constant("1")]))
    assert (verdict.status, verdict.reason) == (UNKNOWN, "unsupported")
    # a session whose only numeral premise is retracted may use the constant afterwards
    other = IncrementalSession()
    other.assert_premise(Atom("P", [Number(7)]))
    other.retract()
    other.assert_premise(Atom("P", [Constant("7")]))
    assert other.decide(Atom("P", [Constant("7")])).status == PROVED


def test_an_incremental_session_reports_one_name_at_two_arities_apart():
    session = IncrementalSession([Atom("P", [A])])
    verdict = session.decide(Atom("P", [A, B]))
    assert verdict.status == REFUTED
    assert set(verdict.countermodel["assignment"]) == {"a", "b", "P/1", "P/2"}
