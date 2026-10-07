"""A constant and a variable of one name are two symbols on the arithmetic route (``atp.z3_arith``).

``Constant('x')`` and the bound variable ``x`` print alike, and the arithmetic translation used to make ONE Z3
numeric constant of them, so the quantifier of ``∀x x ≤ c`` (with ``c = Constant('x')``) bound the constant as
well and read the formula as ``∀x x ≤ x``. The definition, written down once and derived by hand (``c`` is the
constant, ``x`` the variable, over the integers and over the reals):

* a constant is a rigid symbol of the problem; a variable is a place a quantifier binds. The occurrences of the
  variable ``x`` are never the constant ``x``, free or bound.
* ``∀x x ≤ c`` is NOT valid and not satisfiable: ``x := c + 1`` is above every ``c``.
* ``∃x x < c`` is valid (``x := c - 1``), ``∃x c < x`` is valid (``x := c + 1``), and so is
  ``∃x (x < c ∧ c < x + 2)`` (``x := c - 1``: ``c - 1 < c`` and ``c < c + 1``).
* ``x = 1 ∧ c = 2`` with the FREE variable ``x`` is satisfiable: two symbols, one of them 1 and the other 2. A
  model reports the constant under its plain name ``x`` and the free variable as ``x!v`` (it is under its own
  name ``x`` only when no constant of that name is declared).
* ``∀x:S (x ≤ c:S)`` with ``c:S = SortedConstant('x', 'S')`` is NOT valid: the sort ``S`` is any set that
  contains ``c`` (the sort axiom), for instance ``{c, c + 1}``.

The numeral reading is unchanged: ``1`` is the number one, never a symbol.
"""
import random

import pytest
import z3

from unicode_logic_kit.atp._tff_problem import generate_tff_arith_problem
from unicode_logic_kit.atp.z3_arith import (
    ArithEnv, get_model_arith, is_satisfiable_arith, is_valid_arith, to_z3_arith,
)
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Iff, Node, Not, Number, Or, Quantifier, SortedConstant,
    SortedCount, SortedQuantifier, Variable,
)

X = Variable("x")
C = Constant("x")                      # spelled like the bound variable
SORTS = ("int", "real")


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


def le(a, b):
    return Atom("≤", [a, b])


def lt(a, b):
    return Atom("<", [a, b])


# ---------------------------------------------------------------------------------------------
# the three problems of the definition, and the ones next to them
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("sort", SORTS)
def test_a_universal_quantifier_over_x_does_not_bind_the_constant_x(sort):
    formula = forall(X, le(X, C))                                   # ∀x x ≤ c
    assert is_valid_arith(formula, sort=sort) is False
    assert is_satisfiable_arith(formula, sort=sort) is False
    assert get_model_arith(formula, sort=sort) is None


@pytest.mark.parametrize("sort", SORTS)
def test_an_existential_quantifier_over_x_does_not_bind_the_constant_x(sort):
    below = exists(X, lt(X, C))                                     # ∃x x < c
    above = exists(X, lt(C, X))                                     # ∃x c < x
    between = exists(X, And(lt(X, C), lt(C, Function("+", [X, Number(2)]))))     # ∃x (x < c ∧ c < x + 2)
    for formula in (below, above, between):
        assert is_valid_arith(formula, sort=sort) is True
        assert is_satisfiable_arith(formula, sort=sort) is True
        model = get_model_arith(formula, sort=sort)
        assert model is not None and set(model) == {"x"}, model     # the constant, under its plain name


@pytest.mark.parametrize("sort", SORTS)
def test_the_same_formulas_with_the_constant_renamed_agree(sort):
    c = Constant("zeta")
    assert is_valid_arith(forall(X, le(X, c)), sort=sort) is False
    assert is_valid_arith(exists(X, lt(X, c)), sort=sort) is True
    assert is_valid_arith(exists(X, lt(c, X)), sort=sort) is True


@pytest.mark.parametrize("sort", SORTS)
def test_a_free_variable_and_a_constant_of_one_name_are_two_symbols(sort):
    formula = And(Atom("=", [X, Number(1)]), Atom("=", [C, Number(2)]))          # x = 1 ∧ c = 2, x free
    assert is_satisfiable_arith(formula, sort=sort) is True
    assert get_model_arith(formula, sort=sort) == {"x": "2", "x!v": "1"}
    # the free variable alone keeps its own name, as before
    assert get_model_arith(Atom("=", [Function("+", [X, Number(1)]), Number(2)]), sort=sort) == {"x": "1"}
    # as the formula of an entailment: the variable x being 1 says nothing about the constant x
    assert is_valid_arith(Implies(Atom("=", [X, Number(1)]), Atom("=", [C, Number(1)])), sort=sort) is False
    assert is_valid_arith(Implies(Atom("=", [X, Number(1)]), Atom("=", [X, Number(1)])), sort=sort) is True


@pytest.mark.parametrize("sort", SORTS)
def test_a_constant_whose_name_looks_like_the_symbol_of_a_variable_is_still_a_constant(sort):
    marked = Constant("x!v")                    # the Z3 name of the variable x is "x!v"
    assert is_valid_arith(forall(X, le(X, marked)), sort=sort) is False
    assert is_valid_arith(exists(X, lt(X, marked)), sort=sort) is True
    model = get_model_arith(exists(X, lt(X, marked)), sort=sort)
    assert model is not None and set(model) == {"x!v"}                  # the constant, under its plain name
    escaped = Constant("x!c")
    assert is_valid_arith(forall(X, le(X, escaped)), sort=sort) is False
    assert is_valid_arith(exists(X, lt(X, escaped)), sort=sort) is True


@pytest.mark.parametrize("sort", SORTS)
def test_a_function_of_no_arguments_is_the_constant_of_its_name(sort):
    nullary = Function("x", [])
    assert is_valid_arith(forall(X, le(X, nullary)), sort=sort) is False        # not captured by ∀x
    assert is_valid_arith(exists(X, lt(X, nullary)), sort=sort) is True
    one = Atom("=", [Constant("kk"), Number(1)])
    assert is_valid_arith(Implies(one, Atom("=", [Function("kk", []), Number(1)])), sort=sort) is True


@pytest.mark.parametrize("sort", SORTS)
def test_a_sorted_constant_of_the_name_of_a_bound_variable_is_not_bound(sort):
    carl = SortedConstant("x", "S")
    formula = SortedQuantifier("∀", X, "S", le(X, carl))               # ∀x:S x ≤ c:S
    assert is_valid_arith(formula, sort=sort) is False                # S = {c, c + 1}
    if sort == "int":                                                 # S = {c} is a model; over the reals Z3 gives up
        assert is_satisfiable_arith(formula, sort=sort) is True
    plain = SortedQuantifier("∀", X, "S", le(X, C))                  # ∀x:S x ≤ c, the constant c plain
    assert is_valid_arith(plain, sort=sort) is False


# ---------------------------------------------------------------------------------------------
# a variable that is MINTED, next to a user constant of exactly the minted name
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("sort", SORTS)
@pytest.mark.parametrize("name", ["x0", "x1", "x2", "x"])
def test_a_counting_witness_never_meets_a_constant_of_its_name(sort, name):
    # ∃≥2 x:S R(x, k) → ∃y:S R(y, k) is valid (two witnesses are at least one), whatever k is called, and
    # ∃≤1 x:S R(x, k) ∧ R(a, k) ∧ R(b, k) with a, b of the sort entails a = b. The witnesses the lowering mints
    # for the counting variable are x0, x1, … and the constant may be spelled like any of them.
    k = Constant(name)
    y = Variable("y")
    at_least = SortedCount("ge", Number(2), X, "S", Atom("R", [X, k]))
    some = SortedQuantifier("∃", y, "S", Atom("R", [y, k]))
    assert is_valid_arith(Implies(at_least, some), sort=sort) is True
    a, b = SortedConstant("aa", "S"), SortedConstant("bb", "S")
    at_most = SortedCount("le", Number(1), X, "S", Atom("R", [X, k]))
    both = And(Atom("R", [a, k]), Atom("R", [b, k]))
    assert is_valid_arith(Implies(And(at_most, both), Atom("=", [a, b])), sort=sort) is True
    # and it does not say more than it should: with no bound on the count, a ≠ b is possible
    assert is_valid_arith(Implies(both, Atom("=", [a, b])), sort=sort) is False
    assert is_satisfiable_arith(And(at_least, Not(Atom("=", [a, b]))), sort=sort) is True


@pytest.mark.parametrize("sort", SORTS)
@pytest.mark.parametrize("name", ["x0", "x"])
def test_the_guard_variable_of_a_sort_axiom_never_meets_a_constant_of_its_name(sort, name):
    # the sort axioms say ∃x0 S(x0) (x0 a minted variable) and S(c) for the sorted constant c
    carl = SortedConstant(name, "S")
    assert is_satisfiable_arith(Atom("P", [carl]), sort=sort) is True
    assert is_valid_arith(Atom("P", [carl]), sort=sort) is False
    every = SortedQuantifier("∀", X, "S", Atom("P", [X]))
    assert is_valid_arith(Implies(every, Atom("P", [carl])), sort=sort) is True


# ---------------------------------------------------------------------------------------------
# the translation itself
# ---------------------------------------------------------------------------------------------
def test_the_translation_has_a_symbol_for_the_variable_and_another_for_the_constant():
    env = ArithEnv("int")
    atom = to_z3_arith(le(X, C), env)
    assert [atom.arg(0).decl().name(), atom.arg(1).decl().name()] == ["x!v", "x"]
    assert set(env.symbols) == {"x"} and set(env.variables) == {"x"}
    assert env.get_symbol("x") is not env.get_variable("x")
    assert not env.get_symbol("x").eq(env.get_variable("x"))


@pytest.mark.parametrize("sort", SORTS)
def test_a_quantifier_binds_the_variable_and_the_constant_stays_free(sort):
    env = ArithEnv(sort)
    quantified = to_z3_arith(forall(X, le(X, C)), env)
    assert z3.is_quantifier(quantified) and quantified.is_forall()
    body = quantified.body()
    assert z3.is_var(body.arg(0))                                    # the bound variable
    assert body.arg(1).eq(env.get_symbol("x"))                      # the constant, free in the body
    assert body.arg(1).decl().name() == "x"


def test_the_numeral_is_still_the_number_and_a_constant_of_its_text_is_a_symbol():
    # a numeral is its value here, never a symbol: the constant named "1" is not the number 1
    one = Constant("1")
    assert is_valid_arith(forall(X, Implies(Atom("=", [X, Number(1)]), Atom("=", [X, Number(1)])))) is True
    assert is_valid_arith(Atom("=", [one, Number(1)])) is False
    assert is_satisfiable_arith(And(Atom("=", [one, Number(2)]), Atom("=", [Number(2), one]))) is True


# ---------------------------------------------------------------------------------------------
# the text writer for Vampire already keeps them apart; pinned so that it stays so
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("sort", SORTS)
def test_the_tfa_text_binds_an_upper_case_variable_and_declares_the_constant(sort):
    text, _ = generate_tff_arith_problem([], forall(X, le(X, C)), sort=sort)
    token = "$int" if sort == "int" else "$real"
    assert f"tff(const_decl_1, type, x: {token} )." in text
    assert f"![X: {token}]: $lesseq(X,x)" in text                    # the bound X is not the declared x


# ---------------------------------------------------------------------------------------------
# the differential: a formula against the same formula with its constant renamed to a fresh name
# ---------------------------------------------------------------------------------------------
FRESH = "zq9"


def rename_constant(node: Node, old: str, new: str) -> Node:
    """The node with every Constant / SortedConstant called ``old`` called ``new`` (variables are left alone)."""
    def walk(value):
        if isinstance(value, dict):
            if value.get("_type") in ("Constant", "SortedConstant") and value.get("name") == old:
                value = dict(value, name=new)
            return {key: walk(item) for key, item in value.items()}
        if isinstance(value, list):
            return [walk(item) for item in value]
        return value

    return Node.from_dict(walk(node.to_dict()))


def generated_term(rng, depth, bound):
    leaves = [Number(0), Number(1), C, C, Constant("dd")]
    if bound:
        leaves += [X, X, X]                      # a bound occurrence is likely, so that the capture matters
    if depth == 0 or rng.random() < 0.4:
        return rng.choice(leaves)
    return Function(rng.choice(["+", "-"]), [generated_term(rng, depth - 1, bound),
                                             generated_term(rng, depth - 1, bound)])


def generated_formula(rng, depth, bound):
    """A formula of linear arithmetic: no uninterpreted symbol, so Z3 decides it and "unknown" is not in play."""
    pick = rng.random()
    if depth == 0 or pick < 0.3:
        return Atom(rng.choice(["<", "≤", "=", "≠", ">", "≥"]),
                    [generated_term(rng, 1, bound), generated_term(rng, 1, bound)])
    if pick < 0.5:
        return Not(generated_formula(rng, depth - 1, bound))
    if pick < 0.75:
        return rng.choice([And, Or, Implies, Iff])(generated_formula(rng, depth - 1, bound),
                                                   generated_formula(rng, depth - 1, bound))
    return Quantifier(rng.choice(["∀", "∃"]), X, generated_formula(rng, depth - 1, True))


def decided(formula, sort, negate):
    """Z3's own answer (not the module's True/False, which folds unknown into False) for the formula or its negation."""
    env = ArithEnv(sort)
    solver = z3.Solver()
    solver.set("timeout", 3000)
    solver.set("random_seed", 42)
    expr = to_z3_arith(formula, env)
    solver.add(z3.Not(expr) if negate else expr)
    return solver.check()


@pytest.mark.parametrize("sort", SORTS)
def test_renaming_the_constant_changes_no_answer(sort):
    rng = random.Random(20261005)
    compared = skipped = captured = 0
    for _ in range(160):
        formula = Quantifier(rng.choice(["∀", "∃"]), X, generated_formula(rng, 2, True))
        renamed = rename_constant(formula, "x", FRESH)
        captured += any(isinstance(n, Constant) and n.name == "x" for n in formula.walk())
        if z3.unknown in (decided(formula, sort, True), decided(renamed, sort, True),
                          decided(formula, sort, False), decided(renamed, sort, False)):
            skipped += 1                          # Z3 gave up on one of the two: nothing to compare
            continue
        compared += 1
        assert is_valid_arith(formula, sort=sort) == is_valid_arith(renamed, sort=sort), formula.to_unicode_str()
        assert is_satisfiable_arith(formula, sort=sort) == is_satisfiable_arith(renamed, sort=sort), \
            formula.to_unicode_str()
        model, model_renamed = get_model_arith(formula, sort=sort), get_model_arith(renamed, sort=sort)
        assert (model is None) == (model_renamed is None), formula.to_unicode_str()
        if model is not None:
            assert not any("!" in key for key in model), model           # a bound variable never reaches a model
        # the translation is the same one up to the constant's name
        env, env_renamed = ArithEnv(sort), ArithEnv(sort)
        expr, expr_renamed = to_z3_arith(formula, env), to_z3_arith(renamed, env_renamed)
        constant, fresh = z3.Const("x", env.sort), z3.Const(FRESH, env.sort)
        assert z3.substitute(expr, (constant, fresh)).eq(expr_renamed), formula.to_unicode_str()
    assert compared >= 110 and captured >= 70, (compared, skipped, captured)      # the comparison is not vacuous


@pytest.mark.parametrize("sort", SORTS)
def test_renaming_the_constant_changes_no_answer_with_free_variables(sort):
    rng = random.Random(7)
    compared = 0
    for _ in range(90):
        formula = generated_formula(rng, 2, True)           # the variable x may be free as well as bound
        renamed = rename_constant(formula, "x", FRESH)
        if z3.unknown in (decided(formula, sort, True), decided(renamed, sort, True),
                          decided(formula, sort, False), decided(renamed, sort, False)):
            continue
        compared += 1
        assert is_valid_arith(formula, sort=sort) == is_valid_arith(renamed, sort=sort), formula.to_unicode_str()
        assert is_satisfiable_arith(formula, sort=sort) == is_satisfiable_arith(renamed, sort=sort), \
            formula.to_unicode_str()
    assert compared >= 60
