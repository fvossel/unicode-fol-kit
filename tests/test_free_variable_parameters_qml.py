"""A free variable is a parameter of the quantified modal route, in every domain regime.

A model is a Kripke frame ``(W, R)`` (frame K: ``R`` is arbitrary), an outer domain ``D`` and,
for every world ``w``, the individuals ``D_w ⊆ D`` that exist there. A predicate is a total
relation on the OUTER domain at each world (an atom over an individual that does not exist at
``w`` is neither forced true nor forced false, as the embedding leaves it). A constant is a
rigid designator and may denote an individual that does not exist at the world it is read at.
The quantifiers are the actualist ones (``∀x`` ranges over ``D_w``) in a varying regime and range
over all of ``D`` in the constant regime, where ``D_w = D`` at every world. The regimes are
``constant`` / ``possibilist`` (``D_w = D``), ``increasing`` (``wRv`` gives ``D_w ⊆ D_v``),
``decreasing`` (``wRv`` gives ``D_v ⊆ D_w``) and ``varying`` (no condition).

A variable that is free in a formula is a PARAMETER: one unknown individual, the same everywhere in
the formula and rigid, like a constant. A formula is valid iff it is true at every world of every
model under every assignment of its parameters, and what an assignment may give a parameter is
the one thing that depends on the regime:

* constant / possibilist: any individual of ``D``, and every individual exists everywhere;
* a varying regime: an individual that EXISTS AT THE WORLD OF EVALUATION (the existence guard
  that the free-logic route gives its parameters), and nowhere else is it required to exist.

The rows are derived by hand from those clauses. ``F`` is "not valid", ``T`` is "valid".

====  ===============================  =====  ===========  =======  ==========  ==========
row   formula                          const  possibilist  varying  increasing  decreasing
====  ===============================  =====  ===========  =======  ==========  ==========
1     ``P(x) → P(a)``                   F        F            F        F           F
2     ``P(x) → P(x)``                   T        T            T        T           T
3     ``P(x) → ∃y P(y)``                T        T            T        T           T
4     ``∀y P(y) → P(x)``                T        T            T        T           T
5     ``(P(x) ∧ Q(y)) → ∀z (…)``        F        F            F        F           F
6     ``□∀y P(y) → □P(x)``              T        T            F        T           F
7     ``∃y (y = x)``                    T        T            T        T           T
8     ``□∃y (y = x)``                   T        T            F        T           F
9     ``∃y (y = a)`` (constant a)       T        T            F        F           F
====  ===============================  =====  ===========  =======  ==========  ==========

* Row 1: one world, ``D = {0, 1}``, ``x`` ↦ 1, ``a`` ↦ 0, ``P`` = ``{1}``: ``P(x)`` holds and
  ``P(a)`` does not. (All regimes: both individuals exist at the world.)
* Row 2 is trivial. Row 3: ``x`` exists at the world of evaluation (everywhere in the constant
  regime), so ``y := x`` witnesses ``∃y P(y)`` when ``P(x)`` holds. Row 4: ``x`` is in the domain
  the quantifier ranges over, so ``∀y P(y)`` gives ``P(x)``.
* Row 5: one world, ``D = {0, 1}``, ``x`` ↦ 0, ``y`` ↦ 1, ``P`` = ``{0}``, ``Q`` = ``{1}``: the
  antecedent holds and ``z := 0`` falsifies ``Q(z)``.
* Row 6, regimes where ``x`` stays in the domain of every later world (constant, possibilist,
  increasing: ``D_w ⊆ D_v``): ``□∀y P(y)`` at ``w`` gives ``P(d)`` at every successor ``v`` for
  every ``d ∈ D_v``, and ``x ∈ D_v``. In ``varying`` and ``decreasing``: two worlds ``w R v``,
  ``D_w = {0, 1}``, ``D_v = {1}`` (a decreasing pair), ``x`` ↦ 0 (it exists at ``w``), ``P`` =
  ``{1}`` at ``v``: ``□∀y P(y)`` holds at ``w`` (``v`` has only 1) and ``P(0)`` fails at ``v``.
* Row 7: the guard makes ``x`` exist at the world of evaluation, so ``y := x`` witnesses it.
  Row 8 is row 6's pattern: the same two worlds make ``∃y (y = x)`` fail at ``v``, whose domain
  is ``{1}``, and it holds there whenever ``D_v`` contains ``x``.
* Row 9, the formula the documentation writes ``∃x (x = c)`` with ``c`` a CONSTANT: it is valid
  where every individual exists everywhere (constant, possibilist) and not valid elsewhere,
  because a constant may denote an individual outside ``D_w`` (one world, ``D_w = {0}``, ``a``
  ↦ 1). With a free VARIABLE in the place of the constant the formula is row 7: the parameter
  exists at the world of evaluation, so ``∃y (y = c)`` is valid in every regime.
"""

import random
from itertools import product

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import resolution
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, Iff, Implies, Not, Or, Quantifier, Variable,
)
from unicode_logic_kit.fol.qml import (
    qml_equivalent, qml_is_valid, qml_translate, qml_validity_formula, to_thf_modal,
)

x, y, z = Variable("x"), Variable("y"), Variable("z")
alpha = Constant("alpha")
MODES = ["constant", "possibilist", "varying", "increasing", "decreasing"]
VARYING = {"varying", "increasing", "decreasing"}


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


def identity(left, right):
    return Atom("=", [left, right])


# label, formula, the verdict under constant, possibilist, varying, increasing, decreasing
ROWS = [
    ("1 P(x) -> P(a)", Implies(P(x), P(alpha)), "FFFFF"),
    ("2 P(x) -> P(x)", Implies(P(x), P(x)), "TTTTT"),
    ("3 P(x) -> exists y P(y)", Implies(P(x), exists(y, P(y))), "TTTTT"),
    ("4 forall y P(y) -> P(x)", Implies(forall(y, P(y)), P(x)), "TTTTT"),
    ("5 P(x) & Q(y) -> forall z (P(z) & Q(z))",
     Implies(And(P(x), Q(y)), forall(z, And(P(z), Q(z)))), "FFFFF"),
    ("6 box forall y P(y) -> box P(x)", Implies(Box(forall(y, P(y))), Box(P(x))), "TTFTF"),
    ("7 exists y (y = x)", exists(y, identity(y, x)), "TTTTT"),
    ("8 box exists y (y = x)", Box(exists(y, identity(y, x))), "TTFTF"),
    ("9 exists y (y = a), a a constant", exists(y, identity(y, alpha)), "TTFFF"),
]


@pytest.mark.parametrize("label, formula, verdicts", ROWS, ids=[row[0] for row in ROWS])
@pytest.mark.parametrize("mode", MODES)
def test_qml_is_valid_reads_a_free_variable_as_a_parameter(label, formula, verdicts, mode):
    expected = verdicts[MODES.index(mode)] == "T"
    assert qml_is_valid(formula, mode=mode, timeout=20000) is expected


@pytest.mark.parametrize("mode", MODES)
def test_the_documented_formula_is_valid_for_a_variable_in_every_regime(mode):
    # ∃x (x = c) written as the documentation writes it: c is a single letter, so a variable
    assert qml_is_valid(exists(x, identity(x, Variable("c"))), mode=mode, timeout=20000) is True


@pytest.mark.parametrize("mode, valid", [("constant", True), ("possibilist", True),
                                         ("varying", False), ("increasing", False),
                                         ("decreasing", False)])
def test_the_documented_formula_with_a_constant_is_valid_only_without_existence_claims(mode, valid):
    # c a constant: it may denote an individual outside the domain of the world (row 9)
    assert qml_is_valid(exists(x, identity(x, Constant("carl"))), mode=mode, timeout=20000) is valid


@pytest.mark.parametrize("mode", MODES)
def test_a_parameter_and_a_constant_instance_differ_where_domains_vary(mode):
    # P(c) → ∃x P(x) is valid for a constant only where it exists everywhere; for a parameter it
    # is valid in every regime (the parameter exists where the formula is evaluated)
    with_variable = Implies(P(Variable("c")), exists(x, P(x)))
    with_constant = Implies(P(Constant("carl")), exists(x, P(x)))
    assert qml_is_valid(with_variable, mode=mode, timeout=20000) is True
    assert qml_is_valid(with_constant, mode=mode, timeout=20000) is (mode not in VARYING)


# --- names of the parameter that meet names the embedding uses ------------------------------

@pytest.mark.parametrize("name", ["x", "w", "v", "u", "t", "w0", "v0", "_a0"])
@pytest.mark.parametrize("mode", ["constant", "varying"])
def test_a_parameter_named_like_a_world_or_an_axiom_variable_is_still_a_parameter(name, mode):
    parameter = Variable(name)
    assert qml_is_valid(Implies(forall(y, P(y)), P(parameter)), mode=mode, timeout=20000) is True
    assert qml_is_valid(Implies(P(parameter), P(alpha)), mode=mode, timeout=20000) is False


def test_a_variable_free_outside_and_bound_inside_is_two_different_variables():
    # (∀x P(x)) → P(x): the x at the end is free, the others are bound: row 4 with one name
    formula = Implies(forall(x, P(x)), P(x))
    assert qml_is_valid(formula, mode="constant", timeout=20000) is True
    assert qml_is_valid(formula, mode="varying", timeout=20000) is True


# --- one parameter is shared by every part of the query -------------------------------------

def test_equivalence_shares_the_parameter_of_both_sides():
    # (∀y P(y)) ∧ P(x) ↔ ∀y P(y): the conjunct P(x) follows from ∀y P(y) (row 4)
    assert qml_equivalent(And(forall(y, P(y)), P(x)), forall(y, P(y)), timeout=20000) is True
    # P(x) ↔ P(alpha) is not valid: x and alpha may be different individuals
    assert qml_equivalent(P(x), P(alpha), timeout=20000) is False


def test_the_consequence_through_the_backend_follows_the_parameter_reading():
    def status(goal, premises, mode="constant"):
        return api.prove(goal, premises, backends=["qml"], logic="modal", timeout=20000,
                         mode=mode).status

    assert status(P(x), [forall(y, P(y))]) == "proved"                  # ∀y P(y) ⊢ P(x)
    assert status(exists(y, P(y)), [P(x)]) == "proved"                  # P(x) ⊢ ∃y P(y)
    assert status(P(x), [P(x)]) == "proved"                             # P(x) ⊢ P(x)
    assert status(P(alpha), [P(x)]) != "proved"                         # P(x) ⊬ P(alpha)
    assert status(P(x), [forall(y, P(y))], mode="varying") == "proved"


def test_the_resolution_prover_takes_the_same_modal_route_and_proves_the_parameter_instance():
    assert resolution.prove([], Implies(Box(forall(y, P(y))), Box(P(x)))) is True
    assert resolution.prove([], Implies(Box(P(x)), Box(P(alpha)))) is False


# --- what the validity query says ------------------------------------------------------------

def conjuncts(node):
    """The members of a left-nested conjunction (the node itself when it is not one)."""
    if isinstance(node, And):
        return conjuncts(node.left) + conjuncts(node.right)
    return [node]


def test_the_query_types_the_parameter_as_an_object_under_constant_domains():
    # the query is  AX ∧ Object(x) → ∀w (World(w) → ST(P(x), w)):  the typing of the parameter is
    # one of the top-level hypotheses, outside every quantifier (the axioms mention bound
    # variables spelled x too, which is why the test looks at the top level only)
    query = qml_validity_formula(P(x), mode="constant")
    assert Atom("Object", (x,)) in conjuncts(query.left)
    antecedent = query.right.formula.left
    assert conjuncts(antecedent) == [Atom("World", (Variable("w"),))]


def test_the_query_guards_the_parameter_by_existence_under_varying_domains():
    # the query is  AX → ∀w (World(w) ∧ E(x, w) → ST(P(x), w)): no typing hypothesis, the guard
    # sits in the antecedent of the quantified world
    query = qml_validity_formula(P(x), mode="varying")
    assert Atom("Object", (x,)) not in conjuncts(query.left)
    w = Variable("w")
    antecedent = query.right.formula.left
    assert conjuncts(antecedent) == [Atom("World", (w,)), Atom("E", (x, w))]


@pytest.mark.parametrize("mode", MODES)
def test_a_formula_without_a_free_variable_has_the_plain_guarded_query(mode):
    # the module docstring: validity is AX → ∀w (World(w) → ST(φ, w)); a parameter adds a typing
    # fact or an existence guard, and a formula without one adds nothing
    closed = forall(x, P(x))
    w = Variable("w")
    expected = Quantifier("∀", w, Implies(Atom("World", (w,)), qml_translate(closed, mode)))
    assert qml_validity_formula(closed, mode=mode).right == expected


def test_the_translation_leaves_a_free_variable_free():
    image = qml_translate(P(x))
    assert {v.name for v in image.walk() if isinstance(v, Variable)} == {"x", "w"}


# --- THF: no free variable, the parameter is bound in the conjecture --------------------------

def goal_line(text):
    return [line for line in text.splitlines() if line.startswith("thf(goal")][0]


def test_thf_binds_the_parameter_in_the_conjecture_under_constant_domains():
    line = goal_line(to_thf_modal(Implies(Box(P(x)), P(x)), mode="constant"))
    assert line.startswith("thf(goal, conjecture, ( ! [X: $i] : ( mvalid @ ")
    assert "existsAt @ X" not in line


@pytest.mark.parametrize("mode", ["varying", "increasing", "decreasing"])
def test_thf_guards_the_parameter_by_existence_under_varying_domains(mode):
    line = goal_line(to_thf_modal(Implies(Box(P(x)), P(x)), mode=mode))
    assert line.startswith(
        "thf(goal, conjecture, ( ! [X: $i] : ( mvalid @ ( mimplies @ ( existsAt @ X ) @ ")


def test_thf_of_a_formula_without_a_free_variable_has_no_extra_binder():
    line = goal_line(to_thf_modal(Implies(Box(P(alpha)), P(alpha)), mode="varying"))
    assert line == ("thf(goal, conjecture, ( mvalid @ ( mimplies @ ( mbox @ ( p @ alpha ) ) "
                    "@ ( p @ alpha ) ) )).")


def test_thf_parameter_binder_encloses_a_quantifier_that_binds_the_same_name():
    # (∀x P(x)) → P(x): the last x is free. The conjecture binds the parameter OUTSIDE everything;
    # the lambda of the quantifier rebinds X only inside its own parentheses, so the final
    # ``p @ X`` after the lambda is the parameter, as the last x of the formula is.
    line = goal_line(to_thf_modal(Implies(forall(x, P(x)), P(x)), mode="constant"))
    assert line == ("thf(goal, conjecture, ( ! [X: $i] : ( mvalid @ ( mimplies @ "
                    "( mforall @ ( ^ [X: $i] : ( p @ X ) ) ) @ ( p @ X ) ) ) )).")


# --- an independent oracle: brute force over tiny Kripke models ------------------------------

def _terms(node, env, consts):
    if isinstance(node, Variable):
        return env[node.name]
    return consts[node.name]


def holds(f, w, env, m):
    """Truth of ``f`` at world ``w`` of model ``m`` (a dict) under the assignment ``env``."""
    if isinstance(f, Atom):
        args = tuple(_terms(a, env, m["consts"]) for a in f.args)
        if f.predicate == "=":
            return args[0] == args[1]
        return args in m["ext"][f.predicate, w]
    if isinstance(f, Not):
        return not holds(f.formula, w, env, m)
    if isinstance(f, And):
        return holds(f.left, w, env, m) and holds(f.right, w, env, m)
    if isinstance(f, Or):
        return holds(f.left, w, env, m) or holds(f.right, w, env, m)
    if isinstance(f, Implies):
        return (not holds(f.left, w, env, m)) or holds(f.right, w, env, m)
    if isinstance(f, Iff):
        return holds(f.left, w, env, m) == holds(f.right, w, env, m)
    if isinstance(f, Box):
        return all(holds(f.formula, v, env, m) for (u, v) in m["rel"] if u == w)
    if isinstance(f, Diamond):
        return any(holds(f.formula, v, env, m) for (u, v) in m["rel"] if u == w)
    if isinstance(f, Quantifier):
        individuals = m["doms"][w] if m["actualist"] else range(m["size"])
        results = [holds(f.formula, w, {**env, f.variable.name: d}, m) for d in individuals]
        return all(results) if f.type == "∀" else any(results)
    raise TypeError(type(f))


def vocabulary(f):
    predicates, constants, parameters = {}, set(), set()

    def walk(node, bound):
        if isinstance(node, Atom):
            if node.predicate != "=":
                predicates[node.predicate] = len(node.args)
        elif isinstance(node, Variable):
            if node.name not in bound:
                parameters.add(node.name)
        elif isinstance(node, Constant):
            constants.add(node.name)
        if isinstance(node, Quantifier):
            walk(node.formula, bound | {node.variable.name})
        else:
            for child in node._child_nodes():
                walk(child, bound)

    walk(f, frozenset())
    return predicates, sorted(constants), sorted(parameters)


def domains(mode, worlds, size, rel):
    if mode in ("constant", "possibilist"):
        yield tuple(frozenset(range(size)) for _ in range(worlds))
        return
    nonempty = [frozenset(i for i in range(size) if mask >> i & 1) for mask in range(1, 1 << size)]
    for choice in product(nonempty, repeat=worlds):
        if mode == "increasing" and any(not choice[u] <= choice[v] for (u, v) in rel):
            continue
        if mode == "decreasing" and any(not choice[v] <= choice[u] for (u, v) in rel):
            continue
        yield choice


def refuting_model(f, mode, worlds=2, size=2):
    """A model, world and assignment under which ``f`` is false, or ``None`` (a bounded search)."""
    predicates, constants, parameters = vocabulary(f)
    actualist = mode in VARYING
    pairs = [(i, j) for i in range(worlds) for j in range(worlds)]
    for bits in product((False, True), repeat=len(pairs)):
        rel = {p for p, b in zip(pairs, bits) if b}
        for doms in domains(mode, worlds, size, rel):
            slots = [(name, w) for name in sorted(predicates) for w in range(worlds)]
            options = []
            for name, _ in slots:
                tuples = list(product(range(size), repeat=predicates[name]))
                options.append([frozenset(t for t, on in zip(tuples, mask) if on)
                                for mask in product((False, True), repeat=len(tuples))])
            for extension in product(*options):
                for denotation in product(range(size), repeat=len(constants)):
                    m = {"rel": rel, "doms": doms, "size": size, "actualist": actualist,
                         "ext": dict(zip(slots, extension)),
                         "consts": dict(zip(constants, denotation))}
                    for w in range(worlds):
                        for values in product(range(size), repeat=len(parameters)):
                            if actualist and any(v not in doms[w] for v in values):
                                continue        # a parameter exists at the world of evaluation
                            if not holds(f, w, dict(zip(parameters, values)), m):
                                return m, w, dict(zip(parameters, values))
    return None


def model_of(mode, rel, doms, ext, consts=()):
    return {"rel": set(rel), "doms": doms, "size": 2, "actualist": mode in VARYING,
            "ext": ext, "consts": dict(consts)}


def test_the_hand_built_countermodel_of_row_1_refutes_it_in_every_regime():
    # one world, D = {0, 1}, x ↦ 1, alpha ↦ 0, P = {1}
    for mode in MODES:
        m = model_of(mode, [], (frozenset({0, 1}),), {("P", 0): frozenset({(1,)})}, {"alpha": 0})
        assert holds(ROWS[0][1], 0, {"x": 1}, m) is False


def test_the_hand_built_countermodel_of_row_5_refutes_it_in_every_regime():
    # one world, D = {0, 1}, x ↦ 0, y ↦ 1, P = {0}, Q = {1}
    for mode in MODES:
        m = model_of(mode, [], (frozenset({0, 1}),),
                     {("P", 0): frozenset({(0,)}), ("Q", 0): frozenset({(1,)})})
        assert holds(ROWS[4][1], 0, {"x": 0, "y": 1}, m) is False


@pytest.mark.parametrize("mode", ["varying", "decreasing"])
def test_the_hand_built_countermodel_of_rows_6_and_8_refutes_them(mode):
    # w0 R w1, D_w0 = {0, 1}, D_w1 = {1} (a decreasing pair), x ↦ 0 exists at w0, P = {1} at w1
    doms = (frozenset({0, 1}), frozenset({1}))
    m = model_of(mode, [(0, 1)], doms, {("P", 0): frozenset(), ("P", 1): frozenset({(1,)})})
    assert holds(ROWS[5][1], 0, {"x": 0}, m) is False          # □∀y P(y) → □P(x)
    assert holds(ROWS[7][1], 0, {"x": 0}, m) is False          # □∃y (y = x)


def test_the_hand_built_countermodel_of_row_9_refutes_it_where_individuals_may_be_missing():
    # one world, D_w = {0}, alpha ↦ 1 (outside D_w): ∃y (y = alpha) fails
    m = model_of("varying", [], (frozenset({0}),), {}, {"alpha": 1})
    assert holds(ROWS[8][1], 0, {}, m) is False


@pytest.mark.parametrize("label, formula, verdicts", ROWS, ids=[row[0] for row in ROWS])
@pytest.mark.parametrize("mode", MODES)
def test_the_oracle_agrees_with_every_row(label, formula, verdicts, mode):
    valid = verdicts[MODES.index(mode)] == "T"
    # a valid row has no countermodel among the models of two worlds and two individuals; an
    # invalid row has one, derived by hand above
    assert (refuting_model(formula, mode) is None) is valid


def random_formula(rng, depth, bound):
    terms = [Variable("y"), Variable("z"), Constant("alice")] + bound
    if depth == 0:
        if rng.random() < 0.75:
            return Atom("P", [rng.choice(terms)])
        return Atom("=", [rng.choice(terms), rng.choice(terms)])
    r = rng.random()
    if r < 0.15:
        return Not(random_formula(rng, depth - 1, bound))
    if r < 0.40:
        return rng.choice([And, Or, Implies, Iff])(random_formula(rng, depth - 1, bound),
                                                   random_formula(rng, depth - 1, bound))
    if r < 0.60:
        return rng.choice([Box, Diamond])(random_formula(rng, depth - 1, bound))
    if r < 0.90 and not bound:
        return Quantifier(rng.choice(["∀", "∃"]), x, random_formula(rng, depth - 1, [x]))
    return Atom("P", [rng.choice(terms)])


@pytest.mark.parametrize("mode", ["constant", "varying", "increasing", "decreasing"])
def test_random_formulas_with_free_variables_get_the_verdict_of_the_oracle(mode):
    # formulas of depth two or three over P, identity, one constant and the parameters y and z:
    # a countermodel of any of them, when there is one, has two worlds and two individuals
    rng = random.Random(20260705)
    for _ in range(60):
        formula = random_formula(rng, rng.choice([2, 3]), [])
        valid = qml_is_valid(formula, mode=mode, timeout=20000)
        assert valid is (refuting_model(formula, mode) is None), formula.to_unicode_str()
