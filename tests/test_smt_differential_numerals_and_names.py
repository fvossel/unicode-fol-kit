"""Z3 and cvc5 against an enumeration written from the definition: numerals, names spelled like variables.

Generated problems with numerals (``1`` and ``1.0`` are one constant, ``1`` and ``2`` may be one element), the
operators ``+`` (an uninterpreted function) and ``<`` (an uninterpreted binary predicate), constants spelled
like a bound variable (``x``, ``y``) or like a variable the kit mints (``x0``, ``x1`` for the witnesses of a
counting quantifier, ``w`` for a world), and counting quantifiers. Every problem carries the premise "there are
at most two things", so that "no countermodel of at most two elements" is validity.

The ORACLE reads the fields of the nodes only and shares no code with the kit. It enumerates every structure of
one or two elements in which

* a numeral is a constant identified by its value (``Fraction(value)``: ``1`` and ``1.0`` are the same
  constant, ``1`` and ``2`` are two constants that may denote the same element),
* a constant is identified by its name, and a bound variable is not a constant, whatever it is called,
* every function symbol and every predicate symbol, ``+`` and ``<`` among them, is an independent table,
* ``=`` is identity and ``∃≥n`` / ``∃≤n`` / ``∃=n`` count the elements that satisfy the matrix.

Z3 decides every problem and must agree with the enumeration. cvc5 is incomplete on quantified problems and
may say ``unknown``; it must never contradict the enumeration, and it runs in a child process (a text it
cannot read ends the process).
"""
import itertools
import json
import random
import subprocess
import sys
from fractions import Fraction

import pytest

from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, Z3Backend
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Or, Quantifier, Variable,
)

X, Y, Z = Variable("x"), Variable("y"), Variable("z")


def forall(var, body):
    return Quantifier("∀", var, body)


# the premise "there are at most two things": every generated problem carries it
AT_MOST_TWO = forall(X, forall(Y, forall(Z, Or(Atom("=", [X, Y]), Or(Atom("=", [X, Z]), Atom("=", [Y, Z]))))))


class Family:
    """The symbols of one kind of problem: numerals, constants, functions, predicates, and whether to count."""

    def __init__(self, label, numerals=(), constants=(), functions=(), predicates=(), counting=False,
                 variables=("x", "y")):
        self.label = label
        self.numerals = tuple(numerals)         # Number nodes (several spellings of a value may be listed)
        self.constants = tuple(constants)       # Constant names
        self.functions = tuple(functions)       # (name, arity)
        self.predicates = tuple(predicates)     # (name, arity)
        self.counting = counting
        self.variables = tuple(variables)       # the names the generator may bind

    @property
    def identities(self):
        """The independent constants: one per numeral VALUE, one per name."""
        values = sorted({("n", Fraction(n.value)) for n in self.numerals})
        return tuple(values) + tuple(("c", name) for name in self.constants)


FAMILIES = (
    Family("numerals and an order", numerals=(Number(1), Number(1.0), Number(2)), constants=("one",),
           predicates=(("P", 1), ("<", 2))),
    Family("numerals and a sum", numerals=(Number(1), Number(2), Number(2.0)), constants=("one",),
           functions=(("+", 2),), predicates=(("P", 1),)),
    Family("constants spelled like the bound variables", constants=("x", "y", "alpha"),
           predicates=(("P", 2), ("Q", 1))),
    Family("constants spelled like minted variables", constants=("x0", "x1", "w"),
           predicates=(("P", 2),), counting=True, variables=("x", "y")),
)


# -- generation ---------------------------------------------------------------------------------
def _term(rng, family, scope, depth=0):
    options = ["leaf"] * 4
    if scope:
        options += ["var"] * 3
    if family.functions and depth == 0:
        options += ["func"] * 3
    kind = rng.choice(options)
    if kind == "var":
        return Variable(rng.choice(scope))
    if kind == "func":
        name, arity = rng.choice(family.functions)
        return Function(name, [_term(rng, family, scope, depth + 1) for _ in range(arity)])
    leaves = [("n", n) for n in family.numerals] + [("c", c) for c in family.constants]
    tag, leaf = rng.choice(leaves)
    return leaf if tag == "n" else Constant(leaf)


def _atom(rng, family, scope):
    if family.predicates and rng.random() < 0.65:
        name, arity = rng.choice(family.predicates)
        return Atom(name, [_term(rng, family, scope) for _ in range(arity)])
    return Atom(rng.choice(("=", "=", "≠")), [_term(rng, family, scope), _term(rng, family, scope)])


def _formula(rng, family, scope, depth):
    if depth == 0 or rng.random() < 0.25:
        return _atom(rng, family, scope)
    roll = rng.random()
    if roll < 0.15:
        return Not(_formula(rng, family, scope, depth - 1))
    if roll < 0.5:
        make = rng.choice((And, Or, Implies))
        return make(_formula(rng, family, scope, depth - 1), _formula(rng, family, scope, depth - 1))
    free = [v for v in family.variables if v not in scope] or [family.variables[0]]
    var = Variable(rng.choice(free))
    body = _formula(rng, family, scope + (var.name,), depth - 1)
    if family.counting and rng.random() < 0.4:
        return Count(rng.choice(("ge", "le", "eq")), Number(rng.choice((1, 2))), var, body)
    return Quantifier(rng.choice(("∀", "∃")), var, body)


def make_problem(seed, family):
    rng = random.Random(seed * 7919 + FAMILIES.index(family))
    premises = [_formula(rng, family, (), 2) for _ in range(rng.randint(0, 2))]
    goal = _formula(rng, family, (), 2)
    if premises and rng.random() < 0.35:
        goal = Or(rng.choice(premises), goal)                 # valid on its face: keeps valid problems in the batch
    return premises, goal


# -- the oracle: reads the fields of the nodes only ---------------------------------------------
def _structures(family, size):
    domain = tuple(range(size))
    identities = family.identities
    for values in itertools.product(domain, repeat=len(identities)):
        consts = dict(zip(identities, values))
        function_tables = []
        for name, arity in family.functions:
            keys = list(itertools.product(domain, repeat=arity))
            function_tables.append([((name, arity), dict(zip(keys, outputs)))
                                    for outputs in itertools.product(domain, repeat=len(keys))])
        relation_tables = []
        for name, arity in family.predicates:
            keys = list(itertools.product(domain, repeat=arity))
            relation_tables.append([((name, arity), frozenset(k for k, keep in zip(keys, flags) if keep))
                                    for flags in itertools.product((False, True), repeat=len(keys))])
        for functions in itertools.product(*function_tables):
            for relations in itertools.product(*relation_tables):
                yield domain, consts, dict(functions), dict(relations)


def _value(term, world, env):
    domain, consts, functions, relations = world
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, Number):
        return consts[("n", Fraction(term.value))]
    if isinstance(term, Constant):
        return consts[("c", term.name)]
    if isinstance(term, Function):
        args = tuple(_value(a, world, env) for a in term.args)
        return functions[(term.name, len(term.args))][args]
    raise AssertionError(term)


def _holds(node, world, env):
    domain, consts, functions, relations = world
    if isinstance(node, Atom):
        args = tuple(_value(a, world, env) for a in node.args)
        if node.predicate == "=":
            return args[0] == args[1]
        if node.predicate == "≠":
            return args[0] != args[1]
        return args in relations[(node.predicate, len(args))]
    if isinstance(node, Not):
        return not _holds(node.formula, world, env)
    if isinstance(node, And):
        return _holds(node.left, world, env) and _holds(node.right, world, env)
    if isinstance(node, Or):
        return _holds(node.left, world, env) or _holds(node.right, world, env)
    if isinstance(node, Implies):
        return (not _holds(node.left, world, env)) or _holds(node.right, world, env)
    if isinstance(node, Count):
        k = sum(1 for d in domain if _holds(node.formula, world, {**env, node.variable.name: d}))
        bound = node.n.value
        return {"ge": k >= bound, "le": k <= bound, "eq": k == bound}[node.op]
    if isinstance(node, Quantifier):
        results = (_holds(node.formula, world, {**env, node.variable.name: d}) for d in domain)
        return all(results) if node.type == "∀" else any(results)
    raise AssertionError(node)


def oracle_has_countermodel(premises, goal, family):
    for size in (1, 2):
        for world in _structures(family, size):
            if all(_holds(p, world, {}) for p in premises) and not _holds(goal, world, {}):
                return True
    return False


# ---------------------------------------------------------------------------------------------
# the oracle against the hand-derived table (so that a disagreement below is not the oracle's)
# ---------------------------------------------------------------------------------------------
def _P(arg):
    return Atom("P", [arg])


def test_the_oracle_gives_the_derived_answers():
    order = FAMILIES[0]
    sums = FAMILIES[1]
    one, two = Number(1), Number(2)
    # A2  P(1) ⊢ P(1.0) is valid: one constant
    assert not oracle_has_countermodel([_P(one)], _P(Number(1.0)), order)
    # A3  ⊢ 1 ≠ 2 is not valid: a one-element universe
    assert oracle_has_countermodel([], Atom("≠", [one, two]), order)
    # A4  ⊢ 1 < 2 is not valid: < empty
    assert oracle_has_countermodel([], Atom("<", [one, two]), order)
    # A7  P(1) ⊢ P(one) is not valid: universe {0, 1}, 1 = 0, one = 1, P = {0}
    assert oracle_has_countermodel([_P(one)], _P(Constant("one")), order)
    # A5  ⊢ 1 + 1 = 2 is not valid: universe {0, 1}, 1 = 0, 2 = 1, + constantly 0
    assert oracle_has_countermodel([], Atom("=", [Function("+", [one, one]), two]), sums)
    # A8  ∀x∀y x+y = y+x ⊢ 1+2 = 2+1 is valid
    commutes = forall(X, forall(Y, Atom("=", [Function("+", [X, Y]), Function("+", [Y, X])])))
    assert not oracle_has_countermodel([commutes], Atom("=", [Function("+", [one, two]), Function("+", [two, one])]), sums)
    # a constant spelled x under ∀x: ∀x P(x, c) ⊢ P(alpha, c) is valid, ⊢ P(alpha, alpha) is not
    names = FAMILIES[2]
    premise = forall(X, Atom("P", [X, Constant("x")]))
    assert not oracle_has_countermodel([premise], Atom("P", [Constant("alpha"), Constant("x")]), names)
    assert oracle_has_countermodel([premise], Atom("P", [Constant("alpha"), Constant("alpha")]), names)
    # a counting witness name: ∃≥2 x P(x, x0) ⊢ ∃y P(y, x0) is valid, ∃≤1 x P(x, x0) ⊬ ∃≥1 ...
    minted = FAMILIES[3]
    at_least_two = Count("ge", Number(2), X, Atom("P", [X, Constant("x0")]))
    assert not oracle_has_countermodel([at_least_two], Quantifier("∃", Y, Atom("P", [Y, Constant("x0")])), minted)
    assert oracle_has_countermodel([], Count("ge", Number(1), X, Atom("P", [X, Constant("x0")])), minted)


# ---------------------------------------------------------------------------------------------
# the batch
# ---------------------------------------------------------------------------------------------
PER_FAMILY = 50
CVC5_PER_FAMILY = 50
BATCH = [(index, seed) for index in range(len(FAMILIES)) for seed in range(1, PER_FAMILY + 1)]


@pytest.fixture(scope="module")
def problems():
    rows = []
    for index, seed in BATCH:
        family = FAMILIES[index]
        premises, goal = make_problem(seed, family)
        rows.append((family, seed, premises + [AT_MOST_TWO], goal, oracle_has_countermodel(premises, goal, family)))
    return rows


def test_the_batch_has_both_kinds_of_problem(problems):
    refutable = sum(1 for *_, has in problems if has)
    assert 0.2 * len(problems) < refutable < 0.9 * len(problems), (refutable, len(problems))


def test_z3_agrees_with_the_enumeration(problems):
    undecided = 0
    for family, seed, premises, goal, has_countermodel in problems:
        verdict = Z3Backend().decide(goal, premises, timeout=20000)
        label = (family.label, seed)
        if verdict.status == UNKNOWN:
            undecided += 1
            continue
        assert verdict.status == (REFUTED if has_countermodel else PROVED), label
    assert undecided <= len(problems) // 10


_CVC5_CHILD = r"""
import json, sys
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.fol.nodes import Node

out = []
for spec in json.loads(sys.stdin.read()):
    premises = [Node.from_dict(d) for d in spec["premises"]]
    goal = Node.from_dict(spec["goal"])
    out.append(Cvc5Backend().decide(goal, premises, timeout=4000).status)
print(json.dumps(out))
"""


def test_cvc5_never_contradicts_the_enumeration(problems):
    pytest.importorskip("cvc5")
    chosen = [row for row in problems
              if row[1] <= CVC5_PER_FAMILY]
    spec = json.dumps([{"premises": [p.to_dict() for p in premises], "goal": goal.to_dict()}
                       for _, _, premises, goal, _ in chosen])
    done = subprocess.run([sys.executable, "-c", _CVC5_CHILD], input=spec, capture_output=True, text=True,
                          encoding="utf-8", timeout=900)
    assert done.returncode == 0, f"the child process ended with exit code {done.returncode}: {done.stderr[-400:]}"
    statuses = json.loads(done.stdout.strip().splitlines()[-1])
    assert len(statuses) == len(chosen)
    for (family, seed, _, _, has_countermodel), status in zip(chosen, statuses):
        assert status != (PROVED if has_countermodel else REFUTED), (family.label, seed, status)
