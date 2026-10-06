"""Problems that use one name as two symbols, and the enumeration that says what they mean.

Shared by ``test_z3_one_name_two_symbols`` and ``test_cvc5_one_name_two_symbols``. A problem is generated
from a seed and a family of clashing symbols (a predicate at two arities, a function at two arities, a
predicate and a function of one name, a sort and a predicate of another arity, a proposition and a
constant); every problem carries the premise "there are at most two things" (``AT_MOST_TWO``), so that
"no countermodel of at most two elements" is validity.

The ORACLE reads the fields of the nodes only and shares no code with the kit: it enumerates every
structure of one or two elements in which each symbol of the family is independent of the others of the
same name (a sort is a non-empty subset, the unary predicate of its own name; ``c:S`` denotes an element
of ``S``).
"""
import itertools
import random

from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Or, Quantifier, SortedConstant, SortedQuantifier,
    Variable,
)

X, Y, Z = Variable("x"), Variable("y"), Variable("z")


def forall(var, body):
    return Quantifier("∀", var, body)


# the premise "there are at most two things": every generated problem carries it
AT_MOST_TWO = forall(X, forall(Y, forall(Z, Or(Atom("=", [X, Y]),
                                              Or(Atom("=", [X, Z]), Atom("=", [Y, Z]))))))


class Family:
    """The symbols of one kind of clash, as the oracle enumerates them."""

    def __init__(self, label, constants=(), functions=(), predicates=(), sort=None, sorted_constants=()):
        self.label = label
        self.constants = constants                  # plain constant names
        self.functions = functions                  # (name, arity)
        self.predicates = predicates                # (name, arity); a sort's own predicate is the sort
        self.sort = sort                            # a sort name, or None
        self.sorted_constants = sorted_constants    # constant names written c:sort


FAMILIES = (
    Family("predicate at two arities", constants=("a", "b"), predicates=(("P", 1), ("P", 2))),
    Family("function at two arities", constants=("a", "b"), functions=(("f", 1), ("f", 2))),
    Family("predicate and function of one name", constants=("a",), functions=(("Q", 1),),
           predicates=(("Q", 1), ("R", 1))),
    Family("sort and predicate of another arity", constants=("a",), predicates=(("S", 2), ("R", 1)),
           sort="S", sorted_constants=("c",)),
    Family("proposition and constant of one name", constants=("a",), predicates=(("a", 0), ("R", 1))),
)


def _term(rng, family, scope, depth=0):
    options = ["const"] * 3
    if scope:
        options += ["var"] * 4
    if family.sorted_constants:
        options += ["sorted"]
    if family.functions and depth == 0:
        options += ["func"] * 3
    kind = rng.choice(options)
    if kind == "var":
        return Variable(rng.choice(scope))
    if kind == "sorted":
        return SortedConstant(rng.choice(family.sorted_constants), family.sort)
    if kind == "func":
        name, arity = rng.choice(family.functions)
        return Function(name, [_term(rng, family, scope, depth + 1) for _ in range(arity)])
    return Constant(rng.choice(family.constants))


def _atom(rng, family, scope):
    if family.predicates and (not family.functions or rng.random() < 0.3):
        name, arity = rng.choice(family.predicates)
        return Atom(name, [_term(rng, family, scope) for _ in range(arity)])
    if family.sort and rng.random() < 0.4:
        return Atom(family.sort, [_term(rng, family, scope)])           # the sort as the unary predicate
    return Atom("=", [_term(rng, family, scope), _term(rng, family, scope)])


def _formula(rng, family, scope, depth):
    if depth == 0 or rng.random() < 0.25:
        return _atom(rng, family, scope)
    roll = rng.random()
    if roll < 0.15:
        return Not(_formula(rng, family, scope, depth - 1))
    if roll < 0.55:
        make = rng.choice((And, Or, Implies))
        return make(_formula(rng, family, scope, depth - 1), _formula(rng, family, scope, depth - 1))
    free = [v for v in ("x", "y") if v not in scope] or ["x"]
    var = Variable(rng.choice(free))
    body = _formula(rng, family, scope + (var.name,), depth - 1)
    if family.sort and rng.random() < 0.5:
        return SortedQuantifier(rng.choice(("∀", "∃")), var, family.sort, body)
    return Quantifier(rng.choice(("∀", "∃")), var, body)


def make_problem(seed, family):
    rng = random.Random(seed * 1009 + FAMILIES.index(family))
    premises = [_formula(rng, family, (), 2) for _ in range(rng.randint(0, 2))]
    goal = _formula(rng, family, (), 2)
    if premises and rng.random() < 0.35:
        goal = Or(rng.choice(premises), goal)          # valid on its face: keeps valid problems in the batch
    return premises, goal


# -- the oracle: reads the fields of the nodes only ---------------------------------------------
def _structures(family, size):
    """Every structure of ``size`` elements in which each symbol of ``family`` is independent."""
    domain = tuple(range(size))
    sort_choices = [()]
    if family.sort:
        sort_choices = [s for r in range(1, size + 1) for s in itertools.combinations(domain, r)]
    const_names = tuple(family.constants) + tuple(family.sorted_constants)
    for sort_set in sort_choices:
        for values in itertools.product(domain, repeat=len(const_names)):
            consts = dict(zip(const_names, values))
            if any(consts[c] not in sort_set for c in family.sorted_constants):
                continue
            function_tables = []
            for name, arity in family.functions:
                keys = list(itertools.product(domain, repeat=arity))
                function_tables.append([
                    ((name, arity), dict(zip(keys, outputs)))
                    for outputs in itertools.product(domain, repeat=len(keys))])
            relation_tables = []
            for name, arity in family.predicates:
                keys = list(itertools.product(domain, repeat=arity))
                relation_tables.append([
                    ((name, arity), frozenset(k for k, keep in zip(keys, flags) if keep))
                    for flags in itertools.product((False, True), repeat=len(keys))])
            for functions in itertools.product(*function_tables):
                for relations in itertools.product(*relation_tables):
                    yield domain, consts, dict(functions), dict(relations), frozenset(sort_set)


def _value(term, world, env):
    domain, consts, functions, relations, sort_set = world
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, (Constant, SortedConstant)):
        return consts[term.name]
    if isinstance(term, Function):
        args = tuple(_value(a, world, env) for a in term.args)
        return functions[(term.name, len(term.args))][args]
    raise AssertionError(term)


def _holds(node, world, env, sort_name):
    domain, consts, functions, relations, sort_set = world
    if isinstance(node, Atom):
        if node.predicate == "=":
            return _value(node.args[0], world, env) == _value(node.args[1], world, env)
        args = tuple(_value(a, world, env) for a in node.args)
        if sort_name is not None and node.predicate == sort_name and len(args) == 1:
            return args[0] in sort_set                # the sort IS the unary predicate of its name
        return args in relations[(node.predicate, len(args))]
    if isinstance(node, Not):
        return not _holds(node.formula, world, env, sort_name)
    if isinstance(node, And):
        return _holds(node.left, world, env, sort_name) and _holds(node.right, world, env, sort_name)
    if isinstance(node, Or):
        return _holds(node.left, world, env, sort_name) or _holds(node.right, world, env, sort_name)
    if isinstance(node, Implies):
        return (not _holds(node.left, world, env, sort_name)) or _holds(node.right, world, env, sort_name)
    if isinstance(node, SortedQuantifier):
        pool = [d for d in domain if d in sort_set]
    elif isinstance(node, Quantifier):
        pool = domain
    else:
        raise AssertionError(node)
    results = (_holds(node.formula, world, {**env, node.variable.name: d}, sort_name) for d in pool)
    return all(results) if node.type == "∀" else any(results)


def oracle_has_countermodel(premises, goal, family):
    for size in (1, 2):
        for world in _structures(family, size):
            if all(_holds(p, world, {}, family.sort) for p in premises) \
                    and not _holds(goal, world, {}, family.sort):
                return True
    return False
