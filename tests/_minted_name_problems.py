"""Problems whose symbols are named like the names the kit mints, and the enumeration that says what they mean.

Shared by ``test_smt_minted_names``. The kit mints names of its own: the tracking literals of a solver
(``goal``, ``p0``, ``p1``), the witnesses of a counting quantifier and of a sort's non-emptiness axiom
(``x0``, ``x1``, ``y0``), Skolem and tableau symbols (``_sk0``), the marks of the Z3 environment (``x!v``,
``a!c``) and the tokens of the SMT-LIB sanitiser (``P_2``, ``x0_0``). A problem generated here draws EVERY
kind of symbol -- propositions, predicates, functions, constants, sorts -- from that small stock of names,
so that a name is very often used for several kinds, and its formulas use plain, sorted and counting
quantifiers, which are the places where the kit mints.

The ORACLE reads the fields of the nodes only and shares no code with the kit. It enumerates every
structure of one or two elements (``AT_MOST_TWO`` is a premise of every problem, so "no countermodel of
at most two elements" is validity) in which the symbols are independent when their kinds differ:

* a constant, a function (unary), a predicate (unary or binary) and a proposition of one name are four
  symbols; a bound variable is none of them;
* a sort ``S`` is a non-empty subset of the domain and IS the unary predicate ``S`` (the guard reading), so
  a unary predicate named like the sort is that subset;
* a sorted constant ``c:S`` is an element of ``S``, and ``c:S`` and a plain ``c`` are one constant;
* ``∃≥n x φ`` is true when at least ``n`` DIFFERENT elements satisfy ``φ`` (``∃≤n`` at most, ``∃=n``
  exactly), and a sorted one counts the elements of the sort only.
"""
import itertools
import random

from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Or, Quantifier, SortedConstant,
    SortedCount, SortedQuantifier, Variable,
)

#: The names the problems draw their symbols from.
STOCK = ("goal", "p0", "x0", "y0", "_sk0", "x!v", "a!c", "x1")

X, Y, Z = Variable("x"), Variable("y"), Variable("z")

#: the premise "there are at most two things": every generated problem carries it
AT_MOST_TWO = Quantifier("∀", X, Quantifier("∀", Y, Quantifier("∀", Z, Or(
    Atom("=", [X, Y]), Or(Atom("=", [X, Z]), Atom("=", [Y, Z]))))))

#: how many structures of at most two elements a problem may have, for the enumeration to stay quick
_BUDGET = 700


class Symbols:
    """The symbols of one problem, by kind."""

    def __init__(self, constants, functions, predicates, relations, propositions, sort, sorted_constants):
        self.constants = constants                  # plain constant names
        self.functions = functions                  # unary function names
        self.predicates = predicates                # unary predicate names (never the sort's own name)
        self.relations = relations                  # binary predicate names
        self.propositions = propositions            # predicates of no arguments
        self.sort = sort                            # a sort name, or None
        self.sorted_constants = sorted_constants    # names of constants that are written c:sort somewhere

    def structures(self):
        """How many structures of one and of two elements there are: an upper bound for the budget."""
        total = 0
        for size in (1, 2):
            sorts = (2 ** size - 1) if self.sort else 1
            total += (size ** len(self.constants) * size ** (size * len(self.functions))
                      * 2 ** (size * len(self.predicates) + size * size * len(self.relations)
                              + len(self.propositions)) * sorts)
        return total


def _draw(rng, count):
    """``count`` names from the stock, with repetition across kinds but not within one kind."""
    return tuple(rng.sample(STOCK, count))


def _symbols(rng):
    while True:
        constants = _draw(rng, rng.randint(1, 2))
        functions = _draw(rng, rng.randint(0, 1))
        sort = rng.choice(STOCK) if rng.random() < 0.5 else None
        predicates = tuple(n for n in _draw(rng, rng.randint(0, 2)) if n != sort)
        relations = tuple(n for n in _draw(rng, rng.randint(0, 1)) if n != sort) if rng.random() < 0.5 else ()
        propositions = _draw(rng, rng.randint(0, 1))
        sorted_constants = tuple(c for c in constants if sort and rng.random() < 0.5)
        symbols = Symbols(constants, functions, predicates, relations, propositions, sort, sorted_constants)
        if symbols.structures() <= _BUDGET:
            return symbols


def _term(rng, symbols, scope, depth=0):
    options = ["const"] * 3
    if scope:
        options += ["var"] * 4
    if symbols.sorted_constants:
        options += ["sorted"]
    if symbols.functions and depth == 0:
        options += ["func"] * 2
    kind = rng.choice(options)
    if kind == "var":
        return Variable(rng.choice(scope))
    if kind == "sorted":
        return SortedConstant(rng.choice(symbols.sorted_constants), symbols.sort)
    if kind == "func":
        return Function(rng.choice(symbols.functions), [_term(rng, symbols, scope, depth + 1)])
    return Constant(rng.choice(symbols.constants))


def _atom(rng, symbols, scope):
    choices = []
    if symbols.predicates:
        choices += ["pred"] * 3
    if symbols.relations:
        choices += ["rel"] * 2
    if symbols.propositions:
        choices += ["prop"]
    if symbols.sort:
        choices += ["sort"] * 2
    choices += ["eq"]
    kind = rng.choice(choices)
    if kind == "pred":
        return Atom(rng.choice(symbols.predicates), [_term(rng, symbols, scope)])
    if kind == "rel":
        return Atom(rng.choice(symbols.relations), [_term(rng, symbols, scope), _term(rng, symbols, scope)])
    if kind == "prop":
        return Atom(rng.choice(symbols.propositions), [])
    if kind == "sort":
        return Atom(symbols.sort, [_term(rng, symbols, scope)])
    return Atom("=", [_term(rng, symbols, scope), _term(rng, symbols, scope)])


#: the names a quantifier binds: the letters the counting witnesses are made from (so ``x`` mints ``x0``),
#: and the names of the stock that are legal variables
_BINDERS = ("x", "y", "x0", "y0")


def _formula(rng, symbols, scope, depth):
    if depth == 0 or rng.random() < 0.2:
        return _atom(rng, symbols, scope)
    roll = rng.random()
    if roll < 0.12:
        return Not(_formula(rng, symbols, scope, depth - 1))
    if roll < 0.40:
        make = rng.choice((And, Or, Implies))
        return make(_formula(rng, symbols, scope, depth - 1), _formula(rng, symbols, scope, depth - 1))
    var = Variable(rng.choice(_BINDERS))
    body = _formula(rng, symbols, scope + (var.name,), depth - 1)
    sorted_binder = bool(symbols.sort) and rng.random() < 0.5
    if roll < 0.70:
        quantifier = rng.choice(("∀", "∃"))
        if sorted_binder:
            return SortedQuantifier(quantifier, var, symbols.sort, body)
        return Quantifier(quantifier, var, body)
    op, bound = rng.choice(("ge", "le", "eq")), Number(rng.choice((0, 1, 2)))
    if sorted_binder:
        return SortedCount(op, bound, var, symbols.sort, body)
    return Count(op, bound, var, body)


_SORTED_NODES = (SortedQuantifier, SortedCount, SortedConstant)


def _used(nodes, drawn):
    """The symbols the formulas ``nodes`` actually use, by kind (the oracle enumerates those only).

    A sort is DECLARED (non-empty, and its constants inside it) when a sorted node names it. A unary atom of
    the drawn sort's name without one is an ordinary unary predicate.
    """
    constants, sorted_constants, functions, predicates, relations, propositions = [], [], [], [], [], []
    declared = False
    for root in nodes:
        for node in root.walk():
            if isinstance(node, _SORTED_NODES):
                declared = True
            if isinstance(node, SortedConstant):
                for bucket in (constants, sorted_constants):
                    if node.name not in bucket:
                        bucket.append(node.name)
            elif isinstance(node, Constant) and node.name not in constants:
                constants.append(node.name)
            elif isinstance(node, Function) and node.name not in functions:
                functions.append(node.name)
            elif isinstance(node, Atom) and node.predicate != "=":
                bucket = (propositions, predicates, relations)[len(node.args)]
                if node.predicate not in bucket:
                    bucket.append(node.predicate)
    sort = drawn.sort if declared else None
    if sort is not None:
        predicates = [p for p in predicates if p != sort]
    return Symbols(tuple(constants), tuple(functions), tuple(predicates), tuple(relations),
                   tuple(propositions), sort, tuple(sorted_constants))


def make_problem(seed):
    """``(premises, goal, symbols)`` for ``seed``; the premises do not hold ``AT_MOST_TWO`` yet."""
    rng = random.Random(seed * 7919 + 13)
    drawn = _symbols(rng)
    premises = [_formula(rng, drawn, (), 2) for _ in range(rng.randint(0, 2))]
    goal = _formula(rng, drawn, (), 2)
    if premises and rng.random() < 0.3:
        goal = Or(rng.choice(premises), goal)            # valid on its face: keeps valid problems in the batch
    return premises, goal, _used(premises + [goal], drawn)


# -- the oracle ---------------------------------------------------------------------------------------------
def _worlds(symbols, size):
    domain = tuple(range(size))
    sort_choices = [()]
    if symbols.sort:
        sort_choices = [s for r in range(1, size + 1) for s in itertools.combinations(domain, r)]
    names = tuple(symbols.constants)
    for sort_set in sort_choices:
        for values in itertools.product(domain, repeat=len(names)):
            constants = dict(zip(names, values))
            if any(constants[c] not in sort_set for c in symbols.sorted_constants):
                continue
            function_tables = []
            for name in symbols.functions:
                function_tables.append([(name, dict(zip(domain, outputs)))
                                        for outputs in itertools.product(domain, repeat=size)])
            predicate_tables = [[(name, frozenset(d for d, keep in zip(domain, flags) if keep))
                                 for flags in itertools.product((False, True), repeat=size)]
                                for name in symbols.predicates]
            pairs = list(itertools.product(domain, repeat=2))
            relation_tables = [[(name, frozenset(p for p, keep in zip(pairs, flags) if keep))
                                for flags in itertools.product((False, True), repeat=len(pairs))]
                               for name in symbols.relations]
            for functions in itertools.product(*function_tables):
                for predicates in itertools.product(*predicate_tables):
                    for relations in itertools.product(*relation_tables):
                        for flags in itertools.product((False, True), repeat=len(symbols.propositions)):
                            yield {"domain": domain, "constants": constants, "functions": dict(functions),
                                   "predicates": dict(predicates), "relations": dict(relations),
                                   "propositions": dict(zip(symbols.propositions, flags)),
                                   "sort": frozenset(sort_set)}


def _value(term, world, env):
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, (Constant, SortedConstant)):
        return world["constants"][term.name]
    if isinstance(term, Function):
        return world["functions"][term.name][_value(term.args[0], world, env)]
    raise AssertionError(term)


def _holds(node, world, env, sort_name):
    if isinstance(node, Atom):
        if node.predicate == "=":
            return _value(node.args[0], world, env) == _value(node.args[1], world, env)
        if not node.args:
            return world["propositions"][node.predicate]
        args = tuple(_value(a, world, env) for a in node.args)
        if len(args) == 1:
            if node.predicate == sort_name:
                return args[0] in world["sort"]                 # the sort IS the unary predicate of its name
            return args[0] in world["predicates"][node.predicate]
        return args in world["relations"][node.predicate]
    if isinstance(node, Not):
        return not _holds(node.formula, world, env, sort_name)
    if isinstance(node, And):
        return _holds(node.left, world, env, sort_name) and _holds(node.right, world, env, sort_name)
    if isinstance(node, Or):
        return _holds(node.left, world, env, sort_name) or _holds(node.right, world, env, sort_name)
    if isinstance(node, Implies):
        return (not _holds(node.left, world, env, sort_name)) or _holds(node.right, world, env, sort_name)
    if isinstance(node, (SortedQuantifier, SortedCount)):
        pool = [d for d in world["domain"] if d in world["sort"]]
    elif isinstance(node, (Quantifier, Count)):
        pool = world["domain"]
    else:
        raise AssertionError(node)
    results = [_holds(node.formula, world, {**env, node.variable.name: d}, sort_name) for d in pool]
    if isinstance(node, (SortedQuantifier, Quantifier)):
        return all(results) if node.type == "∀" else any(results)
    counted, bound = sum(results), node.n.value
    return {"ge": counted >= bound, "le": counted <= bound, "eq": counted == bound}[node.op]


def has_countermodel(premises, goal, symbols):
    """Is there a structure of one or two elements that satisfies the premises and falsifies the goal?"""
    for size in (1, 2):
        for world in _worlds(symbols, size):
            if all(_holds(p, world, {}, symbols.sort) for p in premises) \
                    and not _holds(goal, world, {}, symbols.sort):
                return True
    return False
