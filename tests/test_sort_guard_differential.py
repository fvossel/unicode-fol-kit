"""Random many-sorted problems: every Z3-family route against an enumeration written from the definition.

The definition: ONE universe; a sort is a non-empty subset of it (the extension of the unary predicate of
its name); sorts may overlap; a sorted constant ``c:S`` denotes an element of ``S`` -- of EVERY sort it is
written with -- and ``c:S`` here and a plain ``c`` there are one constant; an unsorted constant, an unsorted
variable and the value of a function may be any element; a predicate is any relation over the universe.

The ORACLE below enumerates every structure of that definition with one or two elements and evaluates the
formulas itself, reading only the fields of the nodes (it shares no code with the kit's evaluators or with
the guard reduction). A countermodel it finds is definitive: the entailment is invalid. Finding none is not a
proof of validity, so the direction that can be asserted for every problem is

    a route answers "proved"  =>  the oracle has no countermodel of at most two elements,

and the routes must give one and the same verdict on a problem whichever door they enter by (a route that
forgot a fact the others add would differ).

The routes are the ones that build their Z3 query from the sorted formulas: ``Z3Backend``, an
``IncrementalSession``, ``z3_models.is_valid``, ``formulas_are_equivalent`` (P and P ∧ G are equivalent iff
P ⊨ G), the ``eval.equivalence`` solver level, and the ``msfol → fol`` comorphism edge with its ``.axioms``
as premises. The resolution prover is sound but incomplete: it may fail to prove, never prove an invalid
entailment.

Everything runs in this process on Z3 and the kit's own prover: no external binary is needed.
"""
import itertools
import random

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import z3_models
from unicode_fol_kit.atp.incremental import IncrementalSession
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, Z3Backend
from unicode_fol_kit.atp.resolution import prove as resolution_prove
from unicode_fol_kit.atp.z3_equivalence import formulas_are_equivalent
from unicode_fol_kit.eval.equivalence import equivalent
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Iff, Implies, Not, Or, Quantifier,
    SortedConstant, SortedQuantifier, Variable,
)

SORTS = ("A", "B")
UNARY = ("P", "Q")
PLAIN = ("alpha", "beta", "carl")                    # carl is ALSO written sorted: one constant
SORTED = (("carl", "A"), ("dora", "B"), ("emil", "A"), ("dora", "A"))     # dora is written with two sorts
VARIABLES = ("x", "y", "z")

VALID, INVALID = "valid", "invalid"


# ---------------------------------------------------------------------------------------------
# generator
# ---------------------------------------------------------------------------------------------
def _term(rng, scope, depth=0):
    roll = rng.random()
    if scope and roll < 0.45:
        return Variable(rng.choice(scope))
    if roll < 0.62:
        return Constant(rng.choice(PLAIN))
    if roll < 0.88:
        name, sort = rng.choice(SORTED)
        return SortedConstant(name, sort)
    if depth == 0:
        return Function("f", [_term(rng, scope, 1)])
    return Constant(rng.choice(PLAIN))


def _atom(rng, scope):
    if rng.random() < 0.25:
        return Atom("=", [_term(rng, scope), _term(rng, scope)])
    return Atom(rng.choice(UNARY), [_term(rng, scope)])


def _formula(rng, scope, depth):
    if depth == 0 or rng.random() < 0.18:
        return _atom(rng, scope)
    roll = rng.random()
    if roll < 0.14:
        return Not(_formula(rng, scope, depth - 1))
    if roll < 0.46:
        return rng.choice((And, Or, Implies, Iff))(_formula(rng, scope, depth - 1),
                                                     _formula(rng, scope, depth - 1))
    free = [v for v in VARIABLES if v not in scope]
    if not free:
        return _atom(rng, scope)
    kind = rng.choice("∀∃")
    body = _formula(rng, scope + [free[0]], depth - 1)
    if rng.random() < 0.6:
        return SortedQuantifier(kind, Variable(free[0]), rng.choice(SORTS), body)
    return Quantifier(kind, Variable(free[0]), body)


def _substitute(node, name, term):
    """``node`` with the free variable ``name`` replaced by ``term`` (the generator never rebinds a name)."""
    kind = type(node)
    if kind is Variable:
        return term if node.name == name else node
    if kind in (Constant, SortedConstant):
        return node
    if kind is Function:
        return Function(node.name, [_substitute(a, name, term) for a in node.args])
    if kind is Atom:
        return Atom(node.predicate, [_substitute(a, name, term) for a in node.args])
    if kind is Not:
        return Not(_substitute(node.formula, name, term))
    if kind in (And, Or, Implies, Iff):
        return kind(_substitute(node.left, name, term), _substitute(node.right, name, term))
    if kind is Quantifier:
        return Quantifier(node.type, node.variable, _substitute(node.formula, name, term))
    return SortedQuantifier(node.type, node.variable, node.sort, _substitute(node.formula, name, term))


def problem(seed):
    """``(premises, conclusion)``: half random, half in the SHAPE of an entailment (instantiate a sorted or
    unsorted universal at a sorted constant, an unsorted constant or a function value; generalise one back
    to an existential), so that valid ones are common. Which are valid is for the oracle to say."""
    rng = random.Random(seed)
    if rng.random() < 0.5:
        premises = [_formula(rng, [], rng.choice((1, 2, 2, 3))) for _ in range(rng.choice((0, 1, 1, 2)))]
        return premises, _formula(rng, [], rng.choice((1, 2, 2, 3)))
    body = _formula(rng, ["w"], rng.choice((0, 1, 1, 2)))
    name, own_sort = rng.choice(SORTED)
    witness = rng.choice((SortedConstant(name, own_sort), SortedConstant(name, own_sort),
                          Constant(rng.choice(PLAIN)), Function("f", [Constant(rng.choice(PLAIN))])))
    w, sort = Variable("w"), rng.choice(SORTS)
    extra = [_formula(rng, [], 1)] if rng.random() < 0.3 else []
    shape = rng.random()
    if shape < 0.4:                                    # ∀w:S φ(w)  ⊢  φ(t)
        return [SortedQuantifier("∀", w, sort, body)] + extra, _substitute(body, "w", witness)
    if shape < 0.55:                                   # ∀w φ(w)  ⊢  φ(t)
        return [Quantifier("∀", w, body)] + extra, _substitute(body, "w", witness)
    if shape < 0.9:                                    # φ(t)  ⊢  ∃w:S φ(w)
        return [_substitute(body, "w", witness)] + extra, SortedQuantifier("∃", w, sort, body)
    return [_substitute(body, "w", witness)] + extra, Quantifier("∃", w, body)


# ---------------------------------------------------------------------------------------------
# the oracle
# ---------------------------------------------------------------------------------------------
def _vocabulary(formulas):
    constants, annotated, sorts, predicates, functions = set(), {}, set(), set(), set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Constant):
                constants.add(node.name)
            elif isinstance(node, SortedConstant):
                constants.add(node.name)
                annotated.setdefault(node.name, set()).add(node.sort)
                sorts.add(node.sort)
            elif isinstance(node, SortedQuantifier):
                sorts.add(node.sort)
            elif isinstance(node, Atom) and node.predicate != "=":
                predicates.add(node.predicate)
            elif isinstance(node, Function):
                functions.add(node.name)
    return sorted(constants), annotated, sorted(sorts), sorted(predicates), sorted(functions)


def _value(term, structure, env):
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, (Constant, SortedConstant)):
        return structure["const"][term.name]
    return structure["func"][term.name][_value(term.args[0], structure, env)]


def _holds(node, structure, env):
    if isinstance(node, Atom):
        if node.predicate == "=":
            return _value(node.args[0], structure, env) == _value(node.args[1], structure, env)
        return _value(node.args[0], structure, env) in structure["pred"][node.predicate]
    if isinstance(node, Not):
        return not _holds(node.formula, structure, env)
    if isinstance(node, And):
        return _holds(node.left, structure, env) and _holds(node.right, structure, env)
    if isinstance(node, Or):
        return _holds(node.left, structure, env) or _holds(node.right, structure, env)
    if isinstance(node, Implies):
        return (not _holds(node.left, structure, env)) or _holds(node.right, structure, env)
    if isinstance(node, Iff):
        return _holds(node.left, structure, env) == _holds(node.right, structure, env)
    domain = (structure["sort"][node.sort] if isinstance(node, SortedQuantifier) else structure["universe"])
    results = (_holds(node.formula, structure, {**env, node.variable.name: d}) for d in domain)
    return all(results) if node.type == "∀" else any(results)


def countermodel(premises, conclusion, max_size=2):
    """A structure of the definition (at most ``max_size`` elements) in which every premise holds and the
    conclusion does not, or ``None``."""
    constants, annotated, sorts, predicates, functions = _vocabulary(list(premises) + [conclusion])
    for size in range(1, max_size + 1):
        universe = tuple(range(size))
        subsets = [frozenset(c) for r in range(size + 1) for c in itertools.combinations(universe, r)]
        non_empty = [s for s in subsets if s]
        tables = [dict(zip(universe, image)) for image in itertools.product(universe, repeat=size)]
        for sort_choice in itertools.product(non_empty, repeat=len(sorts)):
            sort_map = dict(zip(sorts, sort_choice))
            ranges = []
            for name in constants:
                allowed = set(universe)
                for sort in annotated.get(name, ()):          # an element of EVERY sort it is written with
                    allowed &= sort_map[sort]
                ranges.append(sorted(allowed))
            for const_choice in itertools.product(*ranges):
                for pred_choice in itertools.product(subsets, repeat=len(predicates)):
                    for func_choice in itertools.product(tables, repeat=len(functions)):
                        structure = {"universe": universe, "sort": sort_map,
                                     "const": dict(zip(constants, const_choice)),
                                     "pred": dict(zip(predicates, pred_choice)),
                                     "func": dict(zip(functions, func_choice))}
                        if (all(_holds(p, structure, {}) for p in premises)
                                and not _holds(conclusion, structure, {})):
                            return structure
    return None


# ---------------------------------------------------------------------------------------------
# the routes
# ---------------------------------------------------------------------------------------------
def _conjunction(parts):
    out = parts[0]
    for part in parts[1:]:
        out = And(out, part)
    return out


def _verdict(proved):
    return {True: VALID, False: INVALID, None: None}[proved]


def route_backend(premises, goal):
    status = Z3Backend().decide(goal, premises).status
    return VALID if status == PROVED else INVALID if status == REFUTED else None


def route_session(premises, goal):
    status = IncrementalSession(premises).decide(goal).status
    return VALID if status == PROVED else INVALID if status == REFUTED else None


def route_is_valid(premises, goal):
    sentence = Implies(_conjunction(premises), goal) if premises else goal
    return VALID if z3_models.is_valid(sentence) else INVALID


_TAUTOLOGY = Or(Atom("Tau", []), Not(Atom("Tau", [])))


def route_equivalence(premises, goal):
    """P ⊨ G iff P is equivalent to P ∧ G; with no premises, iff G is equivalent to a tautology."""
    if not premises:
        return VALID if formulas_are_equivalent(goal, _TAUTOLOGY) else INVALID
    p = _conjunction(premises)
    return VALID if formulas_are_equivalent(p, And(p, goal)) else INVALID


def route_eval_equivalence(premises, goal):
    if not premises:
        return _verdict(equivalent(goal, _TAUTOLOGY, method="solver").equivalent)
    p = _conjunction(premises)
    return _verdict(equivalent(p, And(p, goal), method="solver").equivalent)


def route_comorphism(premises, goal):
    """Each formula through the msfol → fol edge; its images, and every edge's axioms, as premises."""
    images = [api.translate(f, "msfol", "fol") for f in [*premises, goal]]
    *premise_images, goal_image = images
    background = [axiom for t in images for axiom in t.axioms]
    status = Z3Backend().decide(goal_image.result, [t.result for t in premise_images] + background).status
    return VALID if status == PROVED else INVALID if status == REFUTED else None


ROUTES = {"Z3Backend": route_backend, "IncrementalSession": route_session,
          "z3_models.is_valid": route_is_valid, "formulas_are_equivalent": route_equivalence,
          "eval.equivalence": route_eval_equivalence, "msfol→fol edge": route_comorphism}

SEEDS = range(1, 301)


@pytest.fixture(scope="module")
def results():
    out = {}
    for seed in SEEDS:
        premises, goal = problem(seed)
        out[seed] = {"premises": premises, "goal": goal,
                     "counter": countermodel(premises, goal),
                     "answers": {name: route(premises, goal) for name, route in ROUTES.items()}}
    return out


def _shown(entry):
    premises = ", ".join(p.to_unicode_str() for p in entry["premises"]) or "(no premises)"
    return f"{premises}  ⊢  {entry['goal'].to_unicode_str()}"


def test_the_routes_never_disagree_with_the_enumeration_about_a_countermodel(results):
    wrong = [(seed, name, _shown(e)) for seed, e in results.items()
             for name, answer in e["answers"].items()
             if answer == VALID and e["counter"] is not None]
    assert wrong == []


def test_the_routes_give_one_verdict_whichever_door_they_enter_by(results):
    split = [(seed, e["answers"], _shown(e)) for seed, e in results.items()
             if len(set(e["answers"].values())) != 1]
    assert split == []


def test_no_route_gives_up_on_these_small_problems(results):
    undecided = [(seed, name) for seed, e in results.items() for name, answer in e["answers"].items()
                 if answer is None]
    assert undecided == []


def test_a_route_that_says_invalid_has_a_countermodel_the_enumeration_can_find(results):
    # "Invalid" is a claim about ONE structure, so the enumeration can check it. Most countermodels have at
    # most two elements; the few that need three (two distinct constants and a third element for a sort to
    # hold) are looked for at that size.
    missed = []
    for seed, e in results.items():
        if e["counter"] is None and set(e["answers"].values()) == {INVALID}:
            if countermodel(e["premises"], e["goal"], max_size=3) is None:
                missed.append((seed, _shown(e)))
    assert missed == []


def test_the_problem_set_is_not_vacuous(results):
    valid = sum(set(e["answers"].values()) == {VALID} for e in results.values())
    invalid = sum(e["counter"] is not None for e in results.values())
    with_sorted_constant = sum(any(isinstance(n, SortedConstant)
                                   for f in [*e["premises"], e["goal"]] for n in f.walk())
                               for e in results.values())
    assert valid >= 60 and invalid >= 60 and with_sorted_constant >= 150


def test_the_resolution_prover_never_proves_an_entailment_the_definition_refutes():
    proved = 0
    for seed in range(1, 121):
        premises, goal = problem(seed)
        if resolution_prove(premises, goal, max_steps=400):
            proved += 1
            assert countermodel(premises, goal) is None, (seed, premises, goal)
    assert proved >= 3        # it is incomplete, but not empty-handed
