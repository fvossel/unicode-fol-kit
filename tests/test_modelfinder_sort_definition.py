"""The finite model finder and the evaluator answer the question the definition asks.

THE DEFINITION. There is ONE universe. A sort ``S`` is the extension of the unary
predicate ``S``: the sort and the predicate of that name are one symbol, and a sort is
never empty. Sorts may overlap. A sorted constant ``c:S`` denotes an element of ``S``;
a constant written with two sorts (``c:A`` here, ``c:B`` there) lies in BOTH, and ``c:S``
in one place with a plain ``c`` in another is ONE constant. An unsorted constant, an
unsorted variable and the value of a function may be any element of the universe; a
predicate is a relation over the whole universe. A subsort edge ``S < T`` is ``S ⊆ T``.

Every expectation below is derived by hand from that, in the test that states it. The
last part compares ``find_model`` / ``find_countermodel`` with a REFERENCE written in this
file from the definition: it enumerates every structure of the definition over one and
two elements and evaluates the formulas itself, sharing no code with
``unicode_fol_kit.semantics`` (it reads node fields, and walks a tree with ``Node.walk``).
It is run on a few hundred
generated problems that include constants with two sorts, a constant sorted in one
place and plain in another, sort names used as predicates, subsort edges, unsorted
quantifiers with equality and sorted counting quantifiers.
"""

import itertools
import random
from types import SimpleNamespace

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import z3_models
from unicode_fol_kit.fol import nonempty_sort_axioms, sort_membership_axioms, subsort_axioms, to_fol
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Iff, Implies, Not, Number, Or, Quantifier,
    SortedConstant, SortedCount, SortedQuantifier, Variable,
)
from unicode_fol_kit.semantics import modelfinder, tarski
from unicode_fol_kit.semantics.modelfinder import find_countermodel, find_model, is_size_exhaustive
from unicode_fol_kit.semantics.tarski import Structure


def parse(text):
    """A formula from text; a node is returned as it is (the parser reads no unsorted constant
    inside a sorted quantifier, so such a formula is built from nodes)."""
    return text if not isinstance(text, str) else api.parse_any(text).formula


X = Variable("x")


# =============================================================================================
# THE REFERENCE: the definition, enumerated and evaluated by this file alone
# =============================================================================================
def _ref_symbols(formulas):
    """What the formulas mention: constants, the sorts of each annotated constant, sort names,
    unary predicate names (a sort name used as a predicate is both), other predicates, functions."""
    constants, annotated, sorts = set(), {}, set()
    unary, other, functions = set(), set(), set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Constant):
                constants.add(node.name)
            elif isinstance(node, SortedConstant):
                constants.add(node.name)
                annotated.setdefault(node.name, set()).add(node.sort)
                sorts.add(node.sort)
            elif isinstance(node, (SortedQuantifier, SortedCount)):
                sorts.add(node.sort)
            elif isinstance(node, Atom) and node.predicate != "=":
                if len(node.args) == 1:
                    unary.add(node.predicate)
                else:
                    other.add((node.predicate, len(node.args)))
            elif isinstance(node, Function):
                functions.add((node.name, len(node.args)))
    return constants, annotated, sorts, unary, other, functions


def _ref_structures(formulas, size, edges):
    """Every structure of the definition over ``{0 .. size-1}`` for these formulas.

    A name that is a sort or a unary predicate denotes ONE subset of the universe
    (non-empty when the name is a sort). A subsort edge ``S < T`` makes the subset of ``S``
    a subset of the one of ``T``; a name that only an edge mentions is a free subset. A
    constant lies in every sort it is annotated with. An edge holds for every theory, one
    with a sorted node or not: ``S < T`` is ``∀x (S(x) → T(x))`` where ``S`` and ``T`` are
    ordinary unary predicates.
    """
    constants, annotated, sorts, unary, other, functions = _ref_symbols(formulas)
    universe = tuple(range(size))
    subsets = [frozenset(c) for r in range(size + 1) for c in itertools.combinations(universe, r)]
    edge_names = set()
    for child, parents in edges.items():
        edge_names |= {child} | set(parents)
    names = sorted(sorts | unary | edge_names)
    name_options = [[s for s in subsets if s or name not in sorts] for name in names]
    relations = sorted(other)
    relation_options = []
    for _, arity in relations:
        cells = list(itertools.product(universe, repeat=arity))
        relation_options.append([frozenset(c) for r in range(len(cells) + 1)
                                 for c in itertools.combinations(cells, r)])
    functions = sorted(functions)
    function_options = []
    for _, arity in functions:
        cells = list(itertools.product(universe, repeat=arity))
        function_options.append([dict(zip(cells, values))
                                 for values in itertools.product(universe, repeat=len(cells))])
    constant_names = sorted(constants)
    for choice in itertools.product(*name_options):
        ext = dict(zip(names, choice))
        if any(not ext[child] <= ext[parent]
               for child, parents in edges.items() for parent in parents):
            continue
        ranges = [[d for d in universe if all(d in ext[s] for s in annotated.get(name, ()))]
                  for name in constant_names]
        for values in itertools.product(*ranges):
            for rel_choice in itertools.product(*relation_options):
                for func_choice in itertools.product(*function_options):
                    yield {"universe": universe, "ext": ext,
                           "const": dict(zip(constant_names, values)),
                           "rel": dict(zip(relations, rel_choice)),
                           "func": dict(zip(functions, func_choice))}


def _ref_term(term, model, env):
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, (Constant, SortedConstant)):
        return model["const"][term.name]
    if isinstance(term, Function):
        args = tuple(_ref_term(a, model, env) for a in term.args)
        return model["func"][(term.name, len(args))][args]
    raise TypeError(type(term).__name__)


def _ref_holds(node, model, env=None):
    env = env or {}
    if isinstance(node, Atom):
        args = tuple(_ref_term(a, model, env) for a in node.args)
        if node.predicate == "=":
            return args[0] == args[1]
        if len(args) == 1:
            return args[0] in model["ext"][node.predicate]
        return args in model["rel"][(node.predicate, len(args))]
    if isinstance(node, Not):
        return not _ref_holds(node.formula, model, env)
    if isinstance(node, And):
        return _ref_holds(node.left, model, env) and _ref_holds(node.right, model, env)
    if isinstance(node, Or):
        return _ref_holds(node.left, model, env) or _ref_holds(node.right, model, env)
    if isinstance(node, Implies):
        return (not _ref_holds(node.left, model, env)) or _ref_holds(node.right, model, env)
    if isinstance(node, Iff):
        return _ref_holds(node.left, model, env) == _ref_holds(node.right, model, env)
    if isinstance(node, (Quantifier, SortedQuantifier, Count, SortedCount)):
        # the sort IS the extension of the unary predicate of its name
        sorted_ = isinstance(node, (SortedQuantifier, SortedCount))
        universe = model["ext"][node.sort] if sorted_ else model["universe"]
        results = [_ref_holds(node.formula, model, {**env, node.variable.name: d}) for d in universe]
        if isinstance(node, (Quantifier, SortedQuantifier)):
            return all(results) if node.type == "∀" else any(results)
        count = sum(results)
        return {"ge": count >= node.n.value, "le": count <= node.n.value,
                "eq": count == node.n.value}[node.op]
    raise TypeError(type(node).__name__)


def _ref_find(true_formulas, false_formula, max_size, edges):
    """A structure of the definition (at most ``max_size`` elements) satisfying every
    formula of ``true_formulas`` and falsifying ``false_formula`` (when given), or None."""
    everything = list(true_formulas) + ([false_formula] if false_formula is not None else [])
    for size in range(1, max_size + 1):
        for model in _ref_structures(everything, size, edges):
            if all(_ref_holds(f, model) for f in true_formulas) and (
                    false_formula is None or not _ref_holds(false_formula, model)):
                return model
    return None


def _ref_closure(edges):
    """The transitive closure of direct subsort edges, as a set of (child, ancestor)."""
    pairs = {(c, p) for c, ps in edges.items() for p in ps}
    changed = True
    while changed:
        changed = False
        for (a, b), (c, d) in itertools.product(list(pairs), list(pairs)):
            if b == c and (a, d) not in pairs:
                pairs.add((a, d))
                changed = True
    return pairs


def _ref_model_of(structure, formulas):
    """The reference's view of a structure the finder returned; asserts, on the way, that the
    two tables of a name that is a sort and a unary predicate hold ONE extension."""
    constants, annotated, sorts, unary, other, functions = _ref_symbols(formulas)
    ext = {}
    for name in sorts | unary:
        in_sorts = frozenset(structure.sorts[name]) if name in structure.sorts else None
        key = (name, 1)
        in_predicates = (frozenset(d for (d,) in structure.predicates[key])
                         if key in structure.predicates else None)
        if in_sorts is not None and in_predicates is not None:
            assert in_sorts == in_predicates, f"{name!r}: sort {sorted(in_sorts)} vs predicate {sorted(in_predicates)}"
        ext[name] = in_sorts if in_sorts is not None else (in_predicates or frozenset())
    return {
        "universe": tuple(structure.domain), "ext": ext,
        "const": {c: structure.constants[c] for c in constants},
        "rel": {key: frozenset(structure.predicates.get(key, ())) for key in other},
        "func": {key: dict(structure.functions[key]) for key in functions},
    }


def _assert_legal(structure, formulas, edges=None):
    """The structure the finder returned is a structure of the definition: checked here from
    the definition first, then by the evaluator's own check (``tarski.check_structure``)."""
    constants, annotated, sorts, unary, other, functions = _ref_symbols(formulas)
    domain = set(structure.domain)
    for name in sorts:
        assert name in structure.sorts, f"sort {name!r} missing from {structure.sorts}"
        assert structure.sorts[name], f"sort {name!r} is empty"
        assert set(structure.sorts[name]) <= domain
    for name, its_sorts in annotated.items():
        for sort in its_sorts:
            assert structure.constants[name] in structure.sorts[sort], \
                f"{name}:{sort} denotes {structure.constants[name]!r}, outside {structure.sorts[sort]}"
    model = _ref_model_of(structure, formulas)             # asserts the two tables agree
    if edges:
        for child, ancestor in _ref_closure(edges):
            if child in model["ext"] and ancestor in model["ext"]:
                assert model["ext"][child] <= model["ext"][ancestor], f"{child} < {ancestor} broken"
    tarski.check_structure(structure, *formulas)
    return model


def _assert_countermodel(premises, goal, max_size=3, edges=None):
    """Find a countermodel, assert it is a legal structure in which the premises hold and the
    goal fails (evaluated by the REFERENCE), and return it."""
    found = find_countermodel(premises, goal, max_size=max_size, subsorts=edges)
    assert found is not None, "expected a countermodel"
    model = _assert_legal(found, list(premises) + [goal], edges)
    assert all(_ref_holds(p, model) for p in premises)
    assert not _ref_holds(goal, model)
    return found


def _assert_model(formulas, max_size=3, edges=None):
    found = find_model(formulas, max_size=max_size, subsorts=edges)
    assert found is not None, "expected a model"
    model = _assert_legal(found, formulas, edges)
    assert all(_ref_holds(f, model) for f in formulas)
    return found


def _z3_entails(premises, goal, edges=None):
    """Z3 over the guard images, the background facts passed as premises: the independent route
    that reads the definition as ``S(x)`` guards. (The non-emptiness and membership axioms are
    taken from the original formulas; the subsort edges from ``subsort_axioms``.)"""
    background = list(nonempty_sort_axioms(*premises, goal)) + list(sort_membership_axioms(*premises, goal))
    if edges:
        background += list(subsort_axioms(SimpleNamespace(subsorts=edges)))
    hypotheses = background + [to_fol(p) for p in premises]
    conclusion = to_fol(goal)
    if not hypotheses:
        return z3_models.is_valid(conclusion)
    conjunction = hypotheses[0]
    for h in hypotheses[1:]:
        conjunction = And(conjunction, h)
    return z3_models.is_valid(Implies(conjunction, conclusion))


# =============================================================================================
# THE FINDER, ON PROBLEMS WHOSE VERDICT IS DERIVED BY HAND
# =============================================================================================
# (name, premises, conclusion, valid?, derivation)
HAND_PROBLEMS = [
    ("socrates is a Human",
     ["∀x:Human Mortal(x)"], "Mortal(socrates:Human)", True,
     "socrates denotes an element of Human and every Human is Mortal"),
    ("an unsorted constant has no sort",
     ["∀x:Human Mortal(x)"], "Mortal(socrates)", False,
     "universe {0,1}, Human={0}, Mortal={0}, socrates=1"),
    ("a function value has no sort",
     ["∀x:Foo R(x)", "Q(g(alpha))"], "R(g(alpha))", False,
     "universe {0,1}, Foo={0}, R={0}, alpha=0, g(0)=1, Q={1}: g(alpha) is outside Foo"),
    ("one constant, two sorts",
     ["P(carl:A)", "Q(carl:B)"], "∃x:A Q(x)", True,
     "carl is in A and Q(carl), so some element of A is Q"),
    ("one constant, two sorts, the other sort",
     ["P(carl:A)", "Q(carl:B)"], "∃x:B P(x)", True,
     "carl is in B and P(carl), so some element of B is P"),
    ("one constant, sorted here and unsorted there",
     ["P(carl)", "Q(carl:A)"], "∃x:A P(x)", True,
     "it is one constant; the sorted occurrence puts it in A, and P(carl)"),
    ("membership is not provable of an unsorted constant",
     ["Mortal(socrates)"], "∃x:Human Mortal(x)", False,
     "universe {0,1}, Human={1}, Mortal={0}, socrates=0"),
    ("a sorted constant witnesses its sort",
     [], "∃x:Human x = socrates:Human", True,
     "socrates is in Human and equals itself"),
    ("two sorted constants of one sort need not be equal",
     [], "anna:S = bert:S", False,
     "universe {0,1}, S={0,1}, anna=0, bert=1"),
    ("nothing follows about a sorted constant from nothing",
     [], "Mortal(socrates:Human)", False,
     "universe {0}, Human={0}, Mortal={}, socrates=0"),
    ("a sort is never empty, so its predicate has an instance",
     [], "∃y:Car Car(y)", True,
     "Car is non-empty and the predicate Car IS the sort Car: any element y of Car satisfies Car(y)"),
    ("a sort is the predicate of its name, so every element satisfies it",
     [], "∀y:Car Car(y)", True,
     "every element of the sort Car is in the extension of Car, which is the sort"),
    ("a sort used as a predicate on an unsorted constant (guard)",
     ["∀x:Human Mortal(x)", "Human(socrates)"], "Mortal(socrates)", True,
     "Human(socrates) says socrates is in the sort Human, and every Human is Mortal"),
    ("a sorted constant satisfies the predicate of its sort",
     ["Mortal(socrates:Human)"], "Human(socrates)", True,
     "socrates:Human puts socrates in the sort Human, the extension of the predicate Human"),
    ("a sort used as a predicate says nothing about other constants",
     ["∀x:Human Mortal(x)"], "Human(socrates)", False,
     "universe {0,1}, Human={0}, Mortal={0}, socrates=1: socrates is not in Human"),
    ("the predicate of a sort restricts the sorted quantifier",
     ["Human(socrates)"], SortedQuantifier("∃", X, "Human", Atom("=", [X, Constant("socrates")])), True,
     "socrates is in Human, and equals itself"),
    ("a sorted universal and an unsorted existence",
     ["∀x:A P(x)"], "∃x P(x)", True,
     "A is non-empty and everything in A is P"),
    ("unsorted quantifiers range over the sorted objects too",
     ["∀x ∀y x = y"], "∀x:A ∀z:A x = z", True,
     "the universe has one element, A is a non-empty subset of it"),
]


def _hand_ids():
    return [name for name, *_ in HAND_PROBLEMS]


@pytest.mark.parametrize("name,premises,goal,valid,why", HAND_PROBLEMS, ids=_hand_ids())
def test_hand_derived_verdicts(name, premises, goal, valid, why):
    premises, goal = [parse(p) for p in premises], parse(goal)
    if valid:
        assert find_countermodel(premises, goal, max_size=3) is None, why
        # and in every premise order
        for order in itertools.permutations(premises):
            assert find_countermodel(list(order), goal, max_size=3) is None, why
    else:
        _assert_countermodel(premises, goal)
    # the independent guard route (Z3 over to_fol images plus the background facts) agrees
    assert _z3_entails(premises, goal) is valid, why


def test_two_sorts_of_one_constant_do_not_depend_on_the_order_of_three_premises():
    """P(carl:A), Q(carl:B), R(carl) ⊢ ∃x:B P(x), in all six orders. By hand: carl is in B
    (Q(carl:B)), P holds of carl (P(carl:A)), so some B-element is P: valid in every order."""
    premises = [parse("P(carl:A)"), parse("Q(carl:B)"), parse("R(carl)")]
    goal = parse("∃x:B P(x)")
    for order in itertools.permutations(premises):
        assert find_countermodel(list(order), goal, max_size=2) is None


def test_the_conclusion_may_add_a_second_sort_to_a_constant():
    """P(carl:A) ⊢ Q(carl:B) → ∃x:A Q(x). By hand: assume Q(carl); carl is in A (premise), so the
    witness of ∃x:A Q(x) is carl: valid. (The conclusion's own annotation is a second sort of
    carl, and it must not displace the premise's.)"""
    assert find_countermodel([parse("P(carl:A)")], parse("Q(carl:B) → ∃x:A Q(x)"), max_size=3) is None


def test_a_constant_with_two_sorts_gives_an_unsatisfiable_theory_when_the_sorts_are_disjoint():
    """∀x:A ∀y:B ¬(x = y), P(carl:A), Q(carl:B) has no model at all: carl is in A and in B, and the
    first sentence, with x = y = carl, says it is not. (Searched up to three elements.)"""
    theory = [parse("∀x:A ∀y:B ¬(x = y)"), parse("P(carl:A)"), parse("Q(carl:B)")]
    assert find_model(theory, max_size=3) is None
    for order in itertools.permutations(theory):
        assert find_model(list(order), max_size=3) is None
    # without the second annotation it is satisfiable: universe {0,1}, A={0}, B={1}, carl=0
    found = _assert_model(theory[:2], max_size=3)
    assert found.constants["carl"] in found.sorts["A"]


def test_the_model_of_a_two_sorted_constant_has_it_in_both_sorts():
    """P(carl:A), Q(carl:B) has a model, and in every one carl is in A and in B."""
    found = _assert_model([parse("P(carl:A)"), parse("Q(carl:B)")], max_size=2)
    assert found.constants["carl"] in found.sorts["A"]
    assert found.constants["carl"] in found.sorts["B"]


def test_a_theory_unsatisfiable_by_the_second_annotation_is_found_unsatisfiable_in_every_order():
    """∀x:A ¬P(x), P(carl:A), Q(carl:B): carl is in A and P(carl), against ∀x:A ¬P(x). No model."""
    theory = [parse("∀x:A ¬P(x)"), parse("P(carl:A)"), parse("Q(carl:B)")]
    for order in itertools.permutations(theory):
        assert find_model(list(order), max_size=3) is None


def test_the_returned_structure_holds_one_extension_for_a_sort_and_its_predicate():
    """Human(alice) ∧ ¬Mortal(alice), ∀x:Human ¬Mortal(x): alice is in the sort Human (that is what
    the atom Human(alice) says), so a model has the SAME set in the sort table and in the table of
    the predicate Human, and alice in it."""
    theory = [parse("Human(alice)"), parse("¬Mortal(alice)"), parse("∀x:Human ¬Mortal(x)")]
    found = _assert_model(theory, max_size=3)
    assert found.constants["alice"] in found.sorts["Human"]
    assert {d for (d,) in found.predicates[("Human", 1)]} == set(found.sorts["Human"])


def test_a_sort_that_is_not_a_predicate_of_the_theory_needs_no_predicate_table():
    """∃x:S P(x): the sort S is not a predicate of the theory, so the structure has no table for it."""
    found = _assert_model([parse("∃x:S P(x)")], max_size=2)
    assert ("S", 1) not in found.predicates and found.sorts["S"]


def test_a_predicate_of_another_arity_with_the_name_of_a_sort_is_another_symbol():
    """⊢ ∃x:Car ∃y:Car Car(x, y) is invalid: the sort Car is the UNARY predicate Car, and the binary
    relation Car is another symbol, free to be empty (universe {0}, Car = {0} as a sort, the binary
    relation empty). The structure holds both, each in its own table."""
    goal = parse("∃x:Car ∃y:Car Car(x, y)")
    found = _assert_countermodel([], goal, max_size=2)
    assert found.sorts["Car"] and ("Car", 1) not in found.predicates
    assert found.predicates[("Car", 2)] == set()
    assert _ref_find([], goal, 2, {}) is not None


def test_a_countermodel_of_a_sort_used_as_a_predicate_has_the_constant_outside_the_sort():
    """∀x:Human Mortal(x) ⊢ Human(socrates) is invalid; in every countermodel socrates is not in the
    sort Human (Human(socrates) fails, and the predicate Human is the sort)."""
    found = _assert_countermodel([parse("∀x:Human Mortal(x)")], parse("Human(socrates)"))
    assert found.constants["socrates"] not in found.sorts["Human"]
    assert (found.constants["socrates"],) not in found.predicates[("Human", 1)]


def test_a_countermodel_of_an_unsorted_constant_puts_it_outside_the_sort():
    """∀x:Human Mortal(x) ⊢ Mortal(socrates): every Human is Mortal and socrates is not, so socrates
    is not a Human. The countermodel must say so."""
    found = _assert_countermodel([parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)"))
    assert found.constants["socrates"] not in found.sorts["Human"]


def test_a_countermodel_of_a_function_value_puts_it_outside_the_sort():
    """∀x:Foo R(x), Q(g(alpha)) ⊢ R(g(alpha)): g(alpha) is not R, every Foo is R, so g(alpha) is not in Foo."""
    found = _assert_countermodel([parse("∀x:Foo R(x)"), parse("Q(g(alpha))")], parse("R(g(alpha))"))
    value = found.functions[("g", 1)][(found.constants["alpha"],)]
    assert value not in found.sorts["Foo"]


# ---------------------------------------------------------------------------------------------
# sorts and subsort edges
# ---------------------------------------------------------------------------------------------
def test_an_edge_to_a_name_used_only_as_a_predicate_bounds_that_predicate():
    """With S < T: ∃x:S P(x) ⊢ ∃x T(x). By hand: S is non-empty and S ⊆ T, and T is the predicate T
    (the sort and the predicate of that name are one symbol), so T has an element. Valid. Without
    the edge T may be empty: a countermodel. (The theory uses T only as a predicate.)"""
    premise, goal = parse("∃x:S P(x)"), parse("∃x T(x)")
    edges = {"S": frozenset({"T"})}
    assert find_countermodel([premise], goal, max_size=3, subsorts=edges) is None
    assert _z3_entails([premise], goal, edges) is True
    _assert_countermodel([premise], goal, max_size=2)
    assert _z3_entails([premise], goal) is False


def test_an_edge_from_a_predicate_into_a_sort_bounds_the_predicate_from_above():
    """With T < S: T(carl), ∀x:S P(x) ⊢ P(carl) (T is the predicate T). By hand: T(carl) puts carl in
    T ⊆ S, and every element of S is P: valid. Without the edge: carl may be outside S, a countermodel."""
    premises, goal = [parse("T(carl)"), parse("∀x:S P(x)")], parse("P(carl)")
    edges = {"T": frozenset({"S"})}
    assert find_countermodel(premises, goal, max_size=3, subsorts=edges) is None
    assert _z3_entails(premises, goal, edges) is True
    _assert_countermodel(premises, goal, max_size=2)


def test_an_edge_chain_through_a_name_the_theory_never_uses_still_holds():
    """With A < D < B and D unused: ∀x:B P(x), ¬P(alpha:A) is unsatisfiable (alpha is in A ⊆ D ⊆ B,
    so P(alpha)). Without the edges it is satisfiable: A = {0}, B = {1}, P = {1}, alpha = 0."""
    edges = {"A": frozenset({"D"}), "D": frozenset({"B"})}
    theory = [parse("∀x:B P(x)"), parse("¬P(alpha:A)")]
    assert find_model(theory, max_size=3, subsorts=edges) is None
    assert find_model(theory, max_size=3) is not None


def test_the_reference_holds_an_edge_for_a_theory_without_a_sorted_node():
    """The reference of the comparison below reads ``A < B`` as ``∀x (A(x) → B(x))`` for a theory whose
    only nodes are unsorted: ``A(carl) ⊢ B(carl)`` has no countermodel with the edge (A ⊆ B puts
    carl in B) and the countermodel A = {0}, B = {}, carl = 0 without it."""
    edges = {"A": frozenset({"B"})}
    premises, goal = [parse("A(carl)")], parse("B(carl)")
    assert _ref_find(premises, goal, 2, edges) is None
    countermodel = _ref_find(premises, goal, 2, {})
    assert countermodel is not None
    assert countermodel["ext"]["A"] == frozenset({0}) and countermodel["ext"]["B"] == frozenset()
    # with the edge the converse is still no entailment: B = {0}, A = {}
    converse = _ref_find([parse("B(carl)")], parse("A(carl)"), 2, edges)
    assert converse is not None and converse["ext"]["A"] == frozenset()
    # an edge to a name the theory never uses is free: B can be everything
    assert _ref_find([parse("A(carl)")], parse("Q(carl)"), 2, edges) is not None


def test_edges_hold_for_a_theory_without_sorted_nodes():
    """An edge ``A < B`` is ``∀x (A(x) → B(x))`` whether or not the theory has a sorted node, so an
    unsorted theory that uses ``A`` and ``B`` as unary predicates is held to it: ``A(carl) ⊢ B(carl)``
    has the countermodel U={0}, A={0}, B={} without the edge and none with it (A ⊆ B puts carl in B).

    The old expectation here, "an unsorted theory ignores ``subsorts`` altogether", was wrong: Z3 with
    ``subsort_axioms`` enforces the edge on exactly this input (it proves ``B(carl)``), so the finder and the
    prover answered one question two ways. Only an edge with an end the theory never mentions is free."""
    edges = {"A": frozenset({"B"})}
    assert find_countermodel([parse("A(carl)")], parse("B(carl)"), max_size=2) is not None
    assert find_countermodel([parse("A(carl)")], parse("B(carl)"), max_size=2, subsorts=edges) is None
    # an edge to a name the theory does not use constrains nothing: B is free to be everything
    assert find_countermodel([parse("A(carl)")], parse("Q(carl)"), max_size=2, subsorts=edges) is not None


# ---------------------------------------------------------------------------------------------
# the pre-flight count
# ---------------------------------------------------------------------------------------------
def test_a_unary_predicate_with_the_name_of_a_sort_is_not_a_candidate_factor():
    """∀x:Car Car(x): one sort, whose predicate IS the sort, so the interpretations over k elements
    are the non-empty subsets alone, 2**k - 1: 1, 3, 7 for k = 1, 2, 3. Were the predicate counted
    separately it would be (2**k - 1) * 2**k: 2, 12, 56."""
    theory = [SortedQuantifier("∀", X, "Car", Atom("Car", [X]))]
    for k, exact in ((1, 1), (2, 3), (3, 7)):
        assert is_size_exhaustive(theory, k, max_candidates=exact)
        assert not is_size_exhaustive(theory, k, max_candidates=exact - 1)
    # a predicate of ANOTHER arity with the sort's name is another symbol and is counted:
    other = [SortedQuantifier("∀", X, "Car", Atom("Car", [X, X]))]
    assert is_size_exhaustive(other, 2, max_candidates=3 * 16)
    assert not is_size_exhaustive(other, 2, max_candidates=3 * 16 - 1)


def test_the_merged_predicate_is_searched_within_the_candidate_bound():
    """⊢ ∃y:Car Car(y) at size 2 has 3 interpretations: a bound of 3 searches the size and finds
    no countermodel; a bound of 2 skips it (and says so through is_size_exhaustive)."""
    goal = parse("∃y:Car Car(y)")
    assert is_size_exhaustive([Not(goal)], 2, max_candidates=3)
    assert not is_size_exhaustive([Not(goal)], 2, max_candidates=2)
    assert find_countermodel([], goal, max_size=2, max_candidates=3) is None


# ---------------------------------------------------------------------------------------------
# the unsorted search is not touched
# ---------------------------------------------------------------------------------------------
def test_the_unsorted_search_never_reaches_the_sorted_machinery(monkeypatch):
    """No sort in the theory: the finder does not enumerate sorted interpretations, and the evaluator
    never reads a sort or checks a structure (the unsorted path pays nothing for sorts)."""
    def boom(*args, **kwargs):
        raise AssertionError("the sorted machinery was reached by an unsorted search")

    monkeypatch.setattr(modelfinder, "_sorted_interpretations", boom)
    monkeypatch.setattr(modelfinder, "_edge_predicate_names", boom)
    monkeypatch.setattr(Structure, "sort_universe", boom)
    monkeypatch.setattr(tarski, "_sort_problems", boom)
    assert find_model([parse("∀x (P(x) → Q(x))"), parse("P(alice)"), parse("¬Q(bob)")], max_size=3) is not None
    assert find_countermodel([parse("P(alice) ∧ Q(alice)")], parse("∃x (P(x) ∧ Q(x))"), max_size=3) is None
    assert find_model([parse("∀x ∃y ¬(x = y)")], max_size=2) is not None


def test_every_structure_the_finder_returns_for_a_sorted_theory_passes_the_check():
    """Over a spread of sorted theories (two sorts for one constant, a sort used as a predicate,
    counting over a sort, an edge) every returned model and countermodel is legal."""
    problems = [
        ([parse("P(carl:A)"), parse("Q(carl:B)")], None, None),
        ([parse("Human(alice)"), parse("∀x:Human Mortal(x)")], None, None),
        ([parse("∃≥2 x:S (P(x))")], None, None),
        ([parse("∃x:A P(x)")], parse("∃x B(x)"), {"A": frozenset({"B"})}),
        ([parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)"), None),
        ([], parse("Human(socrates:Human) → ∃x:Human Mortal(x)"), None),
    ]
    for premises, goal, edges in problems:
        found = (find_model(premises, max_size=3, subsorts=edges) if goal is None
                 else find_countermodel(premises, goal, max_size=3, subsorts=edges))
        if found is None:
            continue                                  # valid / unsatisfiable: nothing returned
        tarski.check_structure(found, *premises, *([goal] if goal is not None else []))


# =============================================================================================
# THE REFERENCE ON ITS OWN: it finds what the definition says on the hand-derived problems
# =============================================================================================
@pytest.mark.parametrize("name,premises,goal,valid,why", HAND_PROBLEMS, ids=_hand_ids())
def test_the_reference_agrees_with_the_hand_derivations(name, premises, goal, valid, why):
    premises, goal = [parse(p) for p in premises], parse(goal)
    found = _ref_find(premises, goal, 3, {})
    assert (found is None) is valid, why


# =============================================================================================
# GENERATED PROBLEMS: find_model / find_countermodel against the reference
# =============================================================================================
_UNARY = ("P", "Q")
_SORTS = ("A", "B")
#: carl is listed with both sorts, and more often than the others, so that a constant with two sorts
#: is common among the problems
_SORTED_CONSTANTS = (("carl", "A"), ("carl", "B"), ("carl", "A"), ("carl", "B"),
                     ("dora", "B"), ("emil", "A"))
_PLAIN_CONSTANTS = ("alpha", "carl")                  # carl also occurs sorted: it is ONE constant
_VARIABLES = ("x", "y", "z")
_EDGE_ORDER = ("A", "D", "P", "B")                    # D occurs in no formula; P only as a predicate
_LIMIT = 4000                                         # structures over two elements, an upper bound


def _gen_term(rng, scope, depth=0):
    r = rng.random()
    if scope and r < 0.45:
        return Variable(rng.choice(scope))
    if r < 0.62:
        return Constant(rng.choice(_PLAIN_CONSTANTS))
    if r < 0.88:
        name, sort = rng.choice(_SORTED_CONSTANTS)
        return SortedConstant(name, sort)
    if depth == 0:
        return Function("f", [_gen_term(rng, scope, 1)])
    return Constant("alpha")


def _gen_atom(rng, scope):
    r = rng.random()
    if r < 0.2:
        return Atom("=", [_gen_term(rng, scope), _gen_term(rng, scope)])
    if r < 0.26:
        return Atom("R", [_gen_term(rng, scope), _gen_term(rng, scope)])
    # a sort name used as a predicate is as likely as a plain unary predicate
    return Atom(rng.choice(_UNARY + _SORTS), [_gen_term(rng, scope)])


def _gen_formula(rng, scope, depth):
    if depth == 0 or rng.random() < 0.2:
        return _gen_atom(rng, scope)
    r = rng.random()
    if r < 0.14:
        return Not(_gen_formula(rng, scope, depth - 1))
    if r < 0.46:
        op = rng.choice((And, Or, Implies, Iff))
        return op(_gen_formula(rng, scope, depth - 1), _gen_formula(rng, scope, depth - 1))
    free = [v for v in _VARIABLES if v not in scope]
    if not free:
        return _gen_atom(rng, scope)
    var = free[0]
    body = _gen_formula(rng, scope + [var], depth - 1)
    kind = rng.random()
    if kind < 0.42:
        return SortedQuantifier(rng.choice("∀∃"), Variable(var), rng.choice(_SORTS), body)
    if kind < 0.76:
        return Quantifier(rng.choice("∀∃"), Variable(var), body)
    if kind < 0.9:
        return SortedCount(rng.choice(("ge", "le", "eq")), Number(rng.choice((1, 2))),
                           Variable(var), rng.choice(_SORTS), body)
    return Count(rng.choice(("ge", "le", "eq")), Number(rng.choice((1, 2))), Variable(var), body)


def _substitute(node, name, term):
    """``node`` with the free variable ``name`` replaced by ``term`` (the generator never rebinds a name)."""
    if isinstance(node, Variable):
        return term if node.name == name else node
    if isinstance(node, (Constant, SortedConstant)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [_substitute(a, name, term) for a in node.args])
    if isinstance(node, Atom):
        return Atom(node.predicate, [_substitute(a, name, term) for a in node.args])
    if isinstance(node, Not):
        return Not(_substitute(node.formula, name, term))
    if isinstance(node, (And, Or, Implies, Iff)):
        return type(node)(_substitute(node.left, name, term), _substitute(node.right, name, term))
    if isinstance(node, Quantifier):
        return Quantifier(node.type, node.variable, _substitute(node.formula, name, term))
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, node.sort, _substitute(node.formula, name, term))
    if isinstance(node, Count):
        return Count(node.op, node.n, node.variable, _substitute(node.formula, name, term))
    if isinstance(node, SortedCount):
        return SortedCount(node.op, node.n, node.variable, node.sort,
                           _substitute(node.formula, name, term))
    raise TypeError(type(node).__name__)


def _gen_edges(rng):
    if rng.random() > 0.35:
        return {}
    pairs = [(a, b) for i, a in enumerate(_EDGE_ORDER) for b in _EDGE_ORDER[i + 1:]]
    edges = {}
    for child, parent in rng.sample(pairs, rng.choice((1, 1, 2))):
        edges.setdefault(child, set()).add(parent)
    return {c: frozenset(ps) for c, ps in edges.items()}


def _gen_equality_problem(rng):
    """An unsorted quantifier with equality bounds the size of the WHOLE universe, the objects of
    every sort included; a sorted quantifier then asks about a sort inside it."""
    x, y = Variable("x"), Variable("y")
    sort, other_sort = rng.sample(_SORTS, 2)
    premise = rng.choice((
        Quantifier("∀", x, Quantifier("∀", y, Atom("=", [x, y]))),                  # one element
        Quantifier("∃", x, Quantifier("∃", y, Not(Atom("=", [x, y])))),             # two or more
        Quantifier("∀", x, Atom("=", [x, Constant("alpha")])),                     # everything is alpha
        Quantifier("∃", x, Quantifier("∀", y, Atom("=", [x, y]))),
        Count("eq", Number(2), x, Atom("=", [x, x])),                              # exactly two
    ))
    conclusion = rng.choice((
        SortedQuantifier("∀", x, sort, SortedQuantifier("∀", y, sort, Atom("=", [x, y]))),
        SortedQuantifier("∃", x, sort, SortedQuantifier("∃", y, other_sort, Not(Atom("=", [x, y])))),
        SortedCount("ge", Number(2), x, sort, Atom("=", [x, x])),
        SortedQuantifier("∀", x, sort, Atom("=", [x, Constant("alpha")])),
        SortedQuantifier("∃", x, sort, Atom("=", [x, SortedConstant("carl", other_sort)])),
    ))
    extra = [_gen_formula(rng, [], 1)] if rng.random() < 0.3 else []
    return [premise] + extra, conclusion


#: The edge ends a theory without a sorted node can use: each is a unary predicate there (``D`` is
#: in no formula).
_EDGE_PREDICATES = frozenset({"A", "B", "P"})


def _gen_unsorted_edge_problem(seed, edges):
    """A theory with no sorted node whose answer turns on an edge between two of its unary predicates,
    or None (no such edge, or the seed does not take this shape). Drawn from a generator of its own,
    so that the problems the other shapes make do not change with it.

    With ``child < parent`` the valid ones are ``child(a) ⊢ parent(a)``, ``∃x child(x) ⊢ ∃x parent(x)``
    and ``∀x (parent(x) → Q(x)) ⊢ ∀x (child(x) → Q(x))``; ``parent(a) ⊢ child(a)`` is not (child = {},
    parent = {a}), and a premise pair ``child(a), ¬parent(a)`` is unsatisfiable under the edge."""
    rng = random.Random(seed + 7919)
    pairs = sorted(pair for pair in _ref_closure(edges) if set(pair) <= _EDGE_PREDICATES)
    if not pairs or rng.random() > 0.3:
        return None
    child, parent = rng.choice(pairs)
    x, a = Variable("x"), Constant("alpha")
    shape = rng.randrange(5)
    if shape == 0:
        return [Atom(child, [a])], Atom(parent, [a])
    if shape == 1:
        return [Quantifier("∃", x, Atom(child, [x]))], Quantifier("∃", x, Atom(parent, [x]))
    if shape == 2:
        return ([Quantifier("∀", x, Implies(Atom(parent, [x]), Atom("Q", [x])))],
                Quantifier("∀", x, Implies(Atom(child, [x]), Atom("Q", [x]))))
    if shape == 3:
        return [Atom(parent, [a])], Atom(child, [a])
    return [Atom(child, [a]), Not(Atom(parent, [a]))], Atom("Q", [a])


def _gen_problem(seed):
    """Some problems are random; most have the SHAPE of an entailment, so that valid ones are common:
    instantiating a sorted or unsorted universal at a sorted constant, an unsorted constant or a
    function value, generalising from one of them, the membership shapes that use a sort as a
    predicate, and unsorted quantifiers with equality against sorted ones. Which are valid is for
    the reference to say."""
    rng = random.Random(seed)
    edges = _gen_edges(rng)
    unsorted_edge_problem = _gen_unsorted_edge_problem(seed, edges)
    if unsorted_edge_problem is not None:
        return unsorted_edge_problem[0], unsorted_edge_problem[1], edges
    if rng.random() < 0.15:
        premises, conclusion = _gen_equality_problem(rng)
        return premises, conclusion, edges
    if rng.random() < 0.45:
        premises = [_gen_formula(rng, [], rng.choice((1, 2, 2))) for _ in range(rng.choice((0, 1, 1, 2)))]
        return premises, _gen_formula(rng, [], rng.choice((1, 2, 2))), edges
    body = _gen_formula(rng, ["w"], rng.choice((0, 1, 1, 2)))
    sort = rng.choice(_SORTS)
    name, own_sort = rng.choice(_SORTED_CONSTANTS)
    witness = rng.choice((SortedConstant(name, own_sort), SortedConstant(name, own_sort),
                          Constant(rng.choice(_PLAIN_CONSTANTS)),
                          Function("f", [Constant(rng.choice(_PLAIN_CONSTANTS))])))
    w = Variable("w")
    extra = [_gen_formula(rng, [], 1)] if rng.random() < 0.3 else []
    shape = rng.random()
    if shape < 0.3:         # ∀w:S φ(w)  ⊢  φ(t)
        return [SortedQuantifier("∀", w, sort, body)] + extra, _substitute(body, "w", witness), edges
    if shape < 0.4:         # ∀w φ(w)  ⊢  φ(t)
        return [Quantifier("∀", w, body)] + extra, _substitute(body, "w", witness), edges
    if shape < 0.6:         # φ(t)  ⊢  ∃w:S φ(w)
        return [_substitute(body, "w", witness)] + extra, SortedQuantifier("∃", w, sort, body), edges
    if shape < 0.7:         # φ(t)  ⊢  ∃w φ(w)
        return [_substitute(body, "w", witness)] + extra, Quantifier("∃", w, body), edges
    if shape < 0.85:        # S(t), ∀w:S φ(w)  ⊢  φ(t):  the sort used as a predicate puts t in the sort
        return ([Atom(sort, [witness]), SortedQuantifier("∀", w, sort, body)] + extra,
                _substitute(body, "w", witness), edges)
    # c:S ⊢ S(c) and its relatives: the annotation and the predicate of that name
    return ([_gen_formula(rng, [], 1), Atom("P", [SortedConstant(name, own_sort)])] + extra,
            Atom(own_sort, [Constant(name)]), edges)


def _structure_bound(formulas, edges):
    """An upper bound on the structures over two elements the reference enumerates."""
    constants, annotated, sorts, unary, other, functions = _ref_symbols(formulas)
    edge_names = set()
    for child, parents in edges.items():
        edge_names |= {child} | set(parents)
    names = sorts | unary | edge_names
    bound = 1
    for name in names:
        bound *= 3 if name in sorts else 4
    bound *= 2 ** len(constants)
    for _, arity in other:
        bound *= 2 ** (2 ** arity)
    for _, arity in functions:
        bound *= 2 ** (2 ** arity)
    return bound


def _features(premises, conclusion, edges):
    """What a generated problem exercises, for the coverage check."""
    formulas = list(premises) + [conclusion]
    constants, annotated, sorts, unary, other, functions = _ref_symbols(formulas)
    nodes = [n for f in formulas for n in f.walk()]
    found = set()
    if any(len(s) > 1 for s in annotated.values()):
        found.add("a constant with two sorts")
    if any(isinstance(n, Constant) and n.name in annotated for n in nodes):
        found.add("a constant sorted in one place and plain in another")
    if unary & sorts:
        found.add("a sort name used as a predicate")
    if any(isinstance(n, SortedCount) for n in nodes):
        found.add("a sorted counting quantifier")
    if sorts and any(isinstance(n, Quantifier) and any(
            isinstance(m, Atom) and m.predicate == "=" and any(
                isinstance(a, Variable) and a.name == n.variable.name for a in m.args)
            for m in n.walk()) for n in nodes):
        found.add("an unsorted quantifier with equality next to a sort")
    edge_names = set(edges).union(*edges.values()) if edges else set()
    if sorts and edges:
        found.add("a subsort edge")
    if sorts and edge_names & (unary - sorts):
        found.add("an edge end that is only a predicate")
    if not sorts and any(child in unary and parent in unary for child, parent in _ref_closure(edges)):
        found.add("an edge between two predicates of a theory without a sorted node")
    if functions:
        found.add("a function value")
    return found


_SEEDS = range(0, 1000)


def _admitted(seed):
    premises, conclusion, edges = _gen_problem(seed)
    if _structure_bound(list(premises) + [conclusion], edges) > _LIMIT:
        return None
    return premises, conclusion, edges


def test_the_generator_covers_what_the_comparison_is_for():
    """The comparison below is only as good as its problems: they include every kind named in the
    module docstring, and both valid and invalid ones."""
    admitted = [(seed, p) for seed in _SEEDS if (p := _admitted(seed)) is not None]
    assert len(admitted) >= 800
    seen = {}
    for seed, (premises, conclusion, edges) in admitted:
        for feature in _features(premises, conclusion, edges):
            seen[feature] = seen.get(feature, 0) + 1
    for feature in ("a constant with two sorts", "a constant sorted in one place and plain in another",
                    "a sort name used as a predicate", "a sorted counting quantifier",
                    "an unsorted quantifier with equality next to a sort", "a subsort edge",
                    "an edge end that is only a predicate", "a function value"):
        assert seen.get(feature, 0) >= 8, (feature, seen)
    # the edges of a theory without a sorted node are pinned by the comparison only if it has many
    assert seen.get("an edge between two predicates of a theory without a sorted node", 0) >= 40, seen
    # both answers occur among them (the reference, not the finder, says which)
    valid = invalid = 0
    for seed, (premises, conclusion, edges) in admitted:
        if _ref_find(premises, conclusion, 2, edges) is None:
            valid += 1
        else:
            invalid += 1
    assert valid >= 100 and invalid >= 100, (valid, invalid)


def _show(premises, conclusion, edges):
    return (", ".join(p.to_unicode_str() for p in premises) + "  ⊢  " + conclusion.to_unicode_str()
            + (f"   edges {dict(edges)}" if edges else ""))


@pytest.mark.parametrize("first", range(0, 1000, 100))
def test_find_countermodel_and_find_model_agree_with_the_reference(first):
    """For each generated problem the finder has a countermodel (a model of the premises) within two
    elements exactly when the reference does, and what it returns is a legal structure in which the
    reference confirms the premises hold and the conclusion fails."""
    for seed in range(first, first + 100):
        problem = _admitted(seed)
        if problem is None:
            continue
        premises, conclusion, edges = problem
        shown = f"seed {seed}: {_show(premises, conclusion, edges)}"
        wanted = _ref_find(premises, conclusion, 2, edges)
        got = find_countermodel(premises, conclusion, max_size=2, subsorts=edges)
        assert (got is None) == (wanted is None), (
            f"{shown}: finder {'none' if got is None else got}; reference "
            f"{'none' if wanted is None else wanted}")
        if got is not None:
            model = _assert_legal(got, list(premises) + [conclusion], edges)
            assert all(_ref_holds(p, model) for p in premises), shown
            assert not _ref_holds(conclusion, model), shown
        # the satisfiability question about the same formulas
        theory = list(premises) + [conclusion]
        wanted = _ref_find(theory, None, 2, edges)
        got = find_model(theory, max_size=2, subsorts=edges)
        assert (got is None) == (wanted is None), (
            f"{shown} (as a theory): finder {'none' if got is None else got}; reference "
            f"{'none' if wanted is None else wanted}")
        if got is not None:
            model = _assert_legal(got, theory, edges)
            assert all(_ref_holds(f, model) for f in theory), shown
