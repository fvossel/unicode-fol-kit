"""``api.prove(signature=...)`` and ``api.countermodel(signature=...)``: what a ``Signature`` declares
reaches every backend of the chain.

THE DEFINITION (one universe). A sort ``S`` is the non-empty extension of the unary predicate ``S``;
sorts may overlap. A constant declared in ``S`` is an element of ``S``; a function declared with
result sort ``S`` maps elements of its argument sorts into ``S``; a subsort edge ``S < T`` is
``S ⊆ T``. A predicate may hold of anything, whatever argument sorts it was declared with. An
unsorted constant, variable and function value may be any element.

The four acceptance problems come with a countermodel written down by hand for the case where the
signature is NOT given (the universe is ``{0, 1}``), and the argument for the case where it is.
The randomised differential then has two independent halves: the same problem with
``signature_axioms(sig)`` passed by hand as premises must be answered alike, and a brute-force search
over every structure of one or two elements that satisfies the declarations (written below from the
definition, sharing no code with the kit's evaluators) must never contradict a "proved".
"""

import itertools
import random
import shutil
from typing import Dict, List, Optional, Tuple

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import protocol
from unicode_fol_kit.atp.protocol import ProverBackend, Verdict, get_backend
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Or, Quantifier, SortedConstant,
    SortedQuantifier, Variable, signature_axioms,
)
from unicode_fol_kit.fol.signature import Signature


def parse(text):
    result = api.parse_any(text)
    assert result.ok, (text, result.errors)
    return result.formula


def exists_in(sort, body):
    """``∃x:sort body``, built as a node (the text grammar reads sorted and unsorted constants apart)."""
    return SortedQuantifier("∃", Variable("x"), sort, body)


# Vampire is reached the way the kit can reach it on this host: a native binary, else the one in WSL.
# Whether it can run is the kit's own answer for exactly these options.
_NATIVE_VAMPIRE = shutil.which("vampire")
VAMPIRE = (dict(vampire_path=_NATIVE_VAMPIRE, use_wsl=False) if _NATIVE_VAMPIRE
           else dict(vampire_path="vampire", use_wsl=True))
HAVE_VAMPIRE = get_backend("vampire").available_for(VAMPIRE)


# =============================================================================
# The four acceptance problems
# =============================================================================

#: name, signature, premises, goal, valid-with-the-signature, the countermodel when it is not given
PROBLEMS = [
    pytest.param(
        Signature.from_dict({"functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}},
                             "sorts": ["A", "B"]}),
        [], "∃x:B x = f(carl:A)", True,
        "U={0,1}, A={0}, B={0}, carl=0, f(0)=1: f(carl)=1 is no element of B",
        id="a function declared from A to B lands in B"),
    pytest.param(
        Signature.from_dict({"constants": {"carl": "A"}, "sorts": ["A"]}),
        ["∀x:A P(x)"], "P(carl)", True,
        "U={0,1}, A={0}, P={0}, carl=1: carl is no element of A",
        id="a constant declared in A is in A"),
    pytest.param(
        Signature.from_dict({"subsorts": {"A": ["B"]}}),
        ["∀x:B P(x)"], "∀x:A P(x)", True,
        "U={0,1}, A={0,1}, B={0}, P={0}: every B is a P, the element 1 of A is not",
        id="a subsort edge is an inclusion"),
    pytest.param(
        Signature.from_dict({"predicates": {"P": {"arity": 1, "arg_sorts": ["A"]}}, "sorts": ["A"]}),
        [], "∀x (P(x) → A(x))", False,
        "U={0,1}, A={0}, P={1}: P holds of 1, which is no A -- and this is a countermodel WITH the "
        "signature too, because a predicate's declared rank says nothing about what it holds of",
        id="a predicate's declared rank gives nothing"),
]


@pytest.mark.parametrize("signature,premises,goal,valid_with,countermodel", PROBLEMS)
def test_z3_answers_each_problem_as_derived_with_and_without_the_signature(
        signature, premises, goal, valid_with, countermodel):
    premises = [parse(p) for p in premises]
    goal = parse(goal)
    without = api.prove(goal, premises, backends=["z3"])
    assert without.status == "refuted", countermodel               # the written countermodel exists
    with_signature = api.prove(goal, premises, backends=["z3"], signature=signature)
    assert with_signature.status == ("proved" if valid_with else "refuted")


@pytest.mark.parametrize("signature,premises,goal,valid_with,countermodel", PROBLEMS)
def test_the_model_finder_finds_the_countermodel_exactly_when_the_signature_leaves_one(
        signature, premises, goal, valid_with, countermodel):
    premises = [parse(p) for p in premises]
    goal = parse(goal)
    without = api.prove(goal, premises, backends=["modelfinder"], max_size=3)
    assert without.status == "refuted", countermodel
    with_signature = api.prove(goal, premises, backends=["modelfinder"], signature=signature, max_size=3)
    # a valid entailment has no countermodel, and exhausting the size bound proves nothing: unknown
    assert with_signature.status == ("unknown" if valid_with else "refuted")


@pytest.mark.skipif(not HAVE_VAMPIRE, reason="no Vampire binary the kit can run (native or WSL)")
@pytest.mark.parametrize("signature,premises,goal,valid_with,countermodel", PROBLEMS)
def test_vampire_answers_each_problem_as_derived_with_and_without_the_signature(
        signature, premises, goal, valid_with, countermodel):
    premises = [parse(p) for p in premises]
    goal = parse(goal)
    without = api.prove(goal, premises, backends=["vampire"], timeout=60000, **VAMPIRE)
    assert without.status == "refuted", countermodel
    with_signature = api.prove(goal, premises, backends=["vampire"], signature=signature,
                               timeout=60000, **VAMPIRE)
    assert with_signature.status == ("proved" if valid_with else "refuted")


def test_a_function_closure_is_guarded_by_the_declared_argument_sort():
    # f: A -> B declares nothing about f(dora) for a dora that is not known to be an A:
    # U={0,1}, A={0}, B={0}, f(0)=0, f(1)=1, dora=1.
    signature = Signature.from_dict({"functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}}})
    goal = exists_in("B", Atom("=", [Variable("x"), Function("f", [Constant("dora")])]))
    assert api.prove(goal, [], backends=["z3"], signature=signature).status == "refuted"
    assert api.prove(goal, [], backends=["modelfinder"], signature=signature,
                     max_size=3).status == "refuted"


def test_a_function_without_an_argument_sort_is_closed_for_every_argument():
    # g: -> B has no guard, so g(dora) is a B whatever dora is.
    signature = Signature.from_dict({"functions": {"g": {"arity": 1, "arg_sorts": None, "result_sort": "B"}}})
    goal = exists_in("B", Atom("=", [Variable("x"), Function("g", [Constant("dora")])]))
    assert api.prove(goal, [], backends=["z3"], signature=signature).status == "proved"
    assert api.prove(goal, [], backends=["z3"]).status == "refuted"


def test_a_constant_declared_in_a_sort_does_not_make_other_constants_members():
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    goal = parse("P(dora)")
    premises = [parse("∀x:A P(x)")]
    assert api.prove(goal, premises, backends=["z3"], signature=signature).status == "refuted"


# =============================================================================
# The signature reaches EVERY backend of the chain, after the caller's premises
# =============================================================================

class _Recorder(ProverBackend):
    """Records the premises it is asked about and never settles anything."""

    logics = frozenset({"fol"})
    external = False
    seen: List[list] = []

    def available(self):
        return True

    def decide(self, formula, premises=(), timeout=10000, **options):
        self.seen.append(list(premises))
        return Verdict("unknown", self.name, reason="incomplete")


def _recorders(monkeypatch, *names):
    seen = []
    for name in names:
        backend = type(f"Recorder_{name}", (_Recorder,), {"name": name, "seen": seen})()
        monkeypatch.setitem(protocol._REGISTRY, name, backend)
    return seen


def test_every_backend_of_the_chain_gets_the_signature_after_the_callers_premises(monkeypatch):
    seen = _recorders(monkeypatch, "rec-one", "rec-two")
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    premise = parse("P(dora)")
    api.prove(parse("Q(dora)"), [premise], backends=["rec-one", "rec-two"], signature=signature)
    expected = [premise, *signature_axioms(signature)]
    assert seen == [expected, expected]


def test_without_a_signature_the_premises_are_exactly_the_callers(monkeypatch):
    seen = _recorders(monkeypatch, "rec-one")
    premise = parse("P(dora)")
    api.prove(parse("Q(dora)"), [premise], backends=["rec-one"])
    assert seen == [[premise]]


# =============================================================================
# What comes back refers to the caller's own premises
# =============================================================================

def test_the_relevant_premises_are_indices_into_the_callers_list():
    # premise 0 is irrelevant, premise 1 says every A is a P; the signature says carl is an A and
    # its sentence A(carl) stands at an index past the caller's two premises.
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    premises = [parse("Q(ann)"), parse("∀x:A P(x)")]
    verdict = api.prove(parse("P(carl)"), premises, backends=["z3"], signature=signature,
                        relevant_premises=True)
    assert verdict.status == "proved"
    assert 1 in verdict.relevant_premises
    assert all(i < len(premises) for i in verdict.relevant_premises)


def test_the_z3_core_names_only_the_callers_premises():
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    premises = [parse("Q(ann)"), parse("∀x:A P(x)")]
    verdict = api.prove(parse("P(carl)"), premises, backends=["z3"], signature=signature)
    core = verdict.proof["core"]
    assert "p1" in core and "goal" in core
    assert all(tag == "goal" or int(tag[1:]) < len(premises) for tag in core)


def test_the_signature_axioms_are_what_the_proof_needed_and_the_core_still_leaves_them_out():
    # without A(carl) the premise p1 alone does not prove P(carl); with it, it does. The reported
    # core still names no index past the caller's premises.
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    premises = [parse("∀x:A P(x)")]
    assert api.prove(parse("P(carl)"), premises, backends=["z3"]).status == "refuted"
    verdict = api.prove(parse("P(carl)"), premises, backends=["z3"], signature=signature)
    assert verdict.status == "proved"
    assert set(verdict.proof["core"]) <= {"goal", "p0"}


# =============================================================================
# The refusals
# =============================================================================

def test_a_dict_is_a_type_error_that_names_the_way_to_build_a_signature():
    with pytest.raises(TypeError, match=r"Signature\.from_dict"):
        api.prove(parse("P(dora)"), [], backends=["z3"], signature={"constants": {"dora": "A"}})
    with pytest.raises(TypeError, match=r"Signature\.from_dict"):
        api.countermodel(parse("P(dora)"), [], signature={"constants": {"dora": "A"}})


@pytest.mark.parametrize("logic,formula", [
    ("modal", "□ P → P"),
    ("intuitionistic", "P → P"),
])
def test_another_logic_than_classical_first_order_is_refused_by_name(logic, formula):
    node = api.parse_any(formula, hint="modal" if logic == "modal" else None).formula
    with pytest.raises(ValueError, match=logic):
        api.prove(node, [], logic=logic, signature=Signature())


def test_a_signature_is_not_a_check_of_the_input():
    # prove does not check the formula against the signature: dora is not declared and the
    # question is still decided as written. api.check is the verb for that.
    signature = Signature.from_dict({"constants": {"carl": "A"}})
    goal = parse("P(dora) → P(dora)")
    assert api.prove(goal, [], backends=["z3"], signature=signature).status == "proved"
    assert not api.check(goal, signature=signature).ok


# =============================================================================
# countermodel
# =============================================================================

def test_countermodel_looks_for_a_structure_in_which_the_declarations_hold():
    signature = Signature.from_dict({"functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}}})
    valid = parse("∃x:B x = f(carl:A)")
    assert api.countermodel(valid, max_size=3).found                       # f(carl) may fall outside B
    assert not api.countermodel(valid, signature=signature, max_size=3).found
    # the same question, with a dora no A: a countermodel exists with the signature too
    unguarded = exists_in("B", Atom("=", [Variable("x"), Function("f", [Constant("dora")])]))
    assert api.countermodel(unguarded, signature=signature, max_size=3).found


# =============================================================================
# The randomised differential
# =============================================================================

SORTS = ("A", "B")
CONSTANTS = ("c1", "c2")
VARIABLES = ("x", "y")


def _pick(rng, options):
    return options[rng.randrange(len(options))]


def random_signature(rng) -> Signature:
    sorts = [s for s in SORTS if rng.random() < 0.8]
    constants = {c: (_pick(rng, SORTS) if rng.random() < 0.75 else None)
                 for c in CONSTANTS if rng.random() < 0.85}
    functions = {}
    roll = rng.random()
    if roll < 0.7:
        functions["f"] = {"arity": 1,
                          "arg_sorts": [_pick(rng, SORTS + (None,))],
                          "result_sort": _pick(rng, SORTS + (None,))}
    elif roll < 0.85:
        functions["g"] = {"arity": 2,
                          "arg_sorts": [_pick(rng, SORTS + (None,)), _pick(rng, SORTS + (None,))],
                          "result_sort": _pick(rng, SORTS + (None,))}
    subsorts = {"A": ["B"]} if rng.random() < 0.4 else {}
    predicates = {"P": {"arity": 1, "arg_sorts": [_pick(rng, SORTS + (None,))]}} if rng.random() < 0.5 else {}
    return Signature.from_dict({"sorts": sorts, "constants": constants, "functions": functions,
                                "subsorts": subsorts, "predicates": predicates})


def random_term(rng, scope, depth=0):
    roll = rng.random()
    if scope and roll < 0.4:
        return Variable(_pick(rng, scope))
    if roll < 0.7:
        return Constant(_pick(rng, CONSTANTS))
    if roll < 0.82:
        return SortedConstant(_pick(rng, CONSTANTS), _pick(rng, SORTS))
    if depth == 0 and roll < 0.93:
        return Function("f", [random_term(rng, scope, 1)])
    if depth == 0:
        return Function("g", [random_term(rng, scope, 1), random_term(rng, scope, 1)])
    return Constant(_pick(rng, CONSTANTS))


def random_atom(rng, scope):
    roll = rng.random()
    if roll < 0.3:
        return Atom("=", [random_term(rng, scope), random_term(rng, scope)])
    return Atom(_pick(rng, ("P", "Q")), [random_term(rng, scope)])


def random_formula(rng, scope, depth):
    if depth == 0 or rng.random() < 0.2:
        return random_atom(rng, scope)
    roll = rng.random()
    if roll < 0.15:
        return Not(random_formula(rng, scope, depth - 1))
    if roll < 0.45:
        connective = _pick(rng, (And, Or, Implies))
        return connective(random_formula(rng, scope, depth - 1), random_formula(rng, scope, depth - 1))
    name = _pick(rng, [v for v in VARIABLES if v not in scope] or list(VARIABLES))
    body = random_formula(rng, tuple(scope) + (name,), depth - 1)
    kind = _pick(rng, ("∀", "∃"))
    if rng.random() < 0.5:
        return SortedQuantifier(kind, Variable(name), _pick(rng, SORTS), body)
    return Quantifier(kind, Variable(name), body)


def _forall_in(sort, body):
    return SortedQuantifier("∀", Variable("x"), sort, body)


def _exists_in(sort, body):
    return SortedQuantifier("∃", Variable("x"), sort, body)


def targeted_problem(rng, signature):
    """A problem of the kind a signature decides: membership of a constant, the sort of a function
    value, an inclusion between sorts. Random formulas almost never depend on a declaration."""
    s, t = _pick(rng, SORTS), _pick(rng, SORTS)
    c = Constant(_pick(rng, CONSTANTS))
    annotated = SortedConstant(_pick(rng, CONSTANTS), s)
    argument = _pick(rng, (c, annotated))
    x = Variable("x")
    template = rng.randrange(6)
    if template == 0:                       # a constant of a sort has what every member of the sort has
        return [_forall_in(s, Atom("P", [x]))], Atom("P", [c])
    if template == 1:                       # ... and is a witness for the sort
        return [Atom("P", [c])], _exists_in(s, Atom("P", [x]))
    if template == 2:                       # the value of a function lies in its result sort
        return [], _exists_in(t, Atom("=", [x, Function("f", [argument])]))
    if template == 3:                       # an inclusion between sorts
        return [_forall_in(t, Atom("P", [x]))], _forall_in(s, Atom("P", [x]))
    if template == 4:                       # a property of every T holds of a value that is a T
        return [_forall_in(t, Atom("P", [x]))], Atom("P", [Function("f", [argument])])
    return [_forall_in(s, Not(Atom("P", [x])))], Not(Atom("P", [c]))


def random_problem(seed):
    rng = random.Random(seed)
    signature = random_signature(rng)
    if seed % 2:
        premises, goal = targeted_problem(rng, signature)
        return signature, premises, goal
    premises = [random_formula(rng, (), 2) for _ in range(rng.randrange(3))]
    goal = random_formula(rng, (), 2)
    return signature, premises, goal


# ---- the oracle: every structure of one or two elements, written from the definition ------------

def _walk(node):
    yield node
    for child in node._child_nodes():
        yield from _walk(child)


def _symbols(signature, formulas):
    """The sorts, constants, functions and unary predicates a search has to interpret."""
    sorts = set(signature.sorts)
    constants = set(signature.constants)
    functions = {(name, decl.arity) for name, decl in signature.functions.items()}
    predicates = set()
    for formula in formulas:
        for node in _walk(formula):
            if isinstance(node, (SortedQuantifier, SortedConstant)):
                sorts.add(node.sort)
            if isinstance(node, (Constant, SortedConstant)):
                constants.add(node.name)
            if isinstance(node, Function):
                functions.add((node.name, len(node.args)))
            if isinstance(node, Atom) and node.predicate not in ("=",) and node.predicate not in sorts:
                predicates.add((node.predicate, len(node.args)))
    for decl in signature.functions.values():
        sorts.update(s for s in (decl.arg_sorts or ()) if s is not None)
        if decl.result_sort is not None:
            sorts.add(decl.result_sort)
    for decl in signature.constants.values():
        if decl.sort is not None:
            sorts.add(decl.sort)
    for child, parents in signature.subsorts.items():
        sorts.add(child)
        sorts.update(parents)
    # a name that is a sort is no separate predicate: the sort and the unary predicate are one symbol
    predicates = {(n, a) for n, a in predicates if not (a == 1 and n in sorts)}
    return sorted(sorts), sorted(constants), sorted(functions), sorted(predicates)


def _value(node, structure, env):
    if isinstance(node, Variable):
        return env[node.name]
    if isinstance(node, (Constant, SortedConstant)):
        return structure["constants"][node.name]
    if isinstance(node, Function):
        args = tuple(_value(a, structure, env) for a in node.args)
        return structure["functions"][(node.name, len(args))][args]
    raise AssertionError(f"oracle: no reading for a term {node!r}")


def _holds(node, structure, env):
    if isinstance(node, Atom):
        args = tuple(_value(a, structure, env) for a in node.args)
        if node.predicate == "=":
            return args[0] == args[1]
        if len(args) == 1 and node.predicate in structure["sorts"]:
            return args[0] in structure["sorts"][node.predicate]
        return args in structure["predicates"][(node.predicate, len(args))]
    if isinstance(node, Not):
        return not _holds(node.formula, structure, env)
    if isinstance(node, And):
        return _holds(node.left, structure, env) and _holds(node.right, structure, env)
    if isinstance(node, Or):
        return _holds(node.left, structure, env) or _holds(node.right, structure, env)
    if isinstance(node, Implies):
        return (not _holds(node.left, structure, env)) or _holds(node.right, structure, env)
    if isinstance(node, (Quantifier, SortedQuantifier)):
        universe = (structure["sorts"][node.sort] if isinstance(node, SortedQuantifier)
                    else range(structure["size"]))
        results = (_holds(node.formula, structure, {**env, node.variable.name: d}) for d in universe)
        return all(results) if node.type == "∀" else any(results)
    raise AssertionError(f"oracle: no reading for a formula {node!r}")


def _nonempty_subsets(size):
    return [frozenset(c) for r in range(1, size + 1) for c in itertools.combinations(range(size), r)]


def countermodel_within_two(signature, premises, goal) -> Optional[dict]:
    """A structure of at most two elements that satisfies the signature's declarations and the
    premises and falsifies the goal, or ``None``."""
    sort_names, constant_names, function_keys, predicate_keys = _symbols(signature, [*premises, goal])
    annotated: Dict[str, set] = {}
    for formula in [*premises, goal]:
        for node in _walk(formula):
            if isinstance(node, SortedConstant):
                annotated.setdefault(node.name, set()).add(node.sort)
    for size in (1, 2):
        domain = range(size)
        for subsets in itertools.product(_nonempty_subsets(size), repeat=len(sort_names)):
            sorts = dict(zip(sort_names, subsets))
            # a subsort edge S < T is S ⊆ T
            if any(not sorts[child] <= sorts[parent]
                   for child, parents in signature.subsorts.items() for parent in parents):
                continue
            allowed = []
            for name in constant_names:
                needs = set(annotated.get(name, ()))
                declared = signature.constants.get(name)
                if declared is not None and declared.sort is not None:
                    needs.add(declared.sort)
                allowed.append([d for d in domain if all(d in sorts[s] for s in needs)])
            for constant_values in itertools.product(*allowed):
                constants = dict(zip(constant_names, constant_values))
                tables = []
                for name, arity in function_keys:
                    arguments = list(itertools.product(domain, repeat=arity))
                    declared = signature.functions.get(name)
                    tables.append([dict(zip(arguments, values))
                                   for values in itertools.product(domain, repeat=len(arguments))
                                   if declared is None or _closed(declared, sorts, dict(zip(arguments, values)))])
                relations = []
                for name, arity in predicate_keys:
                    arguments = list(itertools.product(domain, repeat=arity))
                    relations.append([{a for a, keep in zip(arguments, mask) if keep}
                                      for mask in itertools.product((False, True), repeat=len(arguments))])
                for function_choice in itertools.product(*tables):
                    functions = {key: table for key, table in zip(function_keys, function_choice)}
                    for relation_choice in itertools.product(*relations):
                        structure = {"size": size, "sorts": sorts, "constants": constants,
                                     "functions": functions,
                                     "predicates": dict(zip(predicate_keys, relation_choice))}
                        if all(_holds(p, structure, {}) for p in premises) \
                                and not _holds(goal, structure, {}):
                            return structure
    return None


def _closed(declaration, sorts, table):
    """Does ``table`` map elements of the declared argument sorts into the declared result sort?"""
    if declaration.result_sort is None:
        return True
    guards = declaration.arg_sorts or (None,) * declaration.arity
    return all(value in sorts[declaration.result_sort]
               for arguments, value in table.items()
               if all(g is None or a in sorts[g] for g, a in zip(guards, arguments)))


def test_the_oracle_gives_the_hand_derived_answer_to_the_four_problems():
    # the oracle is what the differential below leans on, so it is checked against the four problems
    # first: a countermodel within two elements exists without the signature; with it, exactly the
    # last one still has one.
    for signature, premises, goal, valid_with, _ in (p.values for p in PROBLEMS):
        premises = [parse(p) for p in premises]
        goal = parse(goal)
        assert countermodel_within_two(Signature(), premises, goal) is not None
        found_with = countermodel_within_two(signature, premises, goal) is not None
        assert found_with == (not valid_with)


SEEDS = range(60)


def _z3(goal, premises, **options):
    return api.prove(goal, premises, backends=["z3"], timeout=20000, **options).status


def test_z3_with_the_signature_equals_z3_with_its_axioms_passed_by_hand():
    differing = 0
    for seed in SEEDS:
        signature, premises, goal = random_problem(seed)
        with_signature = _z3(goal, premises, signature=signature)
        by_hand = _z3(goal, [*premises, *signature_axioms(signature)])
        assert with_signature == by_hand, f"seed {seed}"
        if _z3(goal, premises) != with_signature:
            differing += 1
    # the signature is not decoration: it changes the answer for some generated problems
    assert differing >= 8


def test_a_proved_is_never_contradicted_by_a_structure_of_at_most_two_elements():
    proved = 0
    for seed in SEEDS:
        signature, premises, goal = random_problem(seed)
        if _z3(goal, premises, signature=signature) != "proved":
            continue
        proved += 1
        witness = countermodel_within_two(signature, premises, goal)
        assert witness is None, f"seed {seed}: {witness}"
    assert proved >= 12


def test_the_model_finder_finds_a_countermodel_exactly_when_the_oracle_does():
    refuted = 0
    for seed in range(20):
        signature, premises, goal = random_problem(seed)
        witness = countermodel_within_two(signature, premises, goal)
        verdict = api.prove(goal, premises, backends=["modelfinder"], signature=signature, max_size=2)
        assert (verdict.status == "refuted") == (witness is not None), f"seed {seed}"
        refuted += witness is not None
    assert 5 <= refuted <= 18
