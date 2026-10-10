"""Predicate quantifiers in a Kripke model: ``satisfies_modal`` on ``∀P`` / ``∃P``.

A bound predicate is an INTENSION: it has an extension of its own at each world. So
``∀P`` over a propositional ``P`` ranges over every set of worlds, and a formula with
such a quantifier can state a condition on the frame. The conditions below are the
classical correspondences, each derived by hand next to its formula, and they are
checked on EVERY frame with up to three worlds, at every world.

The second half compares the evaluator with a reference written here from the
definition alone: it carries the interpretation of a bound predicate along as a set
(of worlds, or of world-individual pairs), where the evaluator of the kit changes the
valuation of the model. The two share no code.
"""

import itertools
import random

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, Iff, Implies, Not, Or, Quantifier,
    SecondOrderQuantifier, Variable,
)
from unicode_logic_kit.semantics import kripke
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal

SOM = MSFLParser(second_order=True, modal=True).parse
SOMS = MSFLParser(second_order=True, modal=True, many_sorted=True).parse


def frames(n):
    """Every relation on ``range(n)``, as a set of pairs."""
    pairs = [(a, b) for a in range(n) for b in range(n)]
    for mask in range(1 << len(pairs)):
        yield {pairs[i] for i in range(len(pairs)) if (mask >> i) & 1}


def successors(relation, w):
    return {v for (u, v) in relation if u == w}


# ---------------------------------------------------------------------------
# Correspondence: a formula with a propositional quantifier and its frame condition
# ---------------------------------------------------------------------------
#
# Each condition is on the relation R and the world w the formula is read at.
#
#   ∀P (□P → P)        w sees itself. If it does, □P gives P at w. If it does not, take
#                      P = the successors of w: □P holds at w and P does not.
#   ∀P (□P → □□P)      every world two steps from w is one step from it. With
#                      P = the successors of w, □□P says exactly that.
#   ∀P (P → □◇P)       every successor of w sees w. With P = {w}, ◇P at a successor u
#                      says that u sees w.
#   ∀P (◇P → □P)       w has at most one successor. With two, u and v, take P = {u}.
#   ∃P (◇P ∧ ◇¬P)      w has at least two successors: one in P, one outside.
#   ∀P (□P → ◇P)       w has a successor. Without one □P holds and ◇P does not.
#   ∀P ◇P              never: P = the empty set.
#   ∃P □P              always: P = every world.
#   ∀P (P(a) → □P(a))  every successor of w is w itself. The extension of P at w says
#                      nothing about its extension at another world u: take P true of a
#                      at w alone.
CORRESPONDENCES = {
    "∀P (□P → P)": lambda R, w: (w, w) in R,
    "∀P (□P → □□P)": lambda R, w: all((w, v) in R
                                      for u in successors(R, w) for v in successors(R, u)),
    "∀P (P → □◇P)": lambda R, w: all((u, w) in R for u in successors(R, w)),
    "∀P (◇P → □P)": lambda R, w: len(successors(R, w)) <= 1,
    "∃P (◇P ∧ ◇¬P)": lambda R, w: len(successors(R, w)) >= 2,
    "∀P (□P → ◇P)": lambda R, w: len(successors(R, w)) >= 1,
    "∀P ◇P": lambda R, w: False,
    "∃P □P": lambda R, w: True,
    "∀P (P(a) → □P(a))": lambda R, w: successors(R, w) <= {w},
}


@pytest.mark.parametrize("text", sorted(CORRESPONDENCES))
def test_a_propositional_quantifier_states_its_frame_condition(text):
    formula = SOM(text)
    condition = CORRESPONDENCES[text]
    for n in (1, 2, 3):
        for relation in frames(n):
            model = KripkeModel(range(n), {"alethic": relation})
            for w in range(n):
                assert satisfies_modal(formula, model, w) == condition(relation, w), \
                    (text, sorted(relation), w)


def test_the_same_correspondence_for_the_relation_of_an_agent():
    """``∀P (K_a P → P)`` holds at w exactly when w is one of a's own alternatives."""
    formula = SOM("∀P (K_a P → P)")
    for relation in frames(2):
        model = KripkeModel(range(2), {"K:a": relation})
        for w in range(2):
            assert satisfies_modal(formula, model, w) == ((w, w) in relation)


def test_temporal_and_deontic_operators_under_a_predicate_quantifier():
    # Always reads the reflexive-transitive closure, so ⒼP → P holds whatever the frame is.
    always = SOM("∀P (ⒼP → P)")
    # Next reads one step: ⓃP → P holds for every P exactly when w is its own successor.
    nxt = SOM("∀P (ⓃP → P)")
    # Obligatory / Permitted read the deontic relation: ⓄP → ⓅP needs a successor.
    deontic = SOM("∀P (ⓄP → ⓅP)")
    for relation in frames(2):
        temporal = KripkeModel(range(2), {"temporal": relation})
        obligations = KripkeModel(range(2), {"deontic": relation})
        for w in range(2):
            assert satisfies_modal(always, temporal, w) is True
            assert satisfies_modal(nxt, temporal, w) == ((w, w) in relation)
            assert satisfies_modal(deontic, obligations, w) == bool(successors(relation, w))


def test_a_nominal_under_a_predicate_quantifier():
    """``∀P (@i P → P)`` holds at the world ``i`` names and nowhere else: at another
    world take P = that one world."""
    formula = SOM("∀P (@i P → P)")
    model = KripkeModel(range(3), {}, nominals={"i": 1})
    assert [satisfies_modal(formula, model, w) for w in range(3)] == [False, True, False]


def test_an_announcement_under_a_predicate_quantifier():
    """``[P!]P``: if P is false the announcement is not made; if it is true, P is still
    true at the same world of the model that keeps the P-worlds. So it holds for every P.
    ``⟨P!⟩¬P`` is false for every P for the same reason."""
    model = KripkeModel(range(2), {"K:a": {(0, 1), (1, 0)}})
    assert satisfies_modal(SOM("∀P [P!]P"), model, 0) is True
    assert satisfies_modal(SOM("∃P ⟨P!⟩¬P"), model, 0) is False
    # Q holds at world 0 alone, and the agent cannot tell world 0 from world 1.
    reflexive = KripkeModel(range(2), {"K:a": {(0, 0), (0, 1), (1, 1)}}, {0: {"Q"}})
    assert satisfies_modal(SOM("K_a Q"), reflexive, 0) is False
    # P = {0}: after it is announced world 0 is the one alternative left, and Q holds there.
    assert satisfies_modal(SOM("∃P (P ∧ [P!]K_a Q)"), reflexive, 0) is True
    # P = {0, 1}: the announcement removes nothing, and K_a Q is as false as before.
    assert satisfies_modal(SOM("∀P (P → [P!]K_a Q)"), reflexive, 0) is False
    # A true P is known once it is announced: every world that is left is a P-world.
    assert satisfies_modal(SOM("∀P (P → [P!]K_a P)"), reflexive, 0) is True


# ---------------------------------------------------------------------------
# Scope
# ---------------------------------------------------------------------------

def test_a_predicate_is_bound_inside_its_quantifier_and_free_outside():
    """The valuation of the model says what a FREE ``P`` is; a quantifier overrides it
    for its own scope only."""
    model = KripkeModel([0, 1], {"alethic": {(0, 1)}}, {0: {"P"}})
    assert satisfies_modal(SOM("P ∧ ∃P ¬P"), model, 0) is True
    assert satisfies_modal(SOM("¬P ∧ ∃P ¬P"), model, 0) is False
    assert satisfies_modal(SOM("(∃P ¬P) ∧ P"), model, 0) is True
    assert satisfies_modal(SOM("∀P (P ∨ ¬P) ∧ ◇¬P"), model, 0) is True      # P false at 1


def test_an_inner_quantifier_of_the_same_name_shadows_the_outer_one():
    model = KripkeModel([0])
    assert satisfies_modal(SOM("∀P ∃P P"), model, 0) is True       # the inner ∃P decides
    assert satisfies_modal(SOM("∃P ∀P P"), model, 0) is False
    assert satisfies_modal(SOM("∃P (P ∧ ∀P (P ∨ ¬P))"), model, 0) is True


def test_two_quantifiers_range_independently():
    """``∀P ∃Q □(P ↔ ¬Q)``: Q = the complement of P. ``∃Q ∀P □(P ↔ Q)`` needs a successor
    to fail: at a dead end the box is vacuous."""
    dead_end = KripkeModel([0])
    loop = KripkeModel([0], {"alethic": {(0, 0)}})
    for model in (dead_end, loop):
        assert satisfies_modal(SOM("∀P ∃Q □(P ↔ ¬Q)"), model, 0) is True
    assert satisfies_modal(SOM("∃Q ∀P □(P ↔ Q)"), dead_end, 0) is True
    assert satisfies_modal(SOM("∃Q ∀P □(P ↔ Q)"), loop, 0) is False


# ---------------------------------------------------------------------------
# Predicates with arguments
# ---------------------------------------------------------------------------

def test_a_predicate_of_an_individual_is_chosen_per_world():
    """``∀x ∃P (P(x) ∧ □¬P(x))``: make P true of x here and false of it at every
    successor. That works unless the world is its own successor."""
    model = KripkeModel([0, 1], {"alethic": {(0, 1), (1, 1)}}, domain=["a", "b"])
    formula = SOM("∀x ∃P (P(x) ∧ □¬P(x))")
    assert satisfies_modal(formula, model, 0) is True
    assert satisfies_modal(formula, model, 1) is False


def test_identity_of_indiscernibles_over_the_domain():
    """``∀P (P(x) → P(y))`` holds exactly when x and y are one individual, so the
    formula below asks for ``Q(d, d)`` of every individual and for nothing else."""
    formula = SOM("∀x ∀y (∀P (P(x) → P(y)) → Q(x, y))")
    both = KripkeModel([0], {}, {0: {"Q(a, a)", "Q(b, b)"}}, domain=["a", "b"])
    one = KripkeModel([0], {}, {0: {"Q(a, a)"}}, domain=["a", "b"])
    assert satisfies_modal(formula, both, 0) is True
    assert satisfies_modal(formula, one, 0) is False


def test_a_predicate_quantifier_is_not_restricted_to_what_exists_at_the_world():
    """World 0 holds only ``a`` and its successor only ``b``. ``P`` true of ``b`` at world 1
    and of nothing at world 0 makes ``□∀x P(x) ∧ ¬∃x P(x)`` true at world 0: the quantifier
    ranges over what ``P`` is of ``b``, an individual that does not exist at world 0."""
    model = KripkeModel([0, 1], {"alethic": {(0, 1)}}, domains={0: ["a"], 1: ["b"]})
    assert satisfies_modal(SOM("∃P (□∀x P(x) ∧ ¬∃x P(x))"), model, 0) is True
    # No P is both true and false of b at world 1, and world 0 does see world 1.
    assert satisfies_modal(SOM("∃P (□∃x P(x) ∧ □∀x ¬P(x))"), model, 0) is False


def test_a_binary_bound_predicate():
    """Some relation holds of (a, b) and not of (b, a); none holds of (a, a) and fails
    of (a, a)."""
    model = KripkeModel([0], domain=["a", "b"])
    assert satisfies_modal(SOM("∃R (R(a, b) ∧ ¬R(b, a))"), model, 0) is True
    assert satisfies_modal(SOM("∃R ∃x (R(x, x) ∧ ¬R(x, x))"), model, 0) is False
    assert satisfies_modal(SOM("∃R ∀x ∀y (R(x, y) ↔ ¬R(y, x))"), model, 0) is False   # x = y


def test_an_argument_without_a_binder_is_the_term_as_written():
    """A constant and a free variable are names here: two of them are two individuals."""
    model = KripkeModel([0])
    assert satisfies_modal(SOM("∃P (P(a) ∧ ¬P(b))"), model, 0) is True
    assert satisfies_modal(SOM("∃P (P(a) ∧ ¬P(a))"), model, 0) is False
    assert satisfies_modal(SOM("∀P (P(f(a)) → P(f(a)))"), model, 0) is True


def test_sorted_individuals_under_a_predicate_quantifier():
    """A sorted binder is the guarded unsorted one, and the guard is an atom of the
    valuation. With ``Human`` true of ``a`` alone, the predicate has to hold of ``a``."""
    model = KripkeModel([0], {}, {0: {"Human(a)", "Mortal(a)"}}, domain=["a", "b"])
    assert satisfies_modal(SOMS("∃P ∀x:Human (P(x) ∧ Mortal(x))"), model, 0) is True
    assert satisfies_modal(SOMS("∀P (∀x:Human P(x) → ∃x:Human P(x))"), model, 0) is True
    nobody = KripkeModel([0], {}, {0: set()}, domain=["a", "b"])
    assert satisfies_modal(SOMS("∀P (∀x:Human P(x) → ∃x:Human P(x))"), nobody, 0) is False


# ---------------------------------------------------------------------------
# What is refused
# ---------------------------------------------------------------------------

def test_a_bound_predicate_in_argument_position_is_refused():
    formula = MSFLParser(third_order=True, modal=True).parse("∀P (Pos(P) → □Pos(P))")
    with pytest.raises(NotImplementedError, match="argument position"):
        satisfies_modal(formula, KripkeModel([0]), 0)


def test_a_bound_predicate_named_like_a_sort_is_refused():
    formula = SOMS("∃Human ∀x:Human Human(x)")
    with pytest.raises(NotImplementedError, match="name of a sort"):
        satisfies_modal(formula, KripkeModel([0], domain=["a"]), 0)


def test_a_bound_predicate_at_another_arity_than_its_quantifier_states_is_refused():
    formula = SecondOrderQuantifier("∀", "P", 1, Atom("P", [Constant("a"), Constant("b")]))
    with pytest.raises(ValueError, match="one arity"):
        satisfies_modal(formula, KripkeModel([0]), 0)


def test_an_individual_binder_under_a_predicate_quantifier_needs_domains():
    with pytest.raises(ValueError, match="no object domains"):
        satisfies_modal(SOM("∃P ∀x P(x)"), KripkeModel([0]), 0)


def test_a_quantifier_over_too_many_interpretations_is_refused(monkeypatch):
    """Three worlds and one atom are 2 ** 3 interpretations."""
    model = KripkeModel(range(3), {"alethic": {(0, 1), (1, 2)}})
    monkeypatch.setattr(kripke, "MAX_PREDICATE_INTERPRETATIONS", 8)
    assert satisfies_modal(SOM("∀P (□P → P)"), model, 0) is False
    monkeypatch.setattr(kripke, "MAX_PREDICATE_INTERPRETATIONS", 7)
    with pytest.raises(ValueError, match="MAX_PREDICATE_INTERPRETATIONS"):
        satisfies_modal(SOM("∀P (□P → P)"), model, 0)


def test_equality_stays_refused_under_a_predicate_quantifier():
    with pytest.raises(NotImplementedError):
        satisfies_modal(SOM("∀P (P(a) → a = a)"), KripkeModel([0]), 0)


# ---------------------------------------------------------------------------
# Against a reference evaluator written from the definition
# ---------------------------------------------------------------------------
#
# A formula is a nested tuple:
#   ("p", name)                      a proposition
#   ("app", name, ("var", x))        a unary predicate of a variable
#   ("app", name, ("const", c))      ... of a constant
#   ("not", f) ("and", f, g) ("or", f, g) ("imp", f, g) ("iff", f, g) ("box", f) ("dia", f)
#   ("allx", x, f) ("exx", x, f)     an individual quantifier, over the domain of the world
#   ("all0", name, f) ("ex0", name, f)   a quantifier over a proposition
#   ("all1", name, f) ("ex1", name, f)   a quantifier over a unary predicate
#
# The reference keeps the interpretation of a bound proposition as a set of worlds and
# of a bound unary predicate as a set of (world, individual) pairs, over EVERY
# individual of the model and every constant of the formula.

def _subsets(items):
    items = list(items)
    for mask in range(1 << len(items)):
        yield frozenset(items[i] for i in range(len(items)) if (mask >> i) & 1)


def _constants(formula):
    if formula[0] == "app":
        return {formula[2][1]} if formula[2][0] == "const" else set()
    out = set()
    for part in formula[1:]:
        if isinstance(part, tuple):
            out |= _constants(part)
    return out


def reference(formula, model, w, props, preds, assignment, universe):
    worlds, relation, valuation, domains = model
    op = formula[0]
    if op == "p":
        name = formula[1]
        return (w in props[name]) if name in props else (name in valuation[w])
    if op == "app":
        name, (kind, value) = formula[1], formula[2]
        individual = assignment[value] if kind == "var" else value
        if name in preds:
            return (w, individual) in preds[name]
        return f"{name}({individual})" in valuation[w]
    if op == "not":
        return not reference(formula[1], model, w, props, preds, assignment, universe)
    if op in ("and", "or", "imp", "iff"):
        left = reference(formula[1], model, w, props, preds, assignment, universe)
        right = reference(formula[2], model, w, props, preds, assignment, universe)
        return {"and": left and right, "or": left or right,
                "imp": (not left) or right, "iff": left == right}[op]
    if op in ("box", "dia"):
        results = [reference(formula[1], model, v, props, preds, assignment, universe)
                   for v in worlds if (w, v) in relation]
        return all(results) if op == "box" else any(results)
    if op in ("allx", "exx"):
        results = [reference(formula[2], model, w, props, preds,
                             {**assignment, formula[1]: d}, universe)
                   for d in domains[w]]
        return all(results) if op == "allx" else any(results)
    if op in ("all0", "ex0"):
        results = (reference(formula[2], model, w, {**props, formula[1]: chosen}, preds,
                             assignment, universe)
                   for chosen in _subsets(worlds))
        return all(results) if op == "all0" else any(results)
    if op in ("all1", "ex1"):
        pairs = [(v, d) for v in worlds for d in universe]
        results = (reference(formula[2], model, w, props, {**preds, formula[1]: chosen},
                             assignment, universe)
                   for chosen in _subsets(pairs))
        return all(results) if op == "all1" else any(results)
    raise AssertionError(op)


def to_node(formula):
    op = formula[0]
    if op == "p":
        return Atom(formula[1], [])
    if op == "app":
        kind, value = formula[2]
        return Atom(formula[1], [Variable(value) if kind == "var" else Constant(value)])
    if op == "not":
        return Not(to_node(formula[1]))
    if op in ("and", "or", "imp", "iff"):
        cls = {"and": And, "or": Or, "imp": Implies, "iff": Iff}[op]
        return cls(to_node(formula[1]), to_node(formula[2]))
    if op in ("box", "dia"):
        return (Box if op == "box" else Diamond)(to_node(formula[1]))
    if op in ("allx", "exx"):
        return Quantifier("∀" if op == "allx" else "∃", Variable(formula[1]), to_node(formula[2]))
    if op in ("all0", "ex0", "all1", "ex1"):
        return SecondOrderQuantifier("∀" if op.startswith("all") else "∃", formula[1],
                                     int(op[-1]), to_node(formula[2]))
    raise AssertionError(op)


def random_formula(rng, depth, variables, quantifiers_left, first_order):
    """A random formula; ``variables`` are the individual variables in scope."""
    leaves = ["p"]
    if first_order:
        leaves.append("app")
    if depth == 0:
        op = rng.choice(leaves)
    else:
        ops = leaves + ["not", "and", "or", "imp", "iff", "box", "dia"]
        if quantifiers_left:
            ops += ["all0", "ex0"]
            if first_order:
                ops += ["all1", "ex1"]
        if first_order:
            ops += ["allx", "exx"]
        op = rng.choice(ops)
    if op == "p":
        return ("p", rng.choice(["P", "Q"]))
    if op == "app":
        if variables and rng.random() < 0.75:
            term = ("var", rng.choice(variables))
        else:
            term = ("const", rng.choice(["a", "c"]))
        return ("app", rng.choice(["F", "G"]), term)
    if op in ("not", "box", "dia"):
        return (op, random_formula(rng, depth - 1, variables, quantifiers_left, first_order))
    if op in ("and", "or", "imp", "iff"):
        return (op, random_formula(rng, depth - 1, variables, quantifiers_left, first_order),
                random_formula(rng, depth - 1, variables, quantifiers_left, first_order))
    if op in ("allx", "exx"):
        x = rng.choice(["x", "y"])
        return (op, x, random_formula(rng, depth - 1, variables + [x] if x not in variables
                                      else variables, quantifiers_left, first_order))
    name = rng.choice(["P", "Q"] if op.endswith("0") else ["F", "G"])
    return (op, name,
            random_formula(rng, depth - 1, variables, quantifiers_left - 1, first_order))


def random_model(rng, n, first_order):
    worlds = list(range(n))
    relation = {(a, b) for a in worlds for b in worlds if rng.random() < 0.45}
    keys = ["P", "Q"]
    domains = None
    if first_order:
        individuals = ["a", "b"]
        domains = {w: [d for d in individuals if rng.random() < 0.7] for w in worlds}
        keys += [f"{name}({d})" for name in ("F", "G") for d in individuals + ["c"]]
    valuation = {w: {key for key in keys if rng.random() < 0.5} for w in worlds}
    return worlds, relation, valuation, domains


def _compare(seed, first_order):
    rng = random.Random(seed)
    n = rng.choice([1, 2] if first_order else [1, 2, 3])
    worlds, relation, valuation, domains = random_model(rng, n, first_order)
    formula = random_formula(rng, 4, [], 2, first_order)
    universe = sorted(set().union(*domains.values()) | _constants(formula)) if first_order else []
    model = KripkeModel(worlds, {"alethic": relation}, valuation, domains=domains)
    node = to_node(formula)
    for w in worlds:
        expected = reference(formula, (worlds, relation, valuation, domains), w, {}, {}, {},
                             universe)
        assert satisfies_modal(node, model, w) == expected, (seed, formula, w)


@pytest.mark.parametrize("block", range(10))
def test_propositional_quantifiers_agree_with_the_reference(block):
    for seed in range(block * 40, block * 40 + 40):
        _compare(seed, first_order=False)


@pytest.mark.parametrize("block", range(10))
def test_predicate_quantifiers_over_individuals_agree_with_the_reference(block):
    for seed in range(10_000 + block * 30, 10_000 + block * 30 + 30):
        _compare(seed, first_order=True)


def test_the_random_formulas_do_hold_predicate_quantifiers():
    """The comparison above is about formulas with quantifiers, not about a sample
    that happens to hold none."""
    with_quantifier = 0
    with_individual_under_quantifier = 0
    for seed in range(400):
        rng = random.Random(seed)
        n = rng.choice([1, 2, 3])
        random_model(rng, n, False)
        text = repr(random_formula(rng, 4, [], 2, False))
        with_quantifier += ("all0" in text) or ("ex0" in text)
    for seed in range(10_000, 10_300):
        rng = random.Random(seed)
        n = rng.choice([1, 2])
        random_model(rng, n, True)
        text = repr(random_formula(rng, 4, [], 2, True))
        with_individual_under_quantifier += ("all1" in text) or ("ex1" in text)
    assert with_quantifier >= 250                       # of 400
    assert with_individual_under_quantifier >= 120      # of 300
