"""Resolution on modal input with a sorted constant: ``c:S`` is an element of ``S`` at every world.

A sorted constant ``c:S`` denotes an element of ``S``, and a constant is a rigid designator, so the guard
atom ``S(c)`` holds at EVERY world of every legal model, with no existence condition. The standard
translation's guard atom is world-relative (``S(c, w)``) and says nothing of the kind, so the lowered
problem needs the rigid fact as a hypothesis, in the translation's own vocabulary
(``∀v0 S(c, v0)``, :func:`~unicode_logic_kit.fol.modal_translation.frame_axioms`). The facts below are
derived by hand in the K frame (no condition on the accessibility relation), for ``carl:Human``:

* ``□Human(carl:Human)`` is VALID: at every successor of any world ``carl`` is a ``Human``.
* ``◇Human(carl:Human)`` is NOT valid: one world with no successor makes ``◇`` false there (it is valid
  on a serial frame, where every world has a successor).
* ``□Mortal(carl:Human)`` is NOT valid: nothing says ``carl`` is ``Mortal`` at the successor.
* ``□Human(carl)`` is NOT valid: with ``carl`` unannotated nothing says it is a ``Human``.

The generated differential compares the answer with a brute-force Kripke check written here, over all
models of at most two worlds (and, for the quantified family, two individuals), membership of a sorted
constant true at every world. Resolution may answer "not proved"; it may never prove a formula the
enumeration refutes.
"""

import itertools
import random
import time

import pytest

from unicode_logic_kit.atp.resolution import prove
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, Implies, Not, Or, Quantifier, SortedConstant, SortedQuantifier,
    Variable,
)

_PARSER = MSFLParser(modal=True, many_sorted=True)


def parse(text):
    return _PARSER.parse(text)


def plain(name, predicate="Mortal"):
    """``predicate(name)`` with ``name`` UNannotated (the many-sorted grammar cannot write one)."""
    return Atom(predicate, [Constant(name)])


def proved(formula, premises=()):
    formula = parse(formula) if isinstance(formula, str) else formula
    return prove([parse(p) for p in premises], formula, max_steps=10000)


# ---------------------------------------------------------------------------
# Hand-derived verdicts
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text", [
    "□Human(carl:Human)",
    "□(Human(carl:Human) ∨ Q)",
    "□Q → □(Q ∧ Human(carl:Human))",
    "□(Human(carl:Human) ∧ Animal(carl:Animal))",     # a constant written with two sorts lies in both
    "□□Human(carl:Human)",
])
def test_a_sorted_constant_is_a_member_of_its_sort_at_every_world(text):
    assert proved(text)


def test_a_sorted_and_a_plain_occurrence_of_one_name_are_one_constant():
    # □Mortal(carl:Human) → □Mortal(carl): the same atom twice.
    assert proved(Implies(parse("□Mortal(carl:Human)"), Box(plain("carl"))))
    # The annotation in ONE formula of the problem makes carl a Human everywhere, in every formula of it:
    # premise Human(carl:Human) entails □Human(carl) with the goal's carl unannotated.
    assert proved(Box(plain("carl", "Human")), premises=["Human(carl:Human)"])


def test_the_membership_is_a_fact_of_the_problem_and_not_part_of_the_goal():
    # As a PREMISE the modal Q entails □Q ∧ □Human(carl:Human) too; the fact is never negated or proved.
    assert proved("□Q ∧ □Human(carl:Human)", premises=["□Q"])


@pytest.mark.parametrize("formula", [
    "◇Human(carl:Human)",            # a world without successor
    "□Mortal(carl:Human)",           # carl need not be Mortal at the successor
    Box(plain("carl", "Human")),      # □Human(carl): an unannotated constant is in no sort
    "Mortal(carl:Human) → □Mortal(carl:Human)",
    "□Human(carl:Human) → ◇Human(carl:Human)",
    Implies(parse("□Mortal(carl:Human)"), Box(plain("dora", "Human"))),
])
def test_nothing_else_is_proved(formula):
    assert not proved(formula)


def test_a_sorted_constant_makes_no_other_constant_a_member():
    # dora is annotated nowhere, so nothing says it is a Human: the problem has a countermodel.
    assert not proved(Box(plain("dora", "Human")), premises=["Human(carl:Human)"])


def test_the_hand_built_countermodels_of_the_unproved_ones_are_models_of_the_definition():
    # (formula, worlds, accessibility, valuation of the ground atoms): the membership atom Human(carl) of
    # a sorted carl is true at every world, the unannotated one is free.
    human, mortal = ("Human", ("carl",)), ("Mortal", ("carl",))
    cases = [
        # one world, no successor: ◇ is false there
        (parse("◇Human(carl:Human)"), 1, set(), {human: [True]}),
        # two worlds, 0 → 1, Mortal(carl) false at the successor
        (parse("□Mortal(carl:Human)"), 2, {(0, 1)}, {human: [True, True], mortal: [True, False]}),
        # the unannotated Human(carl) fails at the successor
        (Box(plain("carl", "Human")), 2, {(0, 1)}, {human: [True, False]}),
    ]
    for formula, n, relation, table in cases:
        valuation = {(atom, w): value[w] for atom, value in table.items() for w in range(n)}
        model = (n, relation, valuation)
        assert holds_prop(formula, model, 0) is False, formula.to_unicode_str()
        if sorted_pairs(formula):
            assert all(valuation[(human, w)] for w in range(n))


# ---------------------------------------------------------------------------
# A brute-force Kripke check
# ---------------------------------------------------------------------------

def sorted_pairs(formula):
    out = []
    for node in formula.walk():
        if isinstance(node, SortedConstant) and (node.name, node.sort) not in out:
            out.append((node.name, node.sort))
    return out


def term_key(term):
    if isinstance(term, (SortedConstant, Constant)):
        return term.name
    return ("var", term.name)


def prop_models(formula, max_worlds=2):
    """Every model on at most ``max_worlds`` worlds in which each ``S(c)`` of a sorted ``c:S`` holds everywhere."""
    atoms = []
    for atom in formula.atoms():
        key = (atom.predicate, tuple(term_key(t) for t in atom.args))
        if key not in atoms:
            atoms.append(key)
    members = {(sort, (name,)) for name, sort in sorted_pairs(formula)}
    atoms += [m for m in sorted(members) if m not in atoms]
    for n in range(1, max_worlds + 1):
        worlds = range(n)
        pairs = [(a, b) for a in worlds for b in worlds]
        for rbits in itertools.product((False, True), repeat=len(pairs)):
            relation = {pair for pair, bit in zip(pairs, rbits) if bit}
            free = [(a, w) for a in atoms if a not in members for w in worlds]
            for vbits in itertools.product((False, True), repeat=len(free)):
                valuation = {(a, w): True for a in members for w in worlds}
                valuation.update(dict(zip(free, vbits)))
                yield n, relation, valuation


def holds_prop(node, model, w):
    n, relation, valuation = model
    if isinstance(node, Atom):
        return valuation[((node.predicate, tuple(term_key(t) for t in node.args)), w)]
    if isinstance(node, Not):
        return not holds_prop(node.formula, model, w)
    if isinstance(node, And):
        return holds_prop(node.left, model, w) and holds_prop(node.right, model, w)
    if isinstance(node, Or):
        return holds_prop(node.left, model, w) or holds_prop(node.right, model, w)
    if isinstance(node, Implies):
        return (not holds_prop(node.left, model, w)) or holds_prop(node.right, model, w)
    if isinstance(node, Box):
        return all(holds_prop(node.formula, model, v) for v in range(n) if (w, v) in relation)
    if isinstance(node, Diamond):
        return any(holds_prop(node.formula, model, v) for v in range(n) if (w, v) in relation)
    raise TypeError(type(node))


def refuted_prop(formula):
    return any(not holds_prop(formula, model, w) for model in prop_models(formula) for w in range(model[0]))


def gen_prop(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        carl_human, carl_animal = SortedConstant("carl", "Human"), SortedConstant("carl", "Animal")
        return rng.choice([
            Atom("Q", ()), Atom("Q", ()), Atom("Mortal", (carl_human,)), Atom("Mortal", (Constant("carl"),)),
            Atom("Human", (carl_human,)), Atom("Animal", (carl_animal,)),
            Atom("Mortal", (SortedConstant("dora", "Animal"),)), Atom("Mortal", (Constant("dora"),)),
        ])
    kind = rng.choice(["not", "and", "or", "imp", "box", "dia", "box", "dia"])
    if kind == "not":
        return Not(gen_prop(rng, depth - 1))
    if kind == "box":
        return Box(gen_prop(rng, depth - 1))
    if kind == "dia":
        return Diamond(gen_prop(rng, depth - 1))
    left, right = gen_prop(rng, depth - 1), gen_prop(rng, depth - 1)
    return {"and": And, "or": Or, "imp": Implies}[kind](left, right)


PROP_SEEDS = range(3000, 3300)
TIMEOUT_MS = 1500


def answer_within_limit(formula, **limits):
    """``(proved, finished)``: ``finished`` is False when the saturation ran into the wall-clock limit.

    Resolution is a semi-decision procedure and a few invalid formulas (``◇A ∧ □B``) saturate for a
    long time, so each call carries a limit; a limit hit is "not proved", never a verdict of invalidity.
    """
    start = time.perf_counter()
    answer = prove([], formula, timeout=TIMEOUT_MS, **limits)
    return answer, (time.perf_counter() - start) * 1000 < 0.9 * TIMEOUT_MS


def test_resolution_agrees_with_the_enumeration_on_generated_propositional_modal_formulas():
    n_proved = n_valid = 0
    for seed in PROP_SEEDS:
        formula = gen_prop(random.Random(seed), 2)
        answer, finished = answer_within_limit(formula, max_steps=4000)
        refuted = refuted_prop(formula)
        text = formula.to_unicode_str()
        assert not (answer and refuted), f"seed {seed}: proved a formula with a countermodel: {text}"
        # A formula with no countermodel up to two worlds is proved, unless the search was cut off:
        # these formulas are shallow, and K is decided by saturation.
        assert answer or refuted or not finished, f"seed {seed}: valid up to two worlds, not proved: {text}"
        n_proved += answer
        n_valid += not refuted
    assert n_proved >= 40 and n_valid >= n_proved      # the family is not vacuous


# ---------------------------------------------------------------------------
# The quantified family: constant domain, sort guards world-relative
# ---------------------------------------------------------------------------

def gen_quant(rng, depth, scope):
    if depth == 0 or rng.random() < 0.2:
        pool = [Atom("Q", ()), Atom("Mortal", (SortedConstant("carl", "Human"),)),
                Atom("Human", (SortedConstant("carl", "Human"),))]
        for var in scope:
            pool += [Atom("Mortal", (var,)), Atom("Human", (var,)), Atom("Mortal", (var,))]
        return rng.choice(pool)
    kind = rng.choice(["not", "and", "or", "imp", "box", "dia", "all_s", "ex_s", "all_u", "ex_u"])
    if kind == "not":
        return Not(gen_quant(rng, depth - 1, scope))
    if kind == "box":
        return Box(gen_quant(rng, depth - 1, scope))
    if kind == "dia":
        return Diamond(gen_quant(rng, depth - 1, scope))
    if kind in ("all_s", "ex_s", "all_u", "ex_u"):
        var = Variable("x" if not scope else "y")
        body = gen_quant(rng, depth - 1, scope + (var,))
        if kind in ("all_s", "ex_s"):
            return SortedQuantifier("∀" if kind == "all_s" else "∃", var, "Human", body)
        return Quantifier("∀" if kind == "all_u" else "∃", var, body)
    left, right = gen_quant(rng, depth - 1, scope), gen_quant(rng, depth - 1, scope)
    return {"and": And, "or": Or, "imp": Implies}[kind](left, right)


def quant_models(max_worlds=2, max_individuals=2):
    """Models over Human/1, Mortal/1, Q/0 and the rigid constant carl; every Human extension is non-empty
    at every world and holds carl at every world; the domain is the same at every world."""
    for n in range(1, max_worlds + 1):
        worlds = range(n)
        pairs = [(a, b) for a in worlds for b in worlds]
        for m in range(1, max_individuals + 1):
            domain = tuple(range(m))
            subsets = [frozenset(s) for r in range(m + 1) for s in itertools.combinations(domain, r)]
            nonempty = [s for s in subsets if s]
            for rbits in itertools.product((False, True), repeat=len(pairs)):
                relation = {pair for pair, bit in zip(pairs, rbits) if bit}
                for human in itertools.product(nonempty, repeat=n):
                    for mortal in itertools.product(subsets, repeat=n):
                        for q in itertools.product((False, True), repeat=n):
                            for carl in domain:
                                if all(carl in human[w] for w in worlds):
                                    yield n, relation, domain, human, mortal, q, carl


def holds_quant(node, model, w, env):
    n, relation, domain, human, mortal, q, carl = model
    if isinstance(node, Atom):
        if node.predicate == "Q":
            return q[w]
        arg = node.args[0]
        element = env[arg.name] if isinstance(arg, Variable) else carl
        return element in (human[w] if node.predicate == "Human" else mortal[w])
    if isinstance(node, Not):
        return not holds_quant(node.formula, model, w, env)
    if isinstance(node, And):
        return holds_quant(node.left, model, w, env) and holds_quant(node.right, model, w, env)
    if isinstance(node, Or):
        return holds_quant(node.left, model, w, env) or holds_quant(node.right, model, w, env)
    if isinstance(node, Implies):
        return (not holds_quant(node.left, model, w, env)) or holds_quant(node.right, model, w, env)
    if isinstance(node, Box):
        return all(holds_quant(node.formula, model, v, env) for v in range(n) if (w, v) in relation)
    if isinstance(node, Diamond):
        return any(holds_quant(node.formula, model, v, env) for v in range(n) if (w, v) in relation)
    ranges = human[w] if isinstance(node, SortedQuantifier) else domain
    results = (holds_quant(node.formula, model, w, {**env, node.variable.name: d}) for d in ranges)
    return all(results) if node.type == "∀" else any(results)


QUANT_SEEDS = range(100, 124)


def test_resolution_never_proves_a_quantified_modal_formula_the_enumeration_refutes():
    models = list(quant_models())
    n_proved = 0
    for seed in QUANT_SEEDS:
        formula = gen_quant(random.Random(seed), 3, ())
        answer, _ = answer_within_limit(formula, max_steps=60)
        refuted = any(not holds_quant(formula, model, w, {}) for model in models for w in range(model[0]))
        assert not (answer and refuted), f"seed {seed}: proved a formula with a countermodel: {formula.to_unicode_str()}"
        n_proved += answer
    assert n_proved >= 5
