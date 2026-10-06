"""The probabilistic routes read the truth constants as the constants they are.

Every probability distribution gives the constant true the probability 1 and the constant
false the probability 0: it holds in every possible world and in every total choice. The
two routes used to count ``⊤`` and ``⊥`` as propositional letters, so ``P(⊤)`` came out as
``[0, 1]`` and the impossible constraint ``P(⊥) = 1`` was accepted.

Every expected value below is derived by hand (the world-by-world argument is in the
comment of its case) before it is compared with the routes, and both strategies of
``entailment_bounds`` and both methods of ``query`` must give it.

* ``⊤`` / ``$true`` is the nullary atom ``$true``; ``⊥`` / ``$false`` the nullary atom
  ``$false``; an atom NAMED like a glyph (``Atom('⊤', ())``) is the same constant; the same
  name WITH an argument is an ordinary user predicate.
"""

from fractions import Fraction as F

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.fol._truth_constants import truth_value
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Implies, Not, Or
from unicode_fol_kit.prob import ProbConstraint, ProbFact, ProbProgram, entailment_bounds, query

STRATEGIES = ["direct", "column_generation"]


def f(text):
    return api.parse_any(text).formula


TOP, BOT = Atom("$true", ()), Atom("$false", ())
RAIN, WET = Atom("Rain", ()), Atom("Wet", ())

#: Five spellings of each constant: the two atoms (the one the readers produce and the one named
#: like the glyph), and the texts of four grammars that read to it (unicode, TPTP, SMT-LIB, LaTeX).
#: A bare ``\top`` is not a LaTeX formula, so its text is the conjunction of two.
TRUE_TEXTS = ["⊤", "fof(a, axiom, $true).", "(assert true)", r"\top \land \top"]
FALSE_TEXTS = ["⊥", "fof(a, axiom, $false).", "(assert false)", r"\bot \land \bot"]
TRUE_NODES = [Atom("$true", ()), Atom("⊤", ())] + [f(text) for text in TRUE_TEXTS]
FALSE_NODES = [Atom("$false", ()), Atom("⊥", ())] + [f(text) for text in FALSE_TEXTS]


def bounds(constraints, conclusion, strategy):
    result = entailment_bounds(
        [ProbConstraint(f(text), F(lo), F(hi), f(given) if given else None)
         for text, lo, hi, given in constraints], f(conclusion), strategy=strategy)
    return result.lower, result.upper


# ===========================================================================
# entailment_bounds
# ===========================================================================

# (conclusion, expected [lower, upper]) with NO constraint. In every world ⊤ holds and ⊥ does not.
UNCONSTRAINED = [
    ("⊤", (1, 1)),                 # true in every world
    ("⊥", (0, 0)),                 # false in every world
    ("¬⊥", (1, 1)),                # ¬false = true
    ("¬⊤", (0, 0)),
    ("¬¬⊤", (1, 1)),
    ("P ∨ ⊤", (1, 1)),             # a disjunct that always holds
    ("P ∧ ⊥", (0, 0)),             # a conjunct that never holds
    ("P → ⊤", (1, 1)),             # the consequent always holds
    ("⊥ → P", (1, 1)),             # the antecedent never holds
    ("⊤ → P", (0, 1)),             # equivalent to P: free
    ("P ∧ ⊤", (0, 1)),             # equivalent to P: free
    ("P ↔ ⊤", (0, 1)),             # equivalent to P
    ("P ⊕ ⊤", (0, 1)),             # equivalent to ¬P
    ("(P ∧ ⊥) ∨ (Q ∨ ⊤)", (1, 1)),
]


@pytest.mark.parametrize("strategy", STRATEGIES)
@pytest.mark.parametrize("conclusion,expected", UNCONSTRAINED)
def test_a_truth_constant_has_its_value_in_every_world(conclusion, expected, strategy):
    assert bounds([], conclusion, strategy) == tuple(F(v) for v in expected)


@pytest.mark.parametrize("strategy", STRATEGIES)
def test_a_constant_is_not_a_letter_with_a_world_of_its_own(strategy):
    # No atoms at all: ONE world (2**0). With one letter P: two worlds, constants or not.
    assert entailment_bounds([], f("⊤"), strategy=strategy).n_worlds == 1
    assert entailment_bounds([], f("¬⊥"), strategy=strategy).n_worlds == 1
    assert entailment_bounds([], f("P ∨ ⊤"), strategy=strategy).n_worlds == 2
    assert entailment_bounds([ProbConstraint.exact(f("P ∧ ⊤"), F(1, 2))], f("Q ∨ ⊥"),
                             strategy=strategy).n_worlds == 4


# (constraints [(formula, lower, upper, given)], conclusion, expected)
CONSTRAINED = [
    # P(P ∧ ⊤) = P(P) in every distribution.
    ([("P ∧ ⊤", F(7, 10), F(7, 10), None)], "P", (F(7, 10), F(7, 10))),
    # P(⊤ → Q) = P(Q): with the value 1, Q is certain; with 3/10, Q is 3/10.
    ([("⊤ → Q", F(1), F(1), None)], "Q", (F(1), F(1))),
    ([("⊤ → Q", F(3, 10), F(3, 10), None)], "Q", (F(3, 10), F(3, 10))),
    # ⊥ → Q is a tautology: it constrains nothing.
    ([("⊥ → Q", F(1), F(1), None)], "Q", (F(0), F(1))),
    # P(¬⊥ ∧ P) = P(P).
    ([("¬⊥ ∧ P", F(1, 5), F(2, 5), None)], "P", (F(1, 5), F(2, 5))),
    # Nested: P(P → ⊤) = 1 holds in every distribution, so P(P → ⊤) = 1 constrains nothing.
    ([("P → ⊤", F(1), F(1), None)], "P", (F(0), F(1))),
    # Conditionals. Given ⊤ the condition holds in every world, so P(Q | ⊤) = P(Q).
    ([("Q", F(4, 5), F(4, 5), "⊤")], "Q", (F(4, 5), F(4, 5))),
    # Given ⊥ the condition has probability 0 and the linear form of the conditional is vacuous
    # (see the module docstring of prob.nilsson), so P(Q | ⊥) = 1 is not inconsistent and says nothing.
    ([("Q", F(1), F(1), "⊥")], "Q", (F(0), F(1))),
    # Fréchet: P(A ∧ B) is in [max(0, a + b - 1), min(a, b)] = [0, 1/4] for a = 1/4, b = 1/2, and
    # P(A ∨ B) = a + b - P(A ∧ B) is in [3/4 - 1/4, 3/4 - 0] = [1/2, 3/4]. The constants change nothing.
    ([("P ∧ ⊤", F(1, 4), F(1, 4), None), ("Q ∨ ⊥", F(1, 2), F(1, 2), None)], "P ∧ Q", (F(0), F(1, 4))),
    ([("P ∧ ⊤", F(1, 4), F(1, 4), None), ("Q ∨ ⊥", F(1, 2), F(1, 2), None)], "P ∨ Q", (F(1, 2), F(3, 4))),
    # P(⊤) in [1/2, 1] is satisfiable (it is 1): it constrains nothing.
    ([("⊤", F(1, 2), F(1), None)], "P", (F(0), F(1))),
]


@pytest.mark.parametrize("strategy", STRATEGIES)
@pytest.mark.parametrize("constraints,conclusion,expected", CONSTRAINED)
def test_constraints_that_mention_a_constant_read_it_as_its_value(constraints, conclusion, expected, strategy):
    assert bounds(constraints, conclusion, strategy) == expected


# A constraint that no distribution satisfies, because the constant has its value in every world.
IMPOSSIBLE = [
    ("⊥", F(1), F(1)),             # P(⊥) = 0 always
    ("⊤", F(0), F(0)),             # P(⊤) = 1 always
    ("⊤", F(0), F(1, 2)),
    ("¬⊤", F(1, 10), F(1)),        # P(¬⊤) = 0
    ("P ∧ ⊥", F(1, 2), F(1)),      # P(P ∧ ⊥) = 0
    ("P ∨ ⊤", F(0), F(9, 10)),     # P(P ∨ ⊤) = 1
]


@pytest.mark.parametrize("strategy", STRATEGIES)
@pytest.mark.parametrize("text,lower,upper", IMPOSSIBLE)
def test_an_impossible_constraint_is_inconsistent_like_any_other(text, lower, upper, strategy):
    with pytest.raises(ValueError, match="probabilistically inconsistent"):
        entailment_bounds([ProbConstraint(f(text), lower, upper)], f("P"), strategy=strategy)


@pytest.mark.parametrize("strategy", STRATEGIES)
def test_the_four_spellings_of_a_constant_are_one_constant(strategy):
    for true in TRUE_NODES:
        result = entailment_bounds([], true, strategy=strategy)
        assert (result.lower, result.upper) == (1, 1)
    for false in FALSE_NODES:
        result = entailment_bounds([], false, strategy=strategy)
        assert (result.lower, result.upper) == (0, 0)
        with pytest.raises(ValueError, match="probabilistically inconsistent"):
            entailment_bounds([ProbConstraint.exact(false, F(1))], RAIN, strategy=strategy)


@pytest.mark.parametrize("strategy", STRATEGIES)
def test_a_predicate_spelled_like_a_constant_but_applied_is_an_ordinary_atom(strategy):
    applied = Atom("⊤", (Constant("alpha"),))          # ⊤(alpha): not the constant
    result = entailment_bounds([], applied, strategy=strategy)
    assert (result.lower, result.upper, result.n_worlds) == (0, 1, 2)
    pinned = entailment_bounds([ProbConstraint.exact(applied, F(1, 3))], applied, strategy=strategy)
    assert (pinned.lower, pinned.upper) == (F(1, 3), F(1, 3))


def _fold(node):
    """``node`` with every truth constant folded away: a Python bool when the whole formula is one,
    else a node over letters only. An independent oracle for the routes (it never looks at a world)."""
    from unicode_fol_kit.fol.nodes import Iff, Xor
    if isinstance(node, Atom):
        return truth_value(node) if truth_value(node) is not None else node
    if isinstance(node, Not):
        inner = _fold(node.formula)
        return (not inner) if isinstance(inner, bool) else Not(inner)
    a, b = _fold(node.left), _fold(node.right)
    if isinstance(node, Implies):
        return _fold(Or(Not(_wrap(a)), _wrap(b)))
    if isinstance(a, bool) and isinstance(b, bool):
        return {And: a and b, Or: a or b, Iff: a == b, Xor: a != b}[type(node)]
    if isinstance(a, bool) or isinstance(b, bool):
        constant, other = (a, b) if isinstance(a, bool) else (b, a)
        if isinstance(node, And):
            return other if constant else False
        if isinstance(node, Or):
            return True if constant else other
        if isinstance(node, Iff):
            return other if constant else Not(other)
        return Not(other) if constant else other                           # Xor
    return type(node)(a, b)


def _wrap(folded):
    return (TOP if folded else BOT) if isinstance(folded, bool) else folded


def test_the_routes_agree_with_an_oracle_that_folds_the_constants_away():
    """Metamorphic, seeded: random formulas over two letters and both constants, constraints taken
    from one real distribution (so they are satisfiable). Folding the constants out of the formulas
    first, and then asking the routes, must give the bounds the routes give for the formulas as written.
    A constraint that folds to a constant is no constraint (its value is the one the distribution
    gives it, 0 or 1); a condition that folds to ⊥ makes the conditional vacuous."""
    import random
    from unicode_fol_kit.fol.nodes import Iff, Xor

    rng = random.Random(20241)
    letters = [Atom("P", ()), Atom("Q", ())]

    def random_formula(depth):
        if depth == 0 or rng.random() < 0.25:
            return rng.choice(letters + [TOP, BOT, Atom("⊤", ()), Atom("⊥", ())])
        if rng.random() < 0.2:
            return Not(random_formula(depth - 1))
        return rng.choice([And, Or, Implies, Iff, Xor])(random_formula(depth - 1), random_formula(depth - 1))

    # one distribution over the four worlds (P, Q)
    worlds = [(p, q) for p in (False, True) for q in (False, True)]
    weights = [rng.randint(0, 5) for _ in worlds]
    weights[0] += 1                                             # not all zero
    mass = {w: F(weight, sum(weights)) for w, weight in zip(worlds, weights)}

    def holds(node, world):
        folded = _fold(node)
        if isinstance(folded, bool):
            return folded
        return _evaluate(folded, dict(zip("PQ", world)))

    def _evaluate(node, valuation):
        if isinstance(node, Atom):
            return valuation[node.predicate]
        if isinstance(node, Not):
            return not _evaluate(node.formula, valuation)
        left, right = _evaluate(node.left, valuation), _evaluate(node.right, valuation)
        return {And: left and right, Or: left or right, Iff: left == right, Xor: left != right,
                Implies: (not left) or right}[type(node)]

    def prob(node):
        return sum(mass[w] for w in worlds if holds(node, w))

    checked = 0
    for case in range(120):
        constraints, folded_constraints = [], []
        for _ in range(rng.randint(0, 3)):
            formula = random_formula(3)
            value = prob(formula)
            constraints.append(ProbConstraint.exact(formula, value))
            folded = _fold(formula)
            if not isinstance(folded, bool):                    # a constant constraint says nothing new
                folded_constraints.append(ProbConstraint.exact(folded, value))
        conclusion = random_formula(3)
        folded_conclusion = _fold(conclusion)
        for strategy in STRATEGIES if case % 4 == 0 else ["direct"]:
            got = entailment_bounds(constraints, conclusion, strategy=strategy)
            if isinstance(folded_conclusion, bool):
                assert (got.lower, got.upper) == (int(folded_conclusion),) * 2
            else:
                expected = entailment_bounds(folded_constraints, folded_conclusion, strategy=strategy)
                assert (got.lower, got.upper) == (expected.lower, expected.upper), (
                    [c._describe() for c in constraints], conclusion.to_unicode_str())
            # the distribution that made the constraints satisfiable is one of the candidates
            assert got.lower <= prob(conclusion) <= got.upper
            checked += 1
    assert checked >= 120


def test_the_two_strategies_agree_exactly_on_constant_formulas():
    cases = [c for c in CONSTRAINED] + [([], text, None) for text, _ in UNCONSTRAINED]
    for constraints, conclusion, _ in cases:
        assert bounds(constraints, conclusion, "direct") == bounds(constraints, conclusion, "column_generation")


def test_pinned_premises_with_a_constant_agree_with_classical_entailment():
    """The corner of the polytope: every premise pinned to 1 and the conclusion entailed gives (1, 1).
    ``⊤ → Q ⊨ Q`` is classically valid (modus ponens with the constant), and ``P ⊨ P ∧ ⊤`` too."""
    for premise, conclusion in (("⊤ → Q", "Q"), ("P", "P ∧ ⊤")):
        assert api.prove(f(conclusion), [f(premise)], backends=["z3"]).status == "proved"
        for strategy in STRATEGIES:
            assert bounds([(premise, F(1), F(1), None)], conclusion, strategy) == (F(1), F(1))
    # ``⊥ ⊨ Q`` is classically valid too (ex falso), but ⊥ pinned to probability 1 is no
    # corner of the polytope: it is the inconsistent set.
    assert api.prove(f("Q"), [f("⊥")], backends=["z3"]).status == "proved"
    for strategy in STRATEGIES:
        with pytest.raises(ValueError, match="probabilistically inconsistent"):
            bounds([("⊥", F(1), F(1), None)], "Q", strategy)


# ===========================================================================
# query (distribution semantics)
# ===========================================================================

#: One probabilistic fact: Rain with probability 3/10. A truth constant holds (or fails) in
#: every total choice, so each goal below is the sum over the two total choices
#: ({Rain}: 3/10, {}: 7/10) of the weights of the choices in which it holds.
RAIN_PROGRAM = ProbProgram([ProbFact(RAIN, F(3, 10))], [])

GOALS = [
    ("⊤", F(1)),                 # both choices
    ("⊥", F(0)),                 # none
    ("¬⊤", F(0)),
    ("¬⊥", F(1)),
    ("Rain ∨ ⊤", F(1)),
    ("Rain ∧ ⊤", F(3, 10)),      # = Rain: the choice {Rain}
    ("Rain ∨ ⊥", F(3, 10)),
    ("Rain ∧ ⊥", F(0)),
    ("¬(Rain ∧ ⊤)", F(7, 10)),   # the choice {}
    ("⊤ ∧ ¬Rain", F(7, 10)),
    ("¬(⊥ ∨ ¬Rain)", F(3, 10)),  # = Rain
    ("(Rain ∧ ⊥) ∨ ¬⊥", F(1)),
]


@pytest.mark.parametrize("prune", [True, False])
@pytest.mark.parametrize("method", ["enumerate", "compile"])
@pytest.mark.parametrize("goal,expected", GOALS)
def test_a_goal_with_a_constant_holds_or_fails_in_every_total_choice(goal, expected, method, prune):
    assert query(RAIN_PROGRAM, f(goal), method=method, prune=prune) == expected


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_goals_agree_with_an_oracle_that_folds_the_constants_away(method):
    """Metamorphic, seeded: random ∧ ∨ ¬ goals over the facts and a derived atom of one program
    and both constants. The probability of the goal as written is the probability of the goal with
    the constants folded out (and 1 or 0 when nothing but a constant is left)."""
    import random

    rng = random.Random(8812)
    program = ProbProgram(
        [ProbFact(Atom("Rain", ()), F(3, 10)), ProbFact(Atom("Cold", ()), F(1, 2))],
        [Implies(And(Atom("Rain", ()), Atom("Cold", ())), Atom("Snow", ()))])
    letters = [Atom("Rain", ()), Atom("Cold", ()), Atom("Snow", ())]

    def random_goal(depth):
        if depth == 0 or rng.random() < 0.25:
            return rng.choice(letters + [TOP, BOT, Atom("⊤", ()), Atom("⊥", ())])
        if rng.random() < 0.3:
            return Not(random_goal(depth - 1))
        return rng.choice([And, Or])(random_goal(depth - 1), random_goal(depth - 1))

    def fold(node):
        if isinstance(node, Atom):
            return truth_value(node) if truth_value(node) is not None else node
        if isinstance(node, Not):
            inner = fold(node.formula)
            return (not inner) if isinstance(inner, bool) else Not(inner)
        a, b = fold(node.left), fold(node.right)
        if isinstance(a, bool) or isinstance(b, bool):
            constant, other = (a, b) if isinstance(a, bool) else (b, a)
            if isinstance(other, bool):
                return (a and b) if isinstance(node, And) else (a or b)
            if isinstance(node, And):
                return other if constant else False
            return True if constant else other
        return type(node)(a, b)

    for _ in range(150):
        goal = random_goal(4)
        folded = fold(goal)
        expected = F(int(folded)) if isinstance(folded, bool) else query(program, folded, method=method)
        assert query(program, goal, method=method) == expected, goal.to_unicode_str()


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_a_program_without_facts_still_has_the_constant_true(method):
    assert query(ProbProgram([], []), TOP, method=method) == 1
    assert query(ProbProgram([], []), Not(TOP), method=method) == 0


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_the_four_spellings_of_a_constant_are_one_constant_in_a_goal(method):
    for true in TRUE_NODES:
        assert query(RAIN_PROGRAM, And(RAIN, true), method=method) == F(3, 10)
        assert query(RAIN_PROGRAM, Not(true), method=method) == 0
    for false in FALSE_NODES:
        assert query(RAIN_PROGRAM, Or(RAIN, false), method=method) == F(3, 10)
        assert query(RAIN_PROGRAM, Not(false), method=method) == 1


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_a_constant_under_a_quantifier_over_the_programs_constants(method):
    program = ProbProgram([ProbFact(f("Bird(tweety)"), F(1, 2))], [])
    assert query(program, f("∀x (Bird(x) ∨ ⊤)"), method=method) == 1     # tweety is the only constant
    assert query(program, f("∃x (Bird(x) ∧ ⊥)"), method=method) == 0
    assert query(program, f("∃x (Bird(x) ∧ ⊤)"), method=method) == F(1, 2)


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_a_constant_in_a_rule_body_is_the_value_it_is(method):
    bird = [ProbFact(f("Bird(tweety)"), F(1, 2))]
    # ⊤ in a body always holds: the rule is "Bird(x) → Flies(x)", so Flies(tweety) iff Bird(tweety).
    always = ProbProgram(bird, [f("∀x (⊤ ∧ Bird(x) → Flies(x))")])
    assert query(always, f("Flies(tweety)"), method=method) == F(1, 2)
    # ⊥ in a body never holds: the rule never fires.
    never = ProbProgram(bird, [f("∀x (⊥ ∧ Bird(x) → Flies(x))")])
    assert query(never, f("Flies(tweety)"), method=method) == 0
    # A body that is only ⊤: the clause is a fact, Wet holds in every total choice.
    fact = ProbProgram([ProbFact(RAIN, F(3, 10))], [Implies(TOP, WET)])
    assert query(fact, WET, method=method) == 1
    # A body that is only ⊥: nothing is derived.
    nothing = ProbProgram([ProbFact(RAIN, F(3, 10))], [Implies(BOT, WET)])
    assert query(nothing, WET, method=method) == 0


@pytest.mark.parametrize("constant", [TOP, BOT, Atom("⊤", ()), Atom("⊥", ())], ids=repr)
def test_a_constant_is_not_a_probabilistic_fact_nor_a_head_nor_a_hard_fact(constant):
    with pytest.raises(ValueError, match="truth constant"):
        ProbFact(constant, F(1, 2))
    with pytest.raises(ValueError, match="truth constant"):
        ProbProgram([], [Implies(RAIN, constant)])
    with pytest.raises(ValueError, match="truth constant"):
        ProbProgram([], [], [constant])
    with pytest.raises(ValueError, match="truth constant"):
        ProbProgram([], [constant])


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_a_predicate_spelled_like_a_constant_but_applied_is_an_ordinary_atom(method):
    applied = Atom("⊤", (Constant("alpha"),))
    program = ProbProgram([ProbFact(applied, F(1, 2))], [])         # allowed: a user predicate
    assert query(program, applied, method=method) == F(1, 2)
    assert query(RAIN_PROGRAM, applied, method=method) == 0           # not derived: closed world


# ===========================================================================
# The MCP tools, with each text spelling of the constants
# ===========================================================================

mcp = pytest.importorskip("unicode_fol_kit.mcp.server", reason="optional [mcp] extra not installed")

@pytest.mark.parametrize("text", TRUE_TEXTS + FALSE_TEXTS)
def test_every_text_spelling_reads_to_atoms_that_are_all_constants(text):
    atoms = [n for n in api.parse_any(text).formula.walk() if isinstance(n, Atom)]
    assert atoms and all(truth_value(atom) is not None for atom in atoms)


@pytest.mark.parametrize("strategy", STRATEGIES)
@pytest.mark.parametrize("text", TRUE_TEXTS)
def test_probability_bounds_of_the_constant_true(text, strategy):
    result = mcp.probability_bounds(text, [], strategy=strategy)
    assert (result["lower"], result["upper"]) == ("1", "1")
    refused = mcp.probability_bounds("P", [{"formula": text, "probability": "0"}], strategy=strategy)
    assert refused["error"]["type"] == "ValueError"
    assert "probabilistically inconsistent" in refused["error"]["message"]


@pytest.mark.parametrize("strategy", STRATEGIES)
@pytest.mark.parametrize("text", FALSE_TEXTS)
def test_probability_bounds_of_the_constant_false(text, strategy):
    result = mcp.probability_bounds(text, [], strategy=strategy)
    assert (result["lower"], result["upper"]) == ("0", "0")
    refused = mcp.probability_bounds("P", [{"formula": text, "probability": "1"}], strategy=strategy)
    assert refused["error"]["type"] == "ValueError"
    assert "probabilistically inconsistent" in refused["error"]["message"]


def test_probability_bounds_through_the_tool_with_a_conjunct_that_is_a_constant():
    result = mcp.probability_bounds("P", [{"formula": "P ∧ ⊤", "probability": "7/10"}])
    assert (result["lower"], result["upper"]) == ("7/10", "7/10")
    result = mcp.probability_bounds("Q", [{"formula": "⊤ → Q", "probability": "1"}])
    assert (result["lower"], result["upper"]) == ("1", "1")


@pytest.mark.parametrize("text", TRUE_TEXTS)
def test_probability_query_of_the_constant_true(text):
    facts = [{"atom": "Rain", "prob": "3/10"}]
    assert mcp.probability_query(text, facts)["probability"] == "1"
    assert mcp.probability_query("Rain ∧ ⊤", facts)["probability"] == "3/10"
    assert mcp.probability_query("¬⊤", facts)["probability"] == "0"


@pytest.mark.parametrize("text", FALSE_TEXTS)
def test_probability_query_of_the_constant_false(text):
    facts = [{"atom": "Rain", "prob": "3/10"}]
    assert mcp.probability_query(text, facts)["probability"] == "0"
    assert mcp.probability_query("¬⊥", facts)["probability"] == "1"


@pytest.mark.parametrize("text", FALSE_TEXTS[:3] + TRUE_TEXTS[:3])
def test_probability_query_refuses_a_constant_as_a_probabilistic_fact(text):
    # (the first three spellings of each are single atoms; the LaTeX one is a conjunction)
    refused = mcp.probability_query("Rain", [{"atom": text, "prob": "1/2"}])
    assert refused["error"]["type"] == "ValueError" and "truth constant" in refused["error"]["message"]
