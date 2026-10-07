"""Tests for unicode_logic_kit.prob._bdd and prob.distribution.query(method="compile").

Two independent anchors, per the module's own promise (see distribution.py's
"A second evaluation route" docstring section):

* prob._bdd — an isolated ROBDD engine, tested in complete isolation from
  `query`: the reduced/ordered node invariant, AND/OR/NOT correctness (hand
  truth tables), and weighted model counting on hand-computed literal
  formulas, all BEFORE the engine is ever wired into `distribution.query`.
* distribution.query(method="compile") — tested DIFFERENTIALLY against
  method="enumerate" (which stays in the code as ground truth): every
  existing tests/test_prob.py program shape (alarm, rain/wet chain,
  independent coins, negation, quantified goals), hand-checked textbook
  values (the guide's Rain/Sprinkler "Wet" diamond, 11/25; an independent
  chain's closed form p1*p2*...*pN), a seeded random battery of
  chain/tree/diamond-shaped programs, and a scaling regression that exceeds
  `max_choice_facts` -- where "enumerate" must still refuse and "compile"
  must succeed and match an independently hand-derived closed form.

Everywhere two routes are compared, comparison is exact Fraction equality
(`==`), never a float tolerance -- both routes claim to compute the exact
same number by two different algorithms, so anything other than bit-for-bit
equality is a bug in one of them.
"""

import random
import time
from fractions import Fraction as F

import pytest

from unicode_logic_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Constant,
)
from unicode_logic_kit.prob.distribution import ProbFact, ProbProgram, query
from unicode_logic_kit.prob._bdd import BDDManager, weighted_model_count, FALSE, TRUE


# ===========================================================================
# prob._bdd — isolated ROBDD engine unit tests
# ===========================================================================

def _check_robdd_invariants(manager: BDDManager, root: int, visited=None) -> None:
    """Walk the DAG from `root`, asserting REDUCED (no low==high node) and
    ORDERED (every child's variable index is strictly greater than its
    parent's) -- the two defining invariants of a Reduced Ordered BDD."""
    if visited is None:
        visited = set()
    if manager.is_terminal(root) or root in visited:
        return
    visited.add(root)
    var, low, high = manager.node(root)
    assert low != high, "reduced invariant violated: a node with low == high must never be allocated"
    for child in (low, high):
        if not manager.is_terminal(child):
            child_var = manager.node(child)[0]
            assert child_var > var, "ordered invariant violated: child variable must come strictly after parent"
    _check_robdd_invariants(manager, low, visited)
    _check_robdd_invariants(manager, high, visited)


class TestBDDManagerInvariants:
    def test_reduction_rule_collapses_redundant_node(self):
        # x1 | !x1 is a tautology: both Shannon cofactors (on x1) are TRUE,
        # so the canonical constructor must return the TRUE terminal
        # directly rather than allocating a "node" that ignores x1.
        m = BDDManager(2)
        x1 = m.variable(1)
        tautology = m.OR(x1, m.NOT(x1))
        assert tautology == TRUE

        # x0 & (x1 | !x1) == x0 & TRUE == x0 -- reduction propagates.
        x0 = m.variable(0)
        assert m.AND(x0, tautology) == x0

    def test_unique_table_canonicalizes_regardless_of_build_order(self):
        # The same Boolean function, built two different ways (and with
        # operands in the opposite order, since AND/OR are commutative),
        # must land on the exact same node id -- that identity is what lets
        # distribution.py detect a least-fixpoint "no change" with `!=`.
        m = BDDManager(3)
        x0, x1, x2 = m.variable(0), m.variable(1), m.variable(2)
        a = m.AND(x0, m.AND(x1, x2))
        b = m.AND(m.AND(x2, x1), x0)
        assert a == b

    def test_robdd_invariants_hold_on_a_nontrivial_formula(self):
        m = BDDManager(4)
        x0, x1, x2, x3 = (m.variable(i) for i in range(4))
        # (x0 & x1) | (!x2 & x3) | (x0 & x3)
        f = m.OR(m.OR(m.AND(x0, x1), m.AND(m.NOT(x2), x3)), m.AND(x0, x3))
        _check_robdd_invariants(m, f)

    def test_max_nodes_brake_raises(self):
        # max_nodes=3 leaves room for the 2 terminals plus exactly ONE
        # internal node; allocating a second variable's node must refuse
        # loudly, the same style of brake `max_choice_facts` already is.
        with pytest.raises(ValueError, match="max_nodes"):
            BDDManager(2, max_nodes=3)

    def test_num_vars_zero_is_a_degenerate_but_valid_manager(self):
        # No variables at all -- only the two terminals exist. This is the
        # `method="compile"` analog of a query with zero relevant facts.
        m = BDDManager(0)
        assert weighted_model_count(m, TRUE, []) == F(1)
        assert weighted_model_count(m, FALSE, []) == F(0)


class TestBDDManagerCombinators:
    """Hand-checked truth tables for AND/OR/NOT over 2 variables."""

    @pytest.fixture
    def m2(self):
        m = BDDManager(2)
        return m, m.variable(0), m.variable(1)

    @staticmethod
    def _holds_at(m: BDDManager, f: int, x0: int, x1: int, a: bool, b: bool) -> bool:
        """Whether `f` is true at the point (x0=a, x1=b), evaluated with ONLY
        AND/OR/NOT (no dedicated "restrict"/"evaluate" op exists in _bdd.py,
        by design -- distribution.py never needs point-evaluation, only
        composition + WMC). `minterm` is the single product-of-literals term
        that is true at exactly that one point; `f` holds there iff ANDing
        `f` with `minterm` does not eliminate it (AND(f, minterm) == minterm
        means every model of `minterm` -- i.e. that one point -- is also a
        model of `f`; since `minterm` pins EVERY variable, this is exactly
        "f(point) = True"). Note this is NOT the same as testing `AND(f,
        minterm) == TRUE`, which would ask whether `f` holds EVERYWHERE.
        """
        lit_a = x0 if a else m.NOT(x0)
        lit_b = x1 if b else m.NOT(x1)
        minterm = m.AND(lit_a, lit_b)
        return m.AND(f, minterm) == minterm

    def test_and_truth_table(self, m2):
        m, x0, x1 = m2
        f = m.AND(x0, x1)
        for a in (False, True):
            for b in (False, True):
                assert self._holds_at(m, f, x0, x1, a, b) == (a and b), (a, b)

    def test_or_truth_table(self, m2):
        m, x0, x1 = m2
        f = m.OR(x0, x1)
        for a in (False, True):
            for b in (False, True):
                assert self._holds_at(m, f, x0, x1, a, b) == (a or b), (a, b)

    def test_not_truth_table(self, m2):
        m, x0, _x1 = m2
        f = m.NOT(x0)
        assert m.AND(f, x0) == FALSE
        assert m.AND(f, m.NOT(x0)) == m.NOT(x0)

    def test_de_morgan_identity_holds_as_canonical_equality(self, m2):
        m, x0, x1 = m2
        lhs = m.NOT(m.AND(x0, x1))
        rhs = m.OR(m.NOT(x0), m.NOT(x1))
        assert lhs == rhs

    def test_not_is_involutive(self, m2):
        m, x0, x1 = m2
        f = m.OR(x0, m.NOT(x1))
        assert m.NOT(m.NOT(f)) == f


class TestWeightedModelCountHandComputed:
    def test_single_literal(self):
        m = BDDManager(1)
        x0 = m.variable(0)
        assert weighted_model_count(m, x0, [F(3, 10)]) == F(3, 10)
        assert weighted_model_count(m, m.NOT(x0), [F(3, 10)]) == F(7, 10)

    def test_conjunction(self):
        # P(x0 & x1) = P(x0) * P(x1) = 3/10 * 1/5 = 3/50 (independence).
        m = BDDManager(2)
        x0, x1 = m.variable(0), m.variable(1)
        f = m.AND(x0, x1)
        assert weighted_model_count(m, f, [F(3, 10), F(1, 5)]) == F(3, 50)

    def test_disjunction_matches_inclusion_exclusion(self):
        # P(x0 | x1) = 1 - (1-3/10)(1-1/5) = 1 - 7/10*4/5 = 1 - 28/50 = 11/25.
        m = BDDManager(2)
        x0, x1 = m.variable(0), m.variable(1)
        f = m.OR(x0, x1)
        assert weighted_model_count(m, f, [F(3, 10), F(1, 5)]) == F(11, 25)

    def test_xor_shaped_formula(self):
        # (x0 & !x1) | (!x0 & x1), p=[1/2,1/2]: P = 1/2*1/2 + 1/2*1/2 = 1/2.
        m = BDDManager(2)
        x0, x1 = m.variable(0), m.variable(1)
        f = m.OR(m.AND(x0, m.NOT(x1)), m.AND(m.NOT(x0), x1))
        assert weighted_model_count(m, f, [F(1, 2), F(1, 2)]) == F(1, 2)

    def test_shared_subformula_counted_once(self):
        # (x0 & x1) | (x0 & !x2): the two branches SHARE the x0 subtree in
        # the ROBDD; WMC must still equal the direct hand computation
        # P = P(x0) * (1 - (1-P(x1))(1-P(!x2))) via the same OR-of-branches
        # rule as the disjunction test above, restricted to the x0=True world.
        m = BDDManager(3)
        x0, x1, x2 = (m.variable(i) for i in range(3))
        f = m.OR(m.AND(x0, x1), m.AND(x0, m.NOT(x2)))
        p0, p1, p2 = F(2, 5), F(1, 3), F(3, 4)
        expected = p0 * (1 - (1 - p1) * (1 - (1 - p2)))
        assert weighted_model_count(m, f, [p0, p1, p2]) == expected


# ===========================================================================
# distribution.query(method="compile") vs method="enumerate" — differential
# ===========================================================================

# ---------------------------------------------------------------------------
# (a) The same program shapes tests/test_prob.py already hand-checks.
# ---------------------------------------------------------------------------

_BURGLARY = Atom("burglary", ())
_EARTHQUAKE = Atom("earthquake", ())
_ALARM = Atom("alarm", ())


def _alarm_program():
    facts = [ProbFact(_BURGLARY, F(1, 10)), ProbFact(_EARTHQUAKE, F(1, 5))]
    rules = [Implies(_BURGLARY, _ALARM), Implies(_EARTHQUAKE, _ALARM)]
    return ProbProgram(facts=facts, rules=rules)


def _rain_program_two_people():
    x = Variable("x")
    rain = Atom("Rain", ())
    rule = Quantifier("∀", x, Implies(And(rain, Atom("Outside", (x,))), Atom("Wet", (x,))))
    facts = [ProbFact(rain, F(3, 10))]
    hard_facts = [
        Atom("Outside", (Constant("mary"),)),
        Atom("Person", (Constant("john"),)),
    ]
    return ProbProgram(facts=facts, rules=[rule], hard_facts=hard_facts)


_HEADS1, _HEADS2 = Atom("Heads1", ()), Atom("Heads2", ())


def _coins_program():
    return ProbProgram(facts=[ProbFact(_HEADS1, F(1, 2)), ProbFact(_HEADS2, F(1, 2))], rules=[])


class TestCompileMatchesEnumerateOnExistingShapes:
    def test_alarm_classic(self):
        # P(alarm) = 1 - (9/10)(4/5) = 7/25 (hand-derived, same as test_prob.py).
        prog = _alarm_program()
        assert query(prog, _ALARM, method="compile") == query(prog, _ALARM, method="enumerate") == F(7, 25)

    def test_alarm_negation_and_conjunction(self):
        prog = _alarm_program()
        assert query(prog, Not(_ALARM), method="compile") == F(18, 25)
        assert query(prog, And(_BURGLARY, Not(_EARTHQUAKE)), method="compile") == F(2, 25)

    def test_rain_wet_chain_with_hard_facts(self):
        x = Variable("x")
        rain = Atom("Rain", ())
        rule = Quantifier("∀", x, Implies(And(rain, Atom("Outside", (x,))), Atom("Wet", (x,))))
        prog = ProbProgram(facts=[ProbFact(rain, F(3, 10))], rules=[rule],
                            hard_facts=[Atom("Outside", (Constant("mary"),))])
        wet_mary = Atom("Wet", (Constant("mary"),))
        wet_john = Atom("Wet", (Constant("john"),))
        assert query(prog, wet_mary, method="compile") == F(3, 10)
        assert query(prog, wet_john, method="compile") == F(0)

    def test_independent_coins_conjunction_and_disjunction(self):
        prog = _coins_program()
        assert query(prog, And(_HEADS1, _HEADS2), method="compile") == F(1, 4)
        assert query(prog, Or(_HEADS1, _HEADS2), method="compile") == F(3, 4)
        assert query(prog, Not(_HEADS1), method="compile") == F(1, 2)

    def test_quantified_goals(self):
        prog = _rain_program_two_people()
        x = Variable("x")
        goal_all = Quantifier("∀", x, Atom("Wet", (x,)))
        goal_ex = Quantifier("∃", x, Atom("Wet", (x,)))
        assert query(prog, goal_all, method="compile") == F(0)
        assert query(prog, goal_ex, method="compile") == F(3, 10)

    def test_pruned_and_unpruned_agree_under_compile_too(self):
        prog = _alarm_program()
        pruned = query(prog, _ALARM, method="compile", prune=True)
        unpruned = query(prog, _ALARM, method="compile", prune=False)
        assert pruned == unpruned == F(7, 25)


# ---------------------------------------------------------------------------
# (b) Hand-checked textbook values, worked out on paper.
# ---------------------------------------------------------------------------

class TestHandCheckedTextbookValues:
    def test_wet_diamond_from_the_guide(self):
        # Rain -> Wet, Sprinkler -> Wet, independent causes:
        # P(Wet) = 1 - (1 - 3/10)(1 - 1/5) = 1 - 7/10*4/5 = 1 - 28/50 = 11/25.
        # (Same program the module docstring and docs/guide/probabilistic.md
        # both already hand-derive for method="enumerate".)
        rain, sprinkler, wet = Atom("Rain", ()), Atom("Sprinkler", ()), Atom("Wet", ())
        prog = ProbProgram(
            facts=[ProbFact(rain, F(3, 10)), ProbFact(sprinkler, F(1, 5))],
            rules=[Implies(rain, wet), Implies(sprinkler, wet)],
        )
        e = query(prog, wet, method="enumerate")
        c = query(prog, wet, method="compile")
        assert e == c == F(11, 25)

    def test_independent_and_chain_closed_form(self):
        # D0 <- F0; D_i <- D_{i-1} & F_i: Wet is derivable iff EVERY fact
        # fires, so P(D_{n-1}) = p0 * p1 * ... * p_{n-1} exactly (product
        # rule for independent events), worked out here with n=4 concrete
        # fractions: 1/2 * 2/3 * 3/4 * 4/5 = 24/120 = 1/5.
        probs = [F(1, 2), F(2, 3), F(3, 4), F(4, 5)]
        facts = [ProbFact(Atom(f"F{i}", ()), p) for i, p in enumerate(probs)]
        d = [Atom(f"D{i}", ()) for i in range(len(probs))]
        rules = [Implies(facts[0].atom, d[0])]
        for i in range(1, len(probs)):
            rules.append(Implies(And(d[i - 1], facts[i].atom), d[i]))
        prog = ProbProgram(facts=facts, rules=rules)
        e = query(prog, d[-1], method="enumerate")
        c = query(prog, d[-1], method="compile")
        assert e == c == F(1, 5)


# ---------------------------------------------------------------------------
# (c) Seeded random battery: chain / tree / diamond definite programs.
# ---------------------------------------------------------------------------

_RANDOM_FRACS = [F(0, 1), F(1, 1), F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4),
                  F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 10), F(3, 10), F(7, 10), F(9, 10)]


def _random_frac(rng: random.Random) -> F:
    return rng.choice(_RANDOM_FRACS)


def _random_chain_program(rng: random.Random, n: int):
    """D0 <- F0; D_i <- D_{i-1} & F_i -- a straight AND-chain (no sharing)."""
    facts = [ProbFact(Atom(f"F{i}", ()), _random_frac(rng)) for i in range(n)]
    d = [Atom(f"D{i}", ()) for i in range(n)]
    rules = [Implies(facts[0].atom, d[0])]
    for i in range(1, n):
        rules.append(Implies(And(d[i - 1], facts[i].atom), d[i]))
    return ProbProgram(facts=facts, rules=rules), d[-1]


def _random_tree_program(rng: random.Random, n: int):
    """A binary reduction tree over n leaves; each internal node is either an
    AND of its two children or an OR (via two rules sharing one head)."""
    facts = [ProbFact(Atom(f"L{i}", ()), _random_frac(rng)) for i in range(n)]
    level = [pf.atom for pf in facts]
    rules = []
    lvl = 0
    while len(level) > 1:
        next_level = []
        i, pair = 0, 0
        while i < len(level):
            if i + 1 < len(level):
                new_atom = Atom(f"T{lvl}_{pair}", ())
                if rng.random() < 0.5:
                    rules.append(Implies(And(level[i], level[i + 1]), new_atom))
                else:
                    rules.append(Implies(level[i], new_atom))
                    rules.append(Implies(level[i + 1], new_atom))
                next_level.append(new_atom)
                pair += 1
                i += 2
            else:
                next_level.append(level[i])  # odd one out passes through unchanged
                i += 1
        level = next_level
        lvl += 1
    return ProbProgram(facts=facts, rules=rules), level[0]


def _random_diamond_program(rng: random.Random, n: int):
    """One fact SHARED by two independent branches that reconverge on one
    head via two rules (D <- shared & branchA) | (D <- shared & branchB) --
    the textbook shared-sub-derivation shape BDD sharing is meant to exploit."""
    facts = [ProbFact(Atom(f"F{i}", ()), _random_frac(rng)) for i in range(n)]
    shared = facts[0].atom
    half = (n - 1) // 2
    branch_a = [shared] + [f.atom for f in facts[1:1 + half]]
    branch_b = [shared] + [f.atom for f in facts[1 + half:]]

    def conjunction(atoms):
        result = atoms[0]
        for a in atoms[1:]:
            result = And(result, a)
        return result

    d = Atom("Diamond", ())
    rules = [Implies(conjunction(branch_a), d), Implies(conjunction(branch_b), d)]
    return ProbProgram(facts=facts, rules=rules), d


def _random_goal_wrapper(rng: random.Random, base_goal):
    """Occasionally wrap the base goal in ¬ or ∧ with itself negated-and-back,
    exercising the goal language beyond a bare atom (the closest analog this
    API has to ProbLog-style "evidence": query() only takes one goal, not a
    separate evidence parameter, so composing the goal IS how a caller
    expresses more than "is this atom derivable")."""
    choice = rng.random()
    if choice < 0.34:
        return base_goal
    if choice < 0.67:
        return Not(Not(base_goal))  # double negation: same truth value
    return And(base_goal, Not(Not(base_goal)))  # tautologically same value, exercises And


@pytest.mark.parametrize("shape,gen", [
    ("chain", _random_chain_program),
    ("tree", _random_tree_program),
])
def test_compile_matches_enumerate_random_chain_and_tree(shape, gen):
    for n in range(1, 13):
        for seed in range(10):
            # random.Random hashes str/bytes seeds deterministically via its own
            # algorithm (unaffected by PYTHONHASHSEED, unlike builtin hash()), so
            # this exact battery of programs is stable and reproducible across runs.
            rng = random.Random(f"{shape}-{seed}-{n}")
            prog, goal = gen(rng, n)
            wrapped_goal = _random_goal_wrapper(rng, goal)
            e = query(prog, wrapped_goal, method="enumerate")
            c = query(prog, wrapped_goal, method="compile")
            assert e == c, f"{shape} n={n} seed={seed}: enumerate={e} compile={c}"


def test_compile_matches_enumerate_random_diamond():
    for n in range(3, 13):
        for seed in range(10):
            rng = random.Random(f"diamond-{seed}-{n}")
            prog, goal = _random_diamond_program(rng, n)
            wrapped_goal = _random_goal_wrapper(rng, goal)
            e = query(prog, wrapped_goal, method="enumerate")
            c = query(prog, wrapped_goal, method="compile")
            assert e == c, f"diamond n={n} seed={seed}: enumerate={e} compile={c}"


def test_compile_matches_enumerate_unpruned_random_sample():
    # Same random battery, but a handful of cases with prune=False, to make
    # sure the two routes still agree when the dependency-cone optimization
    # is switched off entirely (relevant == every fact in the program).
    for seed in range(5):
        rng = random.Random(1000 + seed)
        prog, goal = _random_diamond_program(rng, 9)
        e = query(prog, goal, method="enumerate", prune=False)
        c = query(prog, goal, method="compile", prune=False)
        assert e == c


# ---------------------------------------------------------------------------
# (d) Scaling regression: beyond what "enumerate" can answer at all.
# ---------------------------------------------------------------------------

class TestScalingRegression:
    def test_independent_chain_beyond_max_choice_facts(self):
        # 24 facts in a straight AND-chain: enumerate refuses outright
        # (2^24 choices, well past the default max_choice_facts=16); compile
        # must succeed and match the closed form p0*p1*...*p23, computed
        # here directly (NOT via any part of distribution.py) as the
        # independent oracle.
        rng = random.Random(2024)
        n = 24
        probs = [rng.choice([F(1, 2), F(2, 3), F(3, 5), F(7, 10), F(4, 5)]) for _ in range(n)]
        facts = [ProbFact(Atom(f"F{i}", ()), p) for i, p in enumerate(probs)]
        d = [Atom(f"D{i}", ()) for i in range(n)]
        rules = [Implies(facts[0].atom, d[0])]
        for i in range(1, n):
            rules.append(Implies(And(d[i - 1], facts[i].atom), d[i]))
        prog = ProbProgram(facts=facts, rules=rules)
        goal = d[-1]

        with pytest.raises(ValueError, match="max_choice_facts"):
            query(prog, goal, method="enumerate")

        closed_form = F(1)
        for p in probs:
            closed_form *= p
        assert query(prog, goal, method="compile") == closed_form

    def test_shared_diamond_beyond_max_choice_facts(self):
        # A diamond with 25 facts (1 shared + 12 per branch): enumerate
        # refuses; compile must succeed. Closed form, derived independently
        # by hand from the rule D <- shared & (branchA-conj | branchB-conj)
        # (an OR of two rules with the same head is exactly that
        # disjunction -- see the module docstring's grounding note):
        #   P(D) = P(shared) * (1 - (1 - a)(1 - b))
        # where a = product of branch-A-only probs, b = product of
        # branch-B-only probs (each branch's own facts are independent, and
        # the two branches, once `shared` is fixed true, are independent of
        # each other).
        rng = random.Random(4242)
        n = 25
        probs = [rng.choice([F(1, 2), F(2, 3), F(3, 5), F(7, 10), F(4, 5), F(9, 10)]) for _ in range(n)]
        facts = [ProbFact(Atom(f"F{i}", ()), p) for i, p in enumerate(probs)]
        shared = facts[0].atom
        half = (n - 1) // 2
        branch_a_facts = facts[1:1 + half]
        branch_b_facts = facts[1 + half:]

        def conjunction(atoms):
            result = atoms[0]
            for x in atoms[1:]:
                result = And(result, x)
            return result

        d = Atom("Diamond", ())
        rules = [
            Implies(conjunction([shared] + [f.atom for f in branch_a_facts]), d),
            Implies(conjunction([shared] + [f.atom for f in branch_b_facts]), d),
        ]
        prog = ProbProgram(facts=facts, rules=rules)

        with pytest.raises(ValueError, match="max_choice_facts"):
            query(prog, d, method="enumerate")

        a = F(1)
        for f in branch_a_facts:
            a *= f.prob
        b = F(1)
        for f in branch_b_facts:
            b *= f.prob
        closed_form = probs[0] * (1 - (1 - a) * (1 - b))
        assert query(prog, d, method="compile") == closed_form


# ---------------------------------------------------------------------------
# (e) method / max_bdd_nodes / max_choice_facts interaction, and refusal parity.
# ---------------------------------------------------------------------------

class TestMethodKeywordAndBrakes:
    def test_default_method_is_enumerate_and_unaffected(self):
        # Every existing call site (no `method=` kwarg at all) must keep
        # taking the enumerate path, byte-identically -- max_bdd_nodes must
        # not even be consulted.
        prog = _alarm_program()
        assert query(prog, _ALARM) == query(prog, _ALARM, method="enumerate") == F(7, 25)

    def test_unknown_method_rejected(self):
        prog = _coins_program()
        with pytest.raises(ValueError, match="method"):
            query(prog, _HEADS1, method="symbolic")  # not a real method name

    def test_max_choice_facts_does_not_apply_to_compile(self):
        # 17 independent fair coins: enumerate refuses at the default
        # max_choice_facts=16; compile has no such limit and must match the
        # value enumerate gives when max_choice_facts is raised explicitly.
        facts = [ProbFact(Atom(f"C{i}", ()), F(1, 2)) for i in range(17)]
        goal = facts[0].atom
        for pf in facts[1:]:
            goal = Or(goal, pf.atom)
        prog = ProbProgram(facts=facts, rules=[])
        with pytest.raises(ValueError, match="max_choice_facts"):
            query(prog, goal, method="enumerate")
        raised_cap = query(prog, goal, method="enumerate", max_choice_facts=17)
        compiled = query(prog, goal, method="compile")
        assert compiled == raised_cap == F(1) - F(1, 2) ** 17

    def test_max_bdd_nodes_brake_fires_on_compile(self):
        facts = [ProbFact(Atom(f"C{i}", ()), F(1, 2)) for i in range(17)]
        goal = facts[0].atom
        for pf in facts[1:]:
            goal = Or(goal, pf.atom)
        prog = ProbProgram(facts=facts, rules=[])
        with pytest.raises(ValueError, match="max_bdd_nodes|max_nodes"):
            query(prog, goal, method="compile", max_bdd_nodes=5)

    def test_construct_refusals_agree_between_routes(self):
        # A goal outside the goal language (Implies is not ∧/∨/¬/literal)
        # is refused, with the SAME error, under both methods.
        prog = _coins_program()
        with pytest.raises(ValueError) as exc_enum:
            query(prog, Implies(_HEADS1, _HEADS2), method="enumerate")
        with pytest.raises(ValueError) as exc_compile:
            query(prog, Implies(_HEADS1, _HEADS2), method="compile")
        assert str(exc_enum.value) == str(exc_compile.value)

    def test_empty_constant_domain_refusal_agrees_between_routes(self):
        prog = ProbProgram(facts=[ProbFact(Atom("P", ()), F(1, 2))], rules=[])
        x = Variable("x")
        goal = Quantifier("∀", x, Atom("Q", (x,)))
        with pytest.raises(ValueError, match="empty constant domain") as exc_enum:
            query(prog, goal, method="enumerate")
        with pytest.raises(ValueError, match="empty constant domain") as exc_compile:
            query(prog, goal, method="compile")
        assert str(exc_enum.value) == str(exc_compile.value)

    def test_zero_relevant_facts_under_compile(self):
        # Sprinkler is a hard fact -- zero probabilistic facts are relevant
        # to it, so the compiled BDD has zero variables (a degenerate but
        # valid BDDManager(0)); the answer is certain, P = 1.
        prog = ProbProgram(facts=[ProbFact(Atom("Rain", ()), F(3, 10))],
                            rules=[Implies(Atom("Rain", ()), Atom("Wet", ()))],
                            hard_facts=[Atom("Sprinkler", ())])
        assert query(prog, Atom("Sprinkler", ()), method="compile") == F(1)


# ---------------------------------------------------------------------------
# (f) Measured speed-up: a few programs where enumeration is slow.
# ---------------------------------------------------------------------------

class TestMeasuredSpeedup:
    """`compile` must be dramatically faster than `enumerate` once the
    number of relevant facts makes 2^k enumeration expensive, WITHOUT
    changing the answer -- the entire performance claim of this batch item.
    A generous (>= 20x) threshold keeps this from being timing-flaky while
    still failing loudly if the compiled route regresses to no-better-than-
    enumerate performance."""

    @pytest.mark.parametrize("label,gen,n", [
        ("chain(15)", _random_chain_program, 15),
        ("diamond(15)", _random_diamond_program, 15),
        ("tree(13)", _random_tree_program, 13),
    ])
    def test_speedup_on_slow_enumeration_programs(self, label, gen, n):
        rng = random.Random(f"speedup-{label}")
        prog, goal = gen(rng, n)

        t0 = time.perf_counter()
        enumerated = query(prog, goal, method="enumerate")
        t1 = time.perf_counter()
        compiled = query(prog, goal, method="compile")
        t2 = time.perf_counter()

        enumerate_time = t1 - t0
        compile_time = max(t2 - t1, 1e-6)  # guard against a zero-duration measurement
        speedup = enumerate_time / compile_time

        assert enumerated == compiled
        assert speedup >= 20, (
            f"{label}: expected method='compile' to be dramatically faster than "
            f"method='enumerate' (2^{n} = {2 ** n} choices); got enumerate="
            f"{enumerate_time:.4f}s compile={compile_time:.6f}s (speedup={speedup:.1f}x)"
        )
