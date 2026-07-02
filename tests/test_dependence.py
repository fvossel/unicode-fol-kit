"""Tests for team semantics (unicode_fol_kit.semantics.team).

Dependence logic / IF logic in Väänänen's strict team semantics (Dependence
Logic, 2007). Every claim is hand-checked; the flatness suite additionally
cross-checks the team evaluator against the independent classical Tarski
evaluator on ~100 seeded random dependence-free formulas, and the downward-
closure suite pins Väänänen's Prop. 3.10 on seeded random formulas WITH
dependence atoms.
"""

import itertools
import random

import pytest

from unicode_fol_kit import (
    MSFLParser, Structure, satisfies, models,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Function,
    Dependence, SlashedExists,
)
from unicode_fol_kit.semantics.team import (
    team_satisfies, team_models, MAX_TEAM_SEARCH,
)

DEP = MSFLParser(dependence=True)
p = DEP.parse
FOL = MSFLParser()

DOM1 = Structure(domain=[0])
DOM2 = Structure(domain=[0, 1])
DOM3 = Structure(domain=[0, 1, 2])


def _v(name):
    return Variable(name)


def _dep(*names):
    """Dependence atom over variables, last one dependent."""
    return Dependence(tuple(Variable(n) for n in names))


# ---------------------------------------------------------------------------
# Empty-team property: the empty team satisfies EVERY formula of the fragment.
# ---------------------------------------------------------------------------

class TestEmptyTeam:
    # A structure where P is empty, so P(x) is false under every assignment.
    S = Structure(domain=[0, 1], predicates={("P", 1): set()})

    @pytest.mark.parametrize("text", [
        "P(x)",             # atom (false under every single assignment!)
        "¬P(x)",            # negated atom
        "x ≠ x",            # a literal false under EVERY assignment
        "P(x) ∧ ¬P(x)",     # contradiction-shaped conjunction
        "P(x) ∨ P(y)",      # split disjunction (∅ = ∅ ∪ ∅)
        "∀x P(x)",          # duplication of ∅ is ∅
        "∃x P(x)",          # F = ∅ supplements ∅ to ∅
        "=(x)",             # constancy atom, vacuously
        "=(x, y)",          # dependence atom, vacuously
        "∃y/{x} (y = x)",   # slashed existential with F = ∅
        "∀x ∃y (=(y) ∧ y = x)",
    ])
    def test_empty_team_satisfies_everything(self, text):
        assert team_satisfies(self.S, [], p(text)) is True

    def test_empty_team_is_not_sentence_evaluation(self):
        # team_models starts from {∅} (singleton empty assignment), NOT the
        # empty team: ∃x (x ≠ x) is satisfied by ∅ but false as a sentence.
        f = p("∃x (x ≠ x)")
        assert team_satisfies(DOM2, [], f) is True
        assert team_models(DOM2, f) is False


# ---------------------------------------------------------------------------
# Literals are flat: every assignment of the team must satisfy them.
# ---------------------------------------------------------------------------

class TestLiterals:
    S = Structure(domain=[0, 1], predicates={("P", 1): {(0,)}})

    def test_atom_requires_all_assignments(self):
        f = p("P(x)")
        assert team_satisfies(self.S, [{"x": 0}], f) is True
        assert team_satisfies(self.S, [{"x": 1}], f) is False
        # Mixed team: x=1 falsifies P(x) → the whole team fails.
        assert team_satisfies(self.S, [{"x": 0}, {"x": 1}], f) is False

    def test_negated_atom_requires_all_assignments(self):
        f = p("¬P(x)")
        assert team_satisfies(self.S, [{"x": 1}], f) is True
        assert team_satisfies(self.S, [{"x": 0}, {"x": 1}], f) is False

    def test_neither_literal_nor_negation_may_hold(self):
        # On the mixed team NEITHER P(x) nor ¬P(x) holds — teams are not
        # two-valued. But the split disjunction P(x) ∨ ¬P(x) always holds
        # (split the team by P-membership).
        team = [{"x": 0}, {"x": 1}]
        assert team_satisfies(self.S, team, p("P(x)")) is False
        assert team_satisfies(self.S, team, p("¬P(x)")) is False
        assert team_satisfies(self.S, team, p("P(x) ∨ ¬P(x)")) is True

    def test_equality_and_disequality_literals(self):
        assert team_satisfies(DOM2, [{"x": 0, "y": 0}], p("x = y")) is True
        assert team_satisfies(
            DOM2, [{"x": 0, "y": 0}, {"x": 0, "y": 1}], p("x = y")) is False
        assert team_satisfies(
            DOM2, [{"x": 0, "y": 1}, {"x": 1, "y": 0}], p("x ≠ y")) is True

    def test_duplicate_assignments_are_normalised_away(self):
        # A team is a SET: [{x:0}, {x:0}] is the singleton team {x↦0}.
        assert team_satisfies(DOM2, [{"x": 0}, {"x": 0}], p("=(x)")) is True


# ---------------------------------------------------------------------------
# Split disjunction: X = Y ∪ Z with Y ⊨ φ, Z ⊨ ψ.
# ---------------------------------------------------------------------------

class TestSplitDisjunction:
    def test_constancy_or_constancy_is_not_constancy(self):
        # {x↦0, x↦1} fails =(x) but satisfies =(x) ∨ =(x): split into the two
        # singletons, each constant. The hallmark non-classical team fact.
        team = [{"x": 0}, {"x": 1}]
        assert team_satisfies(DOM2, team, p("=(x)")) is False
        assert team_satisfies(DOM2, team, p("=(x) ∨ =(x)")) is True

    def test_three_values_need_three_disjuncts(self):
        # Three distinct x-values cannot split into TWO constant parts
        # (pigeonhole), but they can into THREE.
        team = [{"x": 0}, {"x": 1}, {"x": 2}]
        assert team_satisfies(DOM3, team, p("=(x) ∨ =(x)")) is False
        assert team_satisfies(DOM3, team, p("=(x) ∨ =(x) ∨ =(x)")) is True

    def test_split_may_send_everything_one_way(self):
        # Y = X, Z = ∅ is a legal split: X ⊨ φ implies X ⊨ φ ∨ ψ for any ψ.
        team = [{"x": 0}, {"x": 1}]
        assert team_satisfies(DOM2, team, p("x = x ∨ x ≠ x")) is True


# ---------------------------------------------------------------------------
# Dependence atoms =(t₁,…,tₙ): functional dependencies over the team.
# ---------------------------------------------------------------------------

class TestDependenceAtom:
    def test_constancy_fails_on_two_valued_team(self):
        assert team_satisfies(DOM2, [{"x": 0}, {"x": 1}], p("=(x)")) is False

    def test_constancy_holds_on_single_valued_teams(self):
        assert team_satisfies(DOM2, [{"x": 1}], p("=(x)")) is True
        # Single-valued in x even though y varies.
        team = [{"x": 1, "y": 0}, {"x": 1, "y": 1}]
        assert team_satisfies(DOM2, team, p("=(x)")) is True

    def test_functional_dependence_hand_checked(self):
        f = p("=(x, y)")
        # x-value determines y-value: {0↦1, 1↦1} is a function → True.
        good = [{"x": 0, "y": 1}, {"x": 1, "y": 1}]
        assert team_satisfies(DOM2, good, f) is True
        # x = 0 maps to both y = 0 and y = 1 → not functional → False.
        bad = [{"x": 0, "y": 0}, {"x": 0, "y": 1}]
        assert team_satisfies(DOM2, bad, f) is False

    def test_dependence_atom_with_function_term(self):
        # f interprets 0↦1, 1↦0. =(x, f(x)) holds in EVERY team: the value of
        # f(x) is literally a function of the value of x.
        S = Structure(domain=[0, 1], functions={("f", 1): {(0,): 1, (1,): 0}})
        dep_x_fx = Dependence((_v("x"), Function("f", (_v("x"),))))
        full = [{"x": a, "y": b} for a in (0, 1) for b in (0, 1)]
        assert team_satisfies(S, full, dep_x_fx) is True
        # =(y, f(x)): both rows have y = 0 but f(x) is 1 vs 0 → False.
        dep_y_fx = Dependence((_v("y"), Function("f", (_v("x"),))))
        team = [{"x": 0, "y": 0}, {"x": 1, "y": 0}]
        assert team_satisfies(S, team, dep_y_fx) is False

    def test_transitivity_hand_built_team(self):
        # x↦y: {0↦0, 1↦0, 2↦2} ✓; y↦z: {0↦1, 2↦0} ✓; hence x↦z: {0↦1, 1↦1, 2↦0} ✓.
        team = [{"x": 0, "y": 0, "z": 1},
                {"x": 1, "y": 0, "z": 1},
                {"x": 2, "y": 2, "z": 0}]
        assert team_satisfies(DOM3, team, _dep("x", "y")) is True
        assert team_satisfies(DOM3, team, _dep("y", "z")) is True
        assert team_satisfies(DOM3, team, _dep("x", "z")) is True

    def test_transitivity_exhaustive_over_dom2(self):
        # Functional dependence composes: ANY team satisfying =(x,y) and
        # =(y,z) satisfies =(x,z), because tn-values compose as functions.
        # Exhaustive over ALL 2^8 = 256 teams of assignments {x,y,z} → {0,1}.
        rows = [dict(zip("xyz", bits))
                for bits in itertools.product((0, 1), repeat=3)]
        dxy, dyz, dxz = _dep("x", "y"), _dep("y", "z"), _dep("x", "z")
        antecedent_hits = 0
        for mask in range(256):
            team = [rows[i] for i in range(8) if mask >> i & 1]
            if (team_satisfies(DOM2, team, dxy)
                    and team_satisfies(DOM2, team, dyz)):
                antecedent_hits += 1
                assert team_satisfies(DOM2, team, dxz) is True
        # Non-vacuity: at least ∅ and the 8 singletons trigger the antecedent.
        assert antecedent_hits >= 9


# ---------------------------------------------------------------------------
# Quantifiers and sentences.
# ---------------------------------------------------------------------------

class TestSentences:
    @pytest.mark.parametrize("S", [DOM1, DOM2, DOM3])
    def test_forall_exists_equal_true_everywhere(self, S):
        # ∀x ∃y (y = x): pick F(s) = s(x). True on every structure.
        assert team_models(S, p("∀x ∃y (y = x)")) is True

    @pytest.mark.parametrize("S,expected", [(DOM1, True), (DOM2, False), (DOM3, False)])
    def test_constant_witness_forces_singleton_domain(self, S, expected):
        # ∀x ∃y (=(y) ∧ y = x): after ∀x the team is {x↦a : a ∈ dom}; =(y)
        # forces ONE witness c for the whole team, and y = x forces c = a for
        # every a. Possible iff |dom| = 1.
        assert team_models(S, p("∀x ∃y (=(y) ∧ y = x)")) is expected

    @pytest.mark.parametrize("S,expected", [(DOM1, True), (DOM2, False), (DOM3, False)])
    def test_slashed_exists_equivalent_of_constancy(self, S, expected):
        # IF-logic equivalent ∀x ∃y/{x} (y = x): after ∀x every assignment is
        # {x↦a}; hiding x (and y), all assignments have the SAME visible part
        # ∅, so uniformity forces F constant — exactly the =(y) case above.
        assert team_models(S, p("∀x ∃y/{x} (y = x)")) is expected

    @pytest.mark.parametrize("S", [DOM2, DOM3])
    def test_signalling_restores_the_witness(self, S):
        # Signalling: an intermediate ∃z (with z = x) leaks x back into the
        # visible part — assignments now differ on z outside {x, y}, so the
        # slashed witness may vary with z, hence effectively with x. True on
        # every structure, in contrast to the previous test.
        assert team_models(S, p("∀x ∃z (z = x ∧ ∃y/{x} (y = x))")) is True

    def test_slashed_uniformity_at_team_level(self):
        # Directly at team level: on {x↦0, x↦1}, a plain ∃y finds y = x, but
        # ∃y/{x} must pick ONE witness for both assignments (their visible
        # parts outside {x, y} coincide) — impossible.
        team = [{"x": 0}, {"x": 1}]
        assert team_satisfies(DOM2, team, p("∃y (y = x)")) is True
        assert team_satisfies(DOM2, team, p("∃y/{x} (y = x)")) is False

    def test_forall_duplication_at_team_level(self):
        # ∀y ranging over {0,1} from team {x↦0}: duplicated team has y ∈ {0,1},
        # so y = x fails but =(x) still holds.
        team = [{"x": 0}]
        assert team_satisfies(DOM2, team, p("∀y (y = x)")) is False
        assert team_satisfies(DOM2, team, p("∀y =(x)")) is True


# ---------------------------------------------------------------------------
# A genuine dependence sentence: universal sink in a directed graph.
# ---------------------------------------------------------------------------

class TestUniversalSink:
    # c receives an edge from EVERY vertex (a universal sink).
    SINK = Structure(
        domain=["a", "b", "c"],
        predicates={("Edge", 2): {("a", "c"), ("b", "c"), ("c", "c"), ("a", "b")}},
    )
    # 3-cycle: every vertex has out-degree 1, but no common target.
    NO_SINK = Structure(
        domain=["a", "b", "c"],
        predicates={("Edge", 2): {("a", "b"), ("b", "c"), ("c", "a")}},
    )

    def test_sink_sentence(self):
        # ∀x ∃y (=(y) ∧ Edge(x, y)): the witness y must be the SAME vertex for
        # every x — true iff some vertex receives an edge from all vertices.
        f = p("∀x ∃y (=(y) ∧ Edge(x, y))")
        assert team_models(self.SINK, f) is True     # y = c works
        assert team_models(self.NO_SINK, f) is False

    def test_plain_exists_does_not_see_the_difference(self):
        # Without =(y) the witness may vary with x: true on BOTH graphs.
        f = p("∀x ∃y Edge(x, y)")
        assert team_models(self.SINK, f) is True
        assert team_models(self.NO_SINK, f) is True

    def test_differential_against_tarski_exists_forall(self):
        # ∀x ∃y (=(y) ∧ ψ) expresses exactly the FO sentence ∃y ∀x ψ; the
        # independent Tarski evaluator must agree on both structures.
        team_f = p("∀x ∃y (=(y) ∧ Edge(x, y))")
        fo_f = FOL.parse("∃y ∀x Edge(x, y)")
        for S in (self.SINK, self.NO_SINK):
            assert team_models(S, team_f) == models(fo_f, S)


# ---------------------------------------------------------------------------
# Flatness differential: on dependence-free FO formulas, X ⊨ φ iff every
# singleton {s} ⊨ φ, and singleton satisfaction IS classical satisfaction.
# ---------------------------------------------------------------------------

def _rand_literal(rng, variables):
    """A random literal: P(v), R(v,w), or v = w — possibly negated."""
    kind = rng.randrange(3)
    if kind == 0:
        atom = Atom("P", (Variable(rng.choice(variables)),))
    elif kind == 1:
        atom = Atom("R", (Variable(rng.choice(variables)),
                          Variable(rng.choice(variables))))
    else:
        atom = Atom("=", (Variable(rng.choice(variables)),
                          Variable(rng.choice(variables))))
    return Not(atom) if rng.random() < 0.4 else atom


def _rand_fo(rng, depth, quantifiers, variables):
    """A random dependence-free formula of the team fragment (¬ on atoms only)."""
    if depth <= 0:
        return _rand_literal(rng, variables)
    r = rng.random()
    if quantifiers > 0 and r < 0.35:
        return Quantifier(rng.choice(("∀", "∃")),
                          Variable(rng.choice(variables)),
                          _rand_fo(rng, depth - 1, quantifiers - 1, variables))
    ctor = And if r < 0.7 else Or
    return ctor(_rand_fo(rng, depth - 1, quantifiers, variables),
                _rand_fo(rng, depth - 1, quantifiers, variables))


def _rand_structure(rng, size):
    """A random structure with unary P and binary R over domain {0..size-1}."""
    dom = list(range(size))
    p_ext = {(a,) for a in dom if rng.random() < 0.5}
    r_ext = {(a, b) for a in dom for b in dom if rng.random() < 0.4}
    return Structure(domain=dom, predicates={("P", 1): p_ext, ("R", 2): r_ext})


class TestFlatnessDifferential:
    def test_flatness_and_tarski_agreement(self):
        # THE key oracle test. FO formulas are FLAT (Väänänen 2007,
        # Cor. 3.32): X ⊨ φ iff {s} ⊨ φ for every s ∈ X. And on singletons,
        # team satisfaction must coincide with the independent classical
        # Tarski evaluator. 100 seeded random formulas; sizes are chosen so
        # every witness search stays below MAX_TEAM_SEARCH (with |dom| = 2 the
        # deduplicated team over 3 variables never exceeds 2^3 = 8; with
        # |dom| = 3 and 2 variables never exceeds 3^2 = 9).
        rng = random.Random(20260703)
        flat_true = flat_false = 0
        for i in range(100):
            if i % 2 == 0:
                size, variables, max_team = 2, ("x", "y", "z"), 3
            else:
                size, variables, max_team = 3, ("x", "y"), 2
            S = _rand_structure(rng, size)
            formula = _rand_fo(rng, depth=3, quantifiers=2, variables=variables)
            rows = [dict(zip(variables, values))
                    for values in itertools.product(range(size),
                                                    repeat=len(variables))]
            team = rng.sample(rows, rng.randint(1, max_team))

            singleton_verdicts = []
            for s in team:
                single = team_satisfies(S, [s], formula)
                # Singleton team satisfaction == classical Tarski satisfaction.
                assert single == satisfies(formula, S, s), (
                    f"Tarski disagreement on {formula!r} at {s!r}")
                singleton_verdicts.append(single)

            whole = team_satisfies(S, team, formula)
            assert whole == all(singleton_verdicts), (
                f"Flatness violated for {formula!r} on team {team!r}")
            flat_true += whole
            flat_false += not whole
        # Non-vacuity: the battery must exercise both outcomes.
        assert flat_true > 0 and flat_false > 0


# ---------------------------------------------------------------------------
# Downward closure: X ⊨ φ and Y ⊆ X imply Y ⊨ φ (Väänänen 2007, Prop. 3.10),
# on random formulas WITH dependence atoms / slashed quantifiers.
# ---------------------------------------------------------------------------

def _rand_dep_leaf(rng, variables):
    """A random leaf: a dependence atom (constancy or binary) or a literal."""
    if rng.random() < 0.35:
        if rng.random() < 0.4:
            return Dependence((Variable(rng.choice(variables)),))
        return Dependence((Variable(rng.choice(variables)),
                           Variable(rng.choice(variables))))
    return _rand_literal(rng, variables)


def _rand_dep_formula(rng, depth, quantifiers, variables):
    """A random team-fragment formula that may contain =(…) and ∃x/{…}."""
    if depth <= 0:
        return _rand_dep_leaf(rng, variables)
    r = rng.random()
    if quantifiers > 0 and r < 0.3:
        var = Variable(rng.choice(variables))
        body = _rand_dep_formula(rng, depth - 1, quantifiers - 1, variables)
        if rng.random() < 0.4:
            return SlashedExists(var, (rng.choice(variables),), body)
        return Quantifier(rng.choice(("∀", "∃")), var, body)
    ctor = And if r < 0.65 else Or
    return ctor(_rand_dep_formula(rng, depth - 1, quantifiers, variables),
                _rand_dep_formula(rng, depth - 1, quantifiers, variables))


def _has_team_construct(f):
    """Whether the formula contains a dependence atom or slashed quantifier."""
    if isinstance(f, (Dependence, SlashedExists)):
        return True
    if isinstance(f, (And, Or)):
        return _has_team_construct(f.left) or _has_team_construct(f.right)
    if isinstance(f, Quantifier):
        return _has_team_construct(f.formula)
    return False


class TestDownwardClosure:
    def test_downward_closure_on_random_dependence_formulas(self):
        rng = random.Random(0xD09)
        variables = ("x", "y", "z")
        rows = [dict(zip(variables, bits))
                for bits in itertools.product((0, 1), repeat=3)]
        nontrivial = 0
        for _ in range(60):
            S = _rand_structure(rng, 2)
            formula = _rand_dep_formula(rng, depth=3, quantifiers=1,
                                        variables=variables)
            while not _has_team_construct(formula):
                formula = _rand_dep_formula(rng, depth=3, quantifiers=1,
                                            variables=variables)
            team = rng.sample(rows, 3)
            n = len(team)
            # Satisfaction verdict for every subteam, indexed by bitmask.
            sat = [team_satisfies(
                       S, [team[i] for i in range(n) if mask >> i & 1], formula)
                   for mask in range(2 ** n)]
            # The empty subteam (mask 0) re-checks the empty-team property on
            # formulas with team atoms.
            assert sat[0] is True
            # Downward closure: sub ⊆ sup and sup ⊨ φ imply sub ⊨ φ.
            for sup in range(2 ** n):
                if not sat[sup]:
                    continue
                for sub in range(2 ** n):
                    if sub & sup == sub:
                        assert sat[sub] is True, (
                            f"Downward closure violated for {formula!r}: "
                            f"team mask {sup} satisfies but subteam {sub} "
                            f"does not")
            nontrivial += sat[2 ** n - 1]
        # Non-vacuity: some full teams must actually satisfy their formula.
        assert nontrivial > 0


# ---------------------------------------------------------------------------
# Rejections: nodes outside the fragment, and classical exports.
# ---------------------------------------------------------------------------

class TestRejections:
    P_x = Atom("P", (Variable("x"),))
    Q_x = Atom("Q", (Variable("x"),))

    @pytest.mark.parametrize("formula", [
        Implies(P_x, Q_x),
        Iff(P_x, Q_x),
        Xor(P_x, Q_x),
        Not(And(P_x, Q_x)),                       # ¬ of a non-atom
        Not(Dependence((Variable("x"),))),        # dual negation of =(x)
        Not(SlashedExists(Variable("y"), ("x",), Atom("=", (Variable("y"), Variable("x"))))),
    ])
    def test_outside_fragment_raises_type_error(self, formula):
        with pytest.raises(TypeError, match="team-semantics fragment"):
            team_satisfies(DOM2, [{"x": 0}], formula)

    def test_type_error_also_under_connectives_and_quantifiers(self):
        buried = Quantifier("∀", Variable("x"), Implies(self.P_x, self.Q_x))
        with pytest.raises(TypeError, match="team-semantics fragment"):
            team_models(DOM2, buried)

    def test_no_z3_export_for_dependence(self):
        with pytest.raises(NotImplementedError, match="team semantics"):
            Dependence((Variable("x"),)).to_z3()

    def test_no_z3_export_for_slashed_exists(self):
        f = SlashedExists(Variable("y"), ("x",),
                          Atom("=", (Variable("y"), Variable("x"))))
        with pytest.raises(NotImplementedError, match="team semantics"):
            f.to_z3()


# ---------------------------------------------------------------------------
# The brute-force size guard.
# ---------------------------------------------------------------------------

class TestSizeGuard:
    S4 = Structure(domain=[0, 1, 2, 3])

    def test_existential_search_above_bound_raises(self):
        # 9 assignments over |dom| = 4: the ∃ search would try 4^9 = 262144
        # witness functions > MAX_TEAM_SEARCH = 65536.
        rows = [dict(zip("uv", pair))
                for pair in itertools.product(range(4), repeat=2)][:9]
        with pytest.raises(ValueError, match="MAX_TEAM_SEARCH"):
            team_satisfies(self.S4, rows, p("∃w (w = w)"))

    def test_documented_scale_is_admitted(self):
        # Exactly the documented bound: 8 assignments, |dom| = 4 → 4^8 = 65536
        # candidates is allowed (and w = w succeeds on the first one).
        rows = [dict(zip("uv", pair))
                for pair in itertools.product(range(4), repeat=2)][:8]
        assert team_satisfies(self.S4, rows, p("∃w (w = w)")) is True

    def test_split_search_above_bound_raises(self):
        # 17 assignments: the split search would try 2^17 = 131072 partitions.
        rows = [dict(zip("uvw", triple))
                for triple in itertools.product(range(4), repeat=3)][:17]
        with pytest.raises(ValueError, match="MAX_TEAM_SEARCH"):
            team_satisfies(self.S4, rows, p("P(u) ∨ P(u)"))

    def test_bound_constant_documented_value(self):
        assert MAX_TEAM_SEARCH == 4 ** 8 == 65536
