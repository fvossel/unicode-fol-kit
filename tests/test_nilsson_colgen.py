"""Tests for ``unicode_fol_kit.prob.nilsson.entailment_bounds(strategy="column_generation")``.

The column-generation strategy (:mod:`unicode_fol_kit.prob._column_gen`)
solves the EXACT SAME linear program the default ``strategy="direct"`` path
does, without ever materialising a ``2^n``-sized world array. This file's
central check, repeated in every class below, is DIFFERENTIAL: run both
strategies on the same input and require exact ``Fraction`` equality
(``==``, never a tolerance) — the existing, already-hand-verified
``strategy="direct"`` enumeration is itself an independent oracle for every
case small enough for it to answer. Three things a direct/direct comparison
alone could never check are covered separately:

* ``TestDualConstructionUnit`` hand-computes the optimal dual of one small
  restricted master on paper and asserts the code's own dual solve agrees.
* ``TestWideSparseClusters`` goes past ``max_atoms=12`` far enough (45
  atoms) that ``strategy="direct"`` genuinely cannot serve as an oracle —
  checked instead against the classical Fréchet/Bonferroni bounds for an
  intersection of events with fixed marginals (Hansen & Jaumard's PSAT
  survey discusses these as a textbook decomposition case), AND against an
  independent re-derivation of the returned witness distribution.
* ``TestMeasuredSpeedup`` reports actual wall-clock numbers where the direct
  route is measurably slow, even well inside ``max_atoms``.

``tests/test_prob.py`` remains the byte-for-byte pin on ``strategy="direct"``
itself; this file never touches or re-derives that contract, only builds on
top of it.
"""

import random
import time
from fractions import Fraction as F

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import (
    And, Atom, Iff, Implies, Not, Or, Quantifier, Variable, Xor,
)
from unicode_fol_kit.prob import _column_gen
from unicode_fol_kit.prob.nilsson import ProbBounds, ProbConstraint, _eval, entailment_bounds

P = api.parse_any


def f(text):
    return P(text).formula


A, B, C = f("A"), f("B"), f("C")

STRATEGIES = ("direct", "column_generation")


# ===========================================================================
# Default stays "direct", and every existing call shape is unaffected.
# ===========================================================================

class TestDefaultStrategyUnchanged:
    def test_default_equals_explicit_direct(self):
        cs = [ProbConstraint.exact(A, F(7, 10)), ProbConstraint.exact(f("A → B"), F(8, 10))]
        default = entailment_bounds(cs, B)
        explicit = entailment_bounds(cs, B, strategy="direct")
        # Full dataclass equality (not just .lower/.upper): n_worlds too, so
        # a positional-args ProbBounds(...) built the old way still compares
        # equal, exactly as tests/test_prob.py's existing assertions do.
        assert default == explicit == ProbBounds(F(1, 2), F(4, 5), 4)

    def test_positional_and_max_atoms_only_signature_still_works(self):
        # The exact call shape every pre-existing caller uses: positional
        # constraints/conclusion, keyword-only max_atoms, no strategy at all.
        bounds = entailment_bounds([ProbConstraint(A, F(3, 10), F(6, 10))], A, max_atoms=5)
        assert bounds == ProbBounds(F(3, 10), F(6, 10), 2)

    def test_unknown_strategy_rejected(self):
        with pytest.raises(ValueError, match="unknown strategy"):
            entailment_bounds([ProbConstraint.exact(A, F(1))], A, strategy="bogus")


# ===========================================================================
# Differential: hand-checked cases, both strategies, exact Fraction equality.
# ===========================================================================

class TestDifferentialHandCheckedCases:
    """Every hand-checked case in tests/test_prob.py's TestEntailmentBoundsHandChecked
    and TestClassicalBoundaryDifferential, run under both strategies. The
    derivation is the same LP either way (see nilsson.py's module docstring);
    the comments here restate the hand-worked numbers, not re-derive them
    from scratch, since test_prob.py already carries the full worked-by-hand
    derivation for each.
    """

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_modus_ponens_interval(self, strategy):
        # Nilsson's own textbook example (Nilsson 1986; also Hansen &
        # Jaumard's PSAT survey): P(A)=7/10, P(A→B)=8/10 exactly gives
        # P(B) in [1/2, 4/5] (see test_prob.py for the world-by-world LP).
        cs = [ProbConstraint.exact(A, F(7, 10)), ProbConstraint.exact(f("A → B"), F(8, 10))]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == F(1, 2) and bounds.upper == F(4, 5)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_conditional_pins_conjunction_exactly(self, strategy):
        # P(B|A)=9/10, P(A)=1/2 exactly => P(A∧B) = 9/10 * 1/2 = 9/20 exactly.
        cs = [ProbConstraint.exact(B, F(9, 10), given=A), ProbConstraint.exact(A, F(1, 2))]
        bounds = entailment_bounds(cs, f("A ∧ B"), strategy=strategy)
        assert bounds.lower == bounds.upper == F(9, 20)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_conditional_bounds_on_b(self, strategy):
        # Same premises: P(A∧B)=9/20, P(A)=1/2 forced => P(A∧¬B)=1/20;
        # the remaining 1/2 mass splits freely, so P(B) in [9/20, 19/20].
        cs = [ProbConstraint.exact(B, F(9, 10), given=A), ProbConstraint.exact(A, F(1, 2))]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == F(9, 20) and bounds.upper == F(19, 20)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_conditional_vacuous_when_condition_impossible(self, strategy):
        # P(A)=0 forces every A-world to probability 0, so P(B|A) in
        # [lower,upper] degrades to 0<=P(A∧B)<=0 -- already implied by
        # P(A∧B)<=P(A)=0 -- adding nothing: P(B) is left fully free, [0,1].
        cs = [ProbConstraint.exact(A, F(0)), ProbConstraint.exact(B, F(9, 10), given=A)]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == F(0) and bounds.upper == F(1)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_interval_constraint_passes_through(self, strategy):
        cs = [ProbConstraint(A, F(3, 10), F(6, 10))]
        bounds = entailment_bounds(cs, A, strategy=strategy)
        assert bounds.lower == F(3, 10) and bounds.upper == F(6, 10)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_xor_and_iff_are_pointwise_complements(self, strategy):
        # P(A xor B) + P(A iff B) = 1 on EVERY world, so pinning xor to 3/10
        # exactly pins iff to 7/10 exactly, no freedom left.
        cs = [ProbConstraint.exact(f("A ⊕ B"), F(3, 10))]
        bounds = entailment_bounds(cs, f("A ↔ B"), strategy=strategy)
        assert bounds.lower == bounds.upper == F(7, 10)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_classical_entailment_boundary_entailed(self, strategy):
        # Every premise pinned to 1, and {A, A->B} classically entails B
        # (modus ponens): bounds collapse to exactly (1, 1).
        cs = [ProbConstraint.exact(A, F(1)), ProbConstraint.exact(f("A → B"), F(1))]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == bounds.upper == F(1)
        assert bool(api.prove(B, [A, f("A → B")])) is True

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_classical_entailment_boundary_not_entailed(self, strategy):
        # {A} does not classically entail B (countermodel A=T,B=F exists).
        cs = [ProbConstraint.exact(A, F(1))]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == F(0) and bounds.upper == F(1)
        assert bool(api.prove(B, [A])) is False


# ===========================================================================
# Degenerate bounds, point probabilities, richer conditional assessments.
# ===========================================================================

class TestDegenerateAndPointCases:
    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_fully_degenerate_zero_one_bounds(self, strategy):
        # P(A) in [0, 1] is no constraint at all -- P(A) itself stays [0, 1].
        cs = [ProbConstraint(A, F(0), F(1))]
        bounds = entailment_bounds(cs, A, strategy=strategy)
        assert bounds.lower == F(0) and bounds.upper == F(1)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_empty_constraints_gives_zero_one_bounds(self, strategy):
        # Zero LP rows (constraints=[]) is the m=0 edge case: phase 1's
        # artificial-sum objective z3.Sum([]) is the Python int 0, not a z3
        # AST, which previously crashed opt.minimize(...) with an
        # AttributeError under strategy="column_generation" only (direct
        # already handled it, since it never routes through phase 1 at all).
        # No constraints at all pins nothing, so P(A) stays exactly [0, 1].
        bounds = entailment_bounds([], A, strategy=strategy)
        assert bounds.lower == F(0) and bounds.upper == F(1)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_point_probability_pins_conclusion(self, strategy):
        cs = [ProbConstraint.exact(A, F(1, 3))]
        bounds = entailment_bounds(cs, A, strategy=strategy)
        assert bounds.lower == bounds.upper == F(1, 3)

    @pytest.mark.parametrize("strategy", STRATEGIES)
    def test_conditional_interval_not_exact(self, strategy):
        # P(B|A) in [3/10, 7/10] (interval, not pinned), P(A)=2/5 exactly.
        # Nilsson linear form: 3/10*P(A) <= P(A∧B) <= 7/10*P(A), i.e.
        # P(A∧B) in [3/25, 7/25]. The rest of A's mass (2/5 - P(A∧B)) and all
        # of ¬A's mass (3/5) are free for B, so
        #   P(B) in [3/25, 7/25 + 3/5] = [3/25, 46/25 ... capped at 1]?
        # Concretely: min P(B) = P(A∧B)_min = 3/25 (put all remaining mass on
        # ¬A∧¬B); max P(B) = P(A∧B)_max + P(¬A) = 7/25 + 3/5 = 7/25+15/25=22/25.
        cs = [ProbConstraint(B, F(3, 10), F(7, 10), given=A), ProbConstraint.exact(A, F(2, 5))]
        bounds = entailment_bounds(cs, B, strategy=strategy)
        assert bounds.lower == F(3, 25) and bounds.upper == F(22, 25)


# ===========================================================================
# Inconsistent assessments: same error TYPE, equivalent message, both strategies.
# ===========================================================================

class TestInconsistentAssessments:
    def test_both_strategies_raise_value_error_with_equal_message(self):
        cs = [ProbConstraint.exact(A, F(1)), ProbConstraint.exact(f("¬A"), F(1))]
        with pytest.raises(ValueError, match="probabilistically inconsistent") as direct_exc:
            entailment_bounds(cs, A, strategy="direct")
        with pytest.raises(ValueError, match="probabilistically inconsistent") as cg_exc:
            entailment_bounds(cs, A, strategy="column_generation")
        # Both build the message through the exact same nilsson._infeasible_error
        # helper, so it is not merely "equivalent" here but literally identical.
        assert str(direct_exc.value) == str(cg_exc.value)

    def test_inconsistent_interval_constraints(self):
        # P(A) in [8/10, 1] and P(A) in [0, 2/10] cannot both hold.
        cs = [ProbConstraint(A, F(8, 10), F(1)), ProbConstraint(A, F(0), F(2, 10))]
        for strategy in STRATEGIES:
            with pytest.raises(ValueError, match="probabilistically inconsistent"):
                entailment_bounds(cs, A, strategy=strategy)

    def test_quantified_formula_refused_both_strategies(self):
        x = Variable("x")
        quantified = Quantifier("∀", x, Atom("P", (x,)))
        for strategy in STRATEGIES:
            with pytest.raises(ValueError):
                entailment_bounds([ProbConstraint.exact(quantified, F(1))], A, strategy=strategy)


# ===========================================================================
# Seeded random differential battery (n <= 10-12 atoms), direct as oracle.
# ===========================================================================

def _random_propositional_formula(rng, atoms, depth):
    if depth <= 0 or rng.random() < 0.4:
        return rng.choice(atoms)
    op = rng.choice(["not", "and", "or", "implies", "iff", "xor"])
    if op == "not":
        return Not(_random_propositional_formula(rng, atoms, depth - 1))
    left = _random_propositional_formula(rng, atoms, depth - 1)
    right = _random_propositional_formula(rng, atoms, depth - 1)
    cls = {"and": And, "or": Or, "implies": Implies, "iff": Iff, "xor": Xor}[op]
    return cls(left, right)


def _random_case(rng, n_atoms, n_constraints):
    atoms = [Atom(f"R{i}", ()) for i in range(n_atoms)]
    constraints = []
    for _ in range(n_constraints):
        formula = _random_propositional_formula(rng, atoms, 2)
        lo_num = rng.randint(0, 10)
        hi_num = rng.randint(lo_num, 10)
        lo, hi = F(lo_num, 10), F(hi_num, 10)
        if rng.random() < 0.3:
            given = _random_propositional_formula(rng, atoms, 2)
            constraints.append(ProbConstraint(formula, lo, hi, given=given))
        else:
            constraints.append(ProbConstraint(formula, lo, hi))
    conclusion = _random_propositional_formula(rng, atoms, 2)
    return constraints, conclusion


class TestDifferentialRandomBattery:
    """A seeded, reproducible random generator over small (n <= 6) formulas,
    checked against strategy="direct" as an independent oracle: same bound
    when both succeed, same ValueError when the constraint set is (randomly)
    inconsistent. n is kept small here (<=6) so strategy="direct" itself
    stays fast enough to run as the oracle on every one of many trials;
    TestWideSparseClusters below is the separate, larger-n battery where
    strategy="direct" can no longer serve that role.
    """

    def test_random_battery_agrees_with_direct(self):
        rng = random.Random("nilsson-colgen-differential-v1")
        trials = 60
        both_raised = 0
        for trial in range(trials):
            n_atoms = rng.randint(1, 6)
            n_constraints = rng.randint(1, 4)
            cs, concl = _random_case(rng, n_atoms, n_constraints)

            direct_exc = cg_exc = None
            direct_bounds = cg_bounds = None
            try:
                direct_bounds = entailment_bounds(cs, concl, strategy="direct")
            except ValueError as exc:
                direct_exc = exc
            try:
                cg_bounds = entailment_bounds(cs, concl, strategy="column_generation")
            except ValueError as exc:
                cg_exc = exc

            assert (direct_exc is None) == (cg_exc is None), (
                f"trial {trial}: one strategy raised and the other did not "
                f"(direct={direct_exc}, column_generation={cg_exc})"
            )
            if direct_exc is not None:
                assert "probabilistically inconsistent" in str(direct_exc)
                assert "probabilistically inconsistent" in str(cg_exc)
                both_raised += 1
                continue
            assert direct_bounds.lower == cg_bounds.lower, f"trial {trial}: lower mismatch"
            assert direct_bounds.upper == cg_bounds.upper, f"trial {trial}: upper mismatch"

        # Sanity on the generator itself: with random [0,1]-scaled intervals
        # on small formula sets, SOME trials are expected to be inconsistent
        # and SOME are expected to succeed -- if either were zero the battery
        # would not actually be exercising both code paths.
        assert 0 < both_raised < trials

    def test_n_up_to_twelve_atoms_still_agrees(self):
        # A handful of larger (up to max_atoms=12) cases, where direct is
        # still usable as an oracle but noticeably more work.
        rng = random.Random("nilsson-colgen-differential-wide-v1")
        for trial in range(6):
            n_atoms = rng.randint(9, 12)
            n_constraints = rng.randint(2, 5)
            cs, concl = _random_case(rng, n_atoms, n_constraints)
            try:
                direct_bounds = entailment_bounds(cs, concl, strategy="direct", max_atoms=12)
            except ValueError as exc:
                assert "probabilistically inconsistent" in str(exc)
                with pytest.raises(ValueError, match="probabilistically inconsistent"):
                    entailment_bounds(cs, concl, strategy="column_generation")
                continue
            cg_bounds = entailment_bounds(cs, concl, strategy="column_generation")
            assert direct_bounds.lower == cg_bounds.lower
            assert direct_bounds.upper == cg_bounds.upper


# ===========================================================================
# strategy="column_generation" bypasses max_atoms (the whole point).
# ===========================================================================

class TestMaxAtomsBypassedForColumnGeneration:
    def test_thirteen_atoms_refused_by_direct_default(self):
        atoms = [Atom(f"S{i}", ()) for i in range(13)]
        big = atoms[0]
        for a in atoms[1:]:
            big = Or(big, a)
        with pytest.raises(ValueError, match="max_atoms"):
            entailment_bounds([ProbConstraint.exact(atoms[0], F(1, 2))], big)

    def test_thirteen_atoms_solved_by_column_generation(self):
        # P(atom0) = 1/2 exactly; conclusion = OR of all 13 atoms. atom0=True
        # forces the OR true (so min P(OR) can't dodge that half of the
        # mass); atom0=False mass can always be routed onto an
        # all-remaining-atoms-false world (OR false) for the min, or onto an
        # OR-true world for the max -- min=1/2, max=1, hand-computable.
        atoms = [Atom(f"S{i}", ()) for i in range(13)]
        big = atoms[0]
        for a in atoms[1:]:
            big = Or(big, a)
        bounds = entailment_bounds(
            [ProbConstraint.exact(atoms[0], F(1, 2))], big, strategy="column_generation")
        assert bounds.lower == F(1, 2) and bounds.upper == F(1)
        assert bounds.n_worlds == 2 ** 13

    def test_max_columns_brake_never_returns_unproven_bound(self):
        cs = [ProbConstraint.exact(A, F(7, 10)), ProbConstraint.exact(f("A → B"), F(8, 10))]
        with pytest.raises(ValueError, match="max_columns"):
            entailment_bounds(cs, B, strategy="column_generation", max_columns=1)


# ===========================================================================
# A focused unit test on the dual construction alone (hand-computed by hand).
# ===========================================================================

class TestDualConstructionUnit:
    """P(A) in [3/10, 6/10], minimizing P(A) over columns={A=F, A=T}.

    By hand: rows are (coeff(A=F)=0, coeff(A=T)=1, rhs=3/10) [the >= row]
    and (coeff(A=F)=0, coeff(A=T)=-1, rhs=-6/10) [the <= row, as >= -6/10].
    cost(A=F)=0, cost(A=T)=1 (minimizing P(A)). The dual is
    ``max 3/10*y0 - 6/10*y1 + lam`` s.t. ``lam <= 0`` (from A=F) and
    ``y0 - y1 + lam <= 1`` (from A=T), y0,y1>=0. Since y1 only hurts the
    objective and loosens the binding constraint with no offsetting benefit,
    y1=0 at the optimum; then lam<=0 and y0<=1-lam are both loosest at
    lam=0, giving y0=1 -- the UNIQUE optimum (y0,y1,lam) = (1, 0, 0), dual
    objective = 3/10*1 - 0 + 0 = 3/10, matching the known primal optimum
    exactly (this constraint's own known min bound, see
    test_interval_constraint_passes_through above).
    """

    def _setup(self):
        cs = [ProbConstraint(A, F(3, 10), F(6, 10))]
        rows = _column_gen._build_rows(cs)
        columns = [{"A": False}, {"A": True}]
        cost_of = lambda w: _column_gen._indicator(A, w)
        cost_z3 = lambda av: _column_gen._z3_indicator(A, av)
        return rows, columns, cost_of, cost_z3

    def test_dual_matches_hand_computed_optimum(self):
        rows, columns, cost_of, _ = self._setup()
        y, lam = _column_gen._solve_dual(rows, columns, cost_of)
        assert y == [F(1), F(0)]
        assert lam == F(0)

    def test_pricing_agrees_dual_already_optimal(self):
        # At the hand-computed optimal dual, pricing must find NO world with
        # positive reduced cost -- the two columns already present already
        # span the LP's optimum (this restricted master IS the full 2-world
        # problem, n=1 atom, so there is nothing else to price in anyway).
        rows, columns, cost_of, cost_z3 = self._setup()
        y, lam = _column_gen._solve_dual(rows, columns, cost_of)
        found, _valuation, value = _column_gen._price(["A"], rows, y, lam, cost_z3)
        assert found is True
        assert value <= 0

    def test_primal_matches_dual_objective_exactly(self):
        # Strong duality: the restricted primal's own optimum must equal the
        # dual objective at (y, lam) = (1, 0, 0) bit-for-bit as a Fraction.
        rows, columns, cost_of, _ = self._setup()
        value, witness = _column_gen._solve_restricted_primal(rows, columns, cost_of)
        assert value == F(3, 10)
        assert sum(p for _, p in witness) == F(1)


# ===========================================================================
# Wide/sparse: n well past max_atoms=12, closed form via independent clusters.
# ===========================================================================

class TestWideSparseClusters:
    """Fréchet/Bonferroni bounds for the intersection of k independent-marginal
    events (see e.g. Hansen & Jaumard's PSAT survey for these as a standard
    decomposition device): given ONLY P(A_i) = p for k events with no other
    constraint linking them, P(A_1 ∧ ... ∧ A_k) is bounded by
    ``max(0, k*p - (k-1)) <= P(∧A_i) <= min(p_1,...,p_k)``, and BOTH bounds
    are attained (upper: a comonotonic coupling: order the events by a
    single shared threshold so one event's truth implies every event with a
    smaller marginal is also true; lower, when positive: a "stacking"
    coupling that packs each event's failure probability into a share of the
    unit interval so every point is covered by at least one failure once the
    failure shares exceed k-1). This is the ONE place in this file where
    strategy="direct" cannot itself serve as the oracle (2**45 worlds is not
    an enumerable number), so the check runs against this closed form
    instead, cross-checked (independently of the LP/column-generation code)
    by recomputing every constraint's probability and the objective directly
    from the returned witness distribution via nilsson._eval.

    k=15 (45 atoms, 3 per cluster -- only 1 of the 3 is load-bearing, the
    other 2 are deliberately irrelevant filler, exercising that column
    generation does not choke on irrelevant atoms) is comfortably "well past
    max_atoms=12" while keeping this test's own runtime reasonable; the
    roadmap's suggested 20-30 clusters pushed measured wall-clock time for
    this particular (near-degenerate, many-columns-needed) case well past a
    minute -- see this task's own reported deviation for the measured
    numbers at larger k.
    """

    K = 15
    P_EACH = F(49, 50)

    def _build(self):
        clusters = [
            (Atom(f"W{i}_0", ()), Atom(f"W{i}_1", ()), Atom(f"W{i}_2", ()))
            for i in range(self.K)
        ]
        constraints = [ProbConstraint.exact(clusters[i][0], self.P_EACH) for i in range(self.K)]
        # The other 2 atoms per cluster are deliberately irrelevant filler:
        # a [0,1] "constraint" constrains nothing (see TestDegenerateAndPointCases
        # above) but DOES put the atom in play, so the LP genuinely has all
        # 45 atoms/columns to search over, not just the 15 load-bearing ones
        # -- exercising that column generation does not choke on irrelevant
        # atoms, mirroring tests/test_prob.py's own "with_irrelevant_fact" pattern.
        for i in range(self.K):
            constraints.append(ProbConstraint(clusters[i][1], F(0), F(1)))
            constraints.append(ProbConstraint(clusters[i][2], F(0), F(1)))
        conclusion = clusters[0][0]
        for i in range(1, self.K):
            conclusion = And(conclusion, clusters[i][0])
        atom_list = sorted(a.to_unicode_str() for tri in clusters for a in tri)
        return constraints, conclusion, atom_list

    def test_bounds_match_frechet_closed_form(self):
        constraints, conclusion, _atom_list = self._build()
        bounds = entailment_bounds(constraints, conclusion, strategy="column_generation")

        expected_upper = self.P_EACH
        expected_lower = max(F(0), self.K * self.P_EACH - (self.K - 1))
        assert bounds.n_worlds == 2 ** 45
        assert bounds.lower == expected_lower
        assert bounds.upper == expected_upper
        # Sanity on the test's own construction: the lower bound must be a
        # genuinely nonzero, nontrivial number here (not the vacuous max(0,
        # negative)=0 corner), or this would not actually be testing the
        # "stacking" side of the closed form at all.
        assert expected_lower not in (F(0), F(1))

    def test_witness_distributions_independently_reverified(self):
        # Re-derive both bounds' witness distributions from scratch, using
        # only nilsson._eval (never the LP/column-generation machinery under
        # test): sum to exactly 1, every constraint holds exactly under that
        # distribution, and P(conclusion) under it equals the claimed bound
        # exactly -- the "returned bound is attained by an explicit
        # distribution over the generated columns" check, re-checked
        # independently rather than trusted from the solver's own report.
        constraints, conclusion, atom_list = self._build()
        result = _column_gen.solve(atom_list, constraints, conclusion, 500)
        for name, witness, expected in (
            ("lower", result.lower_witness, result.lower),
            ("upper", result.upper_witness, result.upper),
        ):
            total = sum(p for _, p in witness)
            assert total == F(1), f"{name} witness does not sum to 1: {total}"
            assert all(p > 0 for _, p in witness)
            for c in constraints:
                if c.given is None:
                    p_phi = sum(p for w, p in witness if _eval(c.formula, w))
                    assert c.lower <= p_phi <= c.upper, f"{name}: constraint violated ({p_phi})"
                else:
                    p_given = sum(p for w, p in witness if _eval(c.given, w))
                    p_both = sum(p for w, p in witness if _eval(c.formula, w) and _eval(c.given, w))
                    assert c.lower * p_given <= p_both <= c.upper * p_given
            p_concl = sum(p for w, p in witness if _eval(conclusion, w))
            assert p_concl == expected, f"{name}: witness gives {p_concl}, solver claimed {expected}"


# ===========================================================================
# Measured speed-ups: reported honestly, where the direct 2^n route is slow.
# ===========================================================================

class TestMeasuredSpeedup:
    """A concrete, reproducible speed-up measurement (not just an assertion
    that column generation "should" be faster): 11 independent exact
    marginals P(atom_i) = 49/50, conclusion = AND of all 11. Both strategies
    are well within max_atoms here (n=11 < 12) and return the identical
    bound (checked below), but strategy="direct" already spends measurably
    longer per Z3 call at this size for this near-degenerate constraint
    shape (many simultaneously-binding exact constraints), while
    strategy="column_generation"'s cost is governed by how many columns the
    pricing loop needs, not by 2^n directly. The assertion is deliberately
    loose (colgen strictly faster, not a specific ratio) to stay robust
    across machines; the measured numbers are printed for the record.
    """

    def test_column_generation_faster_than_direct_at_n_eleven(self, capsys):
        n = 11
        p = F(49, 50)
        atoms = [Atom(f"V{i}", ()) for i in range(n)]
        cs = [ProbConstraint.exact(atoms[i], p) for i in range(n)]
        concl = atoms[0]
        for a in atoms[1:]:
            concl = And(concl, a)

        t0 = time.time()
        direct = entailment_bounds(cs, concl, strategy="direct", max_atoms=n)
        t1 = time.time()
        cg = entailment_bounds(cs, concl, strategy="column_generation")
        t2 = time.time()
        direct_time, cg_time = t1 - t0, t2 - t1

        assert direct.lower == cg.lower and direct.upper == cg.upper
        ratio = (direct_time / cg_time) if cg_time > 0 else float("inf")
        with capsys.disabled():
            print(f"\n[measured speed-up] n={n} AND-of-{n}-exact-marginals: "
                  f"direct={direct_time:.2f}s column_generation={cg_time:.2f}s ({ratio:.1f}x)")
        assert cg_time < direct_time
