"""Tests for unicode_fol_kit.prob — exact probabilistic logic (no sampling).

Two independent formal anchors, one per module:

* nilsson.entailment_bounds — every expected bound below is derived BY HAND in
  a comment before the code is run (the world-by-world LP, worked out on
  paper), and the classical-boundary case is additionally cross-checked
  DIFFERENTIALLY against unicode_fol_kit.api.prove.
* distribution.query — every expected probability is derived BY HAND in a
  comment (the finite total-choice sum, worked out on paper), and pruned vs.
  unpruned enumeration is checked to agree on every program below.
"""

from fractions import Fraction as F

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Constant,
)
from unicode_fol_kit.prob.nilsson import ProbConstraint, ProbBounds, entailment_bounds
from unicode_fol_kit.prob.distribution import ProbFact, ProbProgram, query

P = api.parse_any


def f(text):
    return P(text).formula


# ===========================================================================
# nilsson.py — Nilsson probabilistic-entailment bounds
# ===========================================================================

A, B, C = f("A"), f("B"), f("C")


class TestProbConstraint:
    def test_valid_bounds_accepted(self):
        c = ProbConstraint(A, F(1, 4), F(3, 4))
        assert c.lower == F(1, 4) and c.upper == F(3, 4)

    def test_exact_convenience_constructor(self):
        c = ProbConstraint.exact(A, F(7, 10))
        assert c.lower == c.upper == F(7, 10)

    def test_int_coerced_to_fraction(self):
        c = ProbConstraint(A, 0, 1)
        assert c.lower == F(0) and c.upper == F(1)
        assert isinstance(c.lower, F) and isinstance(c.upper, F)

    def test_float_rejected(self):
        # Exact probabilistic logic never takes a float shortcut: Fraction(0.7)
        # is the nearest binary double to 0.7, NOT 7/10 — silently accepting it
        # would smuggle rounding error into a bound advertised as exact.
        with pytest.raises(TypeError):
            ProbConstraint(A, 0.5, 0.5)

    def test_lower_above_upper_rejected(self):
        with pytest.raises(ValueError, match="0 <= lower <= upper <= 1"):
            ProbConstraint(A, F(3, 4), F(1, 4))

    def test_out_of_unit_interval_rejected(self):
        with pytest.raises(ValueError):
            ProbConstraint(A, F(-1, 4), F(1, 2))
        with pytest.raises(ValueError):
            ProbConstraint(A, F(1, 2), F(5, 4))


class TestEntailmentBoundsHandChecked:
    def test_modus_ponens_interval(self):
        # P(A) = 7/10, P(A -> B) = 8/10, exactly. Worlds: (A,B) in
        # {FF, FB=notA&B, AF=A&notB, AB}. Let the four world-probabilities be
        # p00,p01,p10,p11 (p_ij = P(A=i, B=j), i/j = 1 iff true).
        #   P(A)     = p10 + p11              = 7/10
        #   P(A->B)  = p00 + p01 + p11         = 8/10   (A->B holds unless A&!B)
        #   sum      = p00+p01+p10+p11         = 1
        # Subtracting the P(A->B) equation from the sum equation:
        #   p10 = 1 - 8/10 = 1/5
        # Then from P(A) = 7/10: p11 = 7/10 - 1/5 = 1/2  (BOTH FIXED exactly —
        # two independent exact equalities pin two of the four unknowns).
        # p00 + p01 = 8/10 - p11 = 3/10, with p00, p01 >= 0 otherwise free.
        # P(B) = p01 + p11 = p01 + 1/2, p01 in [0, 3/10]
        #      => P(B) in [1/2, 1/2 + 3/10] = [1/2, 4/5].
        cs = [ProbConstraint.exact(A, F(7, 10)), ProbConstraint.exact(f("A → B"), F(8, 10))]
        bounds = entailment_bounds(cs, B)
        assert bounds == ProbBounds(F(1, 2), F(4, 5), 4)

    def test_conditional_pins_conjunction_exactly(self):
        # P(B|A) = 9/10 (conditional), P(A) = 1/2 (exact unconditional).
        # Nilsson's conditional constraint: lower*P(A) <= P(B&A) <= upper*P(A);
        # lower=upper=9/10 and P(A) is itself pinned to exactly 1/2, so
        #   P(B&A) = 9/10 * 1/2 = 9/20   exactly.
        cs = [ProbConstraint.exact(B, F(9, 10), given=A), ProbConstraint.exact(A, F(1, 2))]
        bounds = entailment_bounds(cs, f("A ∧ B"))
        assert bounds == ProbBounds(F(9, 20), F(9, 20), 4)

    def test_conditional_bounds_on_b_derived_by_hand(self):
        # Same constraints as above. P(A&B) = 9/20 is forced (see previous
        # test); P(A) = 1/2 is forced, so P(A&!B) = P(A) - P(A&B) = 1/2 - 9/20
        # = 1/20. The remaining mass 1 - P(A) = 1/2 splits freely between
        # (!A&B) and (!A&!B), each >= 0. So P(!A&B) ranges over [0, 1/2], and
        #   P(B) = P(A&B) + P(!A&B) = 9/20 + P(!A&B)
        #        in [9/20, 9/20 + 1/2] = [9/20, 19/20].
        cs = [ProbConstraint.exact(B, F(9, 10), given=A), ProbConstraint.exact(A, F(1, 2))]
        bounds = entailment_bounds(cs, B)
        assert bounds == ProbBounds(F(9, 20), F(19, 20), 4)

    def test_conditional_vacuous_when_condition_impossible(self):
        # P(A) = 0 forces every A-world's probability to 0; the conditional
        # constraint P(B|A) in [lower, upper] then degrades to
        # 0 <= P(B&A) <= 0, which P(B&A) <= P(A) = 0 already implies — so it
        # adds NOTHING, and P(B) is left completely unconstrained: [0, 1].
        cs = [ProbConstraint.exact(A, F(0)), ProbConstraint.exact(B, F(9, 10), given=A)]
        bounds = entailment_bounds(cs, B)
        assert bounds == ProbBounds(F(0), F(1), 4)

    def test_interval_constraint_passes_through_unconstrained_conclusion(self):
        # P(A) in [3/10, 6/10] with no other constraint; asking about A itself
        # must return exactly that interval back (min/max of P(A) subject only
        # to its own bound).
        cs = [ProbConstraint(A, F(3, 10), F(6, 10))]
        bounds = entailment_bounds(cs, A)
        assert bounds == ProbBounds(F(3, 10), F(6, 10), 2)

    def test_inconsistent_constraints_raise(self):
        # P(A) = 1 forces all mass onto A-worlds; P(!A) = 1 forces all mass
        # onto !A-worlds. No distribution can do both at once.
        cs = [ProbConstraint.exact(A, F(1)), ProbConstraint.exact(f("¬A"), F(1))]
        with pytest.raises(ValueError, match="probabilistically inconsistent"):
            entailment_bounds(cs, A)

    def test_quantified_formula_refused(self):
        x = Variable("x")
        quantified = Quantifier("∀", x, Atom("P", (x,)))
        with pytest.raises(ValueError):
            entailment_bounds([ProbConstraint.exact(quantified, F(1))], A)

    def test_quantified_conclusion_refused(self):
        x = Variable("x")
        quantified = Quantifier("∀", x, Atom("P", (x,)))
        with pytest.raises(ValueError):
            entailment_bounds([ProbConstraint.exact(A, F(1))], quantified)

    def test_max_atoms_refusal(self):
        atoms = [Atom(f"P{i}", ()) for i in range(13)]
        big = atoms[0]
        for a in atoms[1:]:
            big = Or(big, a)
        with pytest.raises(ValueError, match="max_atoms"):
            entailment_bounds([ProbConstraint.exact(atoms[0], F(1, 2))], big)

    def test_max_atoms_raised_explicitly_works(self):
        atoms = [Atom(f"P{i}", ()) for i in range(13)]
        big = atoms[0]
        for a in atoms[1:]:
            big = Or(big, a)
        bounds = entailment_bounds([ProbConstraint.exact(atoms[0], F(1, 2))], big, max_atoms=13)
        assert bounds.n_worlds == 2 ** 13

    def test_to_dict(self):
        bounds = ProbBounds(F(1, 2), F(3, 4), 4)
        assert bounds.to_dict() == {"lower": "1/2", "upper": "3/4", "n_worlds": 4}

    def test_xor_and_iff_are_pointwise_complements(self):
        # A xor B and A iff B disagree on EVERY world (FF: xor=F,iff=T;
        # FB: xor=T,iff=F; AF: xor=T,iff=F; AB: xor=F,iff=T) -- so
        # P(A xor B) + P(A iff B) = 1 identically, whatever the distribution.
        # Pinning P(xor) = 3/10 exactly therefore pins P(iff) = 7/10 exactly,
        # with NO freedom left, even though only the xor formula was
        # constrained -- this exercises the evaluator's Xor and Iff branches
        # together and checks they are genuine pointwise complements.
        cs = [ProbConstraint.exact(f("A ⊕ B"), F(3, 10))]
        bounds = entailment_bounds(cs, f("A ↔ B"))
        assert bounds == ProbBounds(F(7, 10), F(7, 10), 4)


class TestClassicalBoundaryDifferential:
    """Every premise pinned to P=1: bounds collapse to exactly (1,1) IFF the
    conclusion is classically entailed — cross-checked against api.prove."""

    def test_entailed_case_gives_exact_one_bounds(self):
        # {A, A->B} classically entails B (modus ponens).
        cs = [ProbConstraint.exact(A, F(1)), ProbConstraint.exact(f("A → B"), F(1))]
        bounds = entailment_bounds(cs, B)
        verdict = api.prove(B, [A, f("A → B")])
        assert bool(verdict) is True
        assert bounds == ProbBounds(F(1), F(1), 4)

    def test_non_entailed_case_gives_wider_bounds(self):
        # {A} does NOT classically entail B (a countermodel A=T, B=F exists).
        cs = [ProbConstraint.exact(A, F(1))]
        bounds = entailment_bounds(cs, B)
        verdict = api.prove(B, [A])
        assert bool(verdict) is False
        assert not (bounds.lower == bounds.upper == F(1))
        assert bounds == ProbBounds(F(0), F(1), 4)


# ===========================================================================
# distribution.py — Sato distribution semantics (ProbLog core)
# ===========================================================================

class TestProbFactValidation:
    def test_ground_atom_accepted(self):
        pf = ProbFact(Atom("Burglary", ()), F(1, 10))
        assert pf.prob == F(1, 10)

    def test_non_atom_rejected(self):
        with pytest.raises(ValueError):
            ProbFact(And(Atom("P", ()), Atom("Q", ())), F(1, 2))

    def test_non_ground_atom_rejected(self):
        x = Variable("x")
        with pytest.raises(ValueError, match="not ground"):
            ProbFact(Atom("P", (x,)), F(1, 2))

    def test_float_prob_rejected(self):
        with pytest.raises(TypeError):
            ProbFact(Atom("P", ()), 0.5)

    def test_out_of_range_prob_rejected(self):
        with pytest.raises(ValueError):
            ProbFact(Atom("P", ()), F(3, 2))


class TestProbProgramValidation:
    def test_negation_in_body_rejected(self):
        x = Variable("x")
        rule = Quantifier("∀", x, Implies(Not(Atom("P", (x,))), Atom("Q", (x,))))
        with pytest.raises(ValueError, match="conjunction of positive atoms"):
            ProbProgram(facts=[], rules=[rule])

    def test_negation_in_head_rejected(self):
        x = Variable("x")
        rule = Quantifier("∀", x, Implies(Atom("P", (x,)), Not(Atom("Q", (x,)))))
        with pytest.raises(ValueError, match="single positive Atom"):
            ProbProgram(facts=[], rules=[rule])

    def test_disjunctive_head_rejected(self):
        x = Variable("x")
        rule = Quantifier("∀", x, Implies(Atom("P", (x,)), Or(Atom("Q", (x,)), Atom("R", (x,)))))
        with pytest.raises(ValueError, match="single positive Atom"):
            ProbProgram(facts=[], rules=[rule])

    def test_disjunctive_body_rejected(self):
        x = Variable("x")
        rule = Quantifier("∀", x, Implies(Or(Atom("P", (x,)), Atom("Q", (x,))), Atom("R", (x,))))
        with pytest.raises(ValueError, match="conjunction of positive atoms"):
            ProbProgram(facts=[], rules=[rule])

    def test_existential_quantifier_rejected(self):
        x = Variable("x")
        rule = Quantifier("∃", x, Implies(Atom("P", (x,)), Atom("Q", (x,))))
        with pytest.raises(ValueError, match="non-universal quantifier"):
            ProbProgram(facts=[], rules=[rule])

    def test_free_variable_in_head_rejected(self):
        x, y = Variable("x"), Variable("y")
        rule = Quantifier("∀", x, Implies(Atom("P", (x,)), Atom("Q", (y,))))
        with pytest.raises(ValueError, match="free variable"):
            ProbProgram(facts=[], rules=[rule])

    def test_free_variable_bare_atom_rejected(self):
        x = Variable("x")
        with pytest.raises(ValueError, match="free"):
            ProbProgram(facts=[], rules=[Atom("P", (x,))])

    def test_bare_ground_atom_rule_accepted(self):
        prog = ProbProgram(facts=[], rules=[Atom("Sun", ())])
        assert query(prog, Atom("Sun", ())) == F(1)

    def test_hard_facts_validated_the_same_way(self):
        x = Variable("x")
        rule = Quantifier("∃", x, Implies(Atom("P", (x,)), Atom("Q", (x,))))
        with pytest.raises(ValueError, match="non-universal quantifier"):
            ProbProgram(facts=[], rules=[], hard_facts=[rule])

    def test_non_probfact_in_facts_rejected(self):
        with pytest.raises(ValueError):
            ProbProgram(facts=[Atom("P", ())], rules=[])


# ---------------------------------------------------------------------------
# (a) The alarm classic: burglary/earthquake independently cause alarm.
# ---------------------------------------------------------------------------

_BURGLARY = Atom("burglary", ())
_EARTHQUAKE = Atom("earthquake", ())
_ALARM = Atom("alarm", ())
_LIGHTNING = Atom("lightning", ())  # deliberately irrelevant to `alarm`, for pruning checks


def _alarm_program(with_irrelevant_fact=False):
    facts = [ProbFact(_BURGLARY, F(1, 10)), ProbFact(_EARTHQUAKE, F(1, 5))]
    if with_irrelevant_fact:
        facts.append(ProbFact(_LIGHTNING, F(1, 3)))
    rules = [Implies(_BURGLARY, _ALARM), Implies(_EARTHQUAKE, _ALARM)]
    return ProbProgram(facts=facts, rules=rules)


class TestAlarmClassic:
    def test_p_alarm_hand_checked(self):
        # alarm is true unless BOTH causes fail to fire:
        #   P(alarm) = 1 - P(!burglary)*P(!earthquake) = 1 - (9/10)*(4/5)
        #            = 1 - 36/50 = 14/50 = 7/25.
        prog = _alarm_program()
        assert query(prog, _ALARM) == F(7, 25)

    def test_p_not_alarm(self):
        prog = _alarm_program()
        assert query(prog, Not(_ALARM)) == F(1) - F(7, 25) == F(18, 25)

    def test_pruning_ignores_an_irrelevant_fact(self):
        # `lightning` never appears in any rule -- it cannot affect `alarm`,
        # so pruned and unpruned enumeration must agree exactly.
        prog = _alarm_program(with_irrelevant_fact=True)
        pruned = query(prog, _ALARM, prune=True)
        unpruned = query(prog, _ALARM, prune=False)
        assert pruned == unpruned == F(7, 25)


# ---------------------------------------------------------------------------
# (b) A chain rule quantified over variables: Wet(x) <- Rain & Outside(x).
# ---------------------------------------------------------------------------

def _rain_program(with_irrelevant_fact=False):
    x = Variable("x")
    rain = Atom("Rain", ())
    rule = Quantifier("∀", x, Implies(And(rain, Atom("Outside", (x,))), Atom("Wet", (x,))))
    facts = [ProbFact(rain, F(3, 10))]
    if with_irrelevant_fact:
        facts.append(ProbFact(Atom("Lightning", ()), F(1, 3)))
    hard_facts = [Atom("Outside", (Constant("mary"),))]  # john is deliberately NOT outside
    return ProbProgram(facts=facts, rules=[rule], hard_facts=hard_facts)


class TestRainWetChain:
    def test_wet_mary_equals_p_rain(self):
        # Outside(mary) is a hard (deterministic) fact, so Wet(mary) is
        # derivable exactly when Rain is chosen true: P(Wet(mary)) = P(Rain) = 3/10.
        prog = _rain_program()
        assert query(prog, Atom("Wet", (Constant("mary"),))) == F(3, 10)

    def test_wet_john_is_impossible(self):
        # Outside(john) is never asserted (closed-world: it is simply false in
        # every least model), so Wet(john)'s rule body is never satisfiable,
        # regardless of Rain -- P(Wet(john)) = 0.
        prog = _rain_program()
        assert query(prog, Atom("Wet", (Constant("john"),))) == F(0)

    def test_pruning_agrees_with_unpruned(self):
        prog = _rain_program(with_irrelevant_fact=True)
        goal = Atom("Wet", (Constant("mary"),))
        assert query(prog, goal, prune=True) == query(prog, goal, prune=False) == F(3, 10)


# ---------------------------------------------------------------------------
# (c) Independent coins: conjunction / disjunction goals.
# ---------------------------------------------------------------------------

_HEADS1 = Atom("Heads1", ())
_HEADS2 = Atom("Heads2", ())


def _coins_program():
    return ProbProgram(facts=[ProbFact(_HEADS1, F(1, 2)), ProbFact(_HEADS2, F(1, 2))], rules=[])


class TestIndependentCoins:
    def test_conjunction(self):
        # Independent: P(H1 & H2) = 1/2 * 1/2 = 1/4.
        prog = _coins_program()
        assert query(prog, And(_HEADS1, _HEADS2)) == F(1, 4)

    def test_disjunction(self):
        # P(H1 | H2) = 1 - P(!H1)*P(!H2) = 1 - 1/2*1/2 = 3/4.
        prog = _coins_program()
        assert query(prog, Or(_HEADS1, _HEADS2)) == F(3, 4)

    def test_pruning_agrees_with_unpruned_on_conjunction(self):
        prog = _coins_program()
        goal = And(_HEADS1, _HEADS2)
        assert query(prog, goal, prune=True) == query(prog, goal, prune=False) == F(1, 4)


# ---------------------------------------------------------------------------
# (d) Negation goal (closed-world evaluation against the least model).
# ---------------------------------------------------------------------------

class TestNegationGoal:
    def test_negated_independent_fact(self):
        prog = _coins_program()
        assert query(prog, Not(_HEADS1)) == F(1, 2)

    def test_negated_derived_atom(self):
        # !alarm iff neither cause fires: P = P(!burglary)*P(!earthquake)
        #        = 9/10 * 4/5 = 36/50 = 18/25.
        prog = _alarm_program()
        assert query(prog, Not(_ALARM)) == F(18, 25)

    def test_conjunction_with_negation(self):
        # burglary & !earthquake: 1/10 * 4/5 = 4/50 = 2/25.
        prog = _alarm_program()
        assert query(prog, And(_BURGLARY, Not(_EARTHQUAKE))) == F(2, 25)


# ---------------------------------------------------------------------------
# (e) Quantified goal, and refusal cases.
# ---------------------------------------------------------------------------

def _rain_program_two_people():
    # mary enters the constant domain via Outside(mary); john enters it via
    # the otherwise-inert Person(john) hard fact -- WITHOUT ever asserting
    # Outside(john), so grounding sees {mary, john} but john can never be wet.
    x = Variable("x")
    rain = Atom("Rain", ())
    rule = Quantifier("∀", x, Implies(And(rain, Atom("Outside", (x,))), Atom("Wet", (x,))))
    facts = [ProbFact(rain, F(3, 10))]
    hard_facts = [
        Atom("Outside", (Constant("mary"),)),
        Atom("Person", (Constant("john"),)),
    ]
    return ProbProgram(facts=facts, rules=[rule], hard_facts=hard_facts)


class TestQuantifiedGoal:
    def test_universal_goal_over_program_constants(self):
        # Domain = {mary, john}. John is never Outside, so Wet(john) can never
        # be derived regardless of Rain -- the universal goal (Wet(mary) &
        # Wet(john), after grounding) is unsatisfiable in EVERY least model,
        # so P(forall x. Wet(x)) = 0.
        prog = _rain_program_two_people()
        x = Variable("x")
        goal = Quantifier("∀", x, Atom("Wet", (x,)))
        assert query(prog, goal) == F(0)

    def test_existential_goal_over_program_constants(self):
        # Exists x. Wet(x), grounded, is Wet(mary) | Wet(john); only Wet(mary)
        # can ever be true, and exactly when Rain is chosen: P = P(Rain) = 3/10.
        prog = _rain_program_two_people()
        x = Variable("x")
        goal = Quantifier("∃", x, Atom("Wet", (x,)))
        assert query(prog, goal) == F(3, 10)


class TestQueryRefusals:
    def test_implies_goal_rejected(self):
        prog = _coins_program()
        with pytest.raises(ValueError):
            query(prog, Implies(_HEADS1, _HEADS2))

    def test_max_choice_facts_refusal(self):
        facts = [ProbFact(Atom(f"F{i}", ()), F(1, 2)) for i in range(17)]
        goal = facts[0].atom
        for pf in facts[1:]:
            goal = Or(goal, pf.atom)
        prog = ProbProgram(facts=facts, rules=[])
        with pytest.raises(ValueError, match="max_choice_facts"):
            query(prog, goal)

    def test_max_choice_facts_raised_explicitly_works(self):
        facts = [ProbFact(Atom(f"F{i}", ()), F(1, 2)) for i in range(17)]
        goal = facts[0].atom
        for pf in facts[1:]:
            goal = Or(goal, pf.atom)
        prog = ProbProgram(facts=facts, rules=[])
        # P(at least one of 17 fair coins) = 1 - (1/2)**17.
        result = query(prog, goal, max_choice_facts=17)
        assert result == F(1) - F(1, 2) ** 17

    def test_quantified_goal_over_empty_domain_rejected(self):
        prog = ProbProgram(facts=[ProbFact(Atom("P", ()), F(1, 2))], rules=[])
        x = Variable("x")
        goal = Quantifier("∀", x, Atom("Q", (x,)))
        with pytest.raises(ValueError, match="empty constant domain"):
            query(prog, goal)
